#!/usr/bin/env python3
"""Fetch upstream pull request metadata insights for leanprover-community/riemann-hypothesis.

Collects open PRs and recently merged PRs (default 14 days) via GitHub GraphQL
when GITHUB_TOKEN or GH_TOKEN is available, with a rate-limit-aware REST fallback
when unauthenticated. Computes factual size, age, review-wait, triage-wait,
time-to-merge, and batch-PR membership metrics without scoring or priority advice.

Pure Python 3.11+ stdlib only. Run:
  python scripts/fetch_upstream_pr_insights.py [--data data/upstream_pr_insights.json]
"""

from __future__ import annotations

import argparse
import json
import os
import re
import statistics
import time
import urllib.error
import urllib.request
from datetime import datetime, timedelta, timezone
from pathlib import Path

DEFAULT_REPO = "leanprover-community/riemann-hypothesis"
DEFAULT_DATA = "data/upstream_pr_insights.json"
DEFAULT_DAYS = 14
# An unchanged fetch restamps generated_at once the stamp is this old (when no --min-interval-minutes is given).
STAMP_REFRESH_MINUTES = 50.0
GRAPHQL_URL = "https://api.github.com/graphql"
REST_API_BASE = "https://api.github.com"
USER_AGENT = "rh-kernel-backbone-pr-insights/1.0"

GRAPHQL_QUERY = """
query($owner: String!, $name: String!, $states: [PullRequestState!], $first: Int!, $cursor: String) {
  rateLimit {
    cost
    remaining
    limit
  }
  repository(owner: $owner, name: $name) {
    pullRequests(
      states: $states
      first: $first
      orderBy: {field: UPDATED_AT, direction: DESC}
      after: $cursor
    ) {
      pageInfo {
        hasNextPage
        endCursor
      }
      nodes {
        number
        title
        state
        isDraft
        createdAt
        updatedAt
        mergedAt
        closedAt
        baseRefName
        headRefName
        changedFiles
        additions
        deletions
        url
        body
        author {
          __typename
          login
        }
        labels(first: 8) {
          nodes {
            name
          }
        }
        reviews(first: 8) {
          totalCount
          nodes {
            state
            submittedAt
            author {
              __typename
              login
            }
          }
        }
        reviewRequests(first: 3) {
          totalCount
        }
        comments(first: 8) {
          totalCount
          nodes {
            createdAt
            author {
              __typename
              login
            }
          }
        }
        timelineItems(first: 4, itemTypes: [REVIEW_REQUESTED_EVENT, READY_FOR_REVIEW_EVENT]) {
          nodes {
            __typename
            ... on ReviewRequestedEvent {
              createdAt
            }
            ... on ReadyForReviewEvent {
              createdAt
            }
          }
        }
      }
    }
  }
}
"""

_EXCLUSION_SPLIT_RE = re.compile(
    r"(?im)^(?:#{1,6}\s*|\*{1,2})?(?:two prs from [^\n]* are not included|not included|excluded|left out|changes since the last version)\s*:?\*{0,2}"
)
_TABLE_PR_RE = re.compile(r"^\s*\|\s*(?:\[)?#(\d+)\b")
_BULLET_PR_RE = re.compile(
    r"^\s*[-*]\s+(?:\[[ xX]\]\s+)?(?:\[)?(?:https://github\.com/[^/\s]+/[^/\s]+/pull/(\d+)|#(\d+)\b)"
)
_BATCH_TITLE_RE = re.compile(
    r"(?:^batch\b|\bbatch of \d+|cleanup batch|consolidation batch|^chore:\s*batch\b|\bbatch\b.*\b(?:prs?|bundle)\b)",
    re.IGNORECASE,
)


def parse_iso(value: str | None) -> datetime | None:
    if not value or not isinstance(value, str):
        return None
    try:
        return datetime.fromisoformat(value.replace("Z", "+00:00")).astimezone(timezone.utc)
    except ValueError:
        return None


def fmt_iso(dt: datetime | None) -> str | None:
    if dt is None:
        return None
    return dt.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def classify_blast_radius(changed_files: int | None) -> str | None:
    if changed_files is None:
        return None
    if changed_files >= 50000:
        return "whole-tree"
    if changed_files >= 2000:
        return "major"
    if changed_files >= 200:
        return "batch"
    return "focused"


def extract_batch_members(body: str | None, self_number: int) -> list[int]:
    if not body:
        return []
    included_section = _EXCLUSION_SPLIT_RE.split(body, maxsplit=1)[0]
    seen: set[int] = set()
    members: list[int] = []
    for line in included_section.splitlines():
        candidate: int | None = None
        table_match = _TABLE_PR_RE.match(line)
        if table_match:
            candidate = int(table_match.group(1))
        else:
            bullet_match = _BULLET_PR_RE.match(line)
            if bullet_match:
                num_str = bullet_match.group(1) or bullet_match.group(2)
                if num_str:
                    candidate = int(num_str)
        if candidate is not None and candidate != self_number and candidate not in seen:
            seen.add(candidate)
            members.append(candidate)
    return members


def is_batch_pr(title: str, head_ref: str, member_prs: list[int]) -> bool:
    if len(member_prs) < 2:
        return False
    if head_ref.startswith("batch/"):
        return True
    return bool(_BATCH_TITLE_RE.search(title or ""))


def _is_human_non_author(author: dict | None, pr_author: str | None) -> bool:
    if not isinstance(author, dict):
        return False
    login = (author.get("login") or "").strip()
    if not login:
        return False
    if author.get("__typename") == "Bot" or author.get("type") == "Bot" or login.endswith("[bot]"):
        return False
    if pr_author and login == pr_author:
        return False
    return True


def _hours_between(start: datetime | None, end: datetime | None) -> float | None:
    if start is None or end is None:
        return None
    return round(max(0.0, (end - start).total_seconds() / 3600.0), 2)


def _median(values: list[float | int]) -> float | None:
    if not values:
        return None
    return round(float(statistics.median(values)), 2)


def _percentile(values: list[float | int], q: float) -> float | None:
    if not values:
        return None
    ordered = sorted(float(v) for v in values)
    if len(ordered) == 1:
        return round(ordered[0], 2)
    pos = q * (len(ordered) - 1)
    lo = int(pos)
    hi = min(lo + 1, len(ordered) - 1)
    frac = pos - lo
    return round(ordered[lo] * (1.0 - frac) + ordered[hi] * frac, 2)


def build_pr_record(raw: dict, now: datetime) -> tuple[dict, list[int]]:
    """Normalize a raw PR dict (from GraphQL or REST) into output record + batch members."""
    number = int(raw["number"])
    title = raw.get("title") or ""
    author = raw.get("author") or "unknown"
    state = raw["state"]  # "open" | "merged"
    draft = bool(raw.get("draft"))
    base_ref = raw.get("base_ref") or "main"
    head_ref = raw.get("head_ref") or ""
    labels = list(raw.get("labels") or [])
    batch_queue_label = "batch queue" in labels
    changed_files = raw.get("changed_files")
    additions = raw.get("additions")
    deletions = raw.get("deletions")
    blast_radius = classify_blast_radius(changed_files)

    created_dt = parse_iso(raw.get("created_at"))
    updated_dt = parse_iso(raw.get("updated_at"))
    merged_dt = parse_iso(raw.get("merged_at"))
    ready_dt = parse_iso(raw.get("ready_for_review_at"))
    review_req_dt = parse_iso(raw.get("review_requested_at"))
    first_review_dt = parse_iso(raw.get("first_review_at"))
    first_triage_dt = parse_iso(raw.get("first_triage_at"))
    if first_review_dt and (first_triage_dt is None or first_review_dt < first_triage_dt):
        first_triage_dt = first_review_dt

    review_count = int(raw.get("review_count") or 0)
    review_requests_count = int(raw.get("review_requests_count") or 0)

    if draft and review_requests_count == 0 and review_req_dt is None:
        wait_start = None
    elif review_req_dt and ready_dt:
        wait_start = max(review_req_dt, ready_dt)
    elif review_req_dt:
        wait_start = review_req_dt
    elif ready_dt:
        wait_start = ready_dt
    else:
        wait_start = created_dt

    if wait_start is None:
        review_wait_source = "draft"
        review_wait_hours = None
        triage_wait_hours = None
    else:
        if first_review_dt is not None:
            review_wait_source = "first_review"
            review_wait_hours = _hours_between(wait_start, first_review_dt)
        elif state == "open":
            review_wait_source = "awaiting_review"
            review_wait_hours = _hours_between(wait_start, now)
        else:
            review_wait_source = "merged_without_review"
            review_wait_hours = None

        if first_triage_dt is not None:
            triage_wait_hours = _hours_between(wait_start, first_triage_dt)
        elif state == "open":
            triage_wait_hours = _hours_between(wait_start, now)
        else:
            triage_wait_hours = _hours_between(created_dt, merged_dt)

    member_prs = extract_batch_members(raw.get("body"), number)
    batch_flag = is_batch_pr(title, head_ref, member_prs)
    if not batch_flag:
        member_prs = []

    record = {
        "number": number,
        "title": title,
        "author": author,
        "state": state,
        "draft": draft,
        "base_ref": base_ref,
        "head_ref": head_ref,
        "labels": labels,
        "batch_queue_label": batch_queue_label,
        "changed_files": changed_files,
        "additions": additions,
        "deletions": deletions,
        "blast_radius": blast_radius,
        "created_at": fmt_iso(created_dt),
        "updated_at": fmt_iso(updated_dt),
        "ready_for_review_at": fmt_iso(ready_dt),
        "review_requested_at": fmt_iso(review_req_dt),
        "first_review_at": fmt_iso(first_review_dt),
        "first_triage_at": fmt_iso(first_triage_dt),
        "review_count": review_count,
        "review_wait_source": review_wait_source,
        "review_wait_hours": review_wait_hours,
        "triage_wait_hours": triage_wait_hours,
        "is_batch_pr": batch_flag,
        "batch_member_count": len(member_prs),
        "batch_prs": [],
        "in_open_batch": False,
        "merged_via_batch": None,
        "url": raw.get("url") or "",
    }
    if state == "open":
        record["open_age_hours"] = _hours_between(created_dt, now)
    else:
        record["merged_at"] = fmt_iso(merged_dt)
        record["time_to_merge_hours"] = _hours_between(created_dt, merged_dt)

    return record, member_prs


def _graphql_request(query: str, variables: dict, token: str) -> dict:
    payload = json.dumps({"query": query, "variables": variables}).encode("utf-8")
    last_exc: Exception | None = None
    for attempt in range(3):
        req = urllib.request.Request(
            GRAPHQL_URL,
            data=payload,
            method="POST",
            headers={
                "Authorization": f"Bearer {token}",
                "Content-Type": "application/json",
                "Accept": "application/vnd.github+json",
                "User-Agent": USER_AGENT,
            },
        )
        try:
            with urllib.request.urlopen(req, timeout=45) as resp:
                data = json.loads(resp.read().decode("utf-8"))
            if data.get("errors"):
                raise RuntimeError(f"GraphQL errors: {data['errors']}")
            return data["data"]
        except urllib.error.HTTPError as exc:
            last_exc = exc
            if exc.code in (502, 503, 504) and attempt < 2:
                time.sleep(1.5 * (attempt + 1))
                continue
            raise
        except (urllib.error.URLError, TimeoutError) as exc:
            last_exc = exc
            if attempt < 2:
                time.sleep(1.5 * (attempt + 1))
                continue
            raise
    raise RuntimeError(f"GraphQL request failed: {last_exc}")


def _normalize_graphql_node(node: dict) -> dict:
    pr_author = (node.get("author") or {}).get("login") or "unknown"
    labels = [lb["name"] for lb in ((node.get("labels") or {}).get("nodes") or []) if lb and lb.get("name")]

    human_review_times: list[str] = []
    for rev in (node.get("reviews") or {}).get("nodes") or []:
        if rev and rev.get("submittedAt") and _is_human_non_author(rev.get("author"), pr_author):
            human_review_times.append(rev["submittedAt"])

    human_comment_times: list[str] = []
    for cmt in (node.get("comments") or {}).get("nodes") or []:
        if cmt and cmt.get("createdAt") and _is_human_non_author(cmt.get("author"), pr_author):
            human_comment_times.append(cmt["createdAt"])

    review_req_times: list[str] = []
    ready_times: list[str] = []
    for ev in (node.get("timelineItems") or {}).get("nodes") or []:
        if not isinstance(ev, dict):
            continue
        tname = ev.get("__typename")
        ts = ev.get("createdAt")
        if tname == "ReviewRequestedEvent" and ts:
            review_req_times.append(ts)
        elif tname == "ReadyForReviewEvent" and ts:
            ready_times.append(ts)

    all_triage_times = human_review_times + human_comment_times
    return {
        "number": node["number"],
        "title": node.get("title") or "",
        "author": pr_author,
        "state": "merged" if node.get("mergedAt") else "open",
        "draft": bool(node.get("isDraft")),
        "base_ref": node.get("baseRefName") or "main",
        "head_ref": node.get("headRefName") or "",
        "labels": labels,
        "changed_files": node.get("changedFiles"),
        "additions": node.get("additions"),
        "deletions": node.get("deletions"),
        "created_at": node.get("createdAt"),
        "updated_at": node.get("updatedAt"),
        "merged_at": node.get("mergedAt"),
        "ready_for_review_at": max(ready_times) if ready_times else None,
        "review_requested_at": min(review_req_times) if review_req_times else None,
        "first_review_at": min(human_review_times) if human_review_times else None,
        "first_triage_at": min(all_triage_times) if all_triage_times else None,
        "review_count": len(human_review_times),
        "review_requests_count": (node.get("reviewRequests") or {}).get("totalCount") or 0,
        "body": node.get("body") or "",
        "url": node.get("url") or "",
    }


def fetch_via_graphql(owner: str, name: str, cutoff_dt: datetime, token: str) -> tuple[list[dict], list[dict]]:
    open_raw: list[dict] = []
    merged_raw: list[dict] = []
    total_cost = 0
    last_remaining: int | None = None

    for state_arg, stop_on_cutoff in (("OPEN", False), ("MERGED", True)):
        cursor: str | None = None
        page_size = 25
        while True:
            try:
                data = _graphql_request(
                    GRAPHQL_QUERY,
                    {"owner": owner, "name": name, "states": [state_arg], "first": page_size, "cursor": cursor},
                    token,
                )
            except urllib.error.HTTPError as exc:
                if exc.code in (502, 503, 504) and page_size > 10:
                    page_size = 10
                    continue
                raise
            except (urllib.error.URLError, TimeoutError):
                if page_size > 10:
                    page_size = 10
                    continue
                raise
            rl = data.get("rateLimit") or {}
            total_cost += int(rl.get("cost") or 0)
            if rl.get("remaining") is not None:
                last_remaining = int(rl["remaining"])

            pr_conn = ((data.get("repository") or {}).get("pullRequests")) or {}
            nodes = pr_conn.get("nodes") or []
            if not nodes:
                break

            reached_cutoff = False
            for node in nodes:
                if not node:
                    continue
                if stop_on_cutoff:
                    upd = parse_iso(node.get("updatedAt"))
                    mrg = parse_iso(node.get("mergedAt"))
                    if upd and upd < cutoff_dt:
                        reached_cutoff = True
                    if mrg and mrg >= cutoff_dt:
                        merged_raw.append(_normalize_graphql_node(node))
                else:
                    open_raw.append(_normalize_graphql_node(node))

            page_info = pr_conn.get("pageInfo") or {}
            if reached_cutoff or not page_info.get("hasNextPage"):
                break
            cursor = page_info.get("endCursor")

    print(
        f"GraphQL fetch complete: {len(open_raw)} open, {len(merged_raw)} merged in window "
        f"(rateLimit cost={total_cost}, remaining={last_remaining})."
    )
    return open_raw, merged_raw


def _rest_get(path: str, token: str = "") -> tuple[object, int | None]:
    headers = {
        "User-Agent": USER_AGENT,
        "Accept": "application/vnd.github+json",
    }
    if token:
        headers["Authorization"] = f"Bearer {token}"
    req = urllib.request.Request(f"{REST_API_BASE}/{path.lstrip('/')}", headers=headers)
    with urllib.request.urlopen(req, timeout=30) as resp:
        rem_hdr = resp.headers.get("X-RateLimit-Remaining")
        remaining = int(rem_hdr) if rem_hdr is not None and rem_hdr.isdigit() else None
        return json.loads(resp.read().decode("utf-8")), remaining


def fetch_via_rest(
    owner: str,
    name: str,
    cutoff_dt: datetime,
    token: str,
    cached_by_num: dict[int, dict],
) -> tuple[list[dict], list[dict]]:
    _, remaining = _rest_get("rate_limit", token)
    if remaining is not None and remaining < 10:
        raise RuntimeError(f"GitHub REST rate limit too low (remaining={remaining})")

    open_items: list[dict] = []
    for page in range(1, 15):
        batch, remaining = _rest_get(
            f"repos/{owner}/{name}/pulls?state=open&sort=updated&direction=desc&per_page=100&page={page}",
            token,
        )
        if not isinstance(batch, list) or not batch:
            break
        open_items.extend(batch)
        if len(batch) < 100 or (remaining is not None and remaining <= 5):
            break

    merged_items: list[dict] = []
    for page in range(1, 10):
        batch, remaining = _rest_get(
            f"repos/{owner}/{name}/pulls?state=closed&sort=updated&direction=desc&per_page=100&page={page}",
            token,
        )
        if not isinstance(batch, list) or not batch:
            break
        stop = False
        for item in batch:
            upd = parse_iso(item.get("updated_at"))
            mrg = parse_iso(item.get("merged_at"))
            if upd and upd < cutoff_dt:
                stop = True
            if mrg and mrg >= cutoff_dt:
                merged_items.append(item)
        if stop or len(batch) < 100 or (remaining is not None and remaining <= 5):
            break

    hydrated_count = 0
    max_detail_prs = 25

    def _to_raw(item: dict) -> dict:
        nonlocal remaining, hydrated_count
        num = int(item["number"])
        cached = cached_by_num.get(num)
        same_updated = bool(cached and cached.get("updated_at") == fmt_iso(parse_iso(item.get("updated_at"))))

        changed_files = cached.get("changed_files") if same_updated else None
        additions = cached.get("additions") if same_updated else None
        deletions = cached.get("deletions") if same_updated else None
        first_review_at = cached.get("first_review_at") if same_updated else None
        first_triage_at = cached.get("first_triage_at") if same_updated else None
        review_count = cached.get("review_count", 0) if same_updated else 0
        ready_at = cached.get("ready_for_review_at") if same_updated else None
        review_req_at = cached.get("review_requested_at") if same_updated else None

        if not same_updated and hydrated_count < max_detail_prs and (remaining is None or remaining >= 20):
            try:
                detail, remaining = _rest_get(f"repos/{owner}/{name}/pulls/{num}", token)
                if isinstance(detail, dict):
                    changed_files = detail.get("changed_files")
                    additions = detail.get("additions")
                    deletions = detail.get("deletions")
                    hydrated_count += 1
            except Exception:
                pass

        pr_author = (item.get("user") or {}).get("login") or "unknown"
        labels = [lb["name"] for lb in (item.get("labels") or []) if isinstance(lb, dict) and lb.get("name")]
        return {
            "number": num,
            "title": item.get("title") or "",
            "author": pr_author,
            "state": "merged" if item.get("merged_at") else "open",
            "draft": bool(item.get("draft")),
            "base_ref": (item.get("base") or {}).get("ref") or "main",
            "head_ref": (item.get("head") or {}).get("ref") or "",
            "labels": labels,
            "changed_files": changed_files,
            "additions": additions,
            "deletions": deletions,
            "created_at": item.get("created_at"),
            "updated_at": item.get("updated_at"),
            "merged_at": item.get("merged_at"),
            "ready_for_review_at": ready_at,
            "review_requested_at": review_req_at,
            "first_review_at": first_review_at,
            "first_triage_at": first_triage_at,
            "review_count": review_count,
            "review_requests_count": len(item.get("requested_reviewers") or []),
            "body": item.get("body") or "",
            "url": item.get("html_url") or "",
        }

    open_raw = [_to_raw(it) for it in open_items]
    merged_raw = [_to_raw(it) for it in merged_items]
    print(
        f"REST fallback fetch complete: {len(open_raw)} open, {len(merged_raw)} merged "
        f"(hydrated={hydrated_count}, remaining={remaining})."
    )
    return open_raw, merged_raw


def assemble_payload(
    repo: str,
    window_days: int,
    now: datetime,
    cutoff_dt: datetime,
    source_mode: str,
    open_raw: list[dict],
    merged_raw: list[dict],
) -> dict:
    open_prs: list[dict] = []
    merged_prs: list[dict] = []
    batch_members_by_num: dict[int, list[int]] = {}
    all_records_by_num: dict[int, dict] = {}

    for raw in open_raw:
        rec, members = build_pr_record(raw, now)
        open_prs.append(rec)
        all_records_by_num[rec["number"]] = rec
        if rec["is_batch_pr"]:
            batch_members_by_num[rec["number"]] = members

    for raw in merged_raw:
        rec, members = build_pr_record(raw, now)
        merged_prs.append(rec)
        all_records_by_num[rec["number"]] = rec
        if rec["is_batch_pr"]:
            batch_members_by_num[rec["number"]] = members

    open_nums = {p["number"] for p in open_prs}
    merged_nums = {p["number"] for p in merged_prs}

    # Reverse-map batch membership onto every PR.
    member_to_batches: dict[int, list[int]] = {}
    for batch_num, members in batch_members_by_num.items():
        for m in members:
            member_to_batches.setdefault(m, []).append(batch_num)

    for pr_num, rec in all_records_by_num.items():
        batches_for_pr = sorted(member_to_batches.get(pr_num, []))
        rec["batch_prs"] = batches_for_pr
        rec["in_open_batch"] = any(
            all_records_by_num[b]["state"] == "open" for b in batches_for_pr if b in all_records_by_num
        )
        merged_batches = [
            b for b in batches_for_pr if b in all_records_by_num and all_records_by_num[b]["state"] == "merged"
        ]
        if rec["state"] == "merged" and merged_batches:
            rec["merged_via_batch"] = max(merged_batches)

    batches: list[dict] = []
    for batch_num, members in batch_members_by_num.items():
        rec = all_records_by_num[batch_num]
        batches.append(
            {
                "number": batch_num,
                "state": rec["state"],
                "title": rec["title"],
                "author": rec["author"],
                "head_ref": rec["head_ref"],
                "base_ref": rec["base_ref"],
                "created_at": rec["created_at"],
                "merged_at": rec.get("merged_at"),
                "changed_files": rec["changed_files"],
                "member_count": len(members),
                "member_prs": members,
                "open_member_count": sum(1 for m in members if m in open_nums),
                "merged_member_count": sum(1 for m in members if m in merged_nums),
                "url": rec["url"],
            }
        )

    batches.sort(key=lambda b: (0 if b["state"] == "open" else 1, -b["number"]))
    open_prs.sort(key=lambda p: (-(p["changed_files"] if p["changed_files"] is not None else -1), -p["number"]))
    merged_prs.sort(key=lambda p: (p.get("merged_at") or "", p["number"]), reverse=True)

    size_buckets_open = {"1": 0, "2-10": 0, "11-100": 0, "101-1000": 0, "1001+": 0}
    blast_radius_open = {"focused": 0, "batch": 0, "major": 0, "whole_tree": 0}
    for p in open_prs:
        cf = p["changed_files"]
        if cf is not None:
            if cf <= 1:
                size_buckets_open["1"] += 1
            elif cf <= 10:
                size_buckets_open["2-10"] += 1
            elif cf <= 100:
                size_buckets_open["11-100"] += 1
            elif cf <= 1000:
                size_buckets_open["101-1000"] += 1
            else:
                size_buckets_open["1001+"] += 1
        br = p["blast_radius"]
        if br == "whole-tree":
            blast_radius_open["whole_tree"] += 1
        elif br in blast_radius_open:
            blast_radius_open[br] += 1

    open_cf = [p["changed_files"] for p in open_prs if p["changed_files"] is not None]
    open_age = [p["open_age_hours"] for p in open_prs if p["open_age_hours"] is not None]
    open_rw = [p["review_wait_hours"] for p in open_prs if p["review_wait_hours"] is not None]
    open_tw = [p["triage_wait_hours"] for p in open_prs if p["triage_wait_hours"] is not None]
    merged_ttm = [p["time_to_merge_hours"] for p in merged_prs if p["time_to_merge_hours"] is not None]
    merged_rw = [p["review_wait_hours"] for p in merged_prs if p["review_wait_hours"] is not None]
    merged_tw = [p["triage_wait_hours"] for p in merged_prs if p["triage_wait_hours"] is not None]

    summary = {
        "open_count": len(open_prs),
        "open_draft_count": sum(1 for p in open_prs if p["draft"]),
        "open_batch_queue_count": sum(1 for p in open_prs if p["batch_queue_label"]),
        "open_awaiting_review_count": sum(1 for p in open_prs if p["review_wait_source"] == "awaiting_review"),
        "open_in_batch_pr_count": sum(1 for p in open_prs if p["in_open_batch"]),
        "merged_14d_count": len(merged_prs),
        "merged_via_batch_count": sum(1 for p in merged_prs if p["merged_via_batch"] is not None),
        "active_batch_pr_count": sum(1 for b in batches if b["state"] == "open"),
        "merged_batch_pr_14d_count": sum(1 for b in batches if b["state"] == "merged"),
        "open_changed_files_median": _median(open_cf),
        "open_changed_files_p90": _percentile(open_cf, 0.90),
        "open_changed_files_max": max(open_cf) if open_cf else None,
        "open_age_hours_median": _median(open_age),
        "open_age_hours_p90": _percentile(open_age, 0.90),
        "open_review_wait_hours_median": _median(open_rw),
        "open_review_wait_hours_p90": _percentile(open_rw, 0.90),
        "open_triage_wait_hours_median": _median(open_tw),
        "open_triage_wait_hours_p90": _percentile(open_tw, 0.90),
        "merged_time_to_merge_hours_median": _median(merged_ttm),
        "merged_time_to_merge_hours_p90": _percentile(merged_ttm, 0.90),
        "merged_review_wait_hours_median": _median(merged_rw),
        "merged_triage_wait_hours_median": _median(merged_tw),
        "size_buckets_open": size_buckets_open,
        "blast_radius_open": blast_radius_open,
    }

    return {
        "generated_at": fmt_iso(now),
        "repo": repo,
        "window_days": window_days,
        "cutoff_at": fmt_iso(cutoff_dt),
        "source_mode": source_mode,
        "summary": summary,
        "batches": batches,
        "open_prs": open_prs,
        "merged_prs": merged_prs,
    }


def _strip_volatile(payload: dict) -> dict:
    copy = dict(payload)
    copy.pop("generated_at", None)
    return copy


def main() -> int:
    parser = argparse.ArgumentParser(description="Fetch upstream GitHub PR metadata insights.")
    parser.add_argument("--data", default=DEFAULT_DATA, help="Output JSON path")
    parser.add_argument("--repo", default=DEFAULT_REPO, help="GitHub owner/name repository")
    parser.add_argument("--days", type=int, default=DEFAULT_DAYS, help="Merged PR lookback window in days")
    parser.add_argument(
        "--min-interval-minutes",
        type=float,
        default=0.0,
        help="Skip API calls if existing output generated_at is newer than N minutes",
    )
    args = parser.parse_args()

    out_path = Path(args.data)
    now = datetime.now(timezone.utc)
    cutoff_dt = now - timedelta(days=args.days)

    existing_payload: dict | None = None
    if out_path.exists():
        try:
            existing_payload = json.loads(out_path.read_text(encoding="utf-8"))
        except Exception:
            existing_payload = None

    if args.min_interval_minutes > 0 and isinstance(existing_payload, dict):
        prev_dt = parse_iso(existing_payload.get("generated_at"))
        if prev_dt is not None:
            age_min = (now - prev_dt).total_seconds() / 60.0
            if age_min < args.min_interval_minutes:
                print(
                    f"Skipping PR insights fetch: {out_path} generated {age_min:.1f}m ago "
                    f"(< {args.min_interval_minutes:.1f}m)."
                )
                return 0

    if "/" not in args.repo:
        raise SystemExit(f"Invalid --repo format (expected owner/name): {args.repo}")
    owner, name = args.repo.split("/", 1)
    token = (os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN") or "").strip()

    cached_by_num: dict[int, dict] = {}
    if isinstance(existing_payload, dict):
        for group_key in ("open_prs", "merged_prs"):
            for item in existing_payload.get(group_key) or []:
                if isinstance(item, dict) and item.get("number") is not None:
                    cached_by_num[int(item["number"])] = item

    open_raw: list[dict]
    merged_raw: list[dict]
    source_mode: str

    try:
        if token:
            try:
                open_raw, merged_raw = fetch_via_graphql(owner, name, cutoff_dt, token)
                source_mode = "graphql"
            except Exception as exc:
                print(f"GraphQL fetch failed ({exc}); falling back to REST.")
                open_raw, merged_raw = fetch_via_rest(owner, name, cutoff_dt, token, cached_by_num)
                source_mode = "rest"
        else:
            open_raw, merged_raw = fetch_via_rest(owner, name, cutoff_dt, "", cached_by_num)
            source_mode = "rest"
    except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError, RuntimeError, ValueError) as exc:
        if existing_payload is not None and out_path.exists():
            print(f"Fetch failed ({exc}); keeping previous {out_path}.")
            return 0
        raise SystemExit(f"Fetch failed and no previous data at {out_path}: {exc}")

    payload = assemble_payload(
        repo=args.repo,
        window_days=args.days,
        now=now,
        cutoff_dt=cutoff_dt,
        source_mode=source_mode,
        open_raw=open_raw,
        merged_raw=merged_raw,
    )

    if isinstance(existing_payload, dict) and _strip_volatile(payload) == _strip_volatile(existing_payload):
        # generated_at is the --min-interval-minutes guard's only clock. Left untouched on an unchanged fetch, it ages
        # past the interval in a quiet hour and every 10-minute periodic run calls the API again. Restamp an old stamp
        # (at most one timestamp-only write per interval); a fresh one is kept so push/manual runs add no churn.
        refresh_after = args.min_interval_minutes if args.min_interval_minutes > 0 else STAMP_REFRESH_MINUTES
        prev_dt = parse_iso(existing_payload.get("generated_at"))
        age_min = (now - prev_dt).total_seconds() / 60.0 if prev_dt is not None else None
        if age_min is not None and 0 <= age_min < refresh_after:
            print(f"No PR insight changes for {args.repo}; skipping write.")
            return 0
        payload = dict(existing_payload, generated_at=fmt_iso(now))
        print(f"No PR insight changes for {args.repo}; refreshing generated_at only.")

    out_path.parent.mkdir(parents=True, exist_ok=True)
    tmp_path = out_path.with_name(f".{out_path.name}.{os.getpid()}.{int(time.time())}.tmp")
    tmp_path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8", newline="\n")
    os.replace(tmp_path, out_path)

    s = payload["summary"]
    print(
        f"Wrote {out_path} ({source_mode}): {s['open_count']} open, {s['merged_14d_count']} merged ({args.days}d), "
        f"{s['active_batch_pr_count']} active batches, {s['merged_batch_pr_14d_count']} merged batches."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
