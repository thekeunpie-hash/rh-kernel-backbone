/*
 * riemannhypothesis.dev — shared behaviour for the reading pages.
 * Live strip (upstream main), the column list and the timeline. Everything that comes from a
 * data file is written with textContent; only https or same-origin links are rendered.
 */
(function () {
  "use strict";

  const UPSTREAM = "https://github.com/leanprover-community/riemann-hypothesis";
  const RAW = "https://raw.githubusercontent.com/thekeunpie-hash/rh-kernel-backbone/main/";
  const SNAPSHOT_PATH = "data/upstream_frontier.json";
  const DAY = /^\d{4}-\d{2}-\d{2}$/;

  function safeUrl(u) {
    if (!u) return "";
    try {
      const url = new URL(String(u || ""), location.href);
      return url.protocol === "https:" || url.origin === location.origin ? url.href : "";
    } catch (_) { return ""; }
  }
  function el(tag, cls, text) {
    const n = document.createElement(tag);
    if (cls) n.className = cls;
    if (text != null) n.textContent = String(text);
    return n;
  }
  function link(text, href, external) {
    const a = el("a", "", text);
    a.href = href;
    if (external) { a.target = "_blank"; a.rel = "noopener"; }
    return a;
  }
  function dayOf(s) { const d = String(s || "").slice(0, 10); return DAY.test(d) ? d : ""; }
  function validSha(v) { return typeof v === "string" && /^[a-f0-9]{7,40}$/i.test(v); }
  function shortToolchain(v) { return typeof v === "string" ? v.trim().replace(/^leanprover\/lean4:/, "").slice(0, 40) : ""; }
  function metric(v, label) { return Number.isSafeInteger(v) && v >= 0 ? v.toLocaleString("en-US") + " " + label : ""; }

  // The tracker snapshot is fetched once per page and shared by the live strip and the timeline.
  let snapshotPromise = null;
  function loadSnapshot() {
    if (!snapshotPromise) {
      snapshotPromise = (async function () {
        try {
          const r = await fetch(RAW + SNAPSHOT_PATH, { credentials: "omit", cache: "no-cache" });
          if (!r.ok) return null;
          const j = await r.json();
          return j && typeof j === "object" ? j : null;
        } catch (_) { return null; }
      })();
    }
    return snapshotPromise;
  }

  async function loadColumns() {
    try {
      const r = await fetch("data/columns.json", { cache: "no-cache" });
      if (!r.ok) return [];
      const j = await r.json();
      return (Array.isArray(j.columns) ? j.columns : [])
        .map((c) => ({ ...c, date: dayOf(c.date), href: safeUrl(c.href) }))
        .filter((c) => c.date && c.href && c.title)
        .sort((a, b) => b.date.localeCompare(a.date));
    } catch (_) { return []; }
  }

  async function loadEvents() {
    const j = await loadSnapshot();
    if (!j) throw new Error("snapshot unavailable");
    return (Array.isArray(j.community_timeline) ? j.community_timeline : [])
      .map((e) => ({ ...e, date: dayOf(e.date), url: safeUrl(e.url) }))
      .filter((e) => e.date && e.title);
  }

  function columnMeta(c) {
    return [c.date, c.kicker, c.language].filter(Boolean).join(" · ");
  }

  function renderColumnList(list, cols) {
    if (!list || !cols.length) return;
    list.replaceChildren();
    for (const c of cols) {
      const li = el("li");
      li.append(el("span", "item-meta", columnMeta(c)));
      const t = el("span", "item-title");
      const a = link(c.title, c.href);
      if (c.lang) a.lang = c.lang;
      t.append(a);
      li.append(t);
      if (c.summary) {
        const p = el("p", "", c.summary);
        if (c.lang) p.lang = c.lang;
        li.append(p);
      }
      list.append(li);
    }
  }

  // opts.limit: show only the newest N upstream events (the home page); columns are then left out.
  function renderTimeline(list, events, cols, opts) {
    if (!list) return;
    const limit = opts && opts.limit ? opts.limit : 0;
    const byDay = new Map();
    const add = (d, item) => { if (!byDay.has(d)) byDay.set(d, []); byDay.get(d).push(item); };
    if (!limit) for (const c of cols || []) add(c.date, { column: true, ...c });
    const shown = limit
      ? events.slice().sort((a, b) => b.date.localeCompare(a.date)).slice(0, limit)
      : events;
    for (const e of shown) add(e.date, e);
    const days = [...byDay.keys()].sort((a, b) => b.localeCompare(a));
    list.replaceChildren();
    for (const d of days) {
      const day = el("li", "day");
      const time = el("time", "day-date", d);
      time.dateTime = d;
      day.append(time);
      const evs = el("ul", "events");
      for (const it of byDay.get(d)) {
        const li = el("li", "event" + (it.column ? " is-column" : ""));
        if (it.column) {
          li.append(el("span", "event-tag", "Column"));
          const t = el("span", "event-title");
          const a = link(it.title, it.href);
          if (it.lang) a.lang = it.lang;
          t.append(a);
          li.append(t);
        } else {
          if (it.tag) li.append(el("span", "event-tag", it.tag));
          li.append(el("span", "event-title", it.title));
          if (limit) {
            if (it.url) {
              const p = el("p", "event-source");
              p.append(link("Source on GitHub", it.url, true));
              li.append(p);
            }
          } else if (it.detail || it.url) {
            const det = el("details");
            det.append(el("summary", "", "Details and source"));
            if (it.detail) det.append(el("p", "event-detail", it.detail));
            if (it.url) {
              const p = el("p", "event-source");
              p.append(link("Source on GitHub", it.url, true));
              det.append(p);
            }
            li.append(det);
          }
        }
        evs.append(li);
      }
      day.append(evs);
      list.append(day);
    }
  }

  // Fills the strip with the tracker's last snapshot of upstream main, then asks GitHub whether
  // main has moved since. Resolves to the snapshot's live_main object (or null).
  async function liveStrip(strip) {
    function show(sha, parts) {
      if (!strip) return;
      const strong = el("strong");
      strong.append("main@", link(sha.slice(0, 9), UPSTREAM + "/commit/" + sha, true));
      strip.replaceChildren(strong, " · " + parts.filter(Boolean).join(" · "));
    }

    let live = null;
    const j = await loadSnapshot();
    if (j && j.live_main && validSha(j.live_main.sha)) {
      live = j.live_main;
      show(live.sha, [
        "tracker snapshot", shortToolchain(live.toolchain),
        metric(live.lean_files, "Lean files"), metric(live.total_lines, "raw lines")
      ]);
    }

    try {
      const r = await fetch("https://api.github.com/repos/leanprover-community/riemann-hypothesis/commits/main", { credentials: "omit" });
      if (r.ok) {
        const { sha } = await r.json();
        if (validSha(sha) && !(live && sha.startsWith(live.sha))) {
          let toolchain = "";
          try {
            const t = await fetch("https://raw.githubusercontent.com/leanprover-community/riemann-hypothesis/" + sha + "/lean-toolchain", { credentials: "omit" });
            if (t.ok) toolchain = shortToolchain(await t.text());
          } catch (_) {}
          show(sha, ["latest commit on GitHub", toolchain]);
        }
      }
    } catch (_) {}
    return live;
  }

  window.RHSite = { liveStrip, loadColumns, loadEvents, renderColumnList, renderTimeline, metric };
})();
