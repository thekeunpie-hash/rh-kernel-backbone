/*
 * riemannhypothesis.dev — shared behaviour for the reading pages.
 * Live strip (upstream main), the measured facts, the column cards, the merged timeline and the
 * figure on the home page. Everything that comes from a data file is written with textContent;
 * only https or same-origin links are rendered. No libraries.
 */
(function () {
  "use strict";

  const UPSTREAM = "https://github.com/leanprover-community/riemann-hypothesis";
  const RAW = "https://raw.githubusercontent.com/thekeunpie-hash/rh-kernel-backbone/main/";
  const SNAPSHOT_PATH = "data/upstream_frontier.json";
  const DAY = /^\d{4}-\d{2}-\d{2}$/;
  const MONTHS = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"];
  const SVG_NS = "http://www.w3.org/2000/svg";

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
  // "2026-11-26" becomes "26 Nov 2026". Fixed month names, so it reads the same everywhere.
  function fmtDay(d) {
    const m = MONTHS[Number(d.slice(5, 7)) - 1];
    return m ? Number(d.slice(8, 10)) + " " + m + " " + d.slice(0, 4) : d;
  }
  function timeEl(d, cls) {
    const t = el("time", cls || "", fmtDay(d));
    t.dateTime = d;
    return t;
  }
  function validSha(v) { return typeof v === "string" && /^[a-f0-9]{7,40}$/i.test(v); }
  function shortToolchain(v) { return typeof v === "string" ? v.trim().replace(/^leanprover\/lean4:/, "").slice(0, 40) : ""; }
  function count(v) { return Number.isSafeInteger(v) && v >= 0 ? v.toLocaleString("en-US") : ""; }
  function metric(v, label) { const n = count(v); return n ? n + " " + label : ""; }

  // The tracker snapshot is fetched once per page and shared by everything that reads it.
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

  // One column as a card. withDate: print the date in the kicker (the home grid); on the
  // timeline the day already carries it.
  function columnCard(c, withDate) {
    const card = el("div", "col-card");
    const kicker = el("span", "col-kicker", ["Column", c.kicker, c.language].filter(Boolean).join(" · "));
    if (withDate) kicker.append(" · ", timeEl(c.date));
    const title = el("span", "col-title");
    const a = link(c.title, c.href);
    if (c.lang) a.lang = c.lang;
    title.append(a);
    card.append(kicker, title);
    if (c.summary) {
      const p = el("p", "col-sum", c.summary);
      if (c.lang) p.lang = c.lang;
      card.append(p);
    }
    const go = el("span", "col-go", "Read the column");
    go.setAttribute("aria-hidden", "true");
    card.append(go);
    return card;
  }

  function renderColumnCards(list, cols) {
    if (!list || !cols.length) return;
    list.replaceChildren();
    for (const c of cols) {
      const li = el("li");
      li.append(columnCard(c, true));
      list.append(li);
    }
  }

  // The merged timeline: every dated repository event and every column, newest day first.
  // Columns are cards, events are a dot on the rail. opts.limit: only the newest N events,
  // without columns and without the fold-out details (the home page).
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
      day.append(timeEl(d, "day-date"));
      const evs = el("ul", "events");
      for (const it of byDay.get(d)) {
        const li = el("li", "event" + (it.column ? " is-column" : ""));
        if (it.column) {
          if (it.slug && /^[a-z0-9-]+$/.test(it.slug)) li.id = "col-" + it.slug;
          li.append(columnCard(it, false));
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
    // A link such as columns.html#col-manual points at a card that exists only after this render.
    if (!limit && /^#col-[a-z0-9-]+$/.test(location.hash)) {
      const target = document.getElementById(location.hash.slice(1));
      if (target) target.scrollIntoView();
    }
  }

  // The row of measured facts on the home page. Only fields the snapshot really has are shown,
  // and the line under the row names the commit and the time they were counted at.
  function renderFacts(dl, src, live) {
    if (!dl || !live || !validSha(live.sha)) return false;
    const facts = [
      [count(live.lean_files), "Lean files"],
      [count(live.total_lines), "Raw lines"],
      [count(live.declarations), "Declarations"],
      [count(live.open_pr_count), "Open pull requests"],
      [shortToolchain(live.toolchain), "Lean toolchain", true]
    ].filter((f) => f[0]);
    if (!facts.length) return false;
    dl.replaceChildren();
    for (const [value, label, isText] of facts) {
      const cell = el("div");
      cell.append(el("dt", "", label), el("dd", isText ? "is-text" : "", value));
      dl.append(cell);
    }
    dl.hidden = false;
    if (src) {
      const sha = live.sha.slice(0, 9);
      const when = typeof live.measured_at === "string" && dayOf(live.measured_at)
        ? " on " + fmtDay(dayOf(live.measured_at)) + " (" + live.measured_at.slice(11, 16) + " UTC)"
        : "";
      src.replaceChildren(
        "Measured at upstream ",
        link("main@" + sha, UPSTREAM + "/commit/" + live.sha, true),
        " by this site’s tracker script" + when + ". Raw lines include comments and blank lines. ",
        link("How each number is counted", "tracker.html"),
        "."
      );
    }
    return true;
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

  /* ---------- The figure on the home page ---------- */

  // Imaginary parts of the first ten nontrivial zeros of the Riemann zeta function, to six
  // decimals. These are the standard published values; the curve below is computed
  // independently and crosses zero at each of them.
  const ZEROS = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
    37.586178, 40.918719, 43.327073, 48.005151, 49.773832];
  const T_MAX = 52;

  // Hardy's Z(t) = e^{i theta(t)} zeta(1/2 + it). It is real for real t and has the same zeros
  // as zeta on the critical line. zeta comes from the Euler-Maclaurin formula with N = 60 and
  // four Bernoulli terms, which is accurate to about 1e-8 for t up to 52.
  function hardyZ(t) {
    const N = 60, lnN = Math.log(N);
    let re = 0, im = 0;
    for (let n = 1; n < N; n++) {
      const a = t * Math.log(n), m = 1 / Math.sqrt(n);
      re += m * Math.cos(a);
      im -= m * Math.sin(a);
    }
    // p = N^(-s) with s = 1/2 + it
    const pr = Math.cos(t * lnN) / Math.sqrt(N), pi = -Math.sin(t * lnN) / Math.sqrt(N);
    // N^(1-s) / (s - 1)
    const den = 0.25 + t * t;
    re += N * (-0.5 * pr + t * pi) / den;
    im += N * (-0.5 * pi - t * pr) / den;
    re += pr / 2;
    im += pi / 2;
    // B_2k / (2k)! * s (s+1) ... (s+2k-2) * N^(-s-2k+1), k = 1..4
    const B = [1 / 12, -1 / 720, 1 / 30240, -1 / 1209600];
    let fr = pr, fi = pi, j = 0;
    for (let k = 0; k < B.length; k++) {
      for (let q = k === 0 ? 1 : 2; q > 0; q--, j++) {
        const ar = (0.5 + j) / N, ai = t / N;
        const nr = fr * ar - fi * ai;
        fi = fr * ai + fi * ar;
        fr = nr;
      }
      re += B[k] * fr;
      im += B[k] * fi;
    }
    // Below t = 2 the asymptotic series for theta is poor, and Z is negative there anyway.
    if (t < 2) return -Math.hypot(re, im);
    const theta = (t / 2) * Math.log(t / (2 * Math.PI)) - t / 2 - Math.PI / 8 + 1 / (48 * t) + 7 / (5760 * t * t * t);
    return re * Math.cos(theta) - im * Math.sin(theta);
  }

  function svg(tag, cls, attrs) {
    const n = document.createElementNS(SVG_NS, tag);
    if (cls) n.setAttribute("class", cls);
    for (const k in attrs || {}) n.setAttribute(k, attrs[k]);
    return n;
  }

  // Draws the critical line on its side with Z(t) over it and the first ten zeros marked.
  // fig: the <figure>; it holds an <svg> (a static fallback until this runs), an <output> for
  // the pointer readout and an element with [data-zf-note] for the sentence about the curve.
  function zetaHero(fig) {
    const root = fig && fig.querySelector("svg");
    if (!root) return;
    const out = fig.querySelector("output");
    const note = fig.querySelector("[data-zf-note]");
    const idle = out ? out.textContent : "";

    const STEPS = 780;
    const samples = new Array(STEPS + 1);
    let zmax = 0;
    for (let i = 0; i <= STEPS; i++) {
      samples[i] = hardyZ(T_MAX * i / STEPS);
      zmax = Math.max(zmax, Math.abs(samples[i]));
    }
    if (!(zmax > 0) || !isFinite(zmax)) return;

    const calm = window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches;
    let first = true, lastW = 0, geo = null, hair = null;

    function draw() {
      const W = Math.round(root.parentNode.clientWidth);
      if (!W || W === lastW) return;
      lastW = W;
      const narrow = W < 560;
      const H = narrow ? 300 : 380;
      const pad = narrow ? 14 : 30;
      const top = 30;
      const ruler = narrow ? 52 : 82;
      const plotH = H - top - ruler;
      const mid = top + plotH / 2;
      const amp = plotH / 2 - 4;
      const x = (t) => pad + (W - 2 * pad) * t / T_MAX;
      const y = (z) => mid - (z / zmax) * amp;
      geo = { W, pad };

      root.removeAttribute("viewBox");
      root.setAttribute("width", W);
      root.setAttribute("height", H);
      root.replaceChildren();

      for (let t = 0; t <= 50; t += 10) {
        root.append(svg("line", "zf-grid", { x1: x(t), x2: x(t), y1: top - 6, y2: top + plotH }));
        const s = svg("text", "zf-scale", { x: x(t), y: 15, "text-anchor": t === 0 ? "start" : "middle" });
        s.textContent = t === 0 ? "t = 0" : String(t);
        root.append(s);
      }

      root.append(svg("line", "zf-axis", { x1: x(0), x2: x(T_MAX), y1: mid, y2: mid }));
      const lab = svg("text", "zf-axis-label", { x: x(0) + 6, y: mid - 9 });
      if (narrow) lab.style.fontSize = "10px";
      lab.textContent = "Re(s) = 1/2";
      root.append(lab);

      let d = "";
      for (let i = 0; i <= STEPS; i++) {
        d += (i ? "L" : "M") + x(T_MAX * i / STEPS).toFixed(1) + " " + y(samples[i]).toFixed(1);
      }
      const curve = svg("path", "zf-curve", { d });
      root.append(curve);

      const animate = first && !calm && typeof curve.getTotalLength === "function";
      const marks = [];
      for (const z of ZEROS) {
        const g = svg("g", "zf-mark" + (animate ? " is-pending" : ""));
        const zx = x(z);
        g.append(svg("line", "zf-lead", { x1: zx, x2: zx, y1: mid + 6, y2: top + plotH + 4 }));
        g.append(svg("circle", "zf-zero", { cx: zx, cy: mid, r: narrow ? 3.5 : 4.5 }));
        const text = svg("text", "zf-label", {
          x: zx, y: top + plotH + 10, "text-anchor": "end", "dominant-baseline": "middle",
          transform: "rotate(-90 " + zx.toFixed(1) + " " + (top + plotH + 10) + ")"
        });
        if (narrow) text.style.fontSize = "10px";
        text.textContent = z.toFixed(narrow ? 2 : 6);
        g.append(text);
        if (animate) g.style.transitionDelay = Math.round(2600 * z / T_MAX) + "ms";
        root.append(g);
        marks.push(g);
      }

      hair = svg("line", "zf-hair", { y1: top - 6, y2: top + plotH, x1: 0, x2: 0 });
      hair.style.display = "none";
      root.append(hair);

      if (animate) {
        // The pen walks up the line once; each zero appears as the pen reaches it.
        const len = curve.getTotalLength();
        curve.style.strokeDasharray = len + " " + len;
        curve.style.strokeDashoffset = len;
        curve.getBoundingClientRect();
        curve.style.transition = "stroke-dashoffset 2600ms linear";
        curve.style.strokeDashoffset = "0";
        for (const g of marks) g.classList.remove("is-pending");
      }
      first = false;
    }

    function point(ev) {
      if (!geo || !out || !hair) return;
      const box = root.getBoundingClientRect();
      const t = Math.min(T_MAX, Math.max(0, (ev.clientX - box.left - geo.pad) / (geo.W - 2 * geo.pad) * T_MAX));
      const px = geo.pad + (geo.W - 2 * geo.pad) * t / T_MAX;
      hair.setAttribute("x1", px);
      hair.setAttribute("x2", px);
      hair.style.display = "";
      const z = hardyZ(t);
      out.textContent = "s = 1/2 + " + t.toFixed(2) + "i   Z = " + (z < 0 ? "−" : "+") + Math.abs(z).toFixed(3);
    }
    root.addEventListener("pointermove", point);
    root.addEventListener("pointerdown", point);
    root.addEventListener("pointerleave", function () {
      if (hair) hair.style.display = "none";
      if (out) out.textContent = idle;
    });

    draw();
    if (note) note.hidden = false;
    if (typeof ResizeObserver === "function") new ResizeObserver(draw).observe(root.parentNode);
    else window.addEventListener("resize", draw);
  }

  window.RHSite = {
    liveStrip, loadColumns, loadEvents, renderColumnCards, renderTimeline, renderFacts,
    zetaHero, hardyZ, metric, ZEROS
  };
})();
