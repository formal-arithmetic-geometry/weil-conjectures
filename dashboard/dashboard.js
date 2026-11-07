// Quality dashboard: renders data/meta.json + data/history.jsonl (see scripts/quality/history.py
// for the schema). Every metric kind found in the records gets a tile and a chart; metadata
// (label, unit, lower_is_better, ...) comes from meta.json, with defaults for unknown kinds, so
// a new metric needs no change here.
"use strict";

const DAY = 86400000;
const SCHEMA = 1;
const state = { meta: null, records: [], kinds: [], days: 90, charts: [] };

// ---------------------------------------------------------------------------------------------
// Small helpers

const md = (s) => esc(s).replace(/`([^`]+)`/g, "<code>$1</code>");
const esc = (s) => String(s).replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));
const fmt = (n) => (n == null ? "–" : Number(n).toLocaleString("en"));
const fmtDate = (ts) => new Date(ts).toISOString().slice(0, 10);
const shortDate = (ts) => new Date(ts).toLocaleDateString("en", { month: "short", day: "numeric", timeZone: "UTC" });
const cssVar = (name) => getComputedStyle(document.documentElement).getPropertyValue(name).trim();
const commitUrl = (sha) => (state.meta.repo_url ? `${state.meta.repo_url}/commit/${sha}` : null);
const commitLink = (sha) => {
  const url = commitUrl(sha);
  const text = `<code>${esc(sha.slice(0, 10))}</code>`;
  return url ? `<a href="${esc(url)}">${text}</a>` : text;
};
const store = {
  get(k) { try { return localStorage.getItem(k); } catch (e) { return null; } },
  set(k, v) { try { localStorage.setItem(k, v); } catch (e) { /* private mode etc. */ } },
};

// ---------------------------------------------------------------------------------------------
// Data

async function load() {
  const [metaRes, histRes] = await Promise.all([
    fetch("data/meta.json", { cache: "no-cache" }),
    fetch("data/history.jsonl", { cache: "no-cache" }),
  ]);
  if (!metaRes.ok || !histRes.ok) throw new Error(`could not load the data (${metaRes.status}, ${histRes.status})`);
  const meta = await metaRes.json();
  const records = (await histRes.text()).split("\n").filter((l) => l.trim()).map((l) => JSON.parse(l))
    .filter((r) => (r.schema || 1) <= SCHEMA)
    .map((r) => ({ ...r, ts: Date.parse(r.date) }))
    .sort((a, b) => a.ts - b.ts);
  state.meta = meta;
  state.records = records;

  // Kinds: those meta.json declares, in its order, then any others the records contain.
  const declared = new Map((meta.kinds || []).map((k) => [k.id, k]));
  const seen = new Set();
  for (const r of records) for (const id of Object.keys(r.metrics || {})) seen.add(id);
  const ids = [...declared.keys()].filter((id) => seen.has(id)).concat([...seen].filter((id) => !declared.has(id)).sort());
  state.kinds = ids.map((id) => buildKind({ id, label: id, group: "Other metrics", unit: "", lower_is_better: true, max_series: 7, ...declared.get(id) }));
}

// One kind's points (records that measured it), series and totals.
function buildKind(kind) {
  const points = state.records.filter((r) => r.metrics && r.metrics[kind.id]);
  const names = new Set();
  for (const p of points) for (const s of Object.keys(p.metrics[kind.id])) names.add(s);
  const last = points[points.length - 1];
  const value = (p, s) => p.metrics[kind.id][s] || 0;
  // Colour follows the series, not the visible range: rank by the latest value over all data.
  const series = [...names].sort((a, b) => (last ? value(last, b) - value(last, a) : 0) || a.localeCompare(b));
  const total = (p) => Object.values(p.metrics[kind.id]).reduce((a, b) => a + b, 0);
  return { ...kind, points, series, value, total };
}

// The point at or before `ts` (for "change over the last N days").
function pointBefore(points, ts) {
  let found = null;
  for (const p of points) { if (p.ts <= ts) found = p; else break; }
  return found;
}

function deltas(kind, f) {
  const pts = kind.points;
  if (!pts.length) return [];
  const last = pts[pts.length - 1];
  const out = [];
  const add = (label, p) => out.push({ label, d: p ? f(last) - f(p) : null, since: p });
  add("prev", pts.length > 1 ? pts[pts.length - 2] : null);
  add("7 d", pointBefore(pts, last.ts - 7 * DAY));
  add("30 d", pointBefore(pts, last.ts - 30 * DAY));
  return out;
}

function deltaHtml(kind, { label, d, since }) {
  const title = since ? `since ${fmtDate(since.ts)} (${since.commit.slice(0, 10)})` : "no earlier data";
  if (d == null) return `<span class="d" title="${esc(title)}">–<span class="when">${esc(label)}</span></span>`;
  const better = kind.lower_is_better ? d < 0 : d > 0;
  const cls = d === 0 ? "" : better ? "good" : "bad";
  const arrow = d > 0 ? "▲" : d < 0 ? "▼" : "";
  const sign = d > 0 ? "+" : "";
  return `<span class="d ${cls}" title="${esc(title)}"><span class="arrow" aria-hidden="true">${arrow}</span>${sign}${fmt(d)}<span class="when">${esc(label)}</span></span>`;
}

// ---------------------------------------------------------------------------------------------
// Rendering

function renderSummary() {
  const el = document.getElementById("summary");
  const groups = new Map();
  for (const k of state.kinds) {
    if (!k.points.length) continue;
    if (!groups.has(k.group)) groups.set(k.group, []);
    groups.get(k.group).push(k);
  }
  let html = "";
  for (const [group, kinds] of groups) {
    html += `<h2>${esc(group)}</h2><div class="tiles">`;
    for (const k of kinds) {
      const last = k.points[k.points.length - 1];
      html += `<a class="tile" href="#kind-${esc(k.id)}">
        <div class="label">${esc(k.label)}</div>
        <div class="value">${fmt(k.total(last))}<span class="unit">${esc(k.unit || "")}</span></div>
        <div class="deltas">${deltas(k, k.total).map((x) => deltaHtml(k, x)).join("")}</div></a>`;
    }
    html += "</div>";
  }
  el.innerHTML = html;
}

function renderKernelTop() {
  const el = document.getElementById("kernel-top");
  const withKernel = state.records.filter((r) => r.kernel && r.kernel.top && r.kernel.top.length);
  if (!withKernel.length) { el.hidden = true; return; }
  const cur = withKernel[withKernel.length - 1];
  const prev = withKernel.length > 1 ? withKernel[withKernel.length - 2] : null;
  const before = new Map(prev ? prev.kernel.top.map(([ms, mod, name]) => [`${mod}\t${name}`, ms]) : []);
  const display = (mod, name) => {
    const p = `_private.${mod}.0.`;
    return name.startsWith(p) ? `${esc(name.slice(p.length))} <span class="unit">(private)</span>` : esc(name);
  };
  const rows = cur.kernel.top.map(([ms, mod, name], i) => {
    const b = before.get(`${mod}\t${name}`);
    const was = prev ? (b == null ? "new" : `${(b / 1000).toFixed(1)} s`) : "";
    return `<tr><td class="num">${i + 1}</td><td class="num">${(ms / 1000).toFixed(1)} s</td>
      <td class="name"><code>${display(mod, name)}</code></td><td class="name"><code>${esc(mod)}</code></td>
      <td class="num">${esc(was)}</td></tr>`;
  }).join("");
  el.hidden = false;
  el.innerHTML = `<h2>Slowest declarations in the kernel</h2><div class="card">
    <p class="sub">At ${commitLink(cur.commit)} (${fmtDate(cur.ts)}); ${fmt(cur.kernel.modules)} modules measured.
    ${prev ? `“Before”: the table at ${commitLink(prev.commit)}.` : ""}</p>
    <div class="table-wrap"><table><thead><tr><th class="num">#</th><th class="num">Time</th><th>Declaration</th>
    <th>Module</th><th class="num">Before</th></tr></thead><tbody>${rows}</tbody></table></div></div>`;
}

function seriesColors() {
  return [1, 2, 3, 4, 5, 6, 7, 8].map((i) => cssVar(`--s${i}`));
}

function renderCharts() {
  for (const c of state.charts) c.destroy();
  state.charts = [];
  const el = document.getElementById("charts");
  el.innerHTML = "";
  const colors = seriesColors();
  const from = state.days ? Date.now() - state.days * DAY : -Infinity;
  const last = state.records.length ? state.records[state.records.length - 1].ts : 0;
  const minTs = state.days ? Math.min(from, last - state.days * DAY) : -Infinity;
  let group = null;
  for (const k of state.kinds) {
    if (!k.points.length) continue;
    if (k.group !== group) {
      group = k.group;
      el.insertAdjacentHTML("beforeend", `<h2>${esc(group)} over time</h2>`);
    }
    const max = k.max_series || 7;
    const shown = k.series.length > max + 1 ? k.series.slice(0, max) : k.series;
    const rest = k.series.slice(shown.length);
    const color = (i) => colors[i % colors.length];
    const pts = state.records.filter((r) => r.ts >= minTs);
    const lastP = k.points[k.points.length - 1];
    const card = document.createElement("section");
    card.className = "card";
    card.id = `kind-${k.id}`;
    const logKey = `qd-log-${k.id}`;
    const log = store.get(logKey) === "1";
    // Per-series table (every series, also the ones folded into "Other").
    const rowDeltas = (s) => deltas(k, (p) => k.value(p, s));
    const rows = k.series.map((s, i) => {
      const sw = i < shown.length ? color(i) : cssVar("--other");
      return `<tr><td class="name"><span class="swatch" data-sw="${esc(sw)}"></span><code>${esc(s)}</code></td>
        <td class="num">${fmt(k.value(lastP, s))}</td>${rowDeltas(s).map((x) => `<td class="num">${deltaHtml(k, x)}</td>`).join("")}</tr>`;
    }).join("");
    card.innerHTML = `<div class="card-head"><h3>${esc(k.label)}</h3>
        <span class="now">${fmt(k.total(lastP))} ${esc(k.unit || "")} at ${commitLink(lastP.commit)}</span>
        ${k.description ? `<p class="desc">${md(k.description)}</p>` : ""}</div>
      <div class="chart-box"><canvas role="img" aria-label="${esc(k.label)} over time"></canvas></div>
      <div class="tools"><button type="button" class="chip" aria-pressed="${log}">Log scale</button></div>
      <details><summary>All ${k.series.length} series (table)</summary><div class="table-wrap"><table>
        <thead><tr><th>Series</th><th class="num">Now</th><th class="num">vs. prev</th><th class="num">7 d</th><th class="num">30 d</th></tr></thead>
        <tbody>${rows}</tbody></table></div></details>`;
    el.appendChild(card);
    // Colours as properties, not style attributes: the site's CSP has no unsafe-inline.
    card.querySelectorAll("[data-sw]").forEach((s) => { s.style.background = s.dataset.sw; });

    const data = (f) => pts.map((r) => ({ x: r.ts, y: r.metrics && r.metrics[k.id] ? f(r) : null }));
    const datasets = shown.map((s, i) => ({ label: s, data: data((r) => k.value(r, s)), borderColor: color(i), backgroundColor: color(i) }));
    if (rest.length) {
      datasets.push({
        label: `Other (${rest.length})`, data: data((r) => rest.reduce((a, s) => a + k.value(r, s), 0)),
        borderColor: cssVar("--other"), backgroundColor: cssVar("--other"), borderDash: [4, 3],
      });
    }
    const chip = card.querySelector(".chip");
    const xs = pts.map((r) => r.ts);
    const chart = makeChart(card.querySelector("canvas"), datasets, log, datasets.length > 1, Math.min(...xs), Math.max(...xs));
    chip.addEventListener("click", () => {
      const on = chip.getAttribute("aria-pressed") !== "true";
      chip.setAttribute("aria-pressed", String(on));
      store.set(logKey, on ? "1" : "0");
      chart.options.scales.y.type = on ? "logarithmic" : "linear";
      chart.update();
    });
    state.charts.push(chart);
  }
}

function makeChart(canvas, datasets, log, legend, xmin, xmax) {
  const text2 = cssVar("--text-2"), grid = cssVar("--grid"), surface = cssVar("--surface");
  return new Chart(canvas, {
    type: "line",
    data: { datasets: datasets.map((d) => ({ borderWidth: 2, pointRadius: 0, pointHoverRadius: 4, pointHoverBorderColor: surface, pointHoverBorderWidth: 2, tension: 0, spanGaps: false, ...d })) },
    options: {
      responsive: true, maintainAspectRatio: false, animation: false, parsing: true, normalized: true,
      interaction: { mode: "index", intersect: false },
      scales: {
        x: {
          type: "linear", min: xmin, max: xmax, grid: { color: grid }, border: { color: grid },
          ticks: { color: text2, maxRotation: 0, autoSkipPadding: 16, callback: (v) => shortDate(v) },
        },
        y: {
          type: log ? "logarithmic" : "linear", grid: { color: grid }, border: { display: false },
          ticks: { color: text2, callback: (v) => fmt(v) },
        },
      },
      plugins: {
        legend: { display: legend, position: "bottom", labels: { color: text2, boxWidth: 12, boxHeight: 12, usePointStyle: false } },
        tooltip: {
          itemSort: (a, b) => b.parsed.y - a.parsed.y,
          callbacks: {
            title: (items) => {
              const r = items.length && pointAt(items[0].parsed.x);
              return r ? `${fmtDate(r.ts)}  ${r.commit.slice(0, 10)}` : "";
            },
            label: (item) => ` ${item.dataset.label}: ${fmt(item.parsed.y)}`,
          },
        },
      },
      onClick: (evt, elements) => {
        if (!elements.length) return;
        const r = pointAt(elements[0].element.$context.parsed.x);
        const url = r && commitUrl(r.commit);
        if (url) window.open(url, "_blank", "noopener");
      },
    },
  });
}

function pointAt(ts) {
  return state.records.find((r) => r.ts === ts);
}

function renderHeader() {
  const m = state.meta;
  if (m.title) { document.getElementById("title").textContent = m.title; }
  const last = state.records[state.records.length - 1];
  const first = state.records[0];
  document.getElementById("subtitle").innerHTML = last
    ? `master at ${commitLink(last.commit)}, ${fmtDate(last.ts)} · ${fmt(state.records.length)} points since ${fmtDate(first.ts)}`
    : "No data yet.";
  document.getElementById("foot").innerHTML =
    `Data: <a href="data/history.jsonl">history.jsonl</a>, <a href="data/meta.json">meta.json</a>` +
    (m.updated ? ` · updated ${esc(m.updated.replace("T", " ").replace("Z", " UTC"))}` : "") +
    ` · counters by <code>scripts/tech_debt/metrics.py</code> (comments and strings excluded); click a point to open its commit.`;
}

// ---------------------------------------------------------------------------------------------
// Controls

function setupRange() {
  const saved = store.get("qd-days");
  if (saved != null && !Number.isNaN(Number(saved))) state.days = Number(saved);
  const buttons = document.querySelectorAll("#range button");
  const mark = () => buttons.forEach((b) => b.setAttribute("aria-pressed", String(Number(b.dataset.days) === state.days)));
  buttons.forEach((b) => b.addEventListener("click", () => {
    state.days = Number(b.dataset.days);
    store.set("qd-days", String(state.days));
    mark();
    renderCharts();
  }));
  mark();
}

function setupTheme() {
  const btn = document.getElementById("theme");
  const order = ["auto", "light", "dark"];
  let theme = store.get("qd-theme") || "auto";
  const apply = () => {
    if (theme === "auto") document.documentElement.removeAttribute("data-theme");
    else document.documentElement.setAttribute("data-theme", theme);
    btn.textContent = theme[0].toUpperCase() + theme.slice(1);
    btn.title = `Colour theme: ${theme} (click to change)`;
  };
  apply();
  btn.addEventListener("click", () => {
    theme = order[(order.indexOf(theme) + 1) % order.length];
    store.set("qd-theme", theme);
    apply();
    if (state.meta) renderCharts();
  });
  window.matchMedia("(prefers-color-scheme: dark)").addEventListener("change", () => { if (state.meta) renderCharts(); });
}

async function main() {
  setupTheme();
  setupRange();
  try {
    await load();
  } catch (e) {
    document.getElementById("subtitle").innerHTML = `<span class="error">${esc(e.message)}</span>`;
    return;
  }
  renderHeader();
  renderSummary();
  renderKernelTop();
  if (typeof Chart === "undefined") {
    document.getElementById("charts").innerHTML = `<p class="error">The chart library did not load; the current values above are complete.</p>`;
    return;
  }
  renderCharts();
}

main();
