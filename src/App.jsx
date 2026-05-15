import { useState, useCallback } from "react";

// ZIP reader (pure browser, no external deps)
function readZipEntries(buffer) {
  const view = new DataView(buffer);
  const bytes = new Uint8Array(buffer);
  const dec = new TextDecoder("utf-8");
  const entries = {};
  let eocd = -1;
  for (let i = buffer.byteLength - 22; i >= 0; i--) {
    if (view.getUint32(i, true) === 0x06054b50) { eocd = i; break; }
  }
  if (eocd === -1) return entries;
  const cdOffset = view.getUint32(eocd + 16, true);
  const cdSize   = view.getUint32(eocd + 12, true);
  let pos = cdOffset;
  while (pos < cdOffset + cdSize) {
    if (view.getUint32(pos, true) !== 0x02014b50) break;
    const compMethod  = view.getUint16(pos + 10, true);
    const compSize    = view.getUint32(pos + 20, true);
    const fnLen       = view.getUint16(pos + 28, true);
    const extraLen    = view.getUint16(pos + 30, true);
    const commentLen  = view.getUint16(pos + 32, true);
    const localOffset = view.getUint32(pos + 42, true);
    const name        = dec.decode(bytes.slice(pos + 46, pos + 46 + fnLen));
    pos += 46 + fnLen + extraLen + commentLen;
    const localExtraLen = view.getUint16(localOffset + 28, true);
    const dataStart = localOffset + 30 + fnLen + localExtraLen;
    const compData  = bytes.slice(dataStart, dataStart + compSize);
    entries[name] = compMethod === 0 ? dec.decode(compData) : { deflated: compData };
  }
  return entries;
}

async function getEntryText(entry) {
  if (!entry) return "";
  if (typeof entry === "string") return entry;
  if (!entry.deflated) return "";
  try {
    const ds = new DecompressionStream("deflate-raw");
    const writer = ds.writable.getWriter();
    writer.write(entry.deflated);
    writer.close();
    const chunks = [];
    const reader = ds.readable.getReader();
    while (true) {
      const { done, value } = await reader.read();
      if (done) break;
      chunks.push(value);
    }
    const out = new Uint8Array(chunks.reduce((a, c) => a + c.length, 0));
    let off = 0;
    for (const c of chunks) { out.set(c, off); off += c.length; }
    return new TextDecoder("utf-8").decode(out);
  } catch { return ""; }
}

// Helpers
function countWords(text) {
  return text.trim().split(/\s+/).filter(Boolean).length;
}

function longestConsecutiveOverlap(studentText, origText) {
  const tok = (t) => t.toLowerCase().replace(/[^a-z0-9\s]/g, "").split(/\s+/).filter(Boolean);
  const a = tok(studentText);
  const b = tok(origText).join(" ");
  let max = 0;
  for (let i = 0; i < a.length; i++) {
    for (let len = max + 1; i + len <= a.length; len++) {
      if (b.includes(a.slice(i, i + len).join(" "))) max = len;
      else break;
    }
  }
  return max;
}

const REQUIRED_HEADINGS = ["abstract", "緣由與目的", "材料與方法", "結果", "討論", "參考文獻"];

// Build a Set of styleIds that are "heading-type".
// Strategy: any style with w:outlineLevel in its pPr, OR named "heading N",
// OR basedOn a heading style (transitive closure).
function buildHeadingStyleSet(stylesXml) {
  if (!stylesXml) return new Set();
  const doc = new DOMParser().parseFromString(stylesXml, "application/xml");
  const raw = {};
  doc.querySelectorAll("style").forEach((s) => {
    const id      = s.getAttribute("w:styleId") ?? "";
    const nameEl  = s.querySelector("name");
    const name    = nameEl?.getAttribute("w:val") ?? "";
    const basedOn = s.querySelector("basedOn")?.getAttribute("w:val") ?? null;
    // outlineLvl inside the style's pPr marks it as a heading
    const hasOutline = !!s.querySelector("outlineLvl");
    raw[id] = { name, basedOn, hasOutline };
  });

  const headingSet = new Set();
  // Seed
  for (const [id, info] of Object.entries(raw)) {
    if (info.hasOutline || /^heading\s*\d/i.test(info.name)) {
      headingSet.add(id);
    }
  }
  // Propagate via basedOn
  let changed = true;
  while (changed) {
    changed = false;
    for (const [id, info] of Object.entries(raw)) {
      if (!headingSet.has(id) && info.basedOn && headingSet.has(info.basedOn)) {
        headingSet.add(id); changed = true;
      }
    }
  }
  return headingSet;
}

function parseStyleNames(stylesXml) {
  const map = {};
  if (!stylesXml) return map;
  const doc = new DOMParser().parseFromString(stylesXml, "application/xml");
  doc.querySelectorAll("style").forEach((s) => {
    const id = s.getAttribute("w:styleId") ?? "";
    map[id] = s.querySelector("name")?.getAttribute("w:val") ?? id;
  });
  return map;
}

function parseDocument(docXml, styleNames, headingSet) {
  const doc = new DOMParser().parseFromString(docXml, "application/xml");
  return Array.from(doc.querySelectorAll("p")).map((p) => {
    const pStyleEl = p.querySelector("pStyle");
    const styleId  = pStyleEl?.getAttribute("w:val") ?? "Normal";
    const styleName = styleNames[styleId] ?? styleId;
    // Inline outlineLvl override (rare)
    const inlineOutline = !!p.querySelector("outlineLvl");
    const isHeadingStyle = headingSet.has(styleId) || inlineOutline;
    let text = "";
    p.querySelectorAll("r").forEach((r) => {
      const t = r.querySelector("t");
      if (t) text += t.textContent;
    });
    return { styleId, styleName, isHeadingStyle, text: text.trim() };
  });
}

function isHeading(p) { return p.isHeadingStyle === true; }

// Check 2: Heading style usage
function checkStyles(paragraphs) {
  const issues = [], info = [];
  const nonEmpty    = paragraphs.filter((p) => p.text.length > 0);
  const headingParas = nonEmpty.filter(isHeading);
  const reqKw = REQUIRED_HEADINGS.map((h) => h.toLowerCase());

  // Title candidates = heading-styled paras whose text doesn't match any required section keyword
  const titleCandidates = headingParas.filter(
    (p) => !reqKw.some((kw) => p.text.toLowerCase().includes(kw))
  );
  if (titleCandidates.length === 0)
    issues.push("找不到套用標題樣式的論文題目段落（英文與中文題目應各套用任一標題樣式）");
  else
    info.push(`✓ 找到 ${titleCandidates.length} 個套用標題樣式的題目段落`);

  // Required section headings
  const hTexts = headingParas.map((p) => p.text.toLowerCase());
  const missing = REQUIRED_HEADINGS.filter((h) => !hTexts.some((t) => t.includes(h.toLowerCase())));
  if (missing.length > 0)
    issues.push(`以下必要標題未找到（或未套用標題樣式）：${missing.join("、")}`);
  else
    info.push("✓ 所有必要標題均存在且套用標題樣式");

  // Body text misusing heading style (long paragraphs that aren't section titles)
  const misused = headingParas.filter(
    (p) => p.text.length > 250 && !reqKw.some((kw) => p.text.toLowerCase().includes(kw))
  );
  if (misused.length > 0) {
    const snippets = misused.map((p) => `"${p.text.slice(0, 40)}…"`).join("、");
    issues.push(`偵測到 ${misused.length} 個疑似內文段落誤套標題樣式（內文請使用 Normal 或 Body Text）：${snippets}`);
  } else {
    info.push("✓ 內文段落未誤套標題樣式");
  }

  return { issues, info };
}

// Check 3: Citation manager field codes
function checkCitations(docXml) {
  return {
    hasEndnote:  /ADDIN EN\.CITE/i.test(docXml),
    hasZotero:   /ADDIN ZOTERO/i.test(docXml) || /zotero_item/i.test(docXml),
    hasMendeley: /ADDIN Mendeley/i.test(docXml) || /Mendeley_Citation/i.test(docXml),
  };
}

// Check 4: Extract abstract text (paragraphs between "Abstract" heading and next heading)
function extractAbstract(paragraphs) {
  let active = false, text = "";
  for (const p of paragraphs) {
    if (/^abstract[:\s]*$/i.test(p.text.trim())) { active = true; continue; }
    if (active) {
      if (isHeading(p) && p.text.length > 0) break;
      text += " " + p.text;
    }
  }
  return text.trim();
}

// Main component
export default function SeminarChecker() {
  const [file, setFile]         = useState(null);
  const [origAbs, setOrigAbs]   = useState("");
  const [results, setResults]   = useState(null);
  const [loading, setLoading]   = useState(false);
  const [dragOver, setDragOver] = useState(false);

  const handleFile = useCallback((f) => {
    if (!f) return;
    if (!f.name.toLowerCase().endsWith(".docx")) {
      setResults({ fatal: true, message: "請上傳 .docx 檔案（不接受 .doc 或其他格式）" });
      return;
    }
    setFile(f); setResults(null);
  }, []);

  async function runChecks() {
    if (!file) return;
    setLoading(true); setResults(null);
    try {
      const ab        = await file.arrayBuffer();
      const zipMap    = readZipEntries(ab);
      const docXml    = await getEntryText(zipMap["word/document.xml"]);
      const stylesXml = await getEntryText(zipMap["word/styles.xml"]);
      if (!docXml) throw new Error("無法讀取 word/document.xml，請確認為有效的 .docx");

      const headingSet  = buildHeadingStyleSet(stylesXml);
      const styleNames  = parseStyleNames(stylesXml);
      const paragraphs  = parseDocument(docXml, styleNames, headingSet);

      // (1) file format
      const c1 = { pass: true, label: "檔案格式為 .docx", details: ["✓ 已確認為 .docx 格式"] };

      // (2) heading styles
      const s = checkStyles(paragraphs);
      const c2 = {
        pass: s.issues.length === 0,
        label: "標題樣式使用（Word Heading 或自訂標題樣式）",
        details: [...s.info, ...s.issues.map((x) => "⚠ " + x)],
      };

      // (3) citation manager
      const cite = checkCitations(docXml);
      const tool = cite.hasEndnote ? "EndNote" : cite.hasZotero ? "Zotero" : cite.hasMendeley ? "Mendeley" : null;
      const c3 = {
        pass: !!tool,
        label: "文獻管理軟體（EndNote / Zotero / Mendeley）",
        details: tool
          ? [`✓ 偵測到 ${tool} 的引用標記`]
          : ["⚠ 未偵測到 EndNote、Zotero 或 Mendeley 的引用 field code，請確認是否使用文獻管理軟體插入引用"],
      };

      // (4) abstract
      const absText = extractAbstract(paragraphs);
      const c4d = [];
      let c4p = true;

      if (!absText) {
        c4d.push("⚠ 找不到 Abstract 段落內容");
        c4p = false;
      } else {
        const wc      = countWords(absText);
        const engOnly = /^[a-zA-Z0-9\s.,;:()\[\]'"«»\-\u2013\u2014%\u00b0\u03bc\/+*=<>!?@#$&]+$/.test(absText);

        if (!engOnly) { c4d.push("⚠ Abstract 中偵測到非英文字元，Abstract 應全為英文"); c4p = false; }
        else c4d.push("✓ Abstract 全為英文");

        if (wc > 250) { c4d.push(`⚠ Abstract 字數 ${wc} 字，超過上限 250 字`); c4p = false; }
        else c4d.push(`✓ Abstract 字數：${wc} 字（上限 250）`);

        if (origAbs.trim()) {
          const ov = longestConsecutiveOverlap(absText, origAbs);
          if (ov >= 15) { c4d.push(`⚠ 與原文摘要有連續 ${ov} 個詞相同（上限 14 個連續詞）`); c4p = false; }
          else c4d.push(`✓ 與原文摘要無連續 15 詞以上重複（最長連續：${ov} 詞）`);
        } else {
          c4d.push("ℹ 未提供原文摘要，略過抄寫比對");
        }
      }
      const c4 = { pass: c4p, label: "Abstract 格式", details: c4d };

      setResults({ checks: [c1, c2, c3, c4] });
    } catch (err) {
      setResults({ fatal: true, message: "解析檔案時發生錯誤：" + err.message });
    }
    setLoading(false);
  }

  const allPass = results?.checks?.every((c) => c.pass);

  return (
    <div style={S.root}>
      <div style={S.card}>
        <div style={S.header}>
          <div style={S.accent} />
          <div style={S.hBody}>
            <span style={S.hEn}>Seminar Abstract</span>
            <span style={S.hZh}>格式檢查工具</span>
          </div>
        </div>

        <div
          style={{ ...S.drop, ...(dragOver ? S.dropOn : {}) }}
          onDragOver={(e) => { e.preventDefault(); setDragOver(true); }}
          onDragLeave={() => setDragOver(false)}
          onDrop={(e) => { e.preventDefault(); setDragOver(false); handleFile(e.dataTransfer.files[0]); }}
          onClick={() => document.getElementById("_fi").click()}
        >
          <input id="_fi" type="file" accept=".docx" style={{ display: "none" }}
            onChange={(e) => handleFile(e.target.files[0])} />
          <div style={{ fontSize: 36 }}>📄</div>
          {file
            ? <span style={S.fname}>✔ {file.name}</span>
            : <><span style={S.dp}>點擊或拖曳上傳摘要 .docx</span><span style={S.ds}>僅接受 .docx 格式</span></>}
        </div>

        <div style={S.sec}>
          <label style={S.lbl}>原文英文摘要（選填，用於抄寫比對）</label>
          <textarea style={S.ta} rows={4}
            placeholder="貼上原論文英文 Abstract，系統將比對是否有連續 15 字以上相同語句…"
            value={origAbs} onChange={(e) => setOrigAbs(e.target.value)} />
        </div>

        <button style={{ ...S.btn, ...((!file || loading) ? S.btnOff : {}) }}
          onClick={runChecks} disabled={!file || loading}>
          {loading ? "檢查中…" : "開始格式檢查"}
        </button>

        {results?.fatal && <div style={S.fatal}>{results.message}</div>}

        {results?.checks && (
          <div style={S.res}>
            <div style={{ ...S.verdict, ...(allPass ? S.vPass : S.vFail) }}>
              {allPass ? "✅ 格式全部通過" : "❌ 格式有問題，請修正後重新上傳"}
            </div>
            {results.checks.map((c, i) => (
              <div key={i} style={{ ...S.item, ...(c.pass ? S.iPass : S.iFail) }}>
                <div style={S.iHead}>
                  <span>{c.pass ? "✅" : "❌"}</span>
                  <span style={S.iLabel}>({i + 1}) {c.label}</span>
                </div>
                {c.details.map((d, j) => <div key={j} style={S.detail}>{d}</div>)}
              </div>
            ))}
          </div>
        )}
      </div>
    </div>
  );
}

const S = {
  root:    { minHeight: "100vh", background: "linear-gradient(135deg,#0f1923 0%,#1a2e3b 60%,#0f2a1e 100%)", display: "flex", alignItems: "flex-start", justifyContent: "center", padding: "32px 16px", fontFamily: "'Georgia','Noto Serif TC',serif" },
  card:    { background: "rgba(255,255,255,.04)", border: "1px solid rgba(255,255,255,.1)", borderRadius: 16, maxWidth: 640, width: "100%", paddingBottom: 32, backdropFilter: "blur(12px)", boxShadow: "0 32px 64px rgba(0,0,0,.5)" },
  header:  { display: "flex", borderRadius: "16px 16px 0 0", overflow: "hidden", marginBottom: 28 },
  accent:  { width: 6, background: "linear-gradient(180deg,#4ade80,#16a34a)", flexShrink: 0 },
  hBody:   { padding: 28, background: "rgba(255,255,255,.03)", flex: 1, display: "flex", flexDirection: "column", gap: 4 },
  hEn:     { fontSize: 13, letterSpacing: "0.2em", textTransform: "uppercase", color: "#4ade80", fontStyle: "italic" },
  hZh:     { fontSize: 24, fontWeight: 700, color: "#f0fdf4", letterSpacing: "0.05em" },
  drop:    { margin: "0 28px 20px", border: "2px dashed rgba(74,222,128,.3)", borderRadius: 12, padding: "32px 24px", cursor: "pointer", display: "flex", flexDirection: "column", alignItems: "center", gap: 10, background: "rgba(74,222,128,.03)", transition: "all .2s" },
  dropOn:  { border: "2px dashed #4ade80", background: "rgba(74,222,128,.08)" },
  dp:      { color: "#d1fae5", fontSize: 15, fontWeight: 600 },
  ds:      { color: "#6b7280", fontSize: 12 },
  fname:   { color: "#4ade80", fontSize: 14, fontWeight: 600 },
  sec:     { margin: "0 28px 20px" },
  lbl:     { display: "block", color: "#9ca3af", fontSize: 12, letterSpacing: "0.08em", textTransform: "uppercase", marginBottom: 8 },
  ta:      { width: "100%", background: "rgba(255,255,255,.05)", border: "1px solid rgba(255,255,255,.1)", borderRadius: 8, color: "#e5e7eb", fontSize: 13, padding: 12, resize: "vertical", outline: "none", fontFamily: "inherit", boxSizing: "border-box", lineHeight: 1.6 },
  btn:     { display: "block", margin: "0 28px 24px", width: "calc(100% - 56px)", padding: 14, background: "linear-gradient(135deg,#16a34a,#4ade80)", color: "#052e16", border: "none", borderRadius: 8, fontSize: 15, fontWeight: 700, cursor: "pointer", letterSpacing: "0.05em" },
  btnOff:  { opacity: .4, cursor: "not-allowed" },
  fatal:   { margin: "0 28px", background: "rgba(239,68,68,.15)", border: "1px solid rgba(239,68,68,.4)", color: "#fca5a5", borderRadius: 8, padding: "14px 16px", fontSize: 14 },
  res:     { margin: "0 28px", display: "flex", flexDirection: "column", gap: 12 },
  verdict: { borderRadius: 10, padding: "14px 18px", fontWeight: 700, fontSize: 15, textAlign: "center", letterSpacing: "0.04em" },
  vPass:   { background: "rgba(74,222,128,.15)", border: "1px solid rgba(74,222,128,.4)", color: "#4ade80" },
  vFail:   { background: "rgba(239,68,68,.12)", border: "1px solid rgba(239,68,68,.35)", color: "#f87171" },
  item:    { borderRadius: 8, padding: "14px 16px", border: "1px solid" },
  iPass:   { background: "rgba(74,222,128,.06)", borderColor: "rgba(74,222,128,.2)" },
  iFail:   { background: "rgba(239,68,68,.07)", borderColor: "rgba(239,68,68,.25)" },
  iHead:   { display: "flex", alignItems: "center", gap: 8, marginBottom: 6 },
  iLabel:  { color: "#e5e7eb", fontSize: 14, fontWeight: 600 },
  detail:  { color: "#9ca3af", fontSize: 13, paddingLeft: 24, lineHeight: 1.7 },
};
