// ==UserScript==
// @name         深信服案例库爬虫 (support.sangfor.com.cn)
// @name:zh-CN   深信服案例库爬虫
// @namespace    https://github.com/scriptscat
// @version      1.2.0
// @description  批量抓取 support.sangfor.com.cn 案例库：支持按产品线/模块/版本/关键词筛选，并发翻页抓取列表与正文，还原「问题描述/根因/解决方案」章节结构与图片，可导出 单文件HTML / Markdown / CSV / JSON。基于浏览器登录态运行。
// @author       yimu56
// @license      MIT
// @match        https://support.sangfor.com.cn/*
// @icon         https://support.sangfor.com.cn/static/assets/img/favicon.ico
// @grant        GM_xmlhttpRequest
// @grant        GM_setValue
// @grant        GM_getValue
// @grant        GM_deleteValue
// @grant        GM_registerMenuCommand
// @grant        GM_notification
// @grant        unsafeWindow
// @connect      support.sangfor.com.cn
// @run-at       document-idle
// @noframes
// ==/UserScript==

(function () {
  'use strict';

  /* ==========================================================================
   * 0. 常量与配置
   * 接口来源：对 support.sangfor.com.cn 案例列表页 / 详情页的抓包分析
   * ========================================================================== */

  const ORIGIN = 'https://support.sangfor.com.cn';
  const API_BASE = ORIGIN + '/spt/openapi';

  const API = {
    productList: API_BASE + '/product/getProductList',
    moduleTree: (pid) => `${API_BASE}/case/es/getCaseModuleList/${pid}`,
    versionList: (pid) => `${API_BASE}/case/es/getProductVersionList/${pid}`,
    search: API_BASE + '/case/es/search',
    detail: (id) => `${API_BASE}/case/es/getDetailById/${id}`,
  };

  const DETAIL_URL = (pid, sourceId) =>
    `${ORIGIN}/cases/list?product_id=${pid}&type=1&category_id=${sourceId}&isOpen=true`;

  const UA =
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/153.0.0.0 Safari/537.36 Edg/153.0.0.0';

  const K_STORE = 'sfCaseCrawler:v1';

  // 默认配置
  const defaults = {
    productLineId: '',
    keyword: '',
    mainModuleIds: [],
    childModuleIds: [],
    versionId: '',
    pageSize: 20,
    maxPages: 0, // 0 = 全部
    concurrency: 3,
    interval: 400, // ms
    fetchDetail: true,
    detailConcurrency: 4,
    resume: false,
    onlyRecent: '', // '7d' | '30d' | '90d' | '' 按 update_time 过滤
    imageMode: 'link', // 'link' = 保留外链 | 'embed' = 下载内嵌为 base64（可离线）
    htmlPartSize: 0, // HTML 分卷：每个文件多少条，0 = 单文件（内部已分页，不会卡）
  };

  let cfg = Object.assign({}, defaults);

  // 运行时状态
  const state = {
    running: false,
    paused: false,
    cancelToken: 0,
    totalPages: 0,
    donePages: 0,
    listRows: [],
    detailDone: 0,
    startedAt: 0,
    productCache: null,
    moduleCache: {},
    versionCache: {},
    productNameMap: {}, // productLineId -> name
    versionNameMap: {}, // versionId -> code (当前产品线下)
  };

  /* ------------------------------------------------------------------
   * 0.5 正文格式化模块 SFCaseFmt
   * 案例正文的章节标题藏在 <input value="*问题描述"> 里（tinymce 只读输入框），
   * 普通去标签会丢掉整个章节结构；这里用 DOM 解析还原，并输出 Markdown / 单文件 HTML。
   * ------------------------------------------------------------------ */
  const SFCaseFmt = (function () {
    'use strict';


  function getDoc(html) {
    if (typeof DOMParser !== 'undefined') {
      return new DOMParser().parseFromString(html || '', 'text/html');
    }
    if (typeof require === 'function') {
      return new (require('jsdom').JSDOM)(html || '').window.document;
    }
    throw new Error('no DOM implementation');
  }

  const BLOCK_TAGS = { ADDRESS: 1, ARTICLE: 1, ASIDE: 1, BLOCKQUOTE: 1, DD: 1, DIV: 1, DL: 1, DT: 1,
    FIELDSET: 1, FIGCAPTION: 1, FIGURE: 1, FOOTER: 1, FORM: 1, H1: 1, H2: 1, H3: 1, H4: 1, H5: 1, H6: 1,
    HEADER: 1, HR: 1, LI: 1, MAIN: 1, NAV: 1, OL: 1, P: 1, PRE: 1, SECTION: 1, TABLE: 1, TD: 1, TH: 1,
    TR: 1, UL: 1, TBODY: 1, THEAD: 1 };
  const VOID_TAGS = { AREA: 1, BASE: 1, BR: 1, COL: 1, EMBED: 1, HR: 1, IMG: 1, INPUT: 1,
    LINK: 1, META: 1, PARAM: 1, SOURCE: 1, TRACK: 1, WBR: 1 };

  function decode(s) {
    return String(s == null ? '' : s)
      .replace(/&nbsp;/g, ' ')
      .replace(/&amp;/g, '&')
      .replace(/&lt;/g, '<')
      .replace(/&gt;/g, '>')
      .replace(/&quot;/g, '"')
      .replace(/&#39;/g, "'");
  }

  function tidy(s) {
    return String(s || '')
      .replace(/\r\n?/g, '\n')
      .replace(/[ \t\u00a0]+/g, ' ')
      .replace(/ *\n */g, '\n')
      .replace(/\n{3,}/g, '\n\n');
  }

  // MD 特殊字符转义（内联文本）
  function escInline(s) {
    return String(s || '').replace(/([\\`*_[\]])/g, '\\$1');
  }

  function isGoodUrl(u) {
    return /^(https?:)?\/\//i.test(u || '') || /^data:image\//i.test(u || '');
  }

  // 把相对 / 协议相对路径补全为绝对地址（基于站点根 ORIGIN）。
  // 案例正文里的图片常写成 /_static/... 这种站点根相对路径，
  // 导出成独立 HTML/MD 后浏览器会按 file:// 解析而打不开，必须补全为
  // https://support.sangfor.com.cn/_static/... 才能正常显示。
  function toAbs(url) {
    if (!url) return url;
    url = String(url).trim();
    if (/^https?:\/\//i.test(url)) return url;        // 已是绝对地址
    if (/^\/\//i.test(url)) return 'https:' + url;     // 协议相对 //host → https://host
    if (/^data:/i.test(url) || /^blob:/i.test(url)) return url; // 内嵌资源
    if (/^[a-z][a-z0-9+.-]*:/i.test(url)) return url;  // 其它 scheme（mailto:、javascript: 等）保持原样
    if (url.charAt(0) === '/') return ORIGIN + url;    // 站点根相对 /_static/...
    return ORIGIN + '/' + url;                         // 其它相对路径
  }

  /* ---------------------------------------------------------------- 内联渲染 */
  function inline(node, ctx) {
    let out = '';
    (node.childNodes || []).forEach((n) => {
      if (n.nodeType === 3) {
        out += n.nodeValue.replace(/\s+/g, ' ');
        return;
      }
      if (n.nodeType !== 1) return;
      const tag = n.tagName.toUpperCase();
      if (tag === 'BR') { out += '  \n'; return; }
      if (tag === 'IMG') {
        const src = toAbs(n.getAttribute('src') || '');
        const alt = n.getAttribute('alt') || '截图';
        if (isGoodUrl(src)) {
          ctx.images.push(src);
          out += `![${alt}](${src})`;
        } else if (src) {
          out += `[图片:${src}]`;
        }
        return;
      }
      if (tag === 'A') {
        const href = n.getAttribute('href') || '';
        const txt = inline(n, ctx).trim();
        if (!txt) return;
        if (href && !/^#/.test(href) && !/^javascript:/i.test(href)) out += `[${txt}](${href})`;
        else out += txt;
        return;
      }
      if (tag === 'CODE') {
        const t = (n.textContent || '').replace(/`/g, '\\`');
        out += '`' + t + '`';
        return;
      }
      if (tag === 'STRONG' || tag === 'B') {
        const t = inline(n, ctx).trim();
        if (t) out += '**' + t + '**';
        return;
      }
      if (tag === 'EM' || tag === 'I') {
        const t = inline(n, ctx).trim();
        if (t) out += '*' + t + '*';
        return;
      }
      if (tag === 'INPUT') return; // 章节标题输入框，已单独提取
      out += inline(n, ctx);
    });
    return out;
  }

  /* ---------------------------------------------------------------- 块级渲染 */

  // 把容器内的节点拆成「内联部分」和「列表部分」，保持文档顺序
  function splitContent(node, inlineParts, nested) {
    if (node.nodeType === 1) {
      const t = node.tagName.toUpperCase();
      if (t === 'UL' || t === 'OL') { nested.push(node); return; }
      if (t === 'DIV' || t === 'P' || t === 'SECTION' || t === 'SPAN') {
        if (node.querySelector('ul,ol')) {
          Array.prototype.forEach.call(node.childNodes, (c) => splitContent(c, inlineParts, nested));
          return;
        }
      }
    }
    inlineParts.push(node);
  }

  function blockList(listEl, ctx, indent) {
    const isOl = listEl.tagName.toUpperCase() === 'OL';
    const start = parseInt(listEl.getAttribute('start') || '1', 10) || 1;
    const pad = ' '.repeat(indent);
    const lines = [];
    let idx = start;
    const items = Array.prototype.filter.call(listEl.children || [], (c) => c.tagName.toUpperCase() === 'LI');

    items.forEach((li) => {
      const marker = isOl ? idx++ + '. ' : '- ';
      // li 的内容分成「内联部分」和「嵌套列表部分」
      const inlineParts = [];
      const nested = [];
      Array.prototype.forEach.call(li.childNodes, (n) => splitContent(n, inlineParts, nested));

      const fake = { childNodes: inlineParts };
      let txt = tidy(inline(fake, ctx)).replace(/\n/g, ' ').trim();
      lines.push(pad + marker + txt);

      nested.forEach((sub) => {
        const subPad = pad + ' '.repeat(marker.length);
        blockList(sub, ctx, subPad.length).forEach((l) => lines.push(l));
      });
    });
    return lines;
  }

  function renderBlocks(root, ctx, level) {
    const out = [];
    (root.childNodes || []).forEach((n) => {
      if (n.nodeType === 3) {
        const t = tidy(decode(n.nodeValue));
        if (t.trim()) out.push(t);
        return;
      }
      if (n.nodeType !== 1) return;
      const tag = n.tagName.toUpperCase();

      if (tag === 'INPUT') return;
      if (tag === 'A' && n.getAttribute('data-anchor') === 'catalogue') return;
      if (tag === 'SCRIPT' || tag === 'STYLE') return;

      if (tag === 'UL' || tag === 'OL') {
        out.push(blockList(n, ctx, 0).join('\n'));
        return;
      }
      if (tag === 'PRE') {
        const code = n.querySelector('code');
        const txt = (code || n).textContent || '';
        const fence = '```';
        out.push(fence + '\n' + txt.replace(/\n+$/, '') + '\n' + fence);
        return;
      }
      if (tag === 'IMG') {
        const src = toAbs(n.getAttribute('src') || '');
        const alt = n.getAttribute('alt') || '截图';
        if (isGoodUrl(src)) { ctx.images.push(src); out.push(`![${alt}](${src})`); }
        else if (src) out.push(`[图片:${src}]`);
        return;
      }
      if (tag === 'HR') { out.push('---'); return; }
      if (/^H[1-6]$/.test(tag)) {
        const t = tidy(inline(n, ctx)).trim();
        if (t) out.push('#'.repeat(Math.min(6, level + +tag[1])) + ' ' + t);
        return;
      }
      if (tag === 'TABLE') { out.push(renderTable(n, ctx)); return; }

      if (BLOCK_TAGS[tag]) {
        const isChapter = /mceNonEditable/i.test(n.getAttribute('class') || '');
        if (isChapter) {
          const parts = renderBlocks(n, ctx, level);
          if (parts.length) out.push(parts.join('\n\n'));
          return;
        }
        const inner = renderBlocks(n, ctx, level);
        if (inner.length) out.push(inner.join('\n\n'));
        return;
      }

      // 行内级：整块作为段落
      const t = tidy(inline(n, ctx));
      if (t.trim()) out.push(t);
    });
    return out.filter((x) => x && String(x).trim());
  }

  function renderTable(table, ctx) {
    const rows = [];
    (table.querySelectorAll('tr') || []).forEach((tr) => {
      const cells = [];
      (tr.children || []).forEach((c) => {
        cells.push(tidy(inline(c, ctx)).replace(/\|/g, '\\|').replace(/\n/g, ' ').trim());
      });
      if (cells.length) rows.push(cells);
    });
    if (!rows.length) return '';
    const cols = Math.max.apply(null, rows.map((r) => r.length));
    const norm = rows.map((r) => {
      while (r.length < cols) r.push('');
      return r;
    });
    const head = norm[0];
    const body = norm.slice(1);
    const L = ['| ' + head.join(' | ') + ' |', '| ' + head.map(() => '---').join(' | ') + ' |'];
    body.forEach((r) => L.push('| ' + r.join(' | ') + ' |'));
    return L.join('\n');
  }

  /* ------------------------------- 章节切分（核心，从 input[value] 还原标题） */
  // 前端把「有序步骤 + 其说明」渲染成 <ol>…</ol><ul>…</ul> 两个兄弟节点，
  // 语义上 ul 属于 ol 的最后一步，这里把它收进去，Markdown 才能正确缩进。
  // 编辑器会给每个列表套一层 <div>，导致 ol 与其说明 ul 不是兄弟节点。
  // 先把「只含单个列表、无文本」的包装 div 解包。
  function unwrapListWrappers(root) {
    if (!root || !root.children) return;
    let changed = true;
    while (changed) {
      changed = false;
      Array.prototype.slice.call(root.children).forEach((c) => {
        if (c.tagName !== 'DIV') return;
        const kids = Array.prototype.filter.call(c.children, (k) => k.nodeType === 1);
        const texts = Array.prototype.filter.call(
          c.childNodes, (n) => n.nodeType === 3 && n.nodeValue && n.nodeValue.trim()
        );
        if (kids.length === 1 && (kids[0].tagName === 'UL' || kids[0].tagName === 'OL') && !texts.length) {
          root.replaceChild(kids[0], c);
          changed = true;
        }
      });
    }
    Array.prototype.slice.call(root.children).forEach(unwrapListWrappers);
  }

  function normalizeSteps(root) {
    if (!root || !root.children) return;
    unwrapListWrappers(root);
    const kids = Array.prototype.slice.call(root.children || []);
    for (let i = 0; i < kids.length; i++) {
      const k = kids[i], nk = kids[i + 1];
      if (k.tagName === 'OL' && nk && nk.tagName === 'UL') {
        const lis = k.children || [];
        const last = lis[lis.length - 1];
        if (last && last.tagName === 'LI') last.appendChild(nk);
      }
    }
    Array.prototype.slice.call(root.children || []).forEach((c) => normalizeSteps(c));
  }

  function sectionTitle(b) {
    let name = '';
    const inp = b.querySelector('input[value]');
    if (inp) name = decode(inp.getAttribute('value') || '');
    if (!name) {
      const a = b.querySelector('a[data-text]');
      if (a) name = decode(a.getAttribute('data-text') || '');
    }
    return name.replace(/^\s*\*+\s*/, '').trim(); // 去掉必填星号
  }

  function extractSections(html) {
    const doc = getDoc(html);
    const root = doc.body;
    const sections = [];

    // 章节块：div[class*=mceNonEditable]，标题来自内部 input[value] 或 a[data-text]
    const blocks = root.querySelectorAll('div[class*="mceNonEditable"]');
    if (blocks && blocks.length) {
      blocks.forEach((b) => {
        // 跳过嵌套在其它章节块里的容器，只取最外层
        if (b.parentElement && b.parentElement.closest('div[class*="mceNonEditable"]')) return;
        sections.push({ name: sectionTitle(b), node: b });
      });
    }

    // 兜底：没有识别到章节就把整体当一段
    if (!sections.length) {
      sections.push({ name: '', node: root });
      return sections;
    }

    // 章节块之外可能还有零散内容（如开头的 case-tinymce-wrap 包裹层）
    return sections;
  }

  /* ------------------------------------------------------------- 对外：解析 */
  function parseCase(html) {
    const ctx = { images: [] };
    const sections = extractSections(html).map((s) => {
      const body = s.node.cloneNode(true);
      // 移除标题输入框与目录锚点，避免混进正文
      (body.querySelectorAll('input') || []).forEach((i) => i.remove());
      (body.querySelectorAll('a[data-anchor="catalogue"]') || []).forEach((a) => a.remove());
      normalizeSteps(body);
      const parts = renderBlocks(body, ctx, 0);
      return { name: s.name, md: parts.join('\n\n').trim() };
    }).filter((s) => s.md);

    return {
      sections,
      images: ctx.images.slice(),
      markdown: sections.map((s) => (s.name ? '### ' + s.name + '\n\n' : '') + s.md).join('\n\n'),
    };
  }

  /* -------------------------------------------------- 对外：正文转纯文本 */
  function plainText(html) {
    const p = parseCase(html);
    return p.markdown
      .replace(/!\[([^\]]*)\]\(([^)]+)\)/g, (m, alt) => '[图片: ' + (alt || '截图') + ']')
      .replace(/\[([^\]]*)\]\(([^)]+)\)/g, '$1')
      .replace(/\*\*/g, '')
      .replace(/^#+\s*/gm, '')
      .trim();
  }

  /* ------------------------------------------- 对外：清洗后的正文 HTML 片段 */
  function cleanHtml(html) {
    const doc = getDoc(html);
    const root = doc.body;
    (root.querySelectorAll('a[data-anchor="catalogue"]') || []).forEach((a) => a.remove());
    normalizeSteps(root);
    const blocks = root.querySelectorAll('div[class*="mceNonEditable"]');
    (blocks || []).forEach((b) => {
      if (b.parentElement && b.parentElement.closest('div[class*="mceNonEditable"]')) return;
      const inp = b.querySelector('input[value]');
      const name = sectionTitle(b);
      if (inp) inp.remove();
      if (name) {
        const h = doc.createElement('h3');
        h.textContent = name;
        b.insertBefore(h, b.firstChild);
      }
    });
    (root.querySelectorAll('[contenteditable]') || []).forEach((n) => n.removeAttribute('contenteditable'));
    (root.querySelectorAll('input,script,style') || []).forEach((n) => n.remove());
    (root.querySelectorAll('img') || []).forEach((img) => {
      const s = img.getAttribute('src');
      if (s) img.setAttribute('src', toAbs(s)); // 相对路径补全为绝对地址，否则本地打开 HTML 图片失效
      img.setAttribute('style', 'max-width:100%;height:auto;border:1px solid #e3e6ec;border-radius:6px;margin:6px 0');
      img.setAttribute('loading', 'lazy');
    });
    return root.innerHTML;
  }

  /* --------------------------------------------- 对外：生成单文件 HTML 文档 */
  // 版本可能有几十个，全文列出会把元信息行撑爆，这里做折叠
  function shortVersions(s, keep) {
    if (!s) return '';
    const parts = String(s).split(/\s*\|\s*/).filter(Boolean);
    keep = keep || 3;
    if (parts.length <= keep + 1) return parts.join(' ｜ ');
    return parts.slice(0, keep).join(' ｜ ') + ` 等 ${parts.length} 个版本`;
  }

  function buildHtmlDoc(rows, meta, opts) {
    opts = opts || {};
    const title = (meta && meta.title) || '深信服案例库导出';
    const pageSize = opts.pageSize || 20;

    // 预清洗正文；把 img 的 src 换成 data-src，翻到哪一页才加载哪页的图
    const payload = rows.map((r) => {
      let h = r.detail_html
        ? cleanHtml(r.detail_html)
        : '<p>' + esc(r.summary || '').replace(/\n/g, '<br>') + '</p>';
      h = h.replace(/(<img\b[^>]*?)\ssrc="([^"]*)"/gi, '$1 data-src="$2"');
      return {
        t: r.title || '(无标题)',
        p: r.product_name || '',
        m: r.child_modules || r.main_modules || '',
        v: shortVersions(r.version_codes),
        s: r.suite_version || '',
        u: r.update_time || '',
        id: r.case_id || '',
        url: r.url || '',
        h: h,
        img: (h.match(/data-src=/g) || []).length,
      };
    });

    // 防止正文里出现 </script> 提前闭合，同时处理 JSON 中的行分隔符
    const dataJson = JSON.stringify(payload)
      .replace(/<\//g, '<\\/')
      .replace(/\u2028/g, '\\u2028')
      .replace(/\u2029/g, '\\u2029');

    const sub = [
      '共 ' + rows.length + ' 条',
      '导出时间 ' + esc(new Date().toLocaleString('zh-CN')),
      opts.embeddedImages ? '图片已内嵌（可离线阅读）' : '',
      opts.part ? '第 ' + opts.part + ' 卷' : '',
    ].filter(Boolean).join(' ｜ ');

    return `<!DOCTYPE html>
<html lang="zh-CN"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>${esc(title)}</title>
<style>
:root{--bd:#e3e6ec;--fg:#1f2329;--mu:#6b7280;--ac:#1a6fd4}
*{box-sizing:border-box}
body{margin:0;font:15px/1.75 -apple-system,"Segoe UI","Microsoft YaHei",sans-serif;color:var(--fg);background:#f5f6f8}
header{background:#fff;border-bottom:1px solid var(--bd);padding:16px 24px}
header h1{margin:0 0 4px;font-size:20px}
header .sub{color:var(--mu);font-size:12.5px}
.bar{position:sticky;top:0;z-index:9;background:#fff;border-bottom:1px solid var(--bd);
  padding:10px 24px;display:flex;gap:10px;align-items:center;flex-wrap:wrap}
.bar input[type=search]{flex:1;min-width:180px;max-width:340px;padding:6px 10px;border:1px solid var(--bd);
  border-radius:6px;font-size:13px;outline:none}
.bar input[type=search]:focus{border-color:var(--ac)}
.bar button{background:#f2f4f7;border:1px solid var(--bd);border-radius:6px;padding:5px 11px;
  font-size:13px;cursor:pointer;color:#334}
.bar button:hover:not(:disabled){background:#e6ebf3;border-color:var(--ac)}
.bar button:disabled{opacity:.4;cursor:default}
.bar select{padding:5px 6px;border:1px solid var(--bd);border-radius:6px;font-size:13px}
.bar .info{color:var(--mu);font-size:12.5px;margin-left:auto}
main{max-width:960px;margin:0 auto;padding:16px 16px 90px}
nav.toc{background:#fff;border:1px solid var(--bd);border-radius:10px;padding:10px 16px;margin-bottom:14px}
nav.toc h3{margin:0 0 6px;font-size:13px;color:var(--mu);font-weight:600}
nav.toc ol{margin:0;padding-left:22px;columns:2;column-gap:26px}
nav.toc li{font-size:13px;break-inside:avoid;margin:2px 0}
nav.toc a{color:var(--ac);text-decoration:none}
nav.toc a:hover{text-decoration:underline}
article.case{background:#fff;border:1px solid var(--bd);border-radius:10px;padding:18px 24px;margin-bottom:14px}
article.case h2{font-size:17px;margin:0 0 10px;padding-bottom:8px;border-bottom:2px solid var(--ac);line-height:1.5}
.meta{color:var(--mu);font-size:12.5px;margin-bottom:12px;padding:8px 12px;background:#f8f9fb;border-radius:6px}
.meta a{color:var(--ac);text-decoration:none}
.body h3{font-size:15.5px;margin:22px 0 8px;color:var(--ac);border-left:4px solid var(--ac);padding-left:9px}
.body p{margin:8px 0}
.body ul,.body ol{margin:8px 0;padding-left:26px}
.body li{margin:4px 0}
.body pre{background:#f6f8fa;border:1px solid var(--bd);border-radius:6px;padding:12px;overflow:auto;font:13px/1.6 Menlo,Consolas,monospace}
.body code{background:#f2f4f7;padding:1px 5px;border-radius:4px;font-size:13px}
.body img{max-width:100%;border:1px solid var(--bd);border-radius:6px;margin:6px 0;background:#fafbfc;min-height:24px}
mark{background:#ffe9a8;padding:0 2px;border-radius:2px}
.empty{text-align:center;color:var(--mu);padding:60px 0}
@media print{.bar,nav.toc{display:none}body{background:#fff}article.case{break-inside:avoid;border:none;padding:0 0 12px}}
</style></head>
<body>
<header>
  <h1>${esc(title)}</h1>
  <div class="sub">${sub}</div>
</header>
<div class="bar">
  <input type="search" id="q" placeholder="搜索标题 / 产品线 / 模块…" oninput="onSearch(this.value)">
  <button onclick="go(1)" id="b-first">« 首页</button>
  <button onclick="go(st.page-1)" id="b-prev">‹ 上一页</button>
  <button onclick="go(st.page+1)" id="b-next">下一页 ›</button>
  <button onclick="go(pages())" id="b-last">末页 »</button>
  <select onchange="setSize(this.value)" id="sel-size">
    <option value="10">10 条/页</option>
    <option value="20" selected>20 条/页</option>
    <option value="50">50 条/页</option>
    <option value="100">100 条/页</option>
  </select>
  <button onclick="expandAll()" id="b-all">展开全部（便于打印）</button>
  <span class="info" id="info"></span>
</div>
<main>
  <nav class="toc" id="toc"></nav>
  <div id="list"></div>
</main>
<script id="sfc-data" type="application/json">${dataJson}</script>
<script>
var DATA = JSON.parse(document.getElementById('sfc-data').textContent);
var st = { q: '', page: 1, size: ${pageSize}, all: false };

function esc(s){return String(s==null?'':s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;')}
function hl(s){
  var t = esc(s);
  if(!st.q) return t;
  try{ return t.replace(new RegExp('('+st.q.replace(/[.*+?^\${}()|[\]\\]/g,'\\$&')+')','gi'),'<mark>$1</mark>') }catch(e){ return t }
}
function filtered(){
  if(!st.q) return DATA;
  var q = st.q.toLowerCase();
  return DATA.filter(function(d){
    return (d.t+' '+d.p+' '+d.m+' '+d.id).toLowerCase().indexOf(q) >= 0;
  });
}
function pages(){ return st.all ? 1 : Math.max(1, Math.ceil(filtered().length / st.size)) }
function metaOf(d){
  return [d.p?'产品线：'+esc(d.p):'', d.m?'模块：'+esc(d.m):'', d.v?'适用版本：'+esc(d.v):'',
          d.s?'架构：'+esc(d.s):'', d.u?'更新：'+esc(d.u):''].filter(Boolean).join(' ｜ ');
}
function cardOf(d, idx){
  var ml = metaOf(d);
  return '<article class="case" id="case-'+(idx+1)+'">'+
    '<h2>'+(idx+1)+'. '+hl(d.t)+'</h2>'+
    '<div class="meta">'+(ml?'<div>'+ml+'</div>':'')+
      '<div>案例ID：'+esc(d.id)+(d.url?' ｜ <a href="'+esc(d.url)+'" target="_blank" rel="noopener">在官网打开 ↗</a>':'')+'</div>'+
    '</div>'+
    '<div class="body">'+d.h+'</div></article>';
}
function lazyLoad(){
  var imgs = document.querySelectorAll('#list img[data-src]');
  for(var i=0;i<imgs.length;i++){
    var im = imgs[i];
    im.src = im.getAttribute('data-src');
    im.removeAttribute('data-src');
  }
}
function render(){
  var all = filtered();
  if(st.page > pages()) st.page = pages();
  if(st.page < 1) st.page = 1;
  var start = st.all ? 0 : (st.page-1)*st.size;
  var end = st.all ? all.length : Math.min(all.length, start + st.size);
  var slice = all.slice(start, end);

  var box = document.getElementById('list');
  var toc = document.getElementById('toc');
  if(!slice.length){
    box.innerHTML = '<div class="empty">没有匹配的案例</div>';
    toc.style.display = 'none';
  } else {
    toc.style.display = '';
    var html = [];
    for(var i=0;i<slice.length;i++) html.push(cardOf(slice[i], start+i));
    box.innerHTML = html.join('');
    var tl = [];
    for(var j=0;j<slice.length;j++) tl.push('<li><a href="#case-'+(start+j+1)+'">'+(start+j+1)+'. '+esc(slice[j].t.slice(0,44))+'</a></li>');
    toc.innerHTML = '<h3>本页目录'+(st.all?'（全部）':'（第 '+(start+1)+'-'+end+' 条，共 '+all.length+' 条）')+'</h3><ol>'+tl.join('')+'</ol>';
    lazyLoad();
  }
  document.getElementById('info').textContent =
    (all.length === 0 ? '共 0 条'
      : st.all ? '全部 ' + all.length + ' 条'
      : '第 ' + (start + 1) + '-' + end + ' 条 / 共 ' + all.length + ' 条')
    + (st.q ? '（已搜索「' + st.q + '」）' : '');
  var last = st.all || st.page >= pages();
  document.getElementById('b-first').disabled = st.all || st.page <= 1;
  document.getElementById('b-prev').disabled  = st.all || st.page <= 1;
  document.getElementById('b-next').disabled  = last;
  document.getElementById('b-last').disabled  = last;
  try { window.scrollTo(0, 0); } catch (e) {}
}
function go(p){ st.page = p; render() }
function onSearch(v){ st.q = (v||'').trim(); st.page = 1; st.all = false; render() }
function setSize(v){ st.size = parseInt(v,10)||20; st.page = 1; st.all = false; render() }
function expandAll(){
  st.all = true;
  var b = document.getElementById('b-all');
  b.textContent = '已展开全部，可 Ctrl+P 打印';
  b.disabled = true;
  render();
}
document.addEventListener('keydown', function(e){
  if(e.target && e.target.tagName === 'INPUT') return;
  if(e.key === 'ArrowRight' && !document.getElementById('b-next').disabled) go(st.page+1);
  if(e.key === 'ArrowLeft'  && !document.getElementById('b-prev').disabled) go(st.page-1);
});
render();
</script>
</body></html>`;
  }

  function esc(s) {
    return String(s == null ? '' : s)
      .replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
  }

    return { parseCase, plainText, cleanHtml, buildHtmlDoc, shortVersions, esc, tidy };
  })();

  /* ==========================================================================
   * 1. 工具函数
   * ========================================================================== */

  const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
  const pad2 = (n) => String(n).padStart(2, '0');

  function nowStamp() {
    const d = new Date();
    return (
      d.getFullYear() +
      pad2(d.getMonth() + 1) +
      pad2(d.getDate()) + '_' +
      pad2(d.getHours()) + pad2(d.getMinutes()) + pad2(d.getSeconds())
    );
  }

  function safeName(s) {
    return (s || 'all').replace(/[\\/:*?"<>|\s]+/g, '_').slice(0, 40);
  }

  function stripTags(html) {
    if (!html) return '';
    try {
      const D = (typeof unsafeWindow !== 'undefined' && unsafeWindow.DOMParser) || DOMParser;
      const dom = new D().parseFromString(html, 'text/html');
      let t = dom.body.textContent || '';
      return t.replace(/[ \t　]+/g, ' ').replace(/\n{3,}/g, '\n\n').trim();
    } catch (e) {
      return String(html)
        .replace(/<br\s*\/?>/gi, '\n')
        .replace(/<\/(p|div|li|h[1-6]|tr)>/gi, '\n')
        .replace(/<[^>]+>/g, '')
        .replace(/&nbsp;/g, ' ')
        .replace(/&amp;/g, '&')
        .replace(/&lt;/g, '<')
        .replace(/&gt;/g, '>')
        .replace(/[ \t　]+/g, ' ')
        .replace(/\n{3,}/g, '\n\n')
        .trim();
    }
  }

  function csvCell(v) {
    const s = v === null || v === undefined ? '' : String(v);
    return '"' + s.replace(/"/g, '""') + '"';
  }

  function parseTime(s) {
    if (!s) return 0;
    const t = new Date(String(s).replace(/-/g, '/')).getTime();
    return isNaN(t) ? 0 : t;
  }

  const RECENT_MAP = { '7d': 7, '30d': 30, '90d': 90, '180d': 180, '365d': 365 };

  /* ==========================================================================
   * 2. 网络层：优先 GM_xmlhttpRequest（自动携带登录态 Cookie），回退 fetch
   * ========================================================================== */

  function xhr(opts) {
    // opts: { method, url, data(json string|null), headers, timeout }
    return new Promise((resolve, reject) => {
      const doFetch = () => {
        const f = (typeof unsafeWindow !== 'undefined' && unsafeWindow.fetch) || fetch;
        if (!f) return reject(new Error('no transport available'));
        const init = {
          method: opts.method || 'GET',
          credentials: 'include',
          headers: opts.headers || {},
        };
        if (opts.data) init.body = opts.data;
        f(opts.url, init)
          .then(async (res) => {
            const txt = await res.text();
            resolve({ status: res.status, text: txt });
          })
          .catch(reject);
      };

      if (typeof GM_xmlhttpRequest === 'function') {
        try {
          GM_xmlhttpRequest({
            method: opts.method || 'GET',
            url: opts.url,
            data: opts.data || undefined,
            headers: opts.headers || {},
            timeout: opts.timeout || 30000,
            responseType: 'text',
            onload: (r) => resolve({ status: r.status, text: r.responseText }),
            onerror: () => doFetch(),
            ontimeout: () => reject(new Error('请求超时')),
          });
          return;
        } catch (e) {
          /* 落到 fetch */
        }
      }
      doFetch();
    });
  }

  const JSON_HEADERS = {
    Accept: 'application/vnd.edusoho.v2+json',
    'Content-Type': 'application/json',
    'X-Requested-With': 'xmlhttprequest',
    HTTP_X_REQUESTED_WITH: 'xmlhttprequest',
    Origin: ORIGIN,
    Referer: ORIGIN + '/cases/list',
    'User-Agent': UA,
  };

  const PLAIN_HEADERS = {
    Accept: 'application/vnd.edusoho.v2+json',
    'X-Requested-With': 'xmlhttprequest',
    HTTP_X_REQUESTED_WITH: 'xmlhttprequest',
    Referer: ORIGIN + '/cases/list',
    'User-Agent': UA,
  };

  async function getJSON(url, retry = 2) {
    let lastErr;
    for (let i = 0; i <= retry; i++) {
      if (state.cancelToken < 0) throw new Error('CANCELLED');
      try {
        const r = await xhr({ method: 'GET', url, headers: PLAIN_HEADERS });
        if (r.status !== 200) throw new Error('HTTP ' + r.status);
        const obj = JSON.parse(r.text);
        if (obj && (obj.code === 0 || obj.code === 200)) return obj;
        throw new Error('业务码异常: code=' + (obj && obj.code) + ' msg=' + (obj && obj.msg));
      } catch (e) {
        lastErr = e;
        if (i < retry) await sleep(600 * (i + 1));
      }
    }
    throw lastErr;
  }

  async function postJSON(url, payload, retry = 2) {
    let lastErr;
    for (let i = 0; i <= retry; i++) {
      if (state.cancelToken < 0) throw new Error('CANCELLED');
      try {
        const r = await xhr({ method: 'POST', url, headers: JSON_HEADERS, data: JSON.stringify(payload) });
        if (r.status !== 200) {
          // 401/403 通常是登录态失效
          if (r.status === 401 || r.status === 403) throw new Error('AUTH:' + r.status);
          throw new Error('HTTP ' + r.status);
        }
        const obj = JSON.parse(r.text);
        if (obj && (obj.code === 0 || obj.code === 200)) return obj;
        throw new Error('业务码异常: code=' + (obj && obj.code) + ' msg=' + (obj && obj.msg));
      } catch (e) {
        lastErr = e;
        if (String(e.message).startsWith('AUTH')) throw e;
        if (i < retry) await sleep(600 * (i + 1));
      }
    }
    throw lastErr;
  }

  /* ==========================================================================
   * 3. 并发池
   * ========================================================================== */

  async function pool(tasks, limit, onEach) {
    let idx = 0;
    const workers = new Array(Math.min(limit, tasks.length)).fill(0).map(async () => {
      while (true) {
        if (state.cancelToken < 0) return;
        while (state.paused) await sleep(300);
        const i = idx++;
        if (i >= tasks.length) return;
        try {
          await tasks[i]();
          if (onEach) onEach(null, i);
        } catch (e) {
          if (onEach) onEach(e, i);
        }
      }
    });
    await Promise.all(workers);
  }

  /* ==========================================================================
   * 4. 元数据：产品线 / 模块树 / 版本
   * ========================================================================== */

  async function loadProductList(force) {
    if (state.productCache && !force) return state.productCache;
    const obj = await getJSON(API.productList);
    const leaves = [];
    const walk = (nodes, trail) => {
      (nodes || []).forEach((n) => {
        state.productNameMap[n.id] = n.name;
        if (n.caseAble) leaves.push({ id: n.id, name: n.name, group: trail });
        if (n.children && n.children.length) walk(n.children, trail + ' / ' + n.name);
      });
    };
    const groups = [];
    (obj.rows || []).forEach((lv0) => {
      walk(lv0.children || [], lv0.name);
      groups.push({ id: lv0.id, name: lv0.name });
    });
    state.productCache = { leaves, groups, raw: obj.rows };
    return state.productCache;
  }

  async function loadModuleTree(pid) {
    if (!pid) return [];
    if (state.moduleCache[pid]) return state.moduleCache[pid];
    const obj = await getJSON(API.moduleTree(pid));
    state.moduleCache[pid] = obj.rows || [];
    return state.moduleCache[pid];
  }

  async function loadVersionList(pid) {
    if (!pid) return [];
    if (state.versionCache[pid]) return state.versionCache[pid];
    const obj = await getJSON(API.versionList(pid));
    const rows = obj.rows || [];
    rows.forEach((v) => (state.versionNameMap[v.id] = v.code));
    state.versionCache[pid] = rows;
    return rows;
  }

  /* ==========================================================================
   * 5. 断点续跑缓存（localStorage，超出配额自动降级）
   * ========================================================================== */

  const cache = {
    enabled: true,
    key: '',
    keys: [],
    disabled: false,
    init(taskKey) {
      this.key = K_STORE + ':' + taskKey;
      this.keys = [];
      this.disabled = false;
    },
    put(page, rows) {
      if (!this.enabled || this.disabled) return;
      try {
        const k = this.key + ':p:' + page;
        localStorage.setItem(k, JSON.stringify(rows));
        this.keys.push(k);
        localStorage.setItem(this.key + ':idx', JSON.stringify(this.keys));
      } catch (e) {
        this.disabled = true;
        log('⚠ 本地缓存空间不足，已自动关闭断点续跑（不影响本次抓取）', 'warn');
      }
    },
    load() {
      if (!this.enabled || this.disabled) return { pages: {}, list: [] };
      try {
        const idx = JSON.parse(localStorage.getItem(this.key + ':idx') || '[]');
        const out = [];
        const pages = {};
        idx.forEach((k) => {
          const v = localStorage.getItem(k);
          if (v === null) return;
          const rows = JSON.parse(v);
          const p = parseInt(k.split(':p:')[1], 10);
          pages[p] = true;
          out.push(...rows);
        });
        this.keys = idx;
        return { pages, list: out };
      } catch (e) {
        return { pages: {}, list: [] };
      }
    },
    clear() {
      if (!this.key) return;
      try {
        (JSON.parse(localStorage.getItem(this.key + ':idx') || '[]') || []).forEach((k) =>
          localStorage.removeItem(k)
        );
        localStorage.removeItem(this.key + ':idx');
      } catch (e) {}
      this.keys = [];
    },
  };

  function clearAllCache() {
    try {
      const del = [];
      for (let i = 0; i < localStorage.length; i++) {
        const k = localStorage.key(i);
        if (k && k.indexOf(K_STORE) === 0) del.push(k);
      }
      del.forEach((k) => localStorage.removeItem(k));
      log('已清空全部断点缓存（' + del.length + ' 条）');
    } catch (e) {
      log('清空缓存失败: ' + e.message, 'err');
    }
  }

  /* ==========================================================================
   * 6. 核心抓取流程
   * ========================================================================== */

  function buildSearchPayload(pageNum) {
    // 复刻前端 selectPost(): 选中子模块时，需把其父主模块从 mainModuleIds 中剔除
    let main = cfg.mainModuleIds.slice();
    const child = cfg.childModuleIds.slice();
    if (child.length) {
      const flat = [];
      const flatten = (nodes) =>
        (nodes || []).forEach((n) => {
          flat.push(n);
          flatten(n.children);
        });
      flatten(state.moduleCache[cfg.productLineId] || []);
      child.forEach((cid) => {
        const node = flat.find((n) => String(n.id) === String(cid));
        if (node && node.pid) main = main.filter((m) => String(m) !== String(node.pid));
      });
    }
    return {
      childModuleIds: child.map(Number),
      keyword: cfg.keyword || '',
      mainModuleIds: main.map(Number),
      productLineId: cfg.productLineId ? String(cfg.productLineId) : '',
      versionId: cfg.versionId ? String(cfg.versionId) : '',
      pageNum: pageNum,
      pageSize: cfg.pageSize,
    };
  }

  function normalizeRow(r) {
    const pid = r.product || cfg.productLineId || '';
    return {
      case_id: r.id || '',
      source_id: r.source_id || (r.id ? String(r.id).split(':').pop() : ''),
      url: DETAIL_URL(pid, r.source_id || (r.id ? String(r.id).split(':').pop() : '')),
      product_id: pid,
      product_name: state.productNameMap[pid] || '',
      title: r.title || '',
      main_modules: r.main_module_names || '',
      main_module_ids: r.main_module_ids || '',
      child_modules: r.child_module_names || '',
      child_module_ids: r.child_module_ids || '',
      version_ids: r.product_version || '',
      // 只保留能映射出名称的版本；全是裸 id 时再回退显示 id，避免 "70" 这种无意义值
      version_codes: (function () {
        const ids = (r.product_version || '').split(',').filter(Boolean);
        const named = ids.map((v) => state.versionNameMap[v]).filter(Boolean);
        return named.length ? named.join(' | ') : ids.join(',');
      })(),
      create_time: r.create_time || '',
      update_time: r.update_time || '',
      summary: r.content || '',
      detail_html: '',
      detail_md: '',
      detail_text: '',
      images: [],
      sections: [],
      detail_fetched: false,
    };
  }

  async function crawl() {
    if (state.running) return;
    state.running = true;
    state.paused = false;
    state.cancelToken = 1;
    state.startedAt = Date.now();
    state.listRows = [];
    state.donePages = 0;
    state.detailDone = 0;

    const taskKey = [
      cfg.productLineId || 'all',
      cfg.versionId || 'v0',
      cfg.mainModuleIds.join('-') || 'm0',
      cfg.childModuleIds.join('-') || 'c0',
      encodeURIComponent(cfg.keyword || ''),
      cfg.pageSize,
    ].join('|');
    cache.init(taskKey);
    if (!cfg.resume) cache.clear();

    setRunningUI(true);
    log('▶ 开始抓取  ' + describeTask());

    try {
      // 预热：产品名 & 版本名映射
      if (cfg.productLineId) {
        try {
          await loadVersionList(cfg.productLineId);
        } catch (e) {
          log('⚠ 版本列表加载失败：' + e.message, 'warn');
        }
      }

      // 首页探测总数
      log('正在探测总数…');
      const first = await postJSON(API.search, buildSearchPayload(0));
      const rows = first.rows || {};
      const total = rows.totalElements || 0;
      let totalPages = rows.totalPages || 0;
      // ES 深翻页上限 10000 条，超出的页取不到数据，提前截断避免大量无效请求
      const esMaxPage = Math.max(1, Math.floor(10000 / cfg.pageSize));
      if (totalPages > esMaxPage) {
        log(`⚠ 命中 ${total} 条，超过 ES 深翻页上限（10000 条 / 每页 ${cfg.pageSize} = ${esMaxPage} 页），` +
          `本次最多取前 ${esMaxPage} 页；建议加产品线/模块/关键词等条件分批抓取`, 'warn');
        totalPages = esMaxPage;
      }
      if (cfg.maxPages > 0 && totalPages > cfg.maxPages) totalPages = cfg.maxPages;
      state.totalPages = totalPages;
      log(`共 ${total} 条 / ${rows.totalPages} 页${cfg.maxPages > 0 ? `，本次上限 ${totalPages} 页` : ''}`);

      const firstRows = (rows.content || []).map(normalizeRow);
      state.listRows = firstRows.slice();
      cache.put(0, firstRows);
      state.donePages = 1;
      updateProgress();

      // 断点：读取缓存
      const restored = cfg.resume ? cache.load() : { pages: {}, list: [] };
      if (cfg.resume && restored.list.length) {
        log(`↺ 断点恢复：${restored.list.length} 条（${Object.keys(restored.pages).length} 页）`);
        const seen = new Set(state.listRows.map((r) => r.case_id));
        let legacy = 0;
        restored.list.forEach((r) => {
          // 旧版缓存没有结构化正文字段，标记为未抓取，稍后重新拉详情
          if (cfg.fetchDetail && !r.detail_md) { r.detail_fetched = false; legacy++; }
          if (!seen.has(r.case_id)) {
            seen.add(r.case_id);
            state.listRows.push(r);
          }
        });
        if (legacy) log(`（其中 ${legacy} 条为旧格式缓存，将重新抓取正文）`);
      }

      // 翻页
      const pages = [];
      for (let p = 1; p < totalPages; p++) {
        if (restored.pages[p]) {
          state.donePages++;
          continue;
        }
        pages.push(p);
      }
      if (pages.length) {
        log(`开始翻页抓取，剩余 ${pages.length} 页，并发 ${cfg.concurrency}`);
        await pool(
          pages.map((p) => async () => {
            const res = await postJSON(API.search, buildSearchPayload(p));
            const list = (res.rows && res.rows.content) || [];
            const nr = list.map(normalizeRow);
            state.listRows.push(...nr);
            cache.put(p, nr);
            state.donePages++;
            updateProgress();
            if (cfg.interval) await sleep(cfg.interval);
          }),
          cfg.concurrency,
          (err, i) => {
            if (err) {
              state.donePages++;
              log(`✗ 第 ${pages[i]} 页失败：${err.message}`, 'err');
              updateProgress();
            }
          }
        );
      }

      // 去重
      const seen = new Set();
      state.listRows = state.listRows.filter((r) => {
        if (seen.has(r.case_id)) return false;
        seen.add(r.case_id);
        return true;
      });

      // 时间过滤
      if (RECENT_MAP[cfg.onlyRecent]) {
        const days = RECENT_MAP[cfg.onlyRecent];
        const th = Date.now() - days * 86400000;
        const before = state.listRows.length;
        state.listRows = state.listRows.filter((r) => parseTime(r.update_time) >= th);
        log(`时间过滤（近 ${days} 天）：${before} → ${state.listRows.length} 条`);
      }

      log(`✔ 列表完成，共 ${state.listRows.length} 条`);

      // 详情正文
      if (cfg.fetchDetail && state.listRows.length) {
        log('开始抓取正文详情…');
        const targets = state.listRows.filter((r) => !r.detail_fetched && r.source_id);
        let n = 0;
        await pool(
          targets.map((row) => async () => {
            const obj = await getJSON(API.detail(row.source_id), 1);
            const d = obj.rows || {};
            row.detail_html = d.content || d.contentWeb || '';
            // 结构化解析：还原「问题描述 / 告警信息 / 根因 / 解决方案」等章节
            try {
              const parsed = SFCaseFmt.parseCase(row.detail_html);
              row.detail_md = parsed.markdown;
              row.sections = parsed.sections;
              row.images = parsed.images;
              row.detail_text = parsed.markdown
                .replace(/!\[([^\]]*)\]\(([^)]+)\)/g, (m, alt) => '[图片: ' + (alt || '截图') + ']')
                .replace(/\[([^\]]*)\]\(([^)]+)\)/g, '$1')
                .replace(/\*\*/g, '')
                .replace(/^#+\s*/gm, '');
            } catch (pe) {
              row.detail_text = stripTags(row.detail_html);
              row.detail_md = '';
            }
            row.product_name = d.productName || row.product_name;
            row.suite_version = d.suiteVersion || '';
            row.detail_main_modules = d.mainModuleNames || '';
            row.detail_child_modules = d.childModuleNames || '';
            row.detail_name = d.name || row.title;
            row.detail_fetched = true;
            n++;
            state.detailDone = n;
            updateProgress();
            if (cfg.interval) await sleep(Math.floor(cfg.interval / 2));
          }),
          cfg.detailConcurrency,
          (err) => {
            if (err) {
              n++;
              state.detailDone = n;
              log(`✗ 详情失败：${err.message}`, 'err');
              updateProgress();
            }
          }
        );
        log(`✔ 正文完成：${state.listRows.filter((r) => r.detail_fetched).length} / ${state.listRows.length}`);
      }

      log(`🎉 全部完成，共 ${state.listRows.length} 条，耗时 ${((Date.now() - state.startedAt) / 1000).toFixed(1)}s`);
      notify('抓取完成', `共 ${state.listRows.length} 条案例，可点击面板导出`);
    } catch (e) {
      if (String(e.message).startsWith('AUTH')) {
        log('✗ 登录态失效（HTTP ' + e.message.slice(5) + '），请先在浏览器中登录深信服社区后重试', 'err');
        notify('登录态失效', '请先在浏览器登录 support.sangfor.com.cn');
      } else if (e.message === 'CANCELLED') {
        log('⏹ 已停止');
      } else {
        log('✗ 抓取失败：' + e.message, 'err');
      }
    } finally {
      state.running = false;
      state.paused = false;
      setRunningUI(false);
      updateProgress();
    }
  }

  function describeTask() {
    const p = cfg.productLineId ? state.productNameMap[cfg.productLineId] || cfg.productLineId : '全部产品';
    return `产品线=${p} 关键词=${cfg.keyword || '(空)'} 版本=${cfg.versionId || '全部'}`;
  }

  /* ------------------------------------------------------ 关键字预搜索（先搜后爬） */
  // 官方返回的 highlightTitle 用 <span style="color:#1180ff"> 标记命中词，
  // 这里先把它替换成私有占位符，再去标签、转义，最后还原成 <mark>，避免注入风险。
  function safeHighlight(html) {
    let s = String(html || '');
    s = s.replace(/<span[^>]*color:\s*#?1180ff[^>]*>([\s\S]*?)<\/span>/gi, '\u0001$1\u0002');
    s = s.replace(/<[^>]+>/g, '');
    return SFCaseFmt.esc(s).replace(/\u0001/g, '<mark>').replace(/\u0002/g, '</mark>');
  }

  async function previewSearch() {
    const box = document.getElementById('sfc-preview');
    if (!box) return;
    const kw = cfg.keyword || '';
    box.style.display = '';
    box.innerHTML = '<div class="sfc-hint">搜索中…</div>';
    try {
      // 用与实际抓取相同的 pageSize，保证预览里的页数就是真正要爬的页数
      const payload = buildSearchPayload(0);
      const r = await postJSON(API.search, payload);
      const rows = r.rows || {};
      const total = rows.totalElements || 0;
      let pages = rows.totalPages || 0;
      const maxPage = Math.max(1, Math.floor(10000 / (cfg.pageSize || 20)));
      if (pages > maxPage) pages = maxPage; // ES 深翻页上限
      const list = (rows.content || []).slice(0, 8);

      if (!total) {
        box.innerHTML =
          `<div class="sfc-hint">${kw ? `关键字「${SFCaseFmt.esc(kw)}」` : '当前条件'}未命中任何案例</div>`;
        log(`预搜索：命中 0 条${kw ? `（关键字「${kw}」）` : ''}`, 'warn');
        return;
      }

      const items = list.map((c, i) => {
        const pid = c.product || cfg.productLineId || '';
        const title = safeHighlight(c.highlightTitle || c.title);
        const mod = [c.main_module_names, c.child_module_names].filter(Boolean).map(SFCaseFmt.esc).join(' / ');
        return `<div class="sfc-pv-item"><span class="sfc-pv-n">${i + 1}.</span>` +
          `<a href="${SFCaseFmt.esc(DETAIL_URL(pid, c.source_id))}" target="_blank" rel="noopener">${title}</a>` +
          (mod ? `<span class="sfc-pv-m">${mod}</span>` : '') + `</div>`;
      }).join('');

      box.innerHTML =
        `<div class="sfc-pv-head">命中 <b>${total}</b> 条 / ${pages} 页` +
        `${kw ? `　关键字「${SFCaseFmt.esc(kw)}」` : '　（未设置关键字）'}</div>` +
        items +
        `<div class="sfc-hint">确认命中无误后再点「开始抓取」；点标题可在官网打开</div>`;
      log(`预搜索：命中 ${total} 条 / ${pages} 页${kw ? `（关键字「${kw}」）` : ''}`);
    } catch (e) {
      box.innerHTML = `<div class="sfc-hint" style="color:#ff7b72">搜索失败：${SFCaseFmt.esc(e.message)}</div>`;
      log('预搜索失败：' + e.message, 'err');
    }
  }

  // 页面上自带的搜索框（如案例列表页的搜索框）与面板关键字双向同步
  const PAGE_SEARCH_SELECTORS = [
    'input[placeholder*="搜索"]', 'input[placeholder*="关键字"]', 'input[placeholder*="关键词"]',
    '.search-box input', '.search input', '.search-input input', '#searchInput', '#search',
  ];

  function findPageSearch() {
    for (const sel of PAGE_SEARCH_SELECTORS) {
      try {
        const n = document.querySelector(sel);
        if (n && typeof n.value === 'string' && n.offsetParent !== null) return n;
      } catch (e) {}
    }
    return null;
  }

  function syncFromPageSearch(silent) {
    const n = findPageSearch();
    if (!n || !n.value || !n.value.trim()) {
      if (!silent) log('未在页面上找到有内容的搜索框', 'warn');
      return false;
    }
    cfg.keyword = n.value.trim();
    const inp = document.getElementById('sfc-kw');
    if (inp) inp.value = cfg.keyword;
    updateTaskKeyHint();
    log(`已从页面搜索框同步关键字：${cfg.keyword}`);
    return true;
  }

  /* ==========================================================================
   * 7. 导出
   * ========================================================================== */

  const EXPORT_FIELDS = [
    ['case_id', '案例ID'],
    ['source_id', '源ID'],
    ['title', '标题'],
    ['product_id', '产品线ID'],
    ['product_name', '产品线'],
    ['main_modules', '主模块'],
    ['child_modules', '子模块'],
    ['version_codes', '适用版本'],
    ['suite_version', '架构版本'],
    ['create_time', '创建时间'],
    ['update_time', '更新时间'],
    ['url', '详情页链接'],
    ['summary', '列表摘要'],
    ['detail_md', '正文(Markdown)'],
    ['detail_text', '正文(纯文本)'],
    ['detail_html', '正文(HTML)'],
  ];

  function toCSV(rows) {
    const head = EXPORT_FIELDS.map((f) => csvCell(f[1])).join(',');
    const body = rows
      .map((r) => EXPORT_FIELDS.map((f) => csvCell(r[f[0]] !== undefined ? r[f[0]] : '')).join(','))
      .join('\r\n');
    return '\uFEFF' + head + '\r\n' + body;
  }

  function toMarkdown(rows, meta) {
    const L = [];
    L.push('# 深信服案例库导出');
    L.push('');
    L.push('> 产品线：' + (meta.product || '全部') + '　｜　关键词：' + (meta.keyword || '(空)') +
      '　｜　共 ' + rows.length + ' 条　｜　导出时间：' + new Date().toLocaleString('zh-CN'));
    L.push('');
    // 目录
    L.push('## 目录');
    L.push('');
    rows.forEach((r, i) => {
      L.push(`${i + 1}. [${(r.title || '(无标题)').replace(/[[\]]/g, '')}](#case-${i + 1})`);
    });
    L.push('');
    L.push('---');
    L.push('');

    rows.forEach((r, i) => {
      L.push(`<a id="case-${i + 1}"></a>`);
      L.push('');
      L.push(`## ${i + 1}. ${r.title || '(无标题)'}`);
      L.push('');
      const metaLine = [
        r.product_name ? `产品线 ${r.product_name}` : '',
        r.child_modules || r.main_modules ? `模块 ${r.child_modules || r.main_modules}` : '',
        SFCaseFmt.shortVersions(r.version_codes) ? `版本 ${SFCaseFmt.shortVersions(r.version_codes)}` : '',
        r.suite_version ? `架构 ${r.suite_version}` : '',
        r.update_time ? `更新 ${r.update_time}` : '',
        `案例ID ${r.case_id}`,
      ].filter(Boolean).join('　｜　');
      L.push('> ' + metaLine);
      L.push('');
      L.push('> 官网链接：<' + r.url + '>');
      L.push('');

      // 优先用结构化 Markdown（含章节标题、列表层级、图片）
      const body = r.detail_md || r.detail_text || r.summary || '';
      if (body) {
        // 章节 ### 降级为 ####，避免与案例标题 ## 同级混乱
        L.push(body.replace(/^###\s+/gm, '#### '));
      } else {
        L.push('_（无正文）_');
      }
      L.push('');
      L.push('---');
      L.push('');
    });
    return L.join('\n');
  }

  function download(filename, content, mime) {
    const blob = new Blob([content], { type: mime || 'text/plain;charset=utf-8' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = filename;
    a.style.display = 'none';
    document.body.appendChild(a);
    a.click();
    setTimeout(() => {
      URL.revokeObjectURL(url);
      a.remove();
    }, 2000);
  }

  function baseName() {
    const p = cfg.productLineId ? safeName(state.productNameMap[cfg.productLineId] || cfg.productLineId) : 'all';
    return `sangfor_cases_${p}_${safeName(cfg.keyword || 'kw')}_${nowStamp()}`;
  }

  /* ---------------------------------------------------- 图片下载与内嵌（可选） */
  // 把图片下载成 data: URL 内嵌进 HTML/Markdown，导出的文件可离线阅读。
  async function embedImages(rows) {
    // 先把正文里的相对图片路径补全为绝对地址：否则既无法下载，下面的字符串替换也匹配不到
    rows.forEach((r) => {
      if (r.detail_html) {
        r.detail_html = r.detail_html.replace(
          /(<img\b[^>]*?)\ssrc="([^"]*)"/gi,
          (m, pre, url) => `${pre} src="${toAbs(url)}"`
        );
      }
    });
    const urls = [];
    rows.forEach((r) => (r.images || []).forEach((u) => {
      const a = toAbs(u);
      if (urls.indexOf(a) < 0 && /^https?:\/\//i.test(a)) urls.push(a);
    }));
    if (!urls.length) {
      log('正文无外链图片，跳过内嵌');
      return 0;
    }
    log(`开始下载 ${urls.length} 张图片用于内嵌…`);
    const map = {};
    let ok = 0, fail = 0;
    await pool(
      urls.map((u) => async () => {
        const d = await fetchDataURL(u);
        if (d) { map[u] = d; ok++; } else fail++;
      }),
      4
    );
    rows.forEach((r) => {
      if (r.detail_html) {
        let h = r.detail_html;
        Object.keys(map).forEach((u) => { h = h.split(u).join(map[u]); });
        r.detail_html = h;
      }
      if (r.detail_md) {
        let m = r.detail_md;
        Object.keys(map).forEach((u) => { m = m.split(u).join(map[u]); });
        r.detail_md = m;
      }
    });
    log(`图片内嵌完成：成功 ${ok}，失败 ${fail}`);
    return ok;
  }

  function fetchDataURL(url) {
    return new Promise((resolve) => {
      const toB64 = (blob) => {
        if (!blob) return resolve(null);
        try {
          const fr = new FileReader();
          fr.onload = () => resolve(fr.result);
          fr.onerror = () => resolve(null);
          fr.readAsDataURL(blob);
        } catch (e) { resolve(null); }
      };
      if (typeof GM_xmlhttpRequest === 'function') {
        try {
          GM_xmlhttpRequest({
            method: 'GET', url, responseType: 'blob', timeout: 30000,
            headers: { Referer: ORIGIN + '/cases/list', 'User-Agent': UA },
            onload: (r) => toB64(r.response),
            onerror: () => resolve(null),
            ontimeout: () => resolve(null),
          });
          return;
        } catch (e) {}
      }
      const f = (typeof unsafeWindow !== 'undefined' && unsafeWindow.fetch) || fetch;
      if (!f) return resolve(null);
      f(url, { credentials: 'omit' })
        .then((r) => r.blob())
        .then(toB64)
        .catch(() => resolve(null));
    });
  }

  async function doExportHtml() {
    if (!state.listRows.length) { log('没有可导出的数据', 'warn'); return; }
    const rows = state.listRows;
    const name = baseName();
    if (cfg.imageMode === 'embed') {
      await embedImages(rows);
    }
    const baseTitle = `深信服案例导出 - ${state.productNameMap[cfg.productLineId] || '全部产品'}${cfg.keyword ? ' - ' + cfg.keyword : ''}`;

    // 分卷：案例极多时单文件体积会很大，拆成多个文件更好打开
    const size = Math.max(0, cfg.htmlPartSize || 0);
    if (size > 0 && rows.length > size) {
      const n = Math.ceil(rows.length / size);
      log(`开始分卷导出：${rows.length} 条 → ${n} 个文件（每卷 ${size} 条）`);
      for (let i = 0; i < n; i++) {
        const part = rows.slice(i * size, (i + 1) * size);
        const html = SFCaseFmt.buildHtmlDoc(part, { title: baseTitle }, {
          embeddedImages: cfg.imageMode === 'embed',
          part: `${i + 1} / ${n}`,
          pageSize: cfg.pageSize,
        });
        download(`${name}_part${i + 1}.html`, html, 'text/html;charset=utf-8');
        log(`  已导出第 ${i + 1}/${n} 卷（${part.length} 条）`);
        if (i < n - 1) await sleep(900); // 避免浏览器拦截连续下载
      }
      log(`✔ 分卷导出完成，共 ${n} 个文件。若浏览器提示"是否允许多个下载"，请选择允许。`);
      return;
    }

    const html = SFCaseFmt.buildHtmlDoc(rows, { title: baseTitle }, {
      embeddedImages: cfg.imageMode === 'embed',
      pageSize: cfg.pageSize,
    });
    download(name + '.html', html, 'text/html;charset=utf-8');
    log('已导出 HTML（单文件，内部已分页，可直接浏览器打开 / 打印为 PDF）→ ' + name + '.html');
  }

  function doExport(type) {
    if (!state.listRows.length) {
      log('没有可导出的数据', 'warn');
      return;
    }
    const rows = state.listRows;
    const name = baseName();
    if (type === 'json') {
      download(
        name + '.json',
        JSON.stringify(
          {
            meta: {
              exported_at: new Date().toISOString(),
              source: 'support.sangfor.com.cn',
              product_line_id: cfg.productLineId,
              product_line_name: state.productNameMap[cfg.productLineId] || '',
              keyword: cfg.keyword,
              version_id: cfg.versionId,
              main_module_ids: cfg.mainModuleIds,
              child_module_ids: cfg.childModuleIds,
              count: rows.length,
            },
            rows,
          },
          null,
          2
        ),
        'application/json;charset=utf-8'
      );
    } else if (type === 'csv') {
      download(name + '.csv', toCSV(rows), 'text/csv;charset=utf-8');
    } else {
      download(
        name + '.md',
        toMarkdown(rows, {
          product: state.productNameMap[cfg.productLineId] || '全部',
          keyword: cfg.keyword,
        }),
        'text/markdown;charset=utf-8'
      );
    }
    log('已导出 ' + rows.length + ' 条 → ' + name + '.' + type);
  }

  /* ==========================================================================
   * 8. UI
   * ========================================================================== */

  let panel, logBox, progBar, progText, statText;

  function log(msg, level) {
    if (!logBox) return;
    const d = document.createElement('div');
    d.className = 'sfc-log-line' + (level ? ' sfc-' + level : '');
    const t = new Date();
    d.textContent = `[${pad2(t.getHours())}:${pad2(t.getMinutes())}:${pad2(t.getSeconds())}] ${msg}`;
    logBox.appendChild(d);
    logBox.scrollTop = logBox.scrollHeight;
    while (logBox.childElementCount > 300) logBox.removeChild(logBox.firstChild);
  }

  function notify(title, text) {
    if (typeof GM_notification === 'function') {
      try {
        GM_notification({ title, text, timeout: 5000 });
      } catch (e) {}
    }
  }

  function updateProgress() {
    if (!progBar) return;
    const listPct = state.totalPages ? Math.min(100, (state.donePages / state.totalPages) * 100) : 0;
    let pct = listPct;
    if (cfg.fetchDetail && state.running && state.donePages >= state.totalPages && state.totalPages) {
      const d = state.listRows.length ? (state.detailDone / state.listRows.length) * 100 : 0;
      pct = Math.min(100, d);
    }
    progBar.style.width = pct.toFixed(1) + '%';
    progText.textContent = pct.toFixed(1) + '%';
    statText.textContent = `列表 ${state.donePages}/${state.totalPages || '-'} 页 · 案例 ${state.listRows.length} 条 · 正文 ${state.detailDone}`;
  }

  function setRunningUI(running) {
    const b = document.getElementById('sfc-btn-run');
    const pb = document.getElementById('sfc-btn-pause');
    if (b) {
      b.textContent = running ? '■ 停止' : '▶ 开始抓取';
      b.classList.toggle('sfc-danger', running);
    }
    if (pb) pb.style.display = running ? '' : 'none';
  }

  function el(tag, attrs, children) {
    const n = document.createElement(tag);
    if (attrs) {
      Object.keys(attrs).forEach((k) => {
        if (k === 'class') n.className = attrs[k];
        else if (k === 'text') n.textContent = attrs[k];
        else if (k === 'html') n.innerHTML = attrs[k];
        else if (k.startsWith('on')) n.addEventListener(k.slice(2).toLowerCase(), attrs[k]);
        else n.setAttribute(k, attrs[k]);
      });
    }
    (children || []).forEach((c) => n.appendChild(c));
    return n;
  }

  function row(label, ...nodes) {
    return el('div', { class: 'sfc-row' }, [
      el('label', { text: label }),
      el('div', { class: 'sfc-ctl' }, nodes),
    ]);
  }

  function buildPanel() {
    panel = el('div', { id: 'sfc-panel' });

    // 标题栏
    const head = el('div', { class: 'sfc-head', id: 'sfc-head' }, [
      el('span', { class: 'sfc-title', text: '深信服案例库爬虫' }),
      el('span', { class: 'sfc-spacer' }),
      el('button', {
        class: 'sfc-icon',
        title: '收起/展开',
        text: '—',
        onclick: (e) => {
          e.stopPropagation();
          panel.classList.toggle('sfc-min');
          e.target.textContent = panel.classList.contains('sfc-min') ? '□' : '—';
        },
      }),
      el('button', {
        class: 'sfc-icon',
        title: '关闭',
        text: '✕',
        onclick: () => {
          panel.style.display = 'none';
        },
      }),
    ]);

    const body = el('div', { class: 'sfc-body' });

    // 产品线
    const selProduct = el('select', { id: 'sfc-product', class: 'sfc-input' });
    selProduct.appendChild(el('option', { value: '', text: '全部产品线（跨产品搜索）' }));
    selProduct.addEventListener('change', async () => {
      cfg.productLineId = selProduct.value;
      await refreshModules();
      await refreshVersions();
      updateTaskKeyHint();
    });

    // 版本
    const selVersion = el('select', { id: 'sfc-version', class: 'sfc-input' });
    selVersion.appendChild(el('option', { value: '', text: '全部版本' }));
    selVersion.addEventListener('change', () => {
      cfg.versionId = selVersion.value;
      updateTaskKeyHint();
    });

    // 关键词
    const inpKw = el('input', {
      id: 'sfc-kw',
      class: 'sfc-input',
      type: 'search',
      placeholder: '关键字，留空抓全部',
    });
    inpKw.addEventListener('input', () => {
      cfg.keyword = inpKw.value.trim();
      updateTaskKeyHint();
    });
    // 回车 / 点按钮 → 先用该关键字搜一次，确认命中范围再爬
    inpKw.addEventListener('keydown', (e) => {
      if (e.key === 'Enter') { e.preventDefault(); previewSearch(); }
    });
    const btnKwSearch = el('button', {
      class: 'sfc-btn sfc-mini',
      text: '🔍 搜一下',
      title: '先用该关键字搜索，确认命中多少条',
      onclick: () => previewSearch(),
    });
    const btnKwSync = el('button', {
      class: 'sfc-btn sfc-mini',
      text: '⇄ 同步页面',
      title: '读取页面上自带搜索框里的关键字',
      onclick: () => syncFromPageSearch(),
    });

    // 模块树容器
    const modBox = el('div', { class: 'sfc-modbox', id: 'sfc-modbox' });

    // 数值输入
    const inpPageSize = el('input', { id: 'sfc-ps', class: 'sfc-input sfc-num', type: 'number', value: '20', min: '1', max: '100' });
    inpPageSize.addEventListener('change', () => (cfg.pageSize = Math.max(1, Math.min(100, +inpPageSize.value || 20))));

    const inpMaxPages = el('input', { id: 'sfc-mp', class: 'sfc-input sfc-num', type: 'number', value: '0', min: '0' });
    inpMaxPages.addEventListener('change', () => (cfg.maxPages = Math.max(0, +inpMaxPages.value || 0)));

    const inpConc = el('input', { id: 'sfc-cc', class: 'sfc-input sfc-num', type: 'number', value: '3', min: '1', max: '10' });
    inpConc.addEventListener('change', () => (cfg.concurrency = Math.max(1, Math.min(10, +inpConc.value || 3))));

    const inpInterval = el('input', { id: 'sfc-iv', class: 'sfc-input sfc-num', type: 'number', value: '400', min: '0', step: '100' });
    inpInterval.addEventListener('change', () => (cfg.interval = Math.max(0, +inpInterval.value || 0)));

    const inpDConc = el('input', { id: 'sfc-dc', class: 'sfc-input sfc-num', type: 'number', value: '4', min: '1', max: '10' });
    inpDConc.addEventListener('change', () => (cfg.detailConcurrency = Math.max(1, Math.min(10, +inpDConc.value || 4))));

    const chkDetail = el('input', { type: 'checkbox', checked: true });
    chkDetail.addEventListener('change', () => (cfg.fetchDetail = chkDetail.checked));

    const chkResume = el('input', { type: 'checkbox' });
    chkResume.addEventListener('change', () => (cfg.resume = chkResume.checked));

    const selRecent = el('select', { class: 'sfc-input' }, [
      el('option', { value: '', text: '不限' }),
      el('option', { value: '7d', text: '近 7 天更新' }),
      el('option', { value: '30d', text: '近 30 天更新' }),
      el('option', { value: '90d', text: '近 90 天更新' }),
      el('option', { value: '180d', text: '近 180 天更新' }),
      el('option', { value: '365d', text: '近 1 年更新' }),
    ]);
    selRecent.addEventListener('change', () => (cfg.onlyRecent = selRecent.value));

    const selImgMode = el('select', { class: 'sfc-input' }, [
      el('option', { value: 'link', text: '保留外链（文件小）' }),
      el('option', { value: 'embed', text: '下载并内嵌（可离线看）' }),
    ]);
    selImgMode.addEventListener('change', () => (cfg.imageMode = selImgMode.value));

    // 进度
    progBar = el('div', { class: 'sfc-bar-inner', id: 'sfc-bar' });
    progText = el('span', { class: 'sfc-pct', text: '0.0%' });
    statText = el('div', { class: 'sfc-stat', text: '列表 0/0 页 · 案例 0 条 · 正文 0' });

    logBox = el('div', { class: 'sfc-log', id: 'sfc-log' });

    const previewBox = el('div', { class: 'sfc-preview', id: 'sfc-preview', style: 'display:none' });

    body.appendChild(row('产品线', selProduct));
    body.appendChild(row('关键词', inpKw, btnKwSearch, btnKwSync));
    body.appendChild(previewBox);
    body.appendChild(row('版本', selVersion));
    body.appendChild(
      row(
        '模块',
        el('div', {}, [
          el('button', {
            class: 'sfc-btn sfc-mini',
            text: '展开模块树',
            onclick: () => {
              modBox.classList.toggle('sfc-show');
              if (modBox.classList.contains('sfc-show')) refreshModules(true);
            },
          }),
          el('button', {
            class: 'sfc-btn sfc-mini',
            text: '清空选择',
            onclick: () => {
              cfg.mainModuleIds = [];
              cfg.childModuleIds = [];
              refreshModules(true);
              updateTaskKeyHint();
            },
          }),
        ])
      )
    );
    body.appendChild(modBox);
    const inpPart = el('input', { id: 'sfc-part', class: 'sfc-input sfc-num', type: 'number', value: '0', min: '0', step: '50' });
    inpPart.addEventListener('change', () => (cfg.htmlPartSize = Math.max(0, +inpPart.value || 0)));

    body.appendChild(row('每页条数', inpPageSize));
    body.appendChild(row('最大页数', inpMaxPages, el('span', { class: 'sfc-hint', text: '0 = 全部' })));
    body.appendChild(row('HTML 分卷', inpPart, el('span', { class: 'sfc-hint', text: '条/文件，0 = 不分卷' })));
    body.appendChild(row('翻页并发', inpConc));
    body.appendChild(row('请求间隔', inpInterval, el('span', { class: 'sfc-hint', text: 'ms' })));
    body.appendChild(row('抓正文', chkDetail, el('span', { class: 'sfc-hint', text: '调用详情接口获取完整 HTML 正文' }), inpDConc, el('span', { class: 'sfc-hint', text: '并发' })));
    body.appendChild(row('更新时间', selRecent));
    body.appendChild(row('正文图片', selImgMode));
    body.appendChild(
      el('div', { class: 'sfc-tip' }, [
        el('span', {
          text: '正文的「问题描述/告警信息/根因/解决方案」等章节会被还原成 Markdown 小标题，图片以 ![](url) 保留。',
        }),
      ])
    );
    body.appendChild(row('断点续跑', chkResume, el('span', { class: 'sfc-hint', text: '中断后再次开始可从断点继续' })));
    body.appendChild(
      el('div', { class: 'sfc-taskkey', id: 'sfc-taskkey' })
    );

    body.appendChild(
      el('div', { class: 'sfc-prog' }, [progBar, progText])
    );
    body.appendChild(statText);

    body.appendChild(
      el('div', { class: 'sfc-actions' }, [
        el('button', {
          class: 'sfc-btn sfc-primary',
          id: 'sfc-btn-run',
          text: '▶ 开始抓取',
          onclick: () => {
            if (state.running) {
              state.cancelToken = -1;
              log('正在停止…');
            } else {
              crawl();
            }
          },
        }),
        el('button', {
          class: 'sfc-btn',
          id: 'sfc-btn-pause',
          text: '⏸ 暂停',
          style: 'display:none',
          onclick: (e) => {
            state.paused = !state.paused;
            e.target.textContent = state.paused ? '⏵ 继续' : '⏸ 暂停';
            log(state.paused ? '已暂停' : '已继续');
          },
        }),
        el('button', {
          class: 'sfc-btn',
          text: '测试连接',
          onclick: async () => {
            log('测试连接中…');
            try {
              const r = await postJSON(API.search, buildSearchPayload(0));
              log(`✔ 连接正常，可访问案例数据（当前条件命中 ${(r.rows && r.rows.totalElements) || 0} 条）`);
            } catch (e) {
              log('✗ 连接失败：' + e.message, 'err');
            }
          },
        }),
      ])
    );

    body.appendChild(
      el('div', { class: 'sfc-actions' }, [
        el('button', { class: 'sfc-btn sfc-primary', text: '⬇ 导出 HTML（推荐）', onclick: () => doExportHtml() }),
        el('button', { class: 'sfc-btn', text: '导出 Markdown', onclick: () => doExport('md') }),
        el('button', { class: 'sfc-btn', text: '导出 CSV', onclick: () => doExport('csv') }),
        el('button', { class: 'sfc-btn', text: '导出 JSON', onclick: () => doExport('json') }),
      ])
    );

    body.appendChild(
      el('div', { class: 'sfc-actions' }, [
        el('button', { class: 'sfc-btn sfc-mini', text: '清空日志', onclick: () => (logBox.innerHTML = '') }),
        el('button', { class: 'sfc-btn sfc-mini', text: '清空断点缓存', onclick: clearAllCache }),
        el('button', {
          class: 'sfc-btn sfc-mini',
          text: '复制接口说明',
          onclick: () => {
            const txt = [
              '接口（均需浏览器登录态，Cookie 自动携带）：',
              'POST ' + API.search,
              '  body: ' + JSON.stringify(buildSearchPayload(0)),
              'GET  ' + API.detail('{source_id}'),
              'GET  ' + API.productList,
              'GET  ' + API.moduleTree('{productLineId}'),
              'GET  ' + API.versionList('{productLineId}'),
            ].join('\n');
            try {
              navigator.clipboard.writeText(txt);
              log('接口说明已复制到剪贴板');
            } catch (e) {
              log(txt);
            }
          },
        }),
      ])
    );

    body.appendChild(logBox);

    panel.appendChild(head);
    panel.appendChild(body);
    document.body.appendChild(panel);

    // 拖动
    (function draggable() {
      let sx, sy, ox, oy, dragging = false;
      head.addEventListener('mousedown', (e) => {
        if (e.target.classList.contains('sfc-icon')) return;
        dragging = true;
        sx = e.clientX;
        sy = e.clientY;
        const r = panel.getBoundingClientRect();
        ox = r.left;
        oy = r.top;
        panel.style.right = 'auto';
        panel.style.bottom = 'auto';
        panel.style.left = ox + 'px';
        panel.style.top = oy + 'px';
        e.preventDefault();
      });
      document.addEventListener('mousemove', (e) => {
        if (!dragging) return;
        panel.style.left = ox + (e.clientX - sx) + 'px';
        panel.style.top = oy + (e.clientY - sy) + 'px';
      });
      document.addEventListener('mouseup', () => (dragging = false));
    })();

    // 初始加载产品线
    loadProductList()
      .then((data) => {
        data.leaves.forEach((p) => {
          selProduct.appendChild(el('option', { value: String(p.id), text: `${p.name} (${p.id})` }));
        });
        log(`产品线加载完成：${data.leaves.length} 个可选`);
        tryRestoreFromUrl();
        bindPageSearch();
      })
      .catch((e) => log('产品线加载失败：' + e.message + '（可手动刷新页面重试）', 'err'));
  }

  function updateTaskKeyHint() {
    const n = document.getElementById('sfc-taskkey');
    if (!n) return;
    const p = cfg.productLineId ? state.productNameMap[cfg.productLineId] || cfg.productLineId : '全部产品';
    n.textContent = `当前条件：${p} · 版本 ${cfg.versionId || '全部'} · 主模块 ${cfg.mainModuleIds.length} · 子模块 ${cfg.childModuleIds.length} · 关键词「${cfg.keyword || ''}」`;
  }

  async function refreshModules(force) {
    const box = document.getElementById('sfc-modbox');
    if (!box) return;
    if (!cfg.productLineId) {
      box.innerHTML = '<div class="sfc-hint">请先选择产品线</div>';
      return;
    }
    if (!force && state.moduleCache[cfg.productLineId]) {
      renderModules(box, state.moduleCache[cfg.productLineId]);
      return;
    }
    box.innerHTML = '<div class="sfc-hint">加载中…</div>';
    try {
      const tree = await loadModuleTree(cfg.productLineId);
      renderModules(box, tree);
    } catch (e) {
      box.innerHTML = '<div class="sfc-hint">模块加载失败：' + e.message + '</div>';
    }
  }

  function renderModules(box, tree) {
    box.innerHTML = '';
    const mk = (node, depth) => {
      const wrap = el('div', { class: 'sfc-node', style: 'padding-left:' + depth * 14 + 'px' });
      const isMain = depth === 0;
      const cb = el('input', { type: 'checkbox' });
      cb.checked = isMain
        ? cfg.mainModuleIds.map(String).includes(String(node.id))
        : cfg.childModuleIds.map(String).includes(String(node.id));
      cb.addEventListener('change', () => {
        const arr = isMain ? cfg.mainModuleIds : cfg.childModuleIds;
        const i = arr.map(String).indexOf(String(node.id));
        if (cb.checked && i < 0) arr.push(String(node.id));
        if (!cb.checked && i >= 0) arr.splice(i, 1);
        updateTaskKeyHint();
      });
      wrap.appendChild(cb);
      wrap.appendChild(el('span', { text: node.name }));
      if (isMain) wrap.classList.add('sfc-main');
      box.appendChild(wrap);
      (node.children || []).forEach((c) => mk(c, depth + 1));
    };
    (tree || []).forEach((n) => mk(n, 0));
  }

  async function refreshVersions() {
    const sel = document.getElementById('sfc-version');
    if (!sel) return;
    sel.innerHTML = '';
    sel.appendChild(el('option', { value: '', text: '全部版本' }));
    if (!cfg.productLineId) return;
    try {
      const vs = await loadVersionList(cfg.productLineId);
      vs.forEach((v) => sel.appendChild(el('option', { value: String(v.id), text: v.code })));
    } catch (e) {
      log('版本列表加载失败：' + e.message, 'warn');
    }
  }

  // 监听页面自带搜索框：输入即同步到面板，并自动做一次预搜索（先搜后爬）
  function bindPageSearch() {
    const n = findPageSearch();
    if (!n) return;
    let timer = null;
    n.addEventListener('input', () => {
      cfg.keyword = (n.value || '').trim();
      const inp = document.getElementById('sfc-kw');
      if (inp) inp.value = cfg.keyword;
      updateTaskKeyHint();
      clearTimeout(timer);
      timer = setTimeout(() => previewSearch(), 700); // 防抖
    });
    if (n.value && n.value.trim()) {
      cfg.keyword = n.value.trim();
      const inp = document.getElementById('sfc-kw');
      if (inp) inp.value = cfg.keyword;
      updateTaskKeyHint();
      log(`已跟随页面搜索框关键字：${cfg.keyword}（可在面板点「🔍 搜一下」查看命中范围）`);
    }
  }

  // 若当前页面是案例列表页，自动带入 product_id / category_id
  function tryRestoreFromUrl() {
    try {
      const q = new URLSearchParams(location.search);
      const pid = q.get('product_id');
      if (pid) {
        const sel = document.getElementById('sfc-product');
        if (sel) {
          sel.value = pid;
          cfg.productLineId = pid;
          refreshModules();
          refreshVersions();
        }
      }
    } catch (e) {}
    updateTaskKeyHint();
  }

  function addStyle() {
    const css = `
#sfc-panel{position:fixed;right:18px;bottom:18px;width:430px;max-height:82vh;z-index:2147483000;
  background:#1e222b;color:#e6e8ee;border:1px solid #343a48;border-radius:10px;
  box-shadow:0 12px 36px rgba(0,0,0,.45);font:13px/1.6 -apple-system,"Segoe UI","Microsoft YaHei",sans-serif;
  display:flex;flex-direction:column;overflow:hidden}
#sfc-panel.sfc-min .sfc-body{display:none}
.sfc-head{display:flex;align-items:center;gap:6px;padding:9px 12px;background:#252a36;cursor:move;user-select:none;flex:0 0 auto}
.sfc-title{font-weight:600;font-size:13px;color:#7cc0ff}
.sfc-spacer{flex:1}
.sfc-icon{background:transparent;border:none;color:#9aa3b2;font-size:13px;cursor:pointer;padding:0 4px;line-height:1}
.sfc-icon:hover{color:#fff}
.sfc-body{padding:10px 12px 12px;overflow:auto;flex:1 1 auto}
.sfc-row{display:flex;align-items:flex-start;gap:8px;margin-bottom:7px}
.sfc-row>label{flex:0 0 66px;color:#9aa3b2;padding-top:4px;font-size:12px}
.sfc-ctl{flex:1;display:flex;align-items:center;gap:6px;flex-wrap:wrap}
.sfc-input{background:#141821;color:#e6e8ee;border:1px solid #3a4152;border-radius:5px;padding:4px 7px;font-size:12px;flex:1;min-width:90px;outline:none}
.sfc-input:focus{border-color:#4a8fd4}
.sfc-num{flex:0 0 68px;min-width:60px}
.sfc-num.sfc-input{flex:0 0 68px}
.sfc-hint{color:#6f7889;font-size:11px;white-space:nowrap}
.sfc-btn{background:#2c3341;color:#dfe3ec;border:1px solid #3d4557;border-radius:5px;padding:5px 10px;font-size:12px;cursor:pointer}
.sfc-btn:hover{background:#38414f}
.sfc-btn.sfc-primary{background:#2f6fd0;color:#fff}
.sfc-btn.sfc-primary:hover{background:#3a7fe0}
.sfc-btn.sfc-danger{background:#c0392b;color:#fff}
.sfc-btn.sfc-mini{padding:3px 8px;font-size:11px}
.sfc-actions{display:flex;gap:6px;flex-wrap:wrap;margin:8px 0}
.sfc-prog{position:relative;height:16px;background:#141821;border-radius:8px;overflow:hidden;margin:6px 0}
.sfc-bar-inner{height:100%;width:0;background:linear-gradient(90deg,#2f6fd0,#48c9b0);transition:width .25s}
.sfc-pct{position:absolute;right:8px;top:0;line-height:16px;font-size:11px;color:#cfd6e4}
.sfc-stat{font-size:11px;color:#8b94a6;margin-bottom:6px}
.sfc-log{background:#12151c;border:1px solid #2a3040;border-radius:6px;padding:6px 8px;height:150px;overflow:auto;
  font:11px/1.55 Menlo,Consolas,"Courier New",monospace;color:#a9b3c6;white-space:pre-wrap;word-break:break-all}
.sfc-log-line{margin:0}
.sfc-log-line.sfc-err{color:#ff7b72}
.sfc-log-line.sfc-warn{color:#f0b45e}
.sfc-modbox{display:none;max-height:190px;overflow:auto;background:#141821;border:1px solid #2a3040;border-radius:6px;padding:6px;margin-bottom:8px}
.sfc-modbox.sfc-show{display:block}
.sfc-modbox.sfc-show{max-height:190px}
.sfc-node{display:flex;align-items:center;gap:6px;padding:2px 0;font-size:12px;color:#c3cad8}
.sfc-node.sfc-main{color:#9ecbff;font-weight:600;margin-top:4px}
.sfc-taskkey{font-size:11px;color:#7f8a9e;background:#141821;border:1px dashed #333a4a;border-radius:5px;padding:5px 7px;margin-bottom:6px}
.sfc-tip{font-size:11px;color:#6f7889;line-height:1.5;background:#141821;border-left:3px solid #2f6fd0;border-radius:4px;padding:5px 8px;margin:2px 0 8px}
.sfc-preview{max-height:190px;overflow:auto;background:#12151c;border:1px solid #2a3040;border-radius:6px;padding:7px 9px;margin-bottom:8px}
.sfc-pv-head{font-size:12px;color:#9ecbff;margin-bottom:5px}
.sfc-pv-head b{color:#ffd479}
.sfc-pv-item{display:flex;gap:6px;align-items:baseline;font-size:12px;padding:2px 0;line-height:1.5}
.sfc-pv-n{color:#5f6879;flex:0 0 auto}
.sfc-pv-item a{color:#c3cad8;text-decoration:none;flex:1;min-width:0}
.sfc-pv-item a:hover{color:#7cc0ff;text-decoration:underline}
.sfc-pv-m{color:#6f7889;font-size:11px;flex:0 0 auto}
.sfc-preview mark{background:#2f6fd0;color:#fff;padding:0 2px;border-radius:2px}
`;
    const s = document.createElement('style');
    s.textContent = css;
    document.head.appendChild(s);
  }

  /* ==========================================================================
   * 9. 启动
   * ========================================================================== */

  function boot() {
    if (document.getElementById('sfc-panel')) return;
    addStyle();
    buildPanel();
    if (typeof GM_registerMenuCommand === 'function') {
      GM_registerMenuCommand('打开/关闭 案例爬虫面板', () => {
        const p = document.getElementById('sfc-panel');
        if (p) p.style.display = p.style.display === 'none' ? '' : 'none';
      });
      GM_registerMenuCommand('清空断点缓存', clearAllCache);
    }
    log('脚本就绪。请先确认浏览器已登录 support.sangfor.com.cn，再点「测试连接」验证。');
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', boot);
  } else {
    boot();
  }
})();
