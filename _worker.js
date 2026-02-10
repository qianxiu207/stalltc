import { connect } from 'cloudflare:sockets';

// =============================================================================
// 🟣 用户配置区域
// =============================================================================
const UUID = ""; // 你的 UUID (建议在后台环境变量设置)
const WEB_PASSWORD = "";  // 管理面板密码
const SUB_PASSWORD = "";  // 订阅路径密码

// 🟢【重要配置】: 默认 ProxyIP (兜底地址)
// 只有填了这里，生成的默认节点路径才会是干净的路径，不带参数
// 必须填！例如: proxy.aliyun.com 或 ProxyIP.CMLiussss.net
const DEFAULT_PROXY_IP = ""; 

// 🟢【伪装配置】: 默认节点路径
// 配合上面的 IP，用来隐藏真实意图，看起来像 API 请求
const NODE_DEFAULT_PATH = "/api/v1"; 

const ROOT_REDIRECT_URL = ""; 

// =============================================================================
// ⚡️ 核心逻辑区
// =============================================================================
const MAX_PENDING=2097152,KEEPALIVE=15000,STALL_TO=8000,MAX_STALL=12,MAX_RECONN=24;
const buildUUID=(a,i)=>[...a.slice(i,i+16)].map(n=>n.toString(16).padStart(2,'0')).join('').replace(/^(.{8})(.{4})(.{4})(.{4})(.{12})$/,'$1-$2-$3-$4-$5');
const extractAddr=b=>{const o=18+b[17]+1,p=(b[o]<<8)|b[o+1],t=b[o+2];let l,h,O=o+3;switch(t){case 1:l=4;h=b.slice(O,O+l).join('.');break;case 2:l=b[O++];h=new TextDecoder().decode(b.slice(O,O+l));break;case 3:l=16;h=`[${[...Array(8)].map((_,i)=>((b[O+i*2]<<8)|b[O+i*2+1]).toString(16)).join(':')}]`;break;default:throw new Error('Addr type error');}return{host:h,port:p,payload:b.slice(O+l)}};

const PT_TYPE = 'v'+'l'+'e'+'s'+'s';

function getEnv(env, key, fallback) { return env[key] || fallback; }

// 解析单个 IP 或域名
async function parseIP(p){
    if(!p) return null;
    p=p.trim().toLowerCase();
    let a=p,o=443;
    if(p.includes('.tp')){
        const m=p.match(/\.tp(\d+)/);
        if(m)o=parseInt(m[1],10);
        return { address: a, port: o };
    }
    if(p.includes(']:')){
        const s=p.split(']:');
        a=s[0]+']';
        o=parseInt(s[1],10)||o
    } else if(p.includes(':')&&!p.startsWith('[')){
        const i=p.lastIndexOf(':');
        a=p.slice(0,i);
        o=parseInt(p.slice(i+1),10)||o
    }
    return { address: a, port: o };
}

class Pool{constructor(){this.b=new ArrayBuffer(16384);this.p=0;this.l=[];this.m=8}alloc(s){if(s<=4096&&s<=16384-this.p){const v=new Uint8Array(this.b,this.p,s);this.p+=s;return v}const r=this.l.pop();return r&&r.byteLength>=s?new Uint8Array(r.buffer,0,s):new Uint8Array(s)}free(b){if(b.buffer===this.b)this.p=Math.max(0,this.p-b.length);else if(this.l.length<this.m&&b.byteLength>=1024)this.l.push(b)}reset(){this.p=0;this.l=[]}}

async function getDynamicUUID(key, refresh = 86400) {
    const time = Math.floor(Date.now() / 1000 / refresh);
    const msg = new TextEncoder().encode(`${key}-${time}`);
    const hash = await crypto.subtle.digest('SHA-256', msg);
    const b = new Uint8Array(hash);
    return [...b.slice(0, 16)].map(n => n.toString(16).padStart(2, '0')).join('').replace(/^(.{8})(.{4})(.{4})(.{4})(.{12})$/, '$1-$2-$3-$4-$5');
}

/**
 * 核心处理函数
 * @param {WebSocket} ws 
 * @param {Object} proxyConfig 单个 ProxyIP 配置
 * @param {string} uuid 
 */
const handle = (ws, proxyConfig, uuid) => {
  const pool = new Pool();
  let s, w, r, inf, fst = true, rx = 0, stl = 0, cnt = 0, lact = Date.now(), con = false, rd = false, wt = false, tm = {}, pd = [], pb = 0, scr = 1.0, lck = Date.now(), lrx = 0, md = 'buf', asz = 0, tp = [], st = { t: 0, c: 0, ts: Date.now() };
  
  const upd = sz => {
    st.t += sz; st.c++;
    asz = asz * 0.9 + sz * 0.1; const n = Date.now();
    if (n - st.ts > 1000) { const rt = st.t; tp.push(rt); if (tp.length > 5) tp.shift(); st.t = 0;
    st.ts = n; const av = tp.reduce((a, b) => a + b, 0) / tp.length;
    if (st.c >= 20) { if (av > 2e7 && asz > 16384) md = 'dir';
    else if (av < 1e7 || asz < 8192) md = 'buf'; else md = 'adp' } }
  };
  
  const rdL = async () => {
    if (rd) return; rd = true;
    let b = [], bz = 0, tm = null;
    const fl = () => { if (!bz) return;
    const m = new Uint8Array(bz); let p = 0; for (const x of b) { m.set(x, p);
    p += x.length } if (ws.readyState === 1) ws.send(m); b = []; bz = 0; if (tm) clearTimeout(tm);
    tm = null };
    try { while (1) { if (pb > MAX_PENDING) { await new Promise(r => setTimeout(r, 100));
    continue } const { done, value: v } = await r.read(); if (v?.length) { rx += v.length; lact = Date.now();
    stl = 0; upd(v.length); const n = Date.now(); if (n - lck > 5000) { const el = n - lck, by = rx - lrx, r = by / el;
    if (r > 500) scr = Math.min(1, scr + 0.05);
    else if (r < 50) scr = Math.max(0.1, scr - 0.05); lck = n;
    lrx = rx } if (md === 'buf') { if (v.length < 32768) { b.push(v); bz += v.length;
    if (bz >= 131072) fl(); else if (!tm) tm = setTimeout(fl, asz > 16384 ? 5 : 20) } else { fl();
    if (ws.readyState === 1) ws.send(v) } } else { fl();
    if (ws.readyState === 1) ws.send(v) } } if (done) { fl(); rd = false; rcn();
    break } } } catch { fl(); rd = false; rcn() }
  };
  
  const wtL = async () => { if (wt) return; wt = true;
  try { while (wt) { if (!w) { await new Promise(r => setTimeout(r, 100));
  continue } if (!pd.length) { await new Promise(r => setTimeout(r, 20)); continue } const b = pd.shift(); await w.write(b);
  pb -= b.length; pool.free(b) } } catch { wt = false } };
  
  const est = async () => { try { s = await cn(); w = s.writable.getWriter(); r = s.readable.getReader();
  con = false; cnt = 0; scr = Math.min(1, scr + 0.15); lact = Date.now(); rdL();
  wtL() } catch { con = false; scr = Math.max(0.1, scr - 0.2); rcn() } };
  
  // 🟢 智能连接逻辑
  const cn = async () => {
    try {
        const directPromise = connect({ hostname: inf.host, port: inf.port });
        const direct = await Promise.race([
            directPromise.opened.then(() => directPromise),
            new Promise((_, reject) => setTimeout(() => reject('Direct timeout'), 2500))
        ]);
        return direct;
    } catch (e) {}

    if (proxyConfig && proxyConfig.address) {
        try {
            const proxy = connect({ hostname: proxyConfig.address, port: proxyConfig.port });
            await proxy.opened;
            return proxy;
        } catch (e) {}
    }

    throw new Error('Connection failed');
  };
  
  const rcn = async () => { if (!inf || ws.readyState !== 1) { cln(); ws.close(1011);
  return } if (cnt >= MAX_RECONN) { cln(); ws.close(1011); return } if (con) return; cnt++;
  let d = Math.min(50 * Math.pow(1.5, cnt - 1), 3000) * (1.5 - scr * 0.5); d = Math.max(50, Math.floor(d));
  try { csk(); if (pb > MAX_PENDING * 2) while (pb > MAX_PENDING && pd.length > 5) { const k = pd.shift();
  pb -= k.length; pool.free(k) } await new Promise(r => setTimeout(r, d)); con = true; s = await cn();
  w = s.writable.getWriter(); r = s.readable.getReader(); con = false; cnt = 0; scr = Math.min(1, scr + 0.15);
  stl = 0; lact = Date.now(); rdL(); wtL() } catch { con = false; scr = Math.max(0.1, scr - 0.2);
  if (cnt < MAX_RECONN && ws.readyState === 1) setTimeout(rcn, 500); else { cln(); ws.close(1011) } } };
  
  const stT = () => { tm.ka = setInterval(async () => { if (!con && w && Date.now() - lact > KEEPALIVE) try { await w.write(new Uint8Array(0)); lact = Date.now() } catch { rcn() } }, KEEPALIVE / 3);
  tm.hc = setInterval(() => { if (!con && st.t > 0 && Date.now() - lact > STALL_TO) { stl++; if (stl >= MAX_STALL) { if (cnt < MAX_RECONN) { stl = 0; rcn() } else { cln(); ws.close(1011) } } } }, STALL_TO / 2) };
  const csk = () => { rd = false; wt = false; try { w?.releaseLock(); r?.releaseLock();
  s?.close() } catch { } }; 
  const cln = () => { Object.values(tm).forEach(clearInterval); csk(); while (pd.length) pool.free(pd.shift()); pb = 0;
  st = { t: 0, c: 0, ts: Date.now() }; md = 'buf'; asz = 0; tp = [];
  pool.reset() };
  ws.addEventListener('message', async e => { try { if (fst) { fst = false; const b = new Uint8Array(e.data); if (buildUUID(b, 1).toLowerCase() !== uuid.toLowerCase()) throw 0; ws.send(new Uint8Array([0, 0])); const { host, port, payload } = extractAddr(b); inf = { host, port }; con = true; if (payload.length) { const z = pool.alloc(payload.length); z.set(payload); pd.push(z); pb += z.length } stT(); est() } else { lact = Date.now(); if (pb > MAX_PENDING * 2) return; const z = pool.alloc(e.data.byteLength); z.set(new Uint8Array(e.data)); pd.push(z); pb += z.length } } catch { cln(); ws.close(1006) } });
  ws.addEventListener('close', cln); ws.addEventListener('error', cln)
};

// =============================================================================
// 🎨 波谱风格 (Pop Art) 面板代码
// =============================================================================
const COMMON_STYLE = `
    :root {
        --bg-color: #f0f0f0;
        --card-bg: #ffffff;
        --primary-color: #ff4757; /* 鲜艳红 */
        --secondary-color: #3742fa; /* 宝蓝 */
        --accent-color: #ffa502; /* 橙黄 */
        --text-main: #2f3542;
        --border-color: #000000;
        --shadow-offset: 4px;
    }
    body {
        font-family: 'Courier New', 'Verdana', sans-serif;
        background-color: var(--bg-color);
        /* 波点背景 */
        background-image: radial-gradient(var(--text-main) 1px, transparent 1px);
        background-size: 20px 20px;
        color: var(--text-main);
        margin: 0;
        min-height: 100vh;
        display: flex;
        justify-content: center;
        align-items: center;
    }
    .pop-card {
        background: var(--card-bg);
        border: 3px solid var(--border-color);
        box-shadow: var(--shadow-offset) var(--shadow-offset) 0px var(--border-color);
        border-radius: 0px; /* 直角 */
        padding: 2rem;
        max-width: 400px;
        width: 90%;
        position: relative;
    }
    .pop-title {
        font-weight: 900;
        text-transform: uppercase;
        font-size: 1.8rem;
        margin-bottom: 1.5rem;
        color: var(--border-color);
        text-shadow: 2px 2px 0px var(--accent-color);
        letter-spacing: -1px;
    }
    .btn {
        background: var(--primary-color);
        color: white;
        border: 3px solid var(--border-color);
        padding: 10px 20px;
        font-weight: 700;
        text-transform: uppercase;
        cursor: pointer;
        box-shadow: var(--shadow-offset) var(--shadow-offset) 0px var(--border-color);
        transition: all 0.1s;
        display: inline-block;
        text-decoration: none;
    }
    .btn:hover {
        transform: translate(2px, 2px);
        box-shadow: 2px 2px 0px var(--border-color);
    }
    .btn:active {
        transform: translate(var(--shadow-offset), var(--shadow-offset));
        box-shadow: 0px 0px 0px var(--border-color);
    }
    .btn-blue { background: var(--secondary-color); }
    
    input {
        width: 100%;
        padding: 10px;
        border: 3px solid var(--border-color);
        background: #fff;
        font-family: inherit;
        font-weight: 600;
        outline: none;
        box-sizing: border-box;
        margin-bottom: 1rem;
    }
    input:focus {
        background: #ffeaa7;
    }
    .animate-in { animation: popIn 0.4s cubic-bezier(0.175, 0.885, 0.32, 1.275); }
    @keyframes popIn { 
        from { opacity: 0; transform: scale(0.8); } 
        to { opacity: 1; transform: scale(1); } 
    }
`;

function loginPage() {
    return `<!DOCTYPE html><html lang="zh-CN"><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1.0"><title>ACCESS DENIED</title><style>${COMMON_STYLE}</style></head><body>
    <div class="pop-card animate-in">
        <div class="pop-title" style="text-align:center;">SYSTEM LOGIN</div>
        <div style="margin-bottom:20px; font-weight:bold; background:var(--accent-color); color:black; padding:5px; border:2px solid black;">⚠ RESTRICTED AREA</div>
        <input type="password" id="pwd" placeholder="INSERT PASSWORD..." onkeypress="if(event.keyCode===13)verify()">
        <button class="btn" style="width:100%" onclick="verify()">ENTER >></button>
    </div>
    <script>function verify(){const p=document.getElementById("pwd").value;if(!p)return;document.cookie="auth="+p+"; path=/; Max-Age=31536000";location.reload()}</script>
    </body></html>`;
}

function dashPage(host, uuid, proxyip, subpass) {
    // 页面内显示的配置链接，如果 proxyip 存在且不同于默认值，才会在前端拼接参数
    // 但核心逻辑是服务器端的 genNodes，这里只是给用户看的
    const defaultSubLink = `https://${host}/${subpass}`;
    
    return `<!DOCTYPE html><html lang="zh-CN"><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1.0"><title>DASHBOARD</title><link href="https://cdn.jsdelivr.net/npm/remixicon@3.5.0/fonts/remixicon.css" rel="stylesheet"><style>${COMMON_STYLE}
    .info-box { border: 2px solid black; padding: 10px; margin-bottom: 15px; background: white; }
    .label { font-size: 0.8rem; font-weight: 800; color: var(--secondary-color); text-transform: uppercase; }
    .val { font-family: monospace; font-size: 1rem; word-break: break-all; font-weight: bold; }
    #toast {
        position: fixed; bottom: 20px; right: 20px;
        background: var(--border-color); color: white;
        padding: 10px 20px; border: 3px solid white;
        font-weight: bold; transform: translateY(100px); transition: transform 0.3s;
    }
    #toast.show { transform: translateY(0); }
    </style></head><body>
    
    <div class="pop-card animate-in" style="max-width:600px;">
        <div style="display:flex; justify-content:space-between; align-items:center;">
            <div class="pop-title" style="margin:0; font-size:1.5rem;">DASHBOARD</div>
            <button class="btn btn-blue" style="padding:5px 10px;" onclick="logout()"><i class="ri-logout-box-r-line"></i></button>
        </div>
        <div style="height:3px; background:black; margin: 15px 0;"></div>

        <div class="info-box" style="background:#ffeaa7;">
            <div class="label"><i class="ri-links-line"></i> SUBSCRIPTION LINK</div>
            <div style="display:flex; gap:10px; margin-top:5px;">
                <input type="text" id="subLink" value="${defaultSubLink}" readonly style="margin:0;">
                <button class="btn" onclick="copyId('subLink')">COPY</button>
            </div>
        </div>

        <div style="display:grid; grid-template-columns: 1fr 1fr; gap:15px;">
            <div class="info-box">
                <div class="label">UUID</div>
                <div class="val">${uuid.substring(0,8)}...</div>
            </div>
            <div class="info-box">
                <div class="label">HOST</div>
                <div class="val">${host}</div>
            </div>
        </div>

        <div class="info-box">
            <div class="label">ADDRESS OVERRIDE (PROXYIP)</div>
            <div style="margin-top:5px; font-size:0.8rem; color:#666;">Leave empty to use default path (${NODE_DEFAULT_PATH})</div>
            <div style="display:flex; gap:10px; margin-top:5px;">
                <input type="text" id="customIP" value="${proxyip}" placeholder="e.g. 1.2.3.4" style="margin:0;">
                <button class="btn btn-blue" onclick="updateLink()">UPDATE</button>
            </div>
        </div>
    </div>
    
    <div id="toast">COPIED TO CLIPBOARD!</div>

    <script>
    function showToast(m){const t=document.getElementById('toast');t.innerText=m;t.classList.add('show');setTimeout(()=>t.classList.remove('show'),2000)}
    function copyId(id){const el=document.getElementById(id);el.select();navigator.clipboard.writeText(el.value).then(()=>showToast('COPIED!'))}
    function updateLink(){
        const ip=document.getElementById('customIP').value.trim();
        const u="https://"+window.location.hostname+"/${subpass}";
        // 前端逻辑：如果有IP，拼参数；没IP，保持原样(后端会处理成默认路径)
        document.getElementById('subLink').value = ip ? u+"?proxyip="+ip : u;
        showToast('LINK UPDATED!');
    }
    function logout(){document.cookie="auth=; expires=Thu, 01 Jan 1970 00:00:00 GMT; path=/";location.reload()}
    </script></body></html>`;
}

// =============================================================================
// 🟢 主入口 (Fetch Event)
// =============================================================================
export default {
  async fetch(r, env, ctx) {
    try {
      const url = new URL(r.url);
      const host = url.hostname; 
      
      // 加载配置
      const _UUID = env.KEY ? await getDynamicUUID(env.KEY) : getEnv(env, 'UUID', UUID);
      const _WEB_PW = getEnv(env, 'WEB_PASSWORD', WEB_PASSWORD);
      const _SUB_PW = getEnv(env, 'SUB_PASSWORD', SUB_PASSWORD);
      
      // 🟢 变量获取: 优先读取环境变量 -> 然后是代码中的默认值
      const _PROXY_IP_RAW = env.PROXYIP || env.DEFAULT_PROXY_IP || DEFAULT_PROXY_IP;
      const _PS = getEnv(env, 'PS', ""); 
      
      const _PROXY_IP = _PROXY_IP_RAW ? _PROXY_IP_RAW.split(/[,\n]/)[0].trim() : "";
      
      let _ROOT_REDIRECT = getEnv(env, 'ROOT_REDIRECT_URL', ROOT_REDIRECT_URL);
      if (!_ROOT_REDIRECT.includes('://')) _ROOT_REDIRECT = 'https://' + _ROOT_REDIRECT;

      // 1. 订阅接口
      const isSubPath = (_SUB_PW && url.pathname === `/${_SUB_PW}`);
      const isNormalSub = (url.pathname === '/sub' && url.searchParams.get('uuid') === _UUID);

      if (isSubPath || isNormalSub) {
          const requestProxyIp = url.searchParams.get('proxyip') || _PROXY_IP;
          const allIPs = await getCustomIPs(env);
          // 传入 _PROXY_IP 作为默认值进行比对
          const listText = genNodes(host, _UUID, requestProxyIp, allIPs, _PS, _PROXY_IP);
          return new Response(btoa(unescape(encodeURIComponent(listText))), { status: 200, headers: { 'Content-Type': 'text/plain; charset=utf-8' } });
      }

      // 2. HTTP 请求 (面板与重定向)
      if (r.headers.get('Upgrade') !== 'websocket') {
          if (url.pathname === '/') return Response.redirect(_ROOT_REDIRECT, 302);
          if (url.pathname === '/admin' || url.pathname === '/admin/') {
              if (_WEB_PW) {
                  const cookie = r.headers.get('Cookie') || "";
                  if (!cookie.includes(`auth=${_WEB_PW}`)) return new Response(loginPage(), { status: 200, headers: {'Content-Type': 'text/html'} });
              }
              // 传入当前的 _PROXY_IP 方便面板显示
              return new Response(dashPage(host, _UUID, _PROXY_IP, _SUB_PW), { status: 200, headers: {'Content-Type': 'text/html'} });
          }
          // 伪装路径处理 (如果访问的是默认API路径，返回一个假的 json 响应，防止探测)
          if (url.pathname === NODE_DEFAULT_PATH) {
              return new Response(JSON.stringify({ status: "ok", version: "1.0.0" }), { status: 200, headers: { 'Content-Type': 'application/json' } });
          }
          return new Response('Not Found', { status: 404 });
      }

      // 3. WebSocket 代理处理
      let finalProxyConfig = null;
      const remoteProxyIP = url.searchParams.get('proxyip'); 

      // 优先级 1: URL 参数 (?proxyip=...)
      if (remoteProxyIP) {
          try {
              finalProxyConfig = await parseIP(remoteProxyIP);
          } catch (e) {}
      }
      // 优先级 2: Path 路径 (/proxyip=...)
      else if (url.pathname.includes('/proxyip=')) {
        try {
            const proxyParam = url.pathname.split('/proxyip=')[1].split('/')[0];
            finalProxyConfig = await parseIP(proxyParam);
        } catch (e) {}
      } 
      // 优先级 3: 环境变量 (默认兜底)
      else if (_PROXY_IP) {
        try {
            finalProxyConfig = await parseIP(_PROXY_IP);
        } catch (e) {}
      }

      const { 0: c, 1: s } = new WebSocketPair();
      s.accept();
      handle(s, finalProxyConfig, _UUID);
      return new Response(null, { status: 101, webSocket: c });

    } catch (err) {
      return new Response(err.toString(), { status: 500 });
    }
  }
};

// =============================================================================
// 🔧 辅助工具
// =============================================================================
async function getCustomIPs(env) {
    let ips = getEnv(env, 'ADD', "");
    const addApi = getEnv(env, 'ADDAPI', "");
    const addCsv = getEnv(env, 'ADDCSV', "");
    
    if (addApi) {
        const urls = addApi.split('\n').filter(u => u.trim() !== "");
        for (const url of urls) {
            try { const res = await fetch(url.trim(), { headers: { 'User-Agent': 'Mozilla/5.0' } }); if (res.ok) { const text = await res.text(); ips += "\n" + text; } } catch (e) {}
        }
    }
    
    if (addCsv) {
        const urls = addCsv.split('\n').filter(u => u.trim() !== "");
        for (const url of urls) {
            try { const res = await fetch(url.trim(), { headers: { 'User-Agent': 'Mozilla/5.0' } }); if (res.ok) { const text = await res.text(); const lines = text.split('\n'); for (let line of lines) { const parts = line.split(','); if (parts.length >= 2) ips += `\n${parts[0].trim()}:443#${parts[1].trim()}`; } } } catch (e) {}
        }
    }
    return ips;
}

// 🟢 节点生成逻辑
function genNodes(h, u, p, ipsText, ps = "", defaultIP = "") {
    let l = ipsText.split('\n').filter(line => line.trim() !== "");
    
    let safeP = p ? p.trim() : "";
    let safeDef = defaultIP ? defaultIP.trim() : "";
    
    // 默认使用伪装路径
    let finalPath = NODE_DEFAULT_PATH;
    
    // 只有当请求的IP 与 默认IP 不一致时，才在路径后追加参数
    if (safeP && safeP !== "" && safeP !== safeDef) {
        finalPath += `?proxyip=${safeP}`;
    }
    
    const encodedPath = encodeURIComponent(finalPath);

    return l.map(L => {
        const [a, n] = L.split('#'); if (!a) return "";
        const I = a.trim(); 
        
        let N = n ? n.trim() : 'Edge-Instance';
        if (ps) N = `${N} ${ps}`;
        
        let i = I, pt = "443"; 
        if (I.includes(']:')) { 
            const s = I.split(']:');
            i = s[0] + ']';
            pt = s[1];
        } else if (I.includes(':') && !I.includes('[')) { 
            const s = I.split(':');
            i = s[0];
            pt = s[1];
        }
        
        return `${PT_TYPE}://${u}@${i}:${pt}?encryption=none&security=tls&sni=${h}&alpn=h3&fp=random&allowInsecure=1&type=ws&host=${h}&path=${encodedPath}#${encodeURIComponent(N)}`
    }).join('\n');
}
