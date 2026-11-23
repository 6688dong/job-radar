#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import concurrent.futures
import html
import json
import os
import re
import smtplib
import socket
import ssl
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timedelta, timezone
from email.header import Header
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from email.utils import formatdate
from html.parser import HTMLParser

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DOCS_DIR = os.path.join(BASE_DIR, "docs")
JOBS_JSON_FILE = os.path.join(DOCS_DIR, "jobs.json")
SEEN_FILE = os.path.join(BASE_DIR, "seen_jobs.json")

BJ_TZ = timezone(timedelta(hours=8))
MAX_DAILY_NEW = 20
MAX_HISTORY_JOBS = 300

# Python 预过滤只拦两类，语义判断交给 Gemini（不要用“外包/驻场/劳务”等泛词一刀切，
# 否则会把写着“负责管理第三方外包/驻场人员”的纯甲方岗误杀）
# ① 明确的外包/人力公司字号；② 明确的外包合同短语
OUTSOURCE_COMPANY_KEYWORDS = (
    "软通", "中软", "中电金信", "博彦", "亿达", "法本", "诚迈", "文思海辉",
    "微创软件", "润和软件", "纬创", "佰钧成", "汉得", "柯莱特", "信必优", "东软",
    "同方鼎欣", "华路时代", "赛意信息", "海隆软件", "凌志软件", "中和软件",
    "易思博", "拓保软件", "华钦", "音泰思", "浪潮世科", "大展科技", "泽佳",
    "中富通", "博奥杰", "兴融联", "联蔚", "凯捷", "恩梯梯数据", "印孚瑟斯",
    "中科软", "京北方", "神州信息", "神州新桥", "宇信", "高伟达", "新致软件",
    "长亮", "天阳科技", "安硕信息", "赞同科技", "先进数通", "银信科技",
    "南天信息", "科蓝", "四方精创", "中科金财", "信雅达", "友友天宇", "融鑫",
    "首信科技", "百信银行", "深演智能",
    "亚信", "浩鲸", "思特奇", "天源迪科", "东方国信", "直真科技", "亿阳信通",
    "德科", "外企德科", "fesco", "中智", "科锐", "万宝盛华", "任仕达",
    "前锦", "易才", "人瑞", "金柚", "英格玛", "clps",
)
OUTSOURCE_CONTRACT_PHRASES = (
    "签订外包", "劳务派遣合同", "华为od", "od岗", "属于外包", "人力外包岗",
)
# 兼容旧名：预检统一用上面两类
OUTSOURCE_KEYWORDS = OUTSOURCE_COMPANY_KEYWORDS + OUTSOURCE_CONTRACT_PHRASES

SAFE_NON_OUTSOURCE_WORDS = (
    "非外包", "不外包", "非人力外包", "非驻场", "不驻场",
    "非派遣", "非劳务派遣", "不外派", "无外派", "非od"
)

# 原网页正文中一旦出现即可直接判定下架的标记
CLOSED_PAGE_MARKERS = (
    "职位已关闭", "停止招聘", "该职位已下线", "职位不存在",
    "已停止招聘", "该岗位已下架", "抱歉，你访问的页面不存在"
)

# 原网页正文中一旦出现即可直接判定为外包合同岗的短语（只保留明确的合同性质表述，
# “驻场运维/长期驻场/第三方外包”等泛表述交给 Gemini 按上下文判断，不再一刀切）
BODY_OUTSOURCE_PHRASES = (
    "签订外包", "劳务派遣合同", "华为od", "属于外包", "人力外包岗",
)

EXCLUDED_TITLE_KEYWORDS = (
    "智算", "算力池", "gpu集群", "训练平台", "千卡", "万卡",
    "运维开发", "devops开发", "平台开发", "ai应用开发",
    "算法工程师", "后端开发", "java开发", "go开发", "golang", "前端开发"
)

# 公司名黑名单：招聘平台名、带“备注”的说明一律不得冒充公司名，查不到真实企业名硬性丢弃
PLATFORM_COMPANY_BLACKLIST = (
    "智联", "猎聘", "BOSS直聘", "前程无忧", "国聘", "备注",
    "51job", "拉勾", "脉脉",
)

# URL 黑名单：只剔除明显的城市泛列表页/聚合页，不做平台白名单
# （飞书招聘 jobs.feishu.cn、Moka app.mokahr.com 等企业直招源无登录墙、必带真实公司名，绝不能拦）
LIST_URL_BLACKLIST = (
    "/zhaopin/",    # BOSS 直聘泛列表
    "/gongsi/",     # BOSS 直聘公司列表
    "/city-",       # 猎聘城市列表，如 /city-bj/zp.../
    "/city_",       # 城市列表变体
    "/c1010",       # BOSS 直聘城市代码路径，如 /c101010100/
    "zhaopin.com/beijing",
    "zhaopin.com/tianjin",
)

# 每日 6 次 Google 查询（每月约 180 次，安全控制在 SerpApi 免费 250 次额度内）
# 每项独立配置 tbs：锁定详情页路径的查询不限时间（智联/国聘详情页在 Google 无时间戳，qdr:m 会误杀 90% 在招页，下架页靠正文检测拦截）；
# 宽泛搜索保留 qdr:m 防陈旧列表页。每条查询控制在 20 个词以内，每条只放 1～2 个 site:。
# SEARCH_PLAN 每项为 (方向, 查询词, tbs)，tbs 为 None 表示不限时间
SEARCH_PLAN = [
    ("大数据/系统运维", '(site:jobs.zhaopin.com OR site:zhaopin.com/jobdetail) (大数据 OR Hadoop OR Kafka OR 数据平台) 运维 ("北京" OR "天津")', None),
    ("大数据/系统运维", '(site:liepin.com/job OR site:iguopin.com/job/detail) (大数据 OR Hadoop OR Kafka OR 数据平台) 运维 ("北京" OR "天津")', None),
    ("大数据/系统运维", '(site:zhipin.com/job_detail OR 直招 OR 招聘) ("大数据运维" OR "数据平台运维" OR "Hadoop运维") ("北京" OR "天津")', "qdr:m"),
    ("AI部署/交付运维", '("私有化部署" OR "大模型交付" OR "AI交付工程师" OR "大模型运维" OR "vLLM" OR "Dify" OR "Ollama") ("北京" OR "天津") 招聘 -算法工程师', "qdr:m"),
    ("AI部署/交付运维", '(site:jobs.feishu.cn OR site:app.mokahr.com OR site:iguopin.com/job/detail) ("私有化部署" OR "AI交付" OR "大模型运维") ("北京" OR "天津")', None),
    ("AI部署/交付运维", '(site:liepin.com/job/ OR site:jobs.zhaopin.com OR site:zhaopin.com/jobdetail OR site:zhipin.com/job_detail/) ("私有化部署" OR "AI交付" OR "大模型运维") ("北京" OR "天津")', None),
]


class PlainTextExtractor(HTMLParser):
    def __init__(self):
        super().__init__()
        self._skip_depth = 0
        self.parts = []

    def handle_starttag(self, tag, attrs):
        if tag.lower() in ("script", "style", "noscript", "svg"):
            self._skip_depth += 1

    def handle_endtag(self, tag):
        if tag.lower() in ("script", "style", "noscript", "svg") and self._skip_depth > 0:
            self._skip_depth -= 1

    def handle_data(self, data):
        if self._skip_depth == 0:
            s = data.strip()
            if s:
                self.parts.append(s)

    def get_text(self):
        return re.sub(r"\s+", " ", " ".join(self.parts)).strip()


def now_bj():
    return datetime.now(BJ_TZ)


def log(msg):
    ts = now_bj().strftime("%Y-%m-%d %H:%M:%S")
    print("[{}] {}".format(ts, msg), flush=True)


def strip_safe_words(text):
    res = text.lower()
    for w in SAFE_NON_OUTSOURCE_WORDS:
        res = res.replace(w, "")
    return res


def resolve_gemini_models(api_key):
    """自动查询当前项目支持的免费 Flash 模型，按优先级排好序返回候选列表。

    只查“模型存不存在”不代表调用时有额度：主力模型若在调用时报 429/503，
    调用方按此列表逐个降级，彻底杜绝“查得到却调不通就全盘失败”。
    """
    url = "https://generativelanguage.googleapis.com/v1beta/models?key={}".format(
        urllib.parse.quote(api_key)
    )
    req = urllib.request.Request(url, method="GET")
    with urllib.request.urlopen(req, timeout=30) as resp:
        data = json.loads(resp.read().decode("utf-8"))

    available = []
    for m in data.get("models") or []:
        name = str(m.get("name") or "").replace("models/", "")
        methods = m.get("supportedGenerationMethods") or []
        lower = name.lower()
        if "generateContent" not in methods:
            continue
        if any(bad in lower for bad in ("tts", "image", "audio", "live", "embedding", "vision")):
            continue
        available.append(name)

    priority_patterns = [
        "gemini-3.5-flash-lite",
        "gemini-3.1-flash-lite",
        "gemini-2.5-flash-lite",
        "gemini-2.5-flash",
        "flash-lite",
        "flash",
        "gemini-3.8-flash",
    ]
    ordered = []
    for pat in priority_patterns:
        for name in available:
            if pat in name.lower() and name not in ordered:
                ordered.append(name)
    for name in available:
        if name not in ordered:
            ordered.append(name)

    if not ordered:
        raise RuntimeError("当前 API Key 名下未查询到任何支持 generateContent 的文本模型")
    log("已自动匹配可用 Gemini 模型（按优先级）: {}".format(", ".join(ordered)))
    return ordered


def search_serpapi(serpapi_key, query, tbs="qdr:m"):
    """tbs=None 表示不限时间（详情页路径查询专用）；Google 无结果时正常返回空列表，不抛异常"""
    params = {
        "engine": "google",
        "q": query,
        "hl": "zh-CN",
        "gl": "cn",
        "num": "10",
        "api_key": serpapi_key,
    }
    if tbs:
        params["tbs"] = tbs
    url = "https://serpapi.com/search.json?" + urllib.parse.urlencode(params)
    req = urllib.request.Request(url, method="GET")
    with urllib.request.urlopen(req, timeout=35) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    if "error" in data:
        if "hasn't returned any results" in str(data["error"]):
            return []
        raise RuntimeError("SerpApi 返回错误: {}".format(data["error"]))
    return data.get("organic_results") or []


def normalize_url(u):
    u = str(u or "").strip()
    if not u.startswith(("http://", "https://")):
        return ""
    parsed = urllib.parse.urlsplit(u)
    clean_q = urllib.parse.urlencode(
        [(k, v) for k, v in urllib.parse.parse_qsl(parsed.query) if not k.lower().startswith(("utm_", "spm", "ka", "pgref"))]
    )
    return urllib.parse.urlunsplit((parsed.scheme, parsed.netloc, parsed.path, clean_q, ""))


class _NoRedirectHandler(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


def resolve_google_goto(u):
    """解开 google.com/goto（或 /url）跳转：单跳不跟随，只取 302 的 Location。

    Google 从 2026 年下半年起把部分搜索结果包成加密重定向链接，无法本地解密，
    只能发一次轻量请求从响应头剥真实地址。必须单跳不跟随：如果顺手跟随第二跳，
    目标招聘站一旦反爬超时，第一跳已经吐出来的真实地址也会跟着丢掉。
    非 goto 链接原样返回；解不开时也原样返回，绝不丢数据。
    """
    u = str(u or "").strip()
    parsed = urllib.parse.urlsplit(u)
    if parsed.netloc.lower() not in ("www.google.com", "google.com"):
        return u
    if parsed.path not in ("/goto", "/url"):
        return u
    try:
        opener = urllib.request.build_opener(_NoRedirectHandler)
        req = urllib.request.Request(u, method="GET", headers={
            "User-Agent": (
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"
            ),
        })
        with opener.open(req, timeout=10) as resp:
            loc = resp.headers.get("Location")
            return loc.strip() if loc else u
    except urllib.error.HTTPError as e:
        # 不跟随的 opener 会把 302 抛成 HTTPError，Location 就在它的响应头里
        loc = e.headers.get("Location") if e.headers else None
        return loc.strip() if loc else u
    except Exception:
        return u


def fetch_and_verify_candidate(item):
    """访问原网页核验：剔除下架死链、识别登录墙、提取正文供大模型精准比对"""
    url = item["url"]
    headers = {
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"
        ),
        "Accept-Language": "zh-CN,zh;q=0.9,en;q=0.8",
    }
    item["verify_status"] = "搜索摘要核验"
    item["page_text"] = ""

    try:
        ctx = ssl.create_default_context()
        req = urllib.request.Request(url, headers=headers, method="GET")
        with urllib.request.urlopen(req, timeout=10, context=ctx) as resp:
            if resp.status >= 400:
                return None
            final_url = resp.url
            raw_bytes = resp.read(250000)
            charset = resp.headers.get_content_charset() or "utf-8"
            html_str = raw_bytes.decode(charset, errors="ignore")
    except urllib.error.HTTPError as e:
        if e.code in (404, 410):
            return None
        return item
    except Exception:
        return item

    parser = PlainTextExtractor()
    try:
        parser.feed(html_str)
        text = parser.get_text()
    except Exception:
        text = ""

    if not text or len(text) < 120:
        return item

    if any(m in text for m in CLOSED_PAGE_MARKERS):
        log("剔除已下架/关闭页面: {}".format(item["title"][:40]))
        return None

    # 登录墙/安全验证页识别：保留搜索摘要但诚实标注未读到正文
    login_wall_signals = ("请完成安全验证", "扫码登录", "登录后查看", "security-check", "验证码登录")
    if len(text) < 350 and any(s in text.lower() for s in login_wall_signals):
        return item

    cleaned_body = strip_safe_words(text[:3000])
    hit_phrase = next((p for p in BODY_OUTSOURCE_PHRASES if p in cleaned_body), None)
    if hit_phrase:
        log("原网页正文命中驻场/外包短语('{}')，已剔除: {}".format(hit_phrase, item["title"][:40]))
        return None

    item["verify_status"] = "原网页已核验"
    item["page_text"] = text[:3000]
    # 常规域名重定向（如移动端域名跳转）同步更新为最终 URL；登录墙/下架页不走到这里，不会误写登录页地址
    final_clean = normalize_url(final_url)
    if final_clean and final_clean != url:
        item["url"] = final_clean
    return item


def collect_verified_candidates(serpapi_key):
    grouped = {"大数据/系统运维": [], "AI部署/交付运维": []}
    seen_urls = set()

    for track, q, tbs in SEARCH_PLAN:
        log("SerpApi 检索 [{}]: {}".format(track, q[:48]))
        try:
            results = search_serpapi(serpapi_key, q, tbs)
            log("SerpApi 检索 [{}] 返回 {} 条".format(track, len(results)))
        except Exception as e:
            log("SerpApi 单条检索异常: {}".format(e))
            continue

        for r in results:
            # 先解开 google.com/goto 跳转再 normalize 和去重：goto 里可能藏着列表页或重复链接，
            # 不先解开会白白占掉每赛道 18 条的宝贵名额
            url = normalize_url(resolve_google_goto(r.get("link")))
            title = str(r.get("title") or "").strip()
            snippet = str(r.get("snippet") or "").strip()
            date_hint = str(r.get("date") or "").strip()
            if not url or not title or url in seen_urls:
                continue

            pre_check = strip_safe_words(title + " " + snippet)
            if any(kw in pre_check for kw in OUTSOURCE_KEYWORDS):
                continue
            if any(kw in title.lower() for kw in EXCLUDED_TITLE_KEYWORDS):
                continue

            # URL 黑名单：只剔除明显的城市泛列表页/聚合页，不做平台白名单
            # （飞书招聘、Moka 等企业直招源必须放行；域名前不写死 www.，m.liepin.com / m.zhipin.com 也要收）
            if any(b in url for b in LIST_URL_BLACKLIST):
                log("泛列表页 URL，已剔除: {}".format(url[:80]))
                continue

            seen_urls.add(url)
            grouped[track].append({
                "track": track,
                "url": url,
                "title": title,
                "snippet": snippet,
                "date_hint": date_hint,
            })
        time.sleep(1)

    verified_grouped = {}
    for track, items in grouped.items():
        candidates = items[:18]
        log("正在并发访问原网页核验 [{}] 候选链接 ({} 条)...".format(track, len(candidates)))
        valid_items = []
        with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:
            for res in pool.map(fetch_and_verify_candidate, candidates):
                if res is not None:
                    valid_items.append(res)
        verified_grouped[track] = valid_items
        log("[{}] 网页预检完成，剩余有效候选 {} 条".format(track, len(valid_items)))

    return verified_grouped


def call_gemini_pure_text(api_key, model_name, prompt_text, max_retries=2):
    """流式调用 :streamGenerateContent?alt=sse，逐行拼 data: 分片。

    3.8-flash 默认开深度思考，非流式 :generateContent 要等全部思考+JSON 写完才回第一个字节，
    很容易撞上读取超时；流式接口按两次数据块之间的空闲时间算超时，思考期间每 1-2 秒就有分片，
    连接不会空闲超时。Gemini 3 系列思考档位用 thinkingLevel=LOW，筛 JD 不需要复杂推演。
    重试策略：超时不重试、立即降级（别白扣每天 20 次额度）；429/5xx 最多重试 1 次。
    """
    url = "https://generativelanguage.googleapis.com/v1beta/models/{}:streamGenerateContent?alt=sse".format(model_name)
    generation_config = {"temperature": 0.1}
    if model_name.lower().startswith("gemini-3"):
        generation_config["thinkingConfig"] = {"thinkingLevel": "LOW"}
    payload = {
        "contents": [{"parts": [{"text": prompt_text}]}],
        "generationConfig": generation_config,
    }
    body_bytes = json.dumps(payload).encode("utf-8")

    for attempt in range(1, max_retries + 1):
        req = urllib.request.Request(
            url,
            data=body_bytes,
            headers={"Content-Type": "application/json", "x-goog-api-key": api_key},
            method="POST",
        )
        try:
            with urllib.request.urlopen(req, timeout=90) as resp:
                text_parts = []
                for raw_line in resp:
                    line = raw_line.decode("utf-8", errors="ignore").strip()
                    if not line.startswith("data:"):
                        continue
                    data = line[5:].strip()
                    if not data or data == "[DONE]":
                        continue
                    try:
                        chunk = json.loads(data)
                    except ValueError:
                        continue
                    for cand in chunk.get("candidates") or []:
                        content = cand.get("content") or {}
                        for p in content.get("parts") or []:
                            if not p.get("thought") and p.get("text"):
                                text_parts.append(str(p["text"]))
                return "".join(text_parts).strip()
        except urllib.error.HTTPError as e:
            err = e.read().decode("utf-8", errors="ignore")
            if e.code == 400 and "thinkingConfig" in generation_config and attempt == 1:
                # 某子型号不支持 thinkingLevel，去掉该字段再试一次
                log("模型 {} 不支持 thinkingLevel，去掉后重试".format(model_name))
                generation_config.pop("thinkingConfig", None)
                payload["generationConfig"] = generation_config
                body_bytes = json.dumps(payload).encode("utf-8")
                continue
            if e.code in (429, 500, 502, 503, 504) and attempt < max_retries:
                log("Gemini HTTP {}，等待 10s 重试...".format(e.code))
                time.sleep(10)
                continue
            raise RuntimeError("Gemini 调用失败 (HTTP {}): {}".format(e.code, err[:400]))
        except (socket.timeout, TimeoutError) as e:
            raise RuntimeError("Gemini 调用超时: {}".format(e))
        except urllib.error.URLError as e:
            if isinstance(e.reason, (socket.timeout, TimeoutError)):
                raise RuntimeError("Gemini 调用超时: {}".format(e.reason))
            raise RuntimeError("Gemini 调用失败: {}".format(e))


def extract_json_array(raw_text):
    if not raw_text:
        return []
    decoder = json.JSONDecoder()
    idx, length = 0, len(raw_text)
    while idx < length:
        pos = raw_text.find("[", idx)
        if pos == -1:
            break
        try:
            obj, end_pos = decoder.raw_decode(raw_text, pos)
            if isinstance(obj, list):
                return [x for x in obj if isinstance(x, dict)]
            idx = end_pos
        except ValueError:
            idx = pos + 1
    return []


def filter_with_gemini(api_key, model_names, track_label, candidates, today_str):
    """按候选模型列表逐个精筛：主力模型 429/503 重试无果时当场降级到下一个，返回 (岗位列表, 实际用到的模型)。"""
    if not candidates:
        return [], None

    indexed_input = []
    id_map = {}
    for i, c in enumerate(candidates, 1):
        id_map[i] = c
        indexed_input.append({
            "source_id": i,
            "search_title": c["title"],
            "date_hint": c["date_hint"],
            "snippet": c["snippet"],
            "verify_status": c["verify_status"],
            "webpage_excerpt": c["page_text"],
        })

    prompt = """
今天北京时间是 {today}。你是极其严谨的求职情报审核员。下面给你一组刚从 Google 抓取并经过网页预检的【{track}】候选结果 JSON。
请你逐条阅读 `search_title`、`snippet` 和 `webpage_excerpt`，严格按求职者画像筛选出真正值得投递的岗位。

【求职者技术栈画像】
- 具备银行生产级大数据平台运维背景；银行、券商、保险、央国企及各类企业的【甲方自招/直招】是核心目标岗位，严禁以“金融证券行业不符”为由丢弃甲方岗位；仅拦截派驻到银行的第三方外包乙方
- 熟悉 Linux 命令行、大数据组件运维（HDFS/YARN/Kafka/Spark/Hive/HBase）
- Docker/K8s 入门：能部署、能排查常见 Pod 问题
- Python 能写一两百行的运维脚本
- 会用 Ollama/vLLM 部署开源大模型，会用 Dify 搭知识库
- 没有 GPU 集群、RDMA/NCCL、昇腾经验，不会 Go/Java 研发

【一票否决红线】（命中任意一条直接丢弃，不要输出）
1. 任何综合IT外包、银行/金融驻场乙方、运营商驻场、劳务派遣、RPO猎头代招模糊公司、华为OD（如软通、中软、中电金信、博彦、法本、文思海辉、神州信息、京北方、宇信、长亮、银信、友友天宇、亚信、浩鲸、外企德科、FESCO等）
2. 聚合列表页（没有具体某一家公司和具体某一个岗位名称的泛列表页直接丢弃）
3. 工作地点不在【北京、天津、远程】范围内的岗位直接丢弃
4. 纯智算中心底座建设、千卡GPU训练集群组网(RDMA/InfiniBand/NCCL)、大模型训练底层架构岗直接丢弃；但注意：【大模型交付 / AI交付 / 私有化部署 / FDE / 大模型运维】属于核心目标方向——在几台 GPU/昇腾服务器上用 Docker/vLLM 做模型推理私有化交付的保留（不熟的国产硬件写进 gap），不要一见 GPU/昇腾就判死刑
5. 运维开发(SRE研发)、DevOps平台开发、算法工程师、Java/Go后端开发岗
6. 明确要求 5 年以上大模型或智算经验
7. company 栏填的是招聘平台名或带“备注”的说明（如智联、猎聘、BOSS直聘、前程无忧、国聘、智联招聘、备注等），不是真实直招企业名——查不到真实企业名就直接丢弃，绝不输出
8. 当 `webpage_excerpt` 为空（登录墙/安全验证导致没读到正文）时，允许从 `search_title` 或 `snippet` 里的企业署名提取真实公司名（如标题后缀“大数据运维_北京某科技-猎聘”里的“某科技”）；只有当标题和摘要里完全只有“猎聘/智联/某知名企业”且无任何真实字号时，才丢弃该条

【真实性铁律】
- 只能基于提供的候选数据提取，严禁编造公司名、薪资或要求。
- 如果 `webpage_excerpt` 为空（登录墙导致没读到正文），优先从 `search_title`/`snippet` 的企业署名里提取真实公司名；只有标题和摘要里完全只有平台名或“某知名企业”且无任何真实字号时，才丢弃该条。
- 如果 `verify_status` 为 "搜索摘要核验" 且摘要里没写薪资或细节，必须如实把 `salary` 填为 "未知"，并在 `gap` 中注明 "正文受登录墙限制，需点开核对完整JD"。
- 只输出合法的 JSON 数组，不要任何多余解释。数组必须包含输入中每一个 source_id 的判定，严禁遗漏任何一条（拿不准也不许跳过）：
  - 若丢弃：{{"source_id": 1, "decision": "drop", "reason": "一句话具体原因（20字内，如：命中外包公司软通、地点不在北京天津、正文为空且标题无真实公司名、偏Java开发）。严禁写“与目标方向不符”“与目标行业不符”这种模糊套话，必须写明该页实际在招什么或命中了哪条红线（如：主帖实为算法工程师、大模型交付仅为底部推荐词、要求RDMA千卡组网）"}}
  - 若保留：{{"source_id": 2, "decision": "keep", "title": "原帖准确岗位名称（不要把标题和正文里的不同叫法拼在一起）", "company": "准确公司名称（正文为空时可从标题/摘要的企业署名提取；只有标题和摘要里完全只有平台名或“某知名企业”且无任何真实字号时才丢弃该条）", "city": "北京 或 天津 或 远程", "salary": "真实薪资范围 或 未知", "date": "发布时间如 2026-11-22 或 近期 或 未知", "match": "一句话说明与求职者画像的匹配点", "gap": "一句话说明岗位要求中求职者尚不具备的技能差距"}}
- 若全部不符合，也要逐条输出 drop 判定，不要只输出 []。

候选数据如下：
{data_json}
""".strip().format(
        today=today_str,
        track=track_label,
        data_json=json.dumps(indexed_input, ensure_ascii=False, indent=2),
    )

    # 预检快照日志：进模型前看一眼每条候选的核验状态和正文字数，
    # 一眼看穿是不是机房 IP 被招聘站滑块拦成了 0 字正文
    for i, c in enumerate(candidates, 1):
        log("候选 #{} verify={} 正文{}字 | {}".format(
            i, c.get("verify_status"), len(c.get("page_text") or ""), c["title"][:40]))

    raw_reply = ""
    used_model = None
    last_err = None
    for model_name in model_names:
        try:
            raw_reply = call_gemini_pure_text(api_key, model_name, prompt)
            used_model = model_name
            break
        except Exception as e:
            last_err = e
            log("模型 {} 调用失败，降级到下一个模型: {}".format(model_name, str(e)[:200]))
    if used_model is None:
        raise RuntimeError("全部候选模型调用失败: {}".format(last_err))
    log("方向 [{}] 实际使用模型: {}".format(track_label, used_model))
    parsed = extract_json_array(raw_reply)

    final_jobs = []
    for item in parsed:
        try:
            sid = int(item.get("source_id"))
        except Exception:
            continue
        if sid not in id_map:
            continue

        orig = id_map[sid]
        # 丢弃审计日志：模型必须对每条候选输出判定，drop 的原因打进日志，黑盒才能打开
        if item.get("decision") == "drop":
            log("[DROP #{}] 原因: {} | 原标题: {} | {}".format(
                sid, str(item.get("reason") or "未说明")[:40], orig["title"][:40], orig["url"][:60]))
            continue
        title = str(item.get("title") or "").strip()
        company = str(item.get("company") or "").strip()
        city = str(item.get("city") or "").strip()
        if not title or not company or company in ("未知", "某公司", "某知名企业", "猎头代招"):
            log("[DROP #{}] 原因: 标题或公司名缺失 | 原标题: {}".format(sid, orig["title"][:40]))
            continue
        # 平台名冒充公司名：代码层硬性拦截，查不到真实企业名一律丢弃
        hit_platform = next((kw for kw in PLATFORM_COMPANY_BLACKLIST if kw in company), None)
        if hit_platform:
            log("[DROP #{}] 原因: Python 终审拦截平台名冒充公司名('{}') | {} | {}".format(sid, hit_platform, company, title))
            continue
        if not any(c in city for c in ("北京", "天津", "远程")):
            log("[DROP #{}] 原因: 城市不在北京/天津/远程 ({}) | {} | {}".format(sid, city, company, title))
            continue

        check_str = strip_safe_words("{} {} {} {}".format(
            company, title, item.get("match", ""), item.get("gap", "")
        ))
        hit_out = next((kw for kw in OUTSOURCE_KEYWORDS if kw in check_str), None)
        if hit_out:
            log("[DROP #{}] 原因: Python 终审拦截外包词('{}') | {} | {}".format(sid, hit_out, company, title))
            continue
        if any(kw in title.lower() for kw in EXCLUDED_TITLE_KEYWORDS):
            log("[DROP #{}] 原因: 标题命中排除词 | {} | {}".format(sid, company, title))
            continue

        final_jobs.append({
            "title": title,
            "company": company,
            "city": city,
            "salary": str(item.get("salary") or "未知").strip(),
            "date": str(item.get("date") or orig["date_hint"] or "近期").strip(),
            "url": orig["url"],  # 强制锁定原始真实 URL，杜绝模型幻觉
            "verify_status": orig["verify_status"],
            "track": track_label,
            "match": str(item.get("match") or "无").strip(),
            "gap": str(item.get("gap") or "无").strip(),
        })
    return final_jobs, used_model


def make_fingerprint(j):
    comp = re.sub(r"\s+", "", j.get("company", "")).lower()
    title = re.sub(r"\s+", "", j.get("title", "")).lower()
    city = re.sub(r"\s+", "", j.get("city", "")).lower()
    return "{}|{}|{}".format(comp, title, city)


def load_json(path, default):
    if not os.path.exists(path):
        return default
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return default


def save_json_atomic(path, obj):
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(obj, f, ensure_ascii=False, indent=2)
    os.replace(tmp, path)


def build_email_bodies(job_list, today_str, page_url):
    cards_html = []
    plain_lines = [
        "京津大数据 & AI 运维新增岗位（{}｜共 {} 条）".format(today_str, len(job_list)),
        "在线看板：{}".format(page_url or "请在 GitHub Pages 查看"),
        "=" * 48,
        "",
    ]

    for idx, j in enumerate(job_list, 1):
        search_kw = urllib.parse.quote("{} {} {} 招聘".format(j["company"], j["title"], j["city"]))
        google_url = "https://www.google.com/search?q={}".format(search_kw)

        plain_lines.append("#{}. [{}] {} | {} | {} | {}".format(
            idx, j["verify_status"], j["title"], j["company"], j["city"], j["salary"]
        ))
        plain_lines.append("匹配点：{}".format(j["match"]))
        plain_lines.append("差距：{}".format(j["gap"]))
        plain_lines.append("直达链接：{}".format(j["url"]))
        plain_lines.append("-" * 40)

        v_bg = "#dcfce7" if j["verify_status"] == "原网页已核验" else "#f3f4f6"
        v_fg = "#166534" if j["verify_status"] == "原网页已核验" else "#4b5563"

        card = """
        <table width="100%" cellpadding="0" cellspacing="0" style="background:#ffffff;border:1px solid #e5e7eb;border-radius:10px;margin-bottom:14px;font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,sans-serif;">
          <tr>
            <td style="padding:16px 18px;">
              <div style="font-size:16px;font-weight:700;color:#111827;line-height:1.4;">
                #{idx} {title}
                <span style="display:inline-block;margin-left:6px;background:#eff6ff;color:#1d4ed8;font-size:11px;padding:2px 7px;border-radius:4px;">{track}</span>
                <span style="display:inline-block;margin-left:4px;background:{v_bg};color:{v_fg};font-size:11px;padding:2px 7px;border-radius:4px;">{v_status}</span>
                <span style="float:right;background:#fef3c7;color:#b45309;font-size:12px;padding:3px 9px;border-radius:999px;">{salary}</span>
              </div>
              <div style="margin-top:8px;font-size:13px;color:#4b5563;">
                🏢 {company} &nbsp;|&nbsp; 📍 {city} &nbsp;|&nbsp; 📅 {date}
              </div>
              <div style="margin-top:10px;padding:9px 12px;background:#f0fdf4;border-left:4px solid #16a34a;border-radius:4px;font-size:13px;color:#166534;line-height:1.5;">
                <strong>匹配点：</strong>{match}
              </div>
              <div style="margin-top:7px;padding:9px 12px;background:#fffbeb;border-left:4px solid #d97706;border-radius:4px;font-size:13px;color:#92400e;line-height:1.5;">
                <strong>差距：</strong>{gap}
              </div>
              <div style="margin-top:12px;">
                <a href="{url}" target="_blank" style="display:inline-block;background:#2563eb;color:#ffffff;text-decoration:none;font-size:13px;font-weight:600;padding:7px 14px;border-radius:6px;margin-right:8px;">打开原招聘页 &rarr;</a>
                <a href="{g_url}" target="_blank" style="display:inline-block;background:#f3f4f6;color:#374151;border:1px solid #d1d5db;text-decoration:none;font-size:12px;padding:6px 11px;border-radius:6px;">Google 核验</a>
              </div>
            </td>
          </tr>
        </table>
        """.format(
            idx=idx,
            title=html.escape(j["title"]),
            track=html.escape(j["track"]),
            v_bg=v_bg,
            v_fg=v_fg,
            v_status=html.escape(j["verify_status"]),
            salary=html.escape(j["salary"]),
            company=html.escape(j["company"]),
            city=html.escape(j["city"]),
            date=html.escape(j["date"]),
            match=html.escape(j["match"]),
            gap=html.escape(j["gap"]),
            url=html.escape(j["url"], quote=True),
            g_url=html.escape(google_url, quote=True),
        )
        cards_html.append(card)

    board_banner = ""
    if page_url:
        board_banner = (
            '<p style="margin:0 0 16px;"><a href="{u}" target="_blank" '
            'style="color:#2563eb;font-size:13px;font-weight:600;text-decoration:none;">'
            '🌐 点击打开在线求职看板（支持按京/津/方向筛选全部历史岗位）&rarr;</a></p>'
        ).format(u=html.escape(page_url, quote=True))

    html_body = """
    <html><body style="margin:0;padding:18px;background:#f3f4f6;">
      <div style="max-width:680px;margin:0 auto;">
        <h2 style="margin:0 0 6px;color:#111827;font-size:19px;font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;">
          京津大数据 &amp; AI 运维新增岗位（{today}｜新增 {cnt} 条）
        </h2>
        {banner}
        {cards}
      </div>
    </body></html>
    """.format(today=today_str, cnt=len(job_list), banner=board_banner, cards="".join(cards_html))

    return "\n".join(plain_lines), html_body


def send_gmail(smtp_user, smtp_pass, to_email, subject, plain_body, html_body):
    msg = MIMEMultipart("alternative")
    msg["Subject"] = Header(subject, "utf-8")
    msg["From"] = smtp_user
    msg["To"] = to_email
    msg["Date"] = formatdate(localtime=True)
    msg.attach(MIMEText(plain_body, "plain", "utf-8"))
    msg.attach(MIMEText(html_body, "html", "utf-8"))

    ctx = ssl.create_default_context()
    try:
        with smtplib.SMTP_SSL("smtp.gmail.com", 465, timeout=25, context=ctx) as s:
            s.login(smtp_user, smtp_pass)
            s.sendmail(smtp_user, [to_email], msg.as_string())
            log("Gmail 卡片邮件发送成功 (465/SSL -> {})".format(to_email))
            return
    except Exception as e1:
        log("465 端口连接异常 ({})，尝试切换 587/STARTTLS...".format(e1))
        with smtplib.SMTP("smtp.gmail.com", 587, timeout=25) as s:
            s.ehlo()
            s.starttls(context=ctx)
            s.ehlo()
            s.login(smtp_user, smtp_pass)
            s.sendmail(smtp_user, [to_email], msg.as_string())
            log("Gmail 卡片邮件发送成功 (587/STARTTLS -> {})".format(to_email))


def main():
    gemini_key = os.getenv("GEMINI_API_KEY", "").strip()
    serpapi_key = os.getenv("SERPAPI_KEY", "").strip()
    smtp_user = os.getenv("SMTP_USER", "").strip()
    smtp_pass = os.getenv("SMTP_APP_PASS", "").replace(" ", "").strip()
    to_email = os.getenv("TO_EMAIL", smtp_user).strip()
    repo_slug = os.getenv("GITHUB_REPOSITORY", "").strip()

    if not gemini_key or not serpapi_key:
        raise RuntimeError("缺少必要环境变量：请检查 GitHub Secrets 中的 GEMINI_API_KEY 和 SERPAPI_KEY")

    page_url = ""
    if "/" in repo_slug:
        owner, repo = repo_slug.split("/", 1)
        page_url = "https://{}.github.io/{}/".format(owner, repo)

    today_str = now_bj().strftime("%Y-%m-%d")
    updated_at_str = now_bj().strftime("%Y-%m-%d %H:%M:%S")

    model_names = resolve_gemini_models(gemini_key)
    verified_groups = collect_verified_candidates(serpapi_key)

    all_filtered = []
    model_used = None
    for idx, (track, cands) in enumerate(verified_groups.items()):
        if idx > 0:
            # 两次大请求拆进前后两个分钟窗口，避免同分钟重试叠加撞上 250K TPM 上限
            time.sleep(45)
        log("正在调用 {} 精筛方向 [{}]...".format(model_names[0], track))
        jobs, used = filter_with_gemini(gemini_key, model_names, track, cands, today_str)
        if model_used is None:
            model_used = used
        log("方向 [{}] 最终通过审核: {} 条".format(track, len(jobs)))
        all_filtered.extend(jobs)

    seen_dict = load_json(SEEN_FILE, {})
    if not isinstance(seen_dict, dict):
        seen_dict = {}

    new_jobs = []
    batch_fp = set()
    for j in all_filtered:
        fp = make_fingerprint(j)
        if fp in seen_dict or fp in batch_fp:
            continue
        batch_fp.add(fp)
        j["added_date"] = today_str
        j["id"] = fp
        new_jobs.append(j)
        if len(new_jobs) >= MAX_DAILY_NEW:
            break

    log("去重后今日新增岗位: {} 条".format(len(new_jobs)))

    # 更新前端看板数据源 docs/jobs.json（新岗位排最前，保留历史记录供筛选）
    board_data = load_json(JOBS_JSON_FILE, {"jobs": []})
    old_jobs = board_data.get("jobs") if isinstance(board_data, dict) else []
    if not isinstance(old_jobs, list):
        old_jobs = []
    # 顺手清脏数据：历史卡片里带 google.com/goto 的链接也解开写回干净地址，解不开就保留原链接
    for oj in old_jobs:
        u = str(oj.get("url") or "")
        if "google.com/goto" in u or "google.com/url" in u:
            clean = normalize_url(resolve_google_goto(u))
            if clean and clean != u:
                log("历史卡片链接已洗净: {} -> {}".format(u[:50], clean[:80]))
                oj["url"] = clean

    merged_board_jobs = (new_jobs + old_jobs)[:MAX_HISTORY_JOBS]
    save_json_atomic(JOBS_JSON_FILE, {
        "updated_at": updated_at_str,
        "latest_date": today_str,
        "today_new_count": len(new_jobs),
        "model": model_used or ",".join(model_names),
        "jobs": merged_board_jobs,
    })
    log("网页看板数据已写入: {} (累计收录 {} 条)".format(JOBS_JSON_FILE, len(merged_board_jobs)))

    for j in new_jobs:
        seen_dict[j["id"]] = updated_at_str
    trimmed_seen = dict(sorted(seen_dict.items(), key=lambda kv: kv[1])[-2000:])
    save_json_atomic(SEEN_FILE, trimmed_seen)

    # 若今日有新增且配置了邮箱密钥，发送卡片通知邮件
    if new_jobs and smtp_user and smtp_pass:
        subject = "京津运维精选岗位（{}｜新增 {} 条）".format(today_str, len(new_jobs))
        plain_body, html_body = build_email_bodies(new_jobs, today_str, page_url)
        try:
            send_gmail(smtp_user, smtp_pass, to_email, subject, plain_body, html_body)
        except Exception as e:
            print("::warning::网页数据已更新，但 Gmail 发送失败，请检查 SMTP_APP_PASS: {}".format(e))
    elif not new_jobs:
        log("今日无新增岗位，看板时间戳已刷新，跳过发信。")


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        log("运行终止: {}".format(exc))
        sys.exit(1)