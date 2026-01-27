
from __future__ import annotations
import json
import sys
import time
import threading
import random
import logging
import math
import re
from collections import defaultdict, deque
from datetime import datetime, timedelta
from urllib.parse import urlparse, parse_qs
from typing import Any, Dict, Tuple, Optional, List, Union
import statistics

import pytz
import requests
import websocket
from rich.console import Console, Group
from rich.table import Table
from rich.panel import Panel
from rich.live import Live
from rich.align import Align
from rich.rule import Rule
from rich.text import Text
from rich import box
from rich.layout import Layout
from rich.progress import Progress, SpinnerColumn, TextColumn

# -------------------- CONFIG & GLOBALS --------------------
console = Console()
# Thiết lập múi giờ cho Việt Nam
tz = pytz.timezone("Asia/Ho_Chi_Minh")

# Thiết lập hệ thống ghi log
logger = logging.getLogger("escape_vip_ai_rebuild")
logger.setLevel(logging.INFO)
logger.addHandler(logging.FileHandler("escape_vip_ai_rebuild.log", encoding="utf-8"))

# Endpoints (config) - Cấu hình các API và WebSocket
BET_API_URL = "https://api.escapemaster.net/escape_game/bet"
WS_URL = "wss://api.escapemaster.net/escape_master/ws"
WALLET_API_URL = "https://wallet.3games.io/api/wallet/user_asset"

# Thiết lập Session HTTP với Retry/Adapter để tăng độ ổn định kết nối
HTTP = requests.Session()
try:
    from requests.adapters import HTTPAdapter
    from urllib3.util.retry import Retry
    adapter = HTTPAdapter(
        pool_connections=20, pool_maxsize=50,
        max_retries=Retry(total=3, backoff_factor=0.2,
                          status_forcelist=(500, 502, 503, 504))
    )
    HTTP.mount("https://", adapter)
    HTTP.mount("http://", adapter)
except Exception:
    pass

# Tên các phòng (đã được Việt hóa)
ROOM_NAMES = {
    1: "📦 Nhà kho", 2: "🪑 Phòng họp", 3: "👔 Phòng giám đốc", 4: "💬 Phòng trò chuyện",
    5: "🎥 Phòng giám sát", 6: "🏢 Văn phòng", 7: "💰 Phòng tài vụ", 8: "👥 Phòng nhân sự"
}
ROOM_ORDER = [1, 2, 3, 4, 5, 6, 7, 8]

# Trạng thái runtime của chương trình
USER_ID: Optional[int] = None
SECRET_KEY: Optional[str] = None
issue_id: Optional[int] = None # ID của ván hiện tại
issue_start_ts: Optional[float] = None # Thời điểm bắt đầu ván
count_down: Optional[int] = None # Đếm ngược
killed_room: Optional[int] = None # Phòng bị sát thủ tiêu diệt (kết quả)
round_index: int = 0 # Chỉ số ván đã chơi

# Dữ liệu trạng thái phòng (real-time)
room_state: Dict[int, Dict[str, Any]] = {r: {"players": 0, "bet": 0} for r in ROOM_ORDER}
# Dữ liệu thống kê phòng (lịch sử)
room_stats: Dict[int, Dict[str, Any]] = {
    r: {"kills": 0, "survives": 0, "last_kill_round": None, "last_players": 0, "last_bet": 0, "historical_bpp": deque(maxlen=50)} 
    for r in ROOM_ORDER
}

predicted_room: Optional[int] = None # Phòng được AI dự đoán
last_killed_room: Optional[int] = None # Phòng bị tiêu diệt gần nhất
prediction_locked: bool = False # Khóa dự đoán sau khi đã đặt cược

# *** SUPERIOR DEVIL UPGRADE: Track last 20 kills và Pattern Tracker ***
game_kill_history: deque = deque(maxlen=20) # Lịch sử 20 lần sát thủ ra tay
# Dữ liệu theo dõi mô hình tiêu diệt (ví dụ: tần suất, chuỗi lặp)
game_kill_pattern_tracker: Dict[str, Any] = {
    "kill_counts": defaultdict(int), # Đếm số lần tiêu diệt trong lịch sử gần đây
    "kill_seq": deque(maxlen=5), # Chuỗi 5 lần tiêu diệt gần nhất
    "last_kill_ts": time.time(), # Thời điểm tiêu diệt gần nhất
}

# balances & pnl
current_build: Optional[float] = None
current_usdt: Optional[float] = None
current_world: Optional[float] = None
last_balance_ts: Optional[float] = None
last_balance_val: Optional[float] = None
starting_balance: Optional[float] = None
cumulative_profit: float = 0.0 # Tổng lợi nhuận/lỗ

# streaks - Chuỗi thắng/thua
win_streak: int = 0
lose_streak: int = 0
max_win_streak: int = 0
max_lose_streak: int = 0

# betting - Cấu hình đặt cược
auto_bet_enabled: bool = True # --- NEW FEATURE: Biến kiểm soát chế độ tự động cược ---
base_bet: float = 1.0 # Tiền cược cơ sở
multiplier: float = 2.0 # Hệ số nhân khi Martingale
current_bet: Optional[float] = None # Tiền cược hiện tại
run_mode: str = "AUTO" # Chế độ chạy: AUTO hoặc STAT

# Cấu hình bỏ qua ván
bet_rounds_before_skip: int = 0
_rounds_placed_since_skip: int = 0
skip_next_round_flag: bool = False

bet_history: deque = deque(maxlen=2000) # Lịch sử cược (lưu trữ 500 ván)
bet_sent_for_issue: set = set() # Đánh dấu ván đã gửi cược

# Kiểm soát dừng/nghỉ
pause_after_losses: int = 0  # Khi thua thì nghỉ bao nhiêu tay
_skip_rounds_remaining: int = 0
profit_target: Optional[float] = None  # Mục tiêu chốt lời (BUILD)
stop_when_profit_reached: bool = False
stop_loss_target: Optional[float] = None  # Mục tiêu cắt lỗ (BUILD)
stop_when_loss_reached: bool = False
stop_flag: bool = False # Cờ dừng toàn bộ tool

# UI / timing
ui_state: str = "IDLE"
analysis_start_ts: Optional[float] = None
analysis_blur: bool = False # Hiệu ứng làm mờ/nhấp nháy trong phân tích
# ws/poll
last_msg_ts: float = time.time()
last_balance_fetch_ts: float = 0.0
BALANCE_POLL_INTERVAL: float = 4.0
_ws: Dict[str, Any] = {"ws": None} # Đối tượng WebSocket

# selection config (used by algorithms)
SELECTION_CONFIG = {
    "max_bet_allowed": float("inf"),
    "max_players_allowed": 9999,
    "avoid_last_kill": True,
    # === SUPERIOR DEVIL FILTERS ===
    "max_recent_kills": 3, # Số lần bị tiêu diệt tối đa trong 10 ván gần nhất để phòng còn đủ điều kiện
    "min_survive_rate": 0.55, # Tỷ lệ sống tối thiểu để phòng đủ điều kiện
    "bet_management_strategy": "MARTINGALE", # MARTINGALE (default) or ANTI-MARTINGALE
    "bpp_trap_low": 500.0, # Ngưỡng BPP thấp (dưới ngưỡng này là bẫy)
    "bpp_trap_high": 4000.0, # Ngưỡng BPP cao (trên ngưỡng này là bẫy)
}

# *** SUPERIOR DEVIL UPGRADE V4: Change logic name ***
SELECTION_MODES = {
    "DEVILMODE": "SUPERIOR DEVIL - SÓNG THẦN (v4.0)" # New label
}
settings = {"algo": "DEVILMODE"} # Default to new setting

_spinner = ["🌀", "🌐", "🔷", "🌀", "🌐", "🔷"] # New Blue-themed spinner

_num_re = re.compile(r"-?\d+[\d,]*\.?\d*")

# *** THEME CHANGE: Blue/Dark Blue Theme ***
MAIN_COLOR = "blue" # Màu chính (Xanh Dương)
ACCENT_COLOR = "dark_blue" # Màu nhấn (Xanh Dương Đậm)
TEXT_COLOR = "bold white" # Màu chữ mặc định
SUCCESS_COLOR = "bold #00ff00" # Màu thành công (Xanh Neon)
FAILURE_COLOR = "bold #ff0000" # Màu thất bại (Đỏ Neon)
PENDING_COLOR = "bold #add8e6" # Màu chờ (Xanh da trời nhạt)
WARNING_COLOR = "bold yellow" # Màu cảnh báo (Vàng)

# *** ENHANCED RISK VISUALIZATION - ADVANCED DYNAMIC RISK ASSESSMENT ***
# Các mức độ rủi ro cho trực quan hóa
RISK_LEVEL_SAFE = 0        # An toàn - Xanh lá
RISK_LEVEL_LOW = 1         # Rủi ro thấp - Xanh dương
RISK_LEVEL_MEDIUM = 2      # Rủi ro trung bình - Vàng
RISK_LEVEL_HIGH = 3        # Rủi ro cao - Đỏ
RISK_LEVEL_CRITICAL = 4    # Rủi ro cực cao - Đỏ đậm

# *** ADVANCED RISK ASSESSMENT SYSTEM ***
# Biến lưu trữ đánh giá rủi ro nâng cao với EMA
room_risk_ema: Dict[int, float] = {r: 50.0 for r in ROOM_ORDER}  # EMA value for each room (start at 50%)
room_risk_raw: Dict[int, float] = {r: 50.0 for r in ROOM_ORDER}  # Latest raw risk score
room_risk_assessment: Dict[int, Dict[str, Any]] = {
    r: {
        "risk_level": RISK_LEVEL_SAFE,
        "risk_score": 50.0,  # EMA value
        "risk_raw": 50.0,    # Raw risk score
        "risk_color": PENDING_COLOR,
        "risk_icon": "🟡",
        "risk_factors": [],
        "risk_trend": "stable",  # rising, falling, stable
        "last_update": time.time(),
        "update_count": 0
    } for r in ROOM_ORDER
}

# EMA smoothing factor - higher = more responsive, lower = smoother
RISK_EMA_ALPHA = 0.25
# Minimum and maximum risk values to avoid absolute 0% or 100%
MIN_RISK = 5.0
MAX_RISK = 95.0

# Risk factor weights - UPDATED WITH AVF WEIGHTS
RISK_WEIGHTS = {
    "historical_kill_rate": 0.15,      # 15%
    "current_popularity": 0.10,        # 10%
    "bpp_analysis": 0.10,              # 10%
    "cold_room_bonus": 0.05,           # 5%
    "pattern_analysis": 0.05,          # 5%
    "market_state": 0.05,              # 5%
    # AVF Advanced Risk Models (40%)
    "ema_avf": 0.08,                   # 8% - EMA Anti-Volatility Filter
    "std_avf": 0.06,                   # 6% - Standard Deviation Anti-Volatility
    "ent_avf": 0.05,                   # 5% - Entropy Anti-Volatility
    "bayes_avf": 0.07,                 # 7% - Bayesian Posterior Risk
    "ensemble_avf": 0.06,              # 6% - Ensemble Model Consensus
    "trend_avf": 0.04,                 # 4% - Trend Divergence
    "mc_avf": 0.04,                    # 4% - Monte-Carlo Convergence
}

# Advanced pattern detection
risk_pattern_memory: Dict[int, deque] = {r: deque(maxlen=10) for r in ROOM_ORDER}  # Store recent risk values for pattern analysis
risk_oscillation_tracker: Dict[int, Dict[str, Any]] = {
    r: {
        "amplitude": 0.0,
        "frequency": 0.0,
        "last_peak": 50.0,
        "last_trough": 50.0,
        "trend_duration": 0
    } for r in ROOM_ORDER
}

# *** UI REFRESH RATE CONTROL ***
UI_REFRESH_INTERVAL = 0.3  # Giảm từ 0.12 xuống 0.3 giây (từ ~8 FPS xuống ~3 FPS)
RISK_UPDATE_INTERVAL = 1.0  # Cập nhật risk assessment mỗi 1 giây
last_ui_update: float = 0.0
last_risk_update: float = 0.0

# -------------------- UTILITIES --------------------

def log_debug(msg: str) -> None:
    """Ghi log ở mức DEBUG."""
    try:
        logger.debug(msg)
    except Exception:
        pass


def _parse_number(x: Any) -> Optional[float]:
    """
    Phân tích một giá trị (chuỗi, số) thành float.
    Hữu ích khi giá trị số được trả về dưới dạng chuỗi có dấu phẩy.
    """
    if x is None:
        return None
    if isinstance(x, (int, float)):
        return float(x)
    s = str(x)
    m = _num_re.search(s)
    if not m:
        return None
    token = m.group(0).replace(",", "")
    try:
        return float(token)
    except Exception:
        return None


def human_ts() -> str:
    """Trả về timestamp hiện tại dưới dạng chuỗi dễ đọc."""
    return datetime.now(tz).strftime("%Y-%m-%d %H:%M:%S")


def safe_input(prompt: str, default: Any = None, cast: Optional[type] = None) -> Any:
    """Hàm nhập liệu an toàn, hỗ trợ giá trị mặc định và ép kiểu."""
    try:
        s = input(prompt).strip()
    except EOFError:
        return default
    if s == "":
        return default
    if cast:
        try:
            return cast(s)
        except Exception:
            return default
    return s

def exponential_moving_average(current_value: float, previous_ema: float, alpha: float) -> float:
    """Tính Exponential Moving Average."""
    return alpha * current_value + (1 - alpha) * previous_ema

def normalize_value(value: float, min_val: float, max_val: float) -> float:
    """Chuẩn hóa giá trị về khoảng 0-1."""
    if max_val == min_val:
        return 0.5
    return max(0.0, min(1.0, (value - min_val) / (max_val - min_val)))

def smooth_step(x: float) -> float:
    """Hàm làm mượt giá trị."""
    return 3 * x**2 - 2 * x**3

def oscillating_factor(base_value: float, time_factor: float, frequency: float = 1.0) -> float:
    """Tạo hệ số dao động để mô phỏng sóng."""
    return base_value * (0.95 + 0.05 * math.sin(time_factor * frequency))

# -------------------- BALANCE PARSING & FETCH --------------------
def _parse_balance_from_json(j: Dict[str, Any]) -> Tuple[Optional[float], Optional[float], Optional[float]]:
    """
    Phân tích JSON response từ API ví (wallet) để trích xuất số dư BUILD, WORLD, USDT.
    Hỗ trợ nhiều cấu trúc JSON khác nhau.
    """
    if not isinstance(j, dict):
        return None, None, None
    
    build = None
    world = None
    usdt = None

    data = j.get("data") if isinstance(j.get("data"), dict) else j
    
    # Ưu tiên các khóa phổ biến trong data/cwallet
    if isinstance(data, dict):
        cwallet = data.get("cwallet") if isinstance(data.get("cwallet"), dict) else None
        if cwallet:
            for key in ("ctoken_contribute", "ctoken", "build", "balance", "amount"):
                if key in cwallet and build is None:
                    build = _parse_number(cwallet.get(key))
        for k in ("build", "ctoken", "ctoken_contribute"):
            if build is None and k in data:
                build = _parse_number(data.get(k))
        for k in ("usdt", "kusdt", "usdt_balance"):
            if usdt is None and k in data:
                usdt = _parse_number(data.get(k))
        for k in ("world", "xworld"):
            if world is None and k in data:
                world = _parse_number(data.get(k))

    # Fallback: Quét toàn bộ JSON (recursive walk)
    found = []

    def walk(o: Any, path=""):
        if isinstance(o, dict):
            for kk, vv in o.items():
                nk = (path + "." + str(kk)).strip(".")
                if isinstance(vv, (dict, list)):
                    walk(vv, nk)
                else:
                    n = _parse_number(vv)
                    if n is not None:
                        found.append((nk.lower(), n))
        elif isinstance(o, list):
            for idx, it in enumerate(o):
                walk(it, f"{path}[{idx}]")

    walk(j)

    for k, n in found:
        if build is None and any(x in k for x in ("ctoken", "build", "contribute", "balance")):
            build = n
        if usdt is None and "usdt" in k:
            usdt = n
        if world is None and any(x in k for x in ("world", "xworld")):
            world = n

    return build, world, usdt


def balance_headers_for(uid: Optional[int] = None, secret: Optional[str] = None) -> Dict[str, str]:
    """Tạo header cần thiết để gọi API lấy số dư."""
    h = {
        "accept": "*/*",
        "accept-language": "vi,en;q=0.9",
        "cache-control": "no-cache",
        "country-code": "vn",
        "origin": "https://xworld.info",
        "pragma": "no-cache",
        "referer": "https://xworld.info/",
        "user-agent": "Mozilla/5.0 (Linux; Android 6.0; Nexus 5) AppleWebKit/537.36 "
                      "(KHTML, like Gecko) Chrome/137.0.0.0 Mobile Safari/537.36",
        "user-login": "login_v2",
        "xb-language": "vi-VN",
    }
    if uid is not None:
        h["user-id"] = str(uid)
    if secret:
        h["user-secret-key"] = str(secret)
    return h


def fetch_balances_3games(retries: int = 2, timeout: int = 6, params: Optional[Dict[str, str]] = None, uid: Optional[int] = None, secret: Optional[str] = None) -> Tuple[Optional[float], Optional[float], Optional[float]]:
    """
    Fetch số dư người dùng từ API ví (3games).
    Cập nhật các biến global: current_build, cumulative_profit, starting_balance.
    """
    global current_build, current_usdt, current_world, last_balance_ts
    global starting_balance, last_balance_val, cumulative_profit

    uid = uid or USER_ID
    secret = secret or SECRET_KEY
    payload = {"user_id": int(uid) if uid is not None else None, "source": "home"}

    attempt = 0
    while attempt <= retries:
        attempt += 1
        try:
            r = HTTP.post(
                WALLET_API_URL,
                json=payload,
                headers=balance_headers_for(uid, secret),
                timeout=timeout,
            )
            r.raise_for_status()
            j = r.json()

            build, world, usdt = _parse_balance_from_json(j)

            if build is not None:
                if last_balance_val is None:
                    starting_balance = build
                    last_balance_val = build
                else:
                    delta = float(build) - float(last_balance_val)
                    if abs(delta) > 0.000001:
                        cumulative_profit += delta
                        last_balance_val = build
                current_build = build
            if usdt is not None:
                current_usdt = usdt
            if world is not None:
                current_world = world

            last_balance_ts = time.time()
            return current_build, current_world, current_usdt

        except Exception as e:
            log_debug(f"wallet fetch attempt {attempt} error: {e}")
            time.sleep(min(0.6 * attempt, 2))

    return current_build, current_world, current_usdt

# -------------------- ADVANCED AVF RISK ASSESSMENT SYSTEM --------------------

def calculate_historical_kill_rate_factor(room_id: int) -> Tuple[float, List[str]]:
    """
    Tính toán yếu tố tỷ lệ tiêu diệt lịch sử với trọng số thời gian.
    Returns: (score, factors)
    """
    global room_stats, game_kill_history, round_index
    
    stats = room_stats.get(room_id, {})
    factors = []
    
    kill_count = float(stats.get("kills", 0))
    survive_count = float(stats.get("survives", 0))
    total_rounds = kill_count + survive_count
    
    if total_rounds == 0:
        return 50.0, ["Chưa có dữ liệu lịch sử"]
    
    # Tỷ lệ tiêu diệt cơ bản
    base_kill_rate = kill_count / total_rounds
    
    # Trọng số thời gian: các ván gần đây quan trọng hơn
    recent_kills = list(game_kill_history).count(room_id)
    total_recent_rounds = min(10, len(game_kill_history))
    
    if total_recent_rounds > 0:
        recent_kill_rate = recent_kills / total_recent_rounds
        # Kết hợp tỷ lệ cơ bản và tỷ lệ gần đây với trọng số
        weighted_kill_rate = 0.7 * base_kill_rate + 0.3 * recent_kill_rate
    else:
        weighted_kill_rate = base_kill_rate
    
    # Chuyển đổi thành điểm risk (0-100)
    risk_score = weighted_kill_rate * 100
    
    factors.append(f"Tỷ lệ chết lịch sử: {base_kill_rate:.1%}")
    if recent_kills > 0:
        factors.append(f"Bị giết {recent_kills} lần gần đây")
    
    return min(100.0, risk_score), factors

def calculate_current_popularity_factor(room_id: int) -> Tuple[float, List[str]]:
    """
    Tính toán yếu tố độ phổ biến hiện tại của phòng.
    Returns: (score, factors)
    """
    global room_state
    
    st = room_state.get(room_id, {})
    factors = []
    
    players = st.get("players", 0)
    bet = st.get("bet", 0)
    
    # Tính tổng số người chơi và tổng tiền cược toàn bộ thị trường
    all_players = sum(r.get("players", 0) for r in room_state.values())
    all_bet = sum(r.get("bet", 0) for r in room_state.values())
    
    if all_players == 0 or all_bet == 0:
        return 50.0, ["Chưa có dữ liệu thị trường"]
    
    # Tỷ lệ người chơi
    player_ratio = players / all_players
    player_risk = min(100.0, player_ratio * 150)  # Tối đa 150% để tránh quá cao
    
    # Tỷ lệ tiền cược
    bet_ratio = bet / all_bet
    bet_risk = min(100.0, bet_ratio * 150)
    
    # Kết hợp cả hai yếu tố
    popularity_risk = (player_risk + bet_risk) / 2
    
    factors.append(f"Chiếm {player_ratio:.1%} tổng người chơi")
    factors.append(f"Chiếm {bet_ratio:.1%} tổng tiền cược")
    
    if player_ratio > 0.25:
        factors.append("Cảnh báo: Quá đông người chơi")
    
    return popularity_risk, factors

def calculate_bpp_analysis_factor(room_id: int) -> Tuple[float, List[str]]:
    """
    Phân tích BPP (Bet Per Player) hiện tại so với lịch sử và thị trường.
    Returns: (score, factors)
    """
    global room_state, room_stats
    
    st = room_state.get(room_id, {})
    stats = room_stats.get(room_id, {})
    factors = []
    
    players = st.get("players", 0)
    bet = st.get("bet", 0)
    current_bpp = bet / players if players > 0 else 0
    
    # Tính BPP trung bình thị trường
    all_players = sum(r.get("players", 0) for r in room_state.values())
    all_bet = sum(r.get("bet", 0) for r in room_state.values())
    market_avg_bpp = all_bet / all_players if all_players > 0 else 0
    
    # Phân tích lịch sử BPP của phòng
    historical_bpp = stats.get("historical_bpp", deque())
    if len(historical_bpp) >= 5:
        avg_historical_bpp = sum(historical_bpp) / len(historical_bpp)
        bpp_deviation = abs(current_bpp - avg_historical_bpp) / max(1, avg_historical_bpp)
    else:
        avg_historical_bpp = current_bpp
        bpp_deviation = 0
    
    # Tính điểm risk dựa trên độ lệch
    if avg_historical_bpp > 0:
        deviation_risk = min(100.0, bpp_deviation * 100)
    else:
        deviation_risk = 50.0
    
    # So sánh với thị trường
    if market_avg_bpp > 0:
        market_ratio = current_bpp / market_avg_bpp
        if market_ratio > 2.0:
            market_risk = 80.0 + min(20.0, (market_ratio - 2.0) * 20)
        elif market_ratio < 0.5:
            market_risk = 60.0 + min(20.0, (0.5 - market_ratio) * 40)
        else:
            market_risk = 50.0
    else:
        market_risk = 50.0
    
    # Kết hợp các yếu tố BPP
    bpp_risk = (deviation_risk + market_risk) / 2
    
    factors.append(f"BPP hiện tại: {current_bpp:,.0f}")
    if len(historical_bpp) >= 5:
        factors.append(f"BPP trung bình: {avg_historical_bpp:,.0f}")
        factors.append(f"Độ lệch: {bpp_deviation:.1%}")
    
    if market_avg_bpp > 0:
        factors.append(f"BPP thị trường: {market_avg_bpp:,.0f}")
    
    return min(100.0, bpp_risk), factors

def calculate_cold_room_factor(room_id: int) -> Tuple[float, List[str]]:
    """
    Tính toán yếu tố 'phòng lạnh' - thời gian kể từ lần bị tiêu diệt cuối.
    Returns: (score, factors) - score thấp hơn = an toàn hơn
    """
    global room_stats, round_index, game_kill_history
    
    stats = room_stats.get(room_id, {})
    factors = []
    
    last_kill_round = stats.get("last_kill_round")
    current_round = round_index
    
    if last_kill_round is None:
        # Phòng chưa từng bị giết - rất an toàn
        cold_bonus = 20.0  # Giảm risk 20 điểm
        factors.append("Chưa từng bị giết")
    else:
        rounds_since_kill = current_round - last_kill_round
        # Tính bonus dựa trên số ván an toàn (giảm dần theo thời gian)
        cold_bonus = min(25.0, rounds_since_kill * 2.5)  # Tối đa giảm 25 điểm
        
        if rounds_since_kill >= 10:
            factors.append(f"An toàn {rounds_since_kill} ván")
        elif rounds_since_kill >= 5:
            factors.append(f"Đã sống {rounds_since_kill} ván")
        else:
            factors.append(f"Mới bị giết {rounds_since_kill} ván trước")
    
    # Risk score sau khi áp dụng cold bonus (risk thấp hơn)
    cold_risk = max(0.0, 50.0 - cold_bonus)  # Bắt đầu từ 50 và trừ đi bonus
    
    return cold_risk, factors

def calculate_pattern_analysis_factor(room_id: int) -> Tuple[float, List[str]]:
    """
    Phân tích mô hình tiêu diệt và chuỗi sự kiện.
    Returns: (score, factors)
    """
    global game_kill_pattern_tracker, game_kill_history
    factors = []
    
    kill_seq = list(game_kill_pattern_tracker.get("kill_seq", deque()))
    recent_kills = list(game_kill_history)
    
    pattern_risk = 50.0  # Mặc định
    
    # Phát hiện chuỗi lặp
    if len(kill_seq) >= 3:
        # Kiểm tra mô hình A-B-A
        if len(kill_seq) >= 3 and kill_seq[-3] == kill_seq[-1] and kill_seq[-3] != kill_seq[-2]:
            if room_id == kill_seq[-3]:
                pattern_risk = 80.0
                factors.append("Mô hình lặp A-B-A detected")
        
        # Kiểm tra mô hình tăng dần/giảm dần
        if len(kill_seq) >= 4:
            differences = [kill_seq[i+1] - kill_seq[i] for i in range(len(kill_seq)-1)]
            if all(diff > 0 for diff in differences[-3:]):
                if room_id > kill_seq[-1]:
                    pattern_risk = 70.0
                    factors.append("Xu hướng tăng dần")
            elif all(diff < 0 for diff in differences[-3:]):
                if room_id < kill_seq[-1]:
                    pattern_risk = 70.0
                    factors.append("Xu hướng giảm dần")
    
    # Tần suất xuất hiện trong lịch sử gần đây
    kill_frequency = recent_kills.count(room_id)
    if kill_frequency > 0:
        freq_risk = min(30.0, kill_frequency * 10)  # Mỗi lần giết gần đây +10 risk
        pattern_risk = min(100.0, pattern_risk + freq_risk)
        factors.append(f"Bị giết {kill_frequency} lần gần đây")
    
    return pattern_risk, factors

def calculate_market_state_factor(room_id: int) -> Tuple[float, List[str]]:
    """
    Phân tích trạng thái thị trường tổng thể.
    Returns: (score, factors)
    """
    global room_state
    factors = []
    
    all_players = sum(r.get("players", 0) for r in room_state.values())
    all_bet = sum(r.get("bet", 0) for r in room_state.values())
    
    if all_players == 0:
        return 50.0, ["Thị trường không hoạt động"]
    
    # Tính độ tập trung của thị trường
    player_concentrations = []
    bet_concentrations = []
    
    for r in ROOM_ORDER:
        st = room_state.get(r, {})
        player_conc = st.get("players", 0) / all_players
        bet_conc = st.get("bet", 0) / all_bet if all_bet > 0 else 0
        player_concentrations.append(player_conc)
        bet_concentrations.append(bet_conc)
    
    # Độ tập trung Herfindahl–Hirschman Index
    hhi_players = sum(conc * 10000 for conc in player_concentrations)  # Scale to 0-10000
    hhi_bets = sum(conc * 10000 for conc in bet_concentrations)
    
    avg_hhi = (hhi_players + hhi_bets) / 2
    
    # Phân loại thị trường dựa trên HHI
    if avg_hhi > 2500:  # Rất tập trung
        market_state_risk = 70.0
        market_state = "Rất tập trung"
    elif avg_hhi > 1800:  # Tập trung vừa
        market_state_risk = 60.0
        market_state = "Tập trung"
    elif avg_hhi > 1000:  # Cạnh tranh vừa
        market_state_risk = 50.0
        market_state = "Cạnh tranh"
    else:  # Phân tán
        market_state_risk = 40.0
        market_state = "Phân tán"
    
    factors.append(f"Thị trường: {market_state} (HHI: {avg_hhi:.0f})")
    
    # Điều chỉnh risk dựa trên vị trí phòng trong thị trường
    st = room_state.get(room_id, {})
    room_player_share = st.get("players", 0) / all_players
    room_bet_share = st.get("bet", 0) / all_bet if all_bet > 0 else 0
    
    if room_player_share > 0.15 or room_bet_share > 0.15:
        # Phòng chiếm thị phần lớn -> risk cao hơn trong thị trường tập trung
        if avg_hhi > 1800:
            market_state_risk += 15.0
            factors.append("Cảnh báo: Phòng chiếm thị phần lớn")
    
    return min(100.0, market_state_risk), factors

# ==================== ADVANCED AVF RISK MODELS ====================

def calculate_ema_avf_risk(room_id: int) -> Tuple[float, List[str]]:
    """
    EMA-AVF (Exponential Moving Average – Anti Volatility Filter)
    Sử dụng EMA để lọc nhiễu và xác định xu hướng rủi ro thực sự.
    """
    global room_risk_ema, risk_pattern_memory
    
    factors = []
    risk_memory = list(risk_pattern_memory.get(room_id, deque()))
    
    if len(risk_memory) < 3:
        return 50.0, ["Không đủ dữ liệu EMA-AVF"]
    
    # Tính EMA ngắn hạn (3 periods) và dài hạn (8 periods)
    short_ema = risk_memory[-1]  # Latest EMA value
    long_ema = statistics.mean(risk_memory[-8:]) if len(risk_memory) >= 8 else statistics.mean(risk_memory)
    
    # Độ chênh lệch EMA
    ema_diff = abs(short_ema - long_ema)
    
    # Xác định xu hướng
    if short_ema > long_ema + 5.0:
        trend_strength = min(1.0, (short_ema - long_ema) / 20.0)
        risk_score = 60.0 + (trend_strength * 40.0)
        factors.append(f"EMA-AVF: Xu hướng tăng mạnh (+{ema_diff:.1f})")
    elif short_ema < long_ema - 5.0:
        trend_strength = min(1.0, (long_ema - short_ema) / 20.0)
        risk_score = 40.0 - (trend_strength * 20.0)
        factors.append(f"EMA-AVF: Xu hướng giảm mạnh (-{ema_diff:.1f})")
    else:
        risk_score = 50.0
        factors.append(f"EMA-AVF: Ổn định (±{ema_diff:.1f})")
    
    # Thêm độ biến động vào risk
    volatility = statistics.stdev(risk_memory[-5:]) if len(risk_memory) >= 5 else 0
    if volatility > 15.0:
        risk_score += min(20.0, volatility - 15.0)
        factors.append(f"Biến động cao: {volatility:.1f}")
    
    return max(0.0, min(100.0, risk_score)), factors

def calculate_std_avf_risk(room_id: int) -> Tuple[float, List[str]]:
    """
    STD-AVF (Standard Deviation Anti-Volatility Risk)
    Đánh giá rủi ro dựa trên độ lệch chuẩn của lịch sử risk scores.
    """
    global risk_pattern_memory
    
    factors = []
    risk_memory = list(risk_pattern_memory.get(room_id, deque()))
    
    if len(risk_memory) < 5:
        return 50.0, ["Không đủ dữ liệu STD-AVF"]
    
    # Tính độ lệch chuẩn của risk scores gần đây
    recent_risks = risk_memory[-10:] if len(risk_memory) >= 10 else risk_memory
    if len(recent_risks) < 2:
        return 50.0, ["Không đủ dữ liệu STD-AVF"]
    
    std_dev = statistics.stdev(recent_risks)
    mean_risk = statistics.mean(recent_risks)
    
    # Độ lệch chuẩn cao -> rủi ro cao (biến động lớn)
    if std_dev > 20.0:
        risk_score = min(100.0, mean_risk + (std_dev - 20.0))
        factors.append(f"STD-AVF: Biến động cực cao (σ={std_dev:.1f})")
    elif std_dev > 10.0:
        risk_score = min(100.0, mean_risk + (std_dev - 10.0) * 0.5)
        factors.append(f"STD-AVF: Biến động cao (σ={std_dev:.1f})")
    elif std_dev > 5.0:
        risk_score = mean_risk
        factors.append(f"STD-AVF: Biến động vừa (σ={std_dev:.1f})")
    else:
        risk_score = max(0.0, mean_risk - (5.0 - std_dev) * 0.5)
        factors.append(f"STD-AVF: Ổn định (σ={std_dev:.1f})")
    
    return max(0.0, min(100.0, risk_score)), factors

def calculate_ent_avf_risk(room_id: int) -> Tuple[float, List[str]]:
    """
    ENT-AVF (Normalized Entropy Risk)
    Đo lường độ bất định và hỗn loạn trong phân phối risk scores.
    """
    global risk_pattern_memory
    
    factors = []
    risk_memory = list(risk_pattern_memory.get(room_id, deque()))
    
    if len(risk_memory) < 5:
        return 50.0, ["Không đủ dữ liệu ENT-AVF"]
    
    # Phân nhóm risk scores thành 5 mức
    risk_bins = [0] * 5
    bin_size = 100.0 / 5
    
    for risk in risk_memory:
        bin_index = min(4, int(risk / bin_size))
        risk_bins[bin_index] += 1
    
    # Tính xác suất cho mỗi nhóm
    total = len(risk_memory)
    probabilities = [count / total for count in risk_bins]
    
    # Tính entropy
    entropy = 0.0
    for p in probabilities:
        if p > 0:
            entropy -= p * math.log2(p)
    
    # Chuẩn hóa entropy (tối đa là log2(5) ≈ 2.32)
    max_entropy = math.log2(5)
    normalized_entropy = entropy / max_entropy
    
    # Entropy cao -> phân phối đồng đều -> khó dự đoán -> rủi ro cao
    risk_score = normalized_entropy * 100.0
    
    if normalized_entropy > 0.8:
        factors.append(f"ENT-AVF: Độ bất định rất cao (H={entropy:.2f})")
    elif normalized_entropy > 0.6:
        factors.append(f"ENT-AVF: Độ bất định cao (H={entropy:.2f})")
    elif normalized_entropy > 0.4:
        factors.append(f"ENT-AVF: Độ bất định trung bình (H={entropy:.2f})")
    else:
        factors.append(f"ENT-AVF: Dễ dự đoán (H={entropy:.2f})")
    
    return risk_score, factors

def calculate_bayes_avf_risk(room_id: int) -> Tuple[float, List[str]]:
    """
    BAYES-AVF (Bayesian Posterior Risk)
    Sử dụng Bayesian updating để kết hợp prior knowledge với new evidence.
    """
    global room_stats, game_kill_history
    
    stats = room_stats.get(room_id, {})
    factors = []
    
    kill_count = stats.get("kills", 0)
    survive_count = stats.get("survives", 0)
    
    # Prior distribution (Beta distribution parameters)
    # Giả định prior: 2 kills, 8 survives ~ 20% kill rate
    alpha_prior = 2.0
    beta_prior = 8.0
    
    # Update với dữ liệu quan sát được
    alpha_posterior = alpha_prior + kill_count
    beta_posterior = beta_prior + survive_count
    
    # Tính posterior mean
    posterior_mean = alpha_posterior / (alpha_posterior + beta_posterior)
    
    # Tính posterior variance (độ không chắc chắn)
    total_posterior = alpha_posterior + beta_posterior
    posterior_variance = (alpha_posterior * beta_posterior) / (total_posterior ** 2 * (total_posterior + 1))
    
    # Risk score dựa trên posterior mean và variance
    base_risk = posterior_mean * 100.0
    uncertainty_penalty = math.sqrt(posterior_variance * 10000.0) * 2.0
    
    risk_score = base_risk + uncertainty_penalty
    
    factors.append(f"BAYES-AVF: Xác suất posterior {posterior_mean:.1%}")
    if uncertainty_penalty > 10.0:
        factors.append(f"Độ không chắc chắn cao: {uncertainty_penalty:.1f}")
    
    return min(100.0, risk_score), factors

def calculate_ensemble_avf_risk(room_id: int) -> Tuple[float, List[str]]:
    """
    ENSEMBLE-AVF (Multi-Model Consensus Risk)
    Kết hợp nhiều mô hình risk assessment để tạo consensus.
    """
    factors = []
    
    # Lấy risk scores từ các mô hình cơ bản
    historical_risk, _ = calculate_historical_kill_rate_factor(room_id)
    popularity_risk, _ = calculate_current_popularity_factor(room_id)
    bpp_risk, _ = calculate_bpp_analysis_factor(room_id)
    market_risk, _ = calculate_market_state_factor(room_id)
    
    # Lấy risk scores từ các mô hình AVF
    ema_risk, _ = calculate_ema_avf_risk(room_id)
    std_risk, _ = calculate_std_avf_risk(room_id)
    ent_risk, _ = calculate_ent_avf_risk(room_id)
    bayes_risk, _ = calculate_bayes_avf_risk(room_id)
    
    # Tạo ensemble của tất cả các mô hình
    all_risks = [
        historical_risk, popularity_risk, bpp_risk, market_risk,
        ema_risk, std_risk, ent_risk, bayes_risk
    ]
    
    # Tính consensus score (trung bình có trọng số)
    weights = [0.15, 0.10, 0.10, 0.05, 0.15, 0.15, 0.15, 0.15]
    weighted_sum = sum(risk * weight for risk, weight in zip(all_risks, weights))
    total_weight = sum(weights)
    
    ensemble_risk = weighted_sum / total_weight
    
    # Đánh giá độ đồng thuận
    risk_std = statistics.stdev(all_risks) if len(all_risks) > 1 else 0
    if risk_std < 10.0:
        factors.append(f"ENSEMBLE-AVF: Đồng thuận cao (σ={risk_std:.1f})")
    elif risk_std < 20.0:
        factors.append(f"ENSEMBLE-AVF: Đồng thuận trung bình (σ={risk_std:.1f})")
        # Điều chỉnh risk nếu có sự không đồng thuận
        ensemble_risk += (risk_std - 10.0) * 0.5
    else:
        factors.append(f"ENSEMBLE-AVF: Không đồng thuận (σ={risk_std:.1f})")
        # Tăng risk khi các mô hình cho kết quả khác nhau nhiều
        ensemble_risk += (risk_std - 20.0) * 0.3
    
    return max(0.0, min(100.0, ensemble_risk)), factors

def calculate_trend_avf_risk(room_id: int) -> Tuple[float, List[str]]:
    """
    TREND-AVF (EMA Short-Long Trend Divergence)
    Phát hiện divergence giữa xu hướng ngắn hạn và dài hạn.
    """
    global risk_pattern_memory
    
    factors = []
    risk_memory = list(risk_pattern_memory.get(room_id, deque()))
    
    if len(risk_memory) < 8:
        return 50.0, ["Không đủ dữ liệu TREND-AVF"]
    
    # EMA ngắn hạn (3 periods)
    short_ema = risk_memory[-1]  # Latest EMA
    short_trend = risk_memory[-1] - risk_memory[-3] if len(risk_memory) >= 3 else 0
    
    # EMA dài hạn (8 periods)  
    long_ema = statistics.mean(risk_memory[-8:])
    long_trend = risk_memory[-1] - risk_memory[-8] if len(risk_memory) >= 8 else 0
    
    # Phát hiện divergence
    divergence_risk = 0.0
    
    if short_trend > 5.0 and long_trend < -2.0:
        # Bullish divergence: ngắn hạn tăng, dài hạn giảm
        divergence_risk = 30.0
        factors.append(f"TREND-AVF: Bullish divergence (+{short_trend:.1f}/-{abs(long_trend):.1f})")
    elif short_trend < -5.0 and long_trend > 2.0:
        # Bearish divergence: ngắn hạn giảm, dài hạn tăng
        divergence_risk = 70.0
        factors.append(f"TREND-AVF: Bearish divergence (-{abs(short_trend):.1f}/+{long_trend:.1f})")
    elif abs(short_trend - long_trend) > 10.0:
        # Significant trend divergence
        divergence_risk = 60.0
        factors.append(f"TREND-AVF: Trend divergence ({short_trend:.1f} vs {long_trend:.1f})")
    else:
        factors.append(f"TREND-AVF: Trend đồng nhất ({short_trend:.1f} vs {long_trend:.1f})")
    
    # Kết hợp với current risk level
    current_risk = risk_memory[-1]
    trend_risk = (current_risk + divergence_risk) / 2
    
    return max(0.0, min(100.0, trend_risk)), factors

def calculate_mc_avf_risk(room_id: int) -> Tuple[float, List[str]]:
    """
    MC-AVF (Monte-Carlo Convergence Risk)
    Mô phỏng Monte-Carlo để đánh giá xác suất rủi ro cực đoan.
    """
    global risk_pattern_memory
    
    factors = []
    risk_memory = list(risk_pattern_memory.get(room_id, deque()))
    
    if len(risk_memory) < 10:
        return 50.0, ["Không đủ dữ liệu MC-AVF"]
    
    # Thống kê mô phỏng
    recent_risks = risk_memory[-20:] if len(risk_memory) >= 20 else risk_memory
    mean_risk = statistics.mean(recent_risks)
    std_risk = statistics.stdev(recent_risks) if len(recent_risks) > 1 else 0
    
    # Mô phỏng Monte-Carlo với 1000 trials
    extreme_count = 0
    total_trials = 1000
    
    for _ in range(total_trials):
        # Tạo risk score ngẫu nhiên dựa trên phân phối chuẩn
        simulated_risk = random.gauss(mean_risk, std_risk)
        
        # Đếm số lần vượt ngưỡng risk cao
        if simulated_risk > 70.0:
            extreme_count += 1
    
    # Xác suất rủi ro cực đoan
    extreme_probability = extreme_count / total_trials
    
    # Risk score dựa trên xác suất rủi ro cực đoan
    mc_risk = extreme_probability * 100.0
    
    if extreme_probability > 0.3:
        factors.append(f"MC-AVF: Rủi ro cực đoan cao ({extreme_probability:.1%})")
    elif extreme_probability > 0.15:
        factors.append(f"MC-AVF: Rủi ro cực đoan trung bình ({extreme_probability:.1%})")
    else:
        factors.append(f"MC-AVF: Rủi ro cực đoan thấp ({extreme_probability:.1%})")
    
    return max(0.0, min(100.0, mc_risk)), factors

def calculate_advanced_room_risk_level(room_id: int) -> Tuple[float, List[str]]:
    """
    Tính toán mức độ rủi ro nâng cao cho một phòng cụ thể.
    Sử dụng tất cả các mô hình AVF kết hợp với EMA.
    Returns: (raw_risk_score, risk_factors)
    """
    global RISK_WEIGHTS
    
    all_factors = []
    weighted_score = 0.0
    
    # 1. Historical Kill Rate (15%)
    kill_rate_score, kill_factors = calculate_historical_kill_rate_factor(room_id)
    weighted_score += kill_rate_score * RISK_WEIGHTS["historical_kill_rate"]
    all_factors.extend(kill_factors)
    
    # 2. Current Popularity (10%)
    popularity_score, popularity_factors = calculate_current_popularity_factor(room_id)
    weighted_score += popularity_score * RISK_WEIGHTS["current_popularity"]
    all_factors.extend(popularity_factors)
    
    # 3. BPP Analysis (10%)
    bpp_score, bpp_factors = calculate_bpp_analysis_factor(room_id)
    weighted_score += bpp_score * RISK_WEIGHTS["bpp_analysis"]
    all_factors.extend(bpp_factors)
    
    # 4. Cold Room Bonus (5%) - Lưu ý: score này đã được tính để risk thấp hơn
    cold_score, cold_factors = calculate_cold_room_factor(room_id)
    weighted_score += cold_score * RISK_WEIGHTS["cold_room_bonus"]
    all_factors.extend(cold_factors)
    
    # 5. Pattern Analysis (5%)
    pattern_score, pattern_factors = calculate_pattern_analysis_factor(room_id)
    weighted_score += pattern_score * RISK_WEIGHTS["pattern_analysis"]
    all_factors.extend(pattern_factors)
    
    # 6. Market State (5%)
    market_score, market_factors = calculate_market_state_factor(room_id)
    weighted_score += market_score * RISK_WEIGHTS["market_state"]
    all_factors.extend(market_factors)
    
    # ========== ADVANCED AVF MODELS (40%) ==========
    
    # 7. EMA-AVF Risk (8%)
    ema_avf_score, ema_avf_factors = calculate_ema_avf_risk(room_id)
    weighted_score += ema_avf_score * RISK_WEIGHTS["ema_avf"]
    all_factors.extend(ema_avf_factors)
    
    # 8. STD-AVF Risk (6%)
    std_avf_score, std_avf_factors = calculate_std_avf_risk(room_id)
    weighted_score += std_avf_score * RISK_WEIGHTS["std_avf"]
    all_factors.extend(std_avf_factors)
    
    # 9. ENT-AVF Risk (5%)
    ent_avf_score, ent_avf_factors = calculate_ent_avf_risk(room_id)
    weighted_score += ent_avf_score * RISK_WEIGHTS["ent_avf"]
    all_factors.extend(ent_avf_factors)
    
    # 10. BAYES-AVF Risk (7%)
    bayes_avf_score, bayes_avf_factors = calculate_bayes_avf_risk(room_id)
    weighted_score += bayes_avf_score * RISK_WEIGHTS["bayes_avf"]
    all_factors.extend(bayes_avf_factors)
    
    # 11. ENSEMBLE-AVF Risk (6%)
    ensemble_avf_score, ensemble_avf_factors = calculate_ensemble_avf_risk(room_id)
    weighted_score += ensemble_avf_score * RISK_WEIGHTS["ensemble_avf"]
    all_factors.extend(ensemble_avf_factors)
    
    # 12. TREND-AVF Risk (4%)
    trend_avf_score, trend_avf_factors = calculate_trend_avf_risk(room_id)
    weighted_score += trend_avf_score * RISK_WEIGHTS["trend_avf"]
    all_factors.extend(trend_avf_factors)
    
    # 13. MC-AVF Risk (4%)
    mc_avf_score, mc_avf_factors = calculate_mc_avf_risk(room_id)
    weighted_score += mc_avf_score * RISK_WEIGHTS["mc_avf"]
    all_factors.extend(mc_avf_factors)
    
    # Thêm yếu tố dao động tự nhiên để tránh giá trị tĩnh
    time_factor = time.time() / 60.0  # Dao động theo phút
    oscillation = oscillating_factor(1.0, time_factor, frequency=0.1)
    final_raw_score = weighted_score * oscillation
    
    # Đảm bảo trong khoảng MIN_RISK đến MAX_RISK
    final_raw_score = max(MIN_RISK, min(MAX_RISK, final_raw_score))
    
    return final_raw_score, all_factors

def update_room_risk_with_ema(room_id: int) -> Dict[str, Any]:
    """
    Cập nhật đánh giá rủi ro cho một phòng sử dụng EMA.
    Returns: risk_assessment dict
    """
    global room_risk_ema, room_risk_raw, room_risk_assessment, RISK_EMA_ALPHA
    global risk_pattern_memory, risk_oscillation_tracker
    
    # Tính toán raw risk score
    raw_risk, risk_factors = calculate_advanced_room_risk_level(room_id)
    
    # Lấy EMA cũ
    old_ema = room_risk_ema[room_id]
    
    # Áp dụng EMA
    new_ema = exponential_moving_average(raw_risk, old_ema, RISK_EMA_ALPHA)
    
    # Cập nhật giá trị
    room_risk_raw[room_id] = raw_risk
    room_risk_ema[room_id] = new_ema
    
    # Cập nhật bộ nhớ pattern
    risk_pattern_memory[room_id].append(new_ema)
    
    # Phân tích xu hướng
    trend = "stable"
    if len(risk_pattern_memory[room_id]) >= 2:
        current = risk_pattern_memory[room_id][-1]
        previous = risk_pattern_memory[room_id][-2]
        
        if current > previous + 2.0:
            trend = "rising"
        elif current < previous - 2.0:
            trend = "falling"
    
    # Xác định mức độ rủi ro và màu sắc
    risk_level = RISK_LEVEL_SAFE
    risk_color = PENDING_COLOR
    risk_icon = "🟡"
    
    ema_value = new_ema
    
    if ema_value >= 60:
        risk_level = RISK_LEVEL_CRITICAL
        risk_color = FAILURE_COLOR
        risk_icon = "🔴"
    elif ema_value >= 49:
        risk_level = RISK_LEVEL_HIGH
        risk_color = FAILURE_COLOR
        risk_icon = "🟠"
    elif ema_value >= 37:
        risk_level = RISK_LEVEL_MEDIUM
        risk_color = WARNING_COLOR
        risk_icon = "🟡"
    elif ema_value >= 25:
        risk_level = RISK_LEVEL_LOW
        risk_color = PENDING_COLOR
        risk_icon = "🔵"
    else:
        risk_level = RISK_LEVEL_SAFE
        risk_color = SUCCESS_COLOR
        risk_icon = "🟢"
    
    # Tạo assessment
    assessment = {
        "risk_level": risk_level,
        "risk_score": ema_value,  # Sử dụng EMA value
        "risk_raw": raw_risk,     # Raw value for reference
        "risk_color": risk_color,
        "risk_icon": risk_icon,
        "risk_factors": risk_factors,
        "risk_trend": trend,
        "last_update": time.time(),
        "update_count": room_risk_assessment[room_id].get("update_count", 0) + 1
    }
    
    room_risk_assessment[room_id] = assessment
    return assessment

def update_all_room_risks() -> None:
    """
    Cập nhật đánh giá rủi ro cho tất cả các phòng.
    Sử dụng hệ thống EMA nâng cao với AVF models.
    """
    global room_risk_assessment
    
    for room_id in ROOM_ORDER:
        update_room_risk_with_ema(room_id)

def get_risk_description(risk_level: int) -> str:
    """
    Trả về mô tả văn bản cho mức độ rủi ro.
    """
    descriptions = {
        RISK_LEVEL_SAFE: "AN TOÀN",
        RISK_LEVEL_LOW: "RỦI RO THẤP", 
        RISK_LEVEL_MEDIUM: "RỦI RO TRUNG BÌNH",
        RISK_LEVEL_HIGH: "RỦI RO CAO",
        RISK_LEVEL_CRITICAL: "RỦI RO CỰC CAO"
    }
    return descriptions.get(risk_level, "KHÔNG XÁC ĐỊNH")

def get_risk_trend_icon(trend: str) -> str:
    """
    Trả về icon cho xu hướng risk.
    """
    icons = {
        "rising": "📈",
        "falling": "📉", 
        "stable": "➡️"
    }
    return icons.get(trend, "➡️")

# -------------------- SUPERIOR DEVIL V4 SELECTION --------------------
def _room_features(rid: int) -> Dict[str, float]:
    """
    (V4 - Enhanced with Advanced AVF Risk Assessment)
    Tính toán các đặc trưng (features) chi tiết của một phòng để đưa vào mô hình dự đoán.
    """
    global game_kill_history, round_index, room_state, room_stats, last_killed_room, game_kill_pattern_tracker
    global room_risk_assessment
    
    st = room_state.get(rid, {})
    stats = room_stats.get(rid, {})
    
    # 1. Dữ liệu thời gian thực (Real-time Data)
    players = float(st.get("players", 0))
    bet = float(st.get("bet", 0))
    bet_per_player = (bet / players) if players > 0 else 0.0

    # 2. Dữ liệu lịch sử (Historical Stats)
    kill_count = float(stats.get("kills", 0))
    survive_count = float(stats.get("survives", 0))
    
    total_rounds = kill_count + survive_count
    kill_rate = (kill_count + 1.0) / (total_rounds + 2.0) if total_rounds > 0 else 0.5
    survive_score = 1.0 - kill_rate

    # 3. Phân tích trạng thái thị trường (Market State Analysis)
    all_players = sum(r.get("players", 0) for r in room_state.values())
    all_bet = sum(r.get("bet", 0) for r in room_state.values())
    
    players_norm = players / max(1.0, all_players)
    bet_norm = bet / max(1.0, all_bet)

    contrarian_score = 1.0 - (players_norm + bet_norm) / 2.0 

    # 4. Phân tích bẫy (Trap Analysis)
    recent_pen = 0.0
    for i, rec in enumerate(reversed(list(bet_history))):
        if i >= 10: break
        if rec.get("room") == rid and rec.get("result") == "Thua":
            recent_pen += 0.15 * (1.0 / (i + 1))
    
    last_pen = 0.0
    if last_killed_room == rid and SELECTION_CONFIG.get("avoid_last_kill", True):
        last_pen = 0.45 

    safety_score = 0.5
    if total_rounds > 0:
        safety_score = 1.0 - (kill_count / max(1, total_rounds / 8))

    # 5. DEVIL Features với Advanced AVF Risk Assessment Integration
    last_kill_round = stats.get("last_kill_round")
    cold_room_score = 0.0
    min_rounds_safe = 10.0
    if last_kill_round is None:
        cold_room_score = 1.0
    else:
        delta = round_index - last_kill_round
        cold_room_score = min(1.0, delta / min_rounds_safe)

    recent_kills = game_kill_history.count(rid)
    freq_penalty = min(1.0, recent_kills / SELECTION_CONFIG.get("max_recent_kills", 3.0))

    bpp_score = 0.0
    min_h = SELECTION_CONFIG.get("bpp_trap_low", 500.0)
    max_h = SELECTION_CONFIG.get("bpp_trap_high", 4000.0)
    
    if bet_per_player < min_h:
        bpp_score = max(0.0, bet_per_player / min_h)
    elif bet_per_player > max_h:
        bpp_score = max(0.0, 1.0 - (bet_per_player - max_h) / max_h) 
    else:
        bpp_score = 1.0
        
    historical_bpp_deq = stats.get("historical_bpp")
    bpp_deviation_penalty = 0.0
    if historical_bpp_deq and len(historical_bpp_deq) >= 5:
        avg_bpp = sum(historical_bpp_deq) / len(historical_bpp_deq)
        if avg_bpp > 100 and bet_per_player > avg_bpp * 1.5:
             bpp_deviation_penalty = min(1.0, (bet_per_player - avg_bpp * 1.5) / avg_bpp)
        elif avg_bpp > 100 and bet_per_player < avg_bpp * 0.5:
             bpp_deviation_penalty = min(1.0, (avg_bpp * 0.5 - bet_per_player) / avg_bpp)
             
    pattern_penalty = 0.0
    kill_seq = game_kill_pattern_tracker.get("kill_seq", deque())
    
    if len(kill_seq) >= 3:
        if rid == kill_seq[-3] and rid != kill_seq[-2]:
             pattern_penalty = max(pattern_penalty, 0.6)
        
        if len(kill_seq) == 5 and all(r == rid for r in kill_seq):
             pattern_penalty = max(pattern_penalty, 0.9)

    # 6. Advanced AVF Risk Assessment Integration
    risk_data = room_risk_assessment.get(rid, {})
    risk_score = risk_data.get("risk_score", 50.0)
    risk_raw = risk_data.get("risk_raw", 50.0)
    
    # Sử dụng cả EMA và raw risk score từ AVF models
    risk_adjustment = (50.0 - risk_score) / 100.0  # Chuyển đổi risk score thành adjustment
    avf_confidence = 1.0 - (abs(risk_score - risk_raw) / 100.0)  # Độ tin cậy của AVF models

    avg_bpp_all = all_bet / max(1.0, all_players)
    bpp_relative_score = 1.0 - abs(bet_per_player - avg_bpp_all) / max(1.0, avg_bpp_all * 2)
        
    return {
        # Real-time & Normalized
        "players": players, "bet": bet, "bet_per_player": bet_per_player,
        "players_norm": players_norm, "bet_norm": bet_norm,
        "contrarian_score": contrarian_score,
        
        # Historical & Rates
        "kill_rate": kill_rate, "survive_score": survive_score,
        "safety_score": safety_score,
        
        # Penalties & Bonuses
        "recent_pen": recent_pen, "last_pen": last_pen,
        "cold_room_score": cold_room_score,
        "freq_penalty": freq_penalty,
        
        # Trap Analysis (SUPERIOR DEVIL)
        "bpp_score": bpp_score,
        "bpp_deviation_penalty": bpp_deviation_penalty,
        "pattern_penalty": pattern_penalty,
        "bpp_relative_score": bpp_relative_score,
        
        # Advanced AVF Risk Assessment Integration
        "risk_adjustment": risk_adjustment,
        "avf_confidence": avf_confidence,
        "risk_score_ema": risk_score,
        "risk_score_raw": risk_raw,
    }

def choose_room_devilmode() -> Tuple[int, str]:
    """
    SUPERIOR DEVIL MODE (v4.0) - SÓNG THẦN (TSUNAMI)
    Enhanced with Advanced AVF Risk Assessment
    """
    global game_kill_history, round_index, room_state, room_stats, last_killed_room
    
    log_debug("--- SUPERIOR DEVIL V4 PRE-COMPUTATION ---")
    features = {}
    
    # 1. Tính toán trạng thái thị trường chung
    all_players = sum(r.get("players", 0) for r in room_state.values())
    all_bet = sum(r.get("bet", 0) for r in room_state.values())
    avg_players = all_players / max(1, len(ROOM_ORDER))
    avg_bet = all_bet / max(1, len(ROOM_ORDER))
    avg_bpp_all = all_bet / max(1, all_players)

    # 2. Lấy Xếp hạng (Rank)
    player_ranks_sorted = sorted(ROOM_ORDER, key=lambda r: room_state[r].get("players", 0), reverse=True)
    bet_ranks_sorted = sorted(ROOM_ORDER, key=lambda r: room_state[r].get("bet", 0), reverse=True)
    
    # 3. Lấy Thống kê Vùng (Zone Stats)
    recent_10_kills = list(game_kill_history)[-10:]
    low_zone_kills = sum(1 for k in recent_10_kills if k in [1, 2, 3, 4])
    high_zone_kills = sum(1 for k in recent_10_kills if k in [5, 6, 7, 8])

    # 4. V4 - PHÂN TÍCH TRẠNG THÁI THỊ TRƯỜNG VỚI AVF
    market_state = "STABLE"
    max_players_in_room = 0
    if all_players > 0:
        max_players_in_room = max(r.get("players", 0) for r in room_state.values())
        player_concentration = max_players_in_room / all_players
        
        # Sử dụng AVF risk assessment để xác định trạng thái thị trường
        avg_market_risk = sum(room_risk_assessment[r].get("risk_score", 50.0) for r in ROOM_ORDER) / len(ROOM_ORDER)
        
        if player_concentration > 0.35 and avg_market_risk > 60.0:
            market_state = "CONCENTRATED_HIGH_RISK"
        elif player_concentration > 0.35:
            market_state = "CONCENTRATED"
        elif player_concentration < 0.2 and avg_bpp_all < 1000 and avg_market_risk < 40.0:
            market_state = "FEARFUL_LOW_RISK"
        elif player_concentration < 0.2 and avg_bpp_all < 1000:
            market_state = "FEARFUL"
        elif avg_market_risk > 65.0:
            market_state = "HIGH_RISK"
        elif avg_market_risk < 35.0:
            market_state = "LOW_RISK"
            
    log_debug(f"V4 Market State: {market_state} (Conc: {player_concentration:.2f}, Avg Risk: {avg_market_risk:.1f})")

    # 5. Xây dựng bộ đặc trưng (features) cho mỗi phòng với AVF integration
    for r in ROOM_ORDER:
        f = _room_features(r)

        # --- Thêm Đặc trưng V3 ---
        f['player_rank'] = player_ranks_sorted.index(r) + 1
        f['bet_rank'] = bet_ranks_sorted.index(r) + 1
        
        # V3 - Bẫy Cá Voi (Whale Trap)
        whale_bpp_threshold = max(3000.0, avg_bpp_all * 5.0)
        f['whale_trap_score'] = 0.0
        if 0 < f['players'] <= 3 and f['bet_per_player'] > whale_bpp_threshold:
            f['whale_trap_score'] = 1.0
        
        # V3 - Bẫy Chim Mồi (Decoy Trap)
        f['decoy_trap_score'] = 1.0 if f['player_rank'] in [2, 3] else 0.0
        
        # V3 - Phạt Vùng Nóng (Zone Penalty)
        f['zone_penalty'] = 0.0
        my_zone = 'low' if r <= 4 else 'high'
        if my_zone == 'low' and low_zone_kills > high_zone_kills:
            f['zone_penalty'] = min(1.0, (low_zone_kills - high_zone_kills) / 5.0)
        elif my_zone == 'high' and high_zone_kills > low_zone_kills:
            f['zone_penalty'] = min(1.0, (high_zone_kills - low_zone_kills) / 5.0)

        # V4 - AVF Confidence Bonus
        f['avf_confidence_bonus'] = f['avf_confidence'] * 0.3

        features[r] = f

    # --- PHASE 2: SUPERIOR TITANIUM FILTERING (V3) với AVF Enhancement ---
    filtered_cand = []
    
    for r in ROOM_ORDER:
        f = features[r]
        
        # F1: Né phòng vừa bị giết
        if SELECTION_CONFIG.get("avoid_last_kill", True) and last_killed_room == r:
            log_debug(f"Filter R{r}: Last killed (F1).")
            continue
        
        # F2: Tỷ lệ sống tối thiểu
        if f["survive_score"] < SELECTION_CONFIG.get("min_survive_rate", 0.55):
            log_debug(f"Filter R{r}: Low survive rate ({f['survive_score']:.2f}) (F2).")
            continue
        
        # F3: Bẫy quá đông/cược cao
        if (f["players"] > avg_players * 1.8) and (f["bet"] > avg_bet * 1.8):
            log_debug(f"Filter R{r}: Overcrowded/High bet (Dynamic Trap F3).")
            continue

        # F4: Tần suất bị giết gần đây
        if f["freq_penalty"] > 0.8:
            log_debug(f"Filter R{r}: High recent kill freq ({f['freq_penalty']:.2f}) (F4).")
            continue
            
        # F5: Bẫy BPP
        if f["bpp_score"] < 0.3: 
            log_debug(f"Filter R{r}: Extreme BPP score ({f['bpp_score']:.2f}) (F5).")
            continue

        # F6: Bẫy BPP Lệch
        if f["bpp_deviation_penalty"] > 0.5: 
            log_debug(f"Filter R{r}: High BPP Deviation Penalty ({f['bpp_deviation_penalty']:.2f}) (F6).")
            continue
            
        # F7: Bẫy Mô hình
        if f["pattern_penalty"] > 0.5: 
            log_debug(f"Filter R{r}: High Pattern Penalty ({f['pattern_penalty']:.2f}) (F7).")
            continue

        # F8: Lọc Bẫy Cá Voi
        if f['whale_trap_score'] > 0.5:
            log_debug(f"Filter R{r}: Whale Trap detected (F8).")
            continue
        
        # F9: Lọc Vùng Cực Nóng
        if f['zone_penalty'] > 0.8:
            log_debug(f"Filter R{r}: Extreme Hot Zone Penalty ({f['zone_penalty']:.2f}) (F9).")
            continue

        # F10: AVF Critical Risk Filter
        if f['risk_score_ema'] > 80.0 and f['avf_confidence'] > 0.7:
            log_debug(f"Filter R{r}: AVF Critical Risk ({f['risk_score_ema']:.1f}) (F10).")
            continue

        filtered_cand.append(r)

    # Fallback: Nếu tất cả đều bị lọc
    if not filtered_cand:
        log_debug("All rooms filtered. Fallback to lowest AVF risk (excl. last kill).")
        fallback_scores = {r: features[r]["risk_score_ema"] for r in ROOM_ORDER if r != last_killed_room}
        if not fallback_scores:
             fallback_scores = {r: features[r]["risk_score_ema"] for r in ROOM_ORDER}
             
        best_room = min(fallback_scores.items(), key=lambda x: x[1])[0]
        return best_room, "SUPERIOR_DEVIL_V4_AVF_FALLBACK"

    # --- PHASE 3: V4 - Adaptive Scoring với Advanced AVF Integration ---
    weights = {
        "safety_contrarian": 1.5, "safety_bpp_health": 1.2, "safety_cold_room": 1.0,
        "safety_survive_hist": 0.5, "safety_bpp_relative": 0.3, "safety_risk_adjustment": 1.0,
        "safety_avf_confidence": 0.8,
        "trap_decoy": 2.5, "trap_whale": 2.5, "trap_bpp_dev": 1.5,
        "trap_freq": 1.5, "trap_pattern": 1.2, "trap_zone": 1.0, "trap_last_kill": 0.8,
    }
    
    # Điều chỉnh trọng số thích ứng với AVF
    if market_state == "CONCENTRATED_HIGH_RISK":
        log_debug("V4 Adaptive: CONCENTRATED_HIGH_RISK market. Increasing risk adjustment weights.")
        weights["safety_risk_adjustment"] *= 2.0
        weights["trap_decoy"] *= 1.8
    elif market_state == "FEARFUL_LOW_RISK":
        log_debug("V4 Adaptive: FEARFUL_LOW_RISK market. Increasing contrarian/confidence rewards.")
        weights["safety_contrarian"] *= 1.6
        weights["safety_avf_confidence"] *= 1.5
    elif market_state == "HIGH_RISK":
        log_debug("V4 Adaptive: HIGH_RISK market. Conservative weighting.")
        weights["safety_risk_adjustment"] *= 1.5
        weights["trap_decoy"] *= 0.7
        weights["trap_whale"] *= 0.7
    elif market_state == "LOW_RISK":
        log_debug("V4 Adaptive: LOW_RISK market. Aggressive weighting.")
        weights["safety_contrarian"] *= 1.3
        weights["safety_cold_room"] *= 1.3

    agg_scores = {r: 0.0 for r in filtered_cand}
    log_debug(f"--- SUPERIOR DEVIL V4 AVF Scoring (Candidates: {filtered_cand}) ---")
    
    for r in filtered_cand:
        f = features[r]
        
        # --- Tính Điểm An Toàn ---
        safety_score = 0.0
        safety_score += weights["safety_contrarian"] * f["contrarian_score"]
        safety_score += weights["safety_bpp_health"] * f["bpp_score"]
        safety_score += weights["safety_cold_room"] * f["cold_room_score"]
        safety_score += weights["safety_survive_hist"] * f["survive_score"]
        safety_score += weights["safety_bpp_relative"] * f["bpp_relative_score"]
        safety_score += weights["safety_risk_adjustment"] * f["risk_adjustment"]
        safety_score += weights["safety_avf_confidence"] * f["avf_confidence_bonus"]
        
        # --- Tính Điểm Bẫy ---
        trap_score = 0.0
        trap_score += weights["trap_decoy"] * f["decoy_trap_score"]
        trap_score += weights["trap_whale"] * f["whale_trap_score"]
        trap_score += weights["trap_bpp_dev"] * f["bpp_deviation_penalty"]
        trap_score += weights["trap_freq"] * f["freq_penalty"]
        trap_score += weights["trap_pattern"] * f["pattern_penalty"]
        trap_score += weights["trap_zone"] * f["zone_penalty"]
        trap_score += weights["trap_last_kill"] * f["last_pen"]

        # Điểm cuối cùng = An Toàn - Bẫy
        final_score = safety_score - trap_score
        agg_scores[r] = final_score
        log_debug(f"Room {r}: Safety={safety_score:.3f}, Trap={trap_score:.3f}, AVF Risk={f['risk_score_ema']:.1f} -> FINAL={final_score:.3f}")

    # Xếp hạng
    ranked = sorted(agg_scores.items(), key=lambda kv: (-kv[1], kv[0]))
    
    # --- PHASE 4: V4 - TSUNAMI FINAL CHECK VỚI AVF VALIDATION ---
    if len(ranked) < 2:
        best_room = ranked[0][0]
        log_debug(f"V4 FINAL CHOICE (Only 1): R{best_room} (Score: {ranked[0][1]:.3f}, AVF Risk: {features[best_room]['risk_score_ema']:.1f})")
        return best_room, "SUPERIOR_DEVIL_V4_AVF"

    best_cand = ranked[0]
    second_cand = ranked[1]
    third_cand = ranked[2] if len(ranked) > 2 else None

    # Kiểm tra Bẫy Tách (Split Trap) với AVF validation
    score_diff_percent = (best_cand[1] - second_cand[1]) / max(0.01, abs(best_cand[1]))
    
    if score_diff_percent < 0.15:
        log_debug(f"V4 Tsunami: Top 2 candidates (R{best_cand[0]}, R{second_cand[0]}) have very close scores. AVF Analyzing...")
        
        f1 = features[best_cand[0]]
        f2 = features[second_cand[0]]
        zone1 = 'low' if best_cand[0] <= 4 else 'high'
        zone2 = 'low' if second_cand[0] <= 4 else 'high'
        player_diff_percent = abs(f1['players'] - f2['players']) / max(1, (f1['players'] + f2['players']) / 2)
        
        # Sử dụng AVF risk để quyết định
        risk_diff = abs(f1['risk_score_ema'] - f2['risk_score_ema'])
        
        if zone1 == zone2 and player_diff_percent < 0.4 and risk_diff < 15.0:
            log_debug(f"V4 TACTICAL PIVOT: R{best_cand[0]} and R{second_cand[0]} are a 'Split Trap' (Same Zone, Similar Players, Similar Risk).")
            
            if third_cand:
                f3 = features[third_cand[0]]
                zone3 = 'low' if third_cand[0] <= 4 else 'high'
                
                # Ưu tiên phòng có risk thấp hơn và zone khác
                if zone3 != zone1 and f3['risk_score_ema'] < min(f1['risk_score_ema'], f2['risk_score_ema']) and third_cand[1] > max(0, best_cand[1] * 0.5):
                    log_debug(f"V4 Pivot successful: Pivoting to safer zone candidate R{third_cand[0]} with lower AVF risk.")
                    return third_cand[0], "SUPERIOR_DEVIL_V4_AVF_PIVOT"
                else:
                    log_debug(f"V4 Pivot failed: 3rd cand (R{third_cand[0]}) has higher risk or bad score. Sticking with R{best_cand[0]}.")
            else:
                log_debug(f"V4 Pivot failed: No 3rd candidate. Sticking with R{best_cand[0]}.")
        else:
            log_debug(f"V4 Tsunami: R{best_cand[0]} and R{second_cand[0]} are not a Split Trap (Diff Zone/Players/Risk).")

    # Final AVF validation
    best_risk = features[best_cand[0]]['risk_score_ema']
    if best_risk > 70.0 and features[best_cand[0]]['avf_confidence'] > 0.6:
        log_debug(f"V4 AVF WARNING: Best candidate R{best_cand[0]} has high AVF risk ({best_risk:.1f}). Checking alternatives...")
        
        # Tìm candidate có risk thấp hơn và score không quá thấp
        low_risk_candidates = [(r, score) for r, score in ranked if features[r]['risk_score_ema'] < 60.0 and score > best_cand[1] * 0.7]
        if low_risk_candidates:
            alternative = low_risk_candidates[0]
            log_debug(f"V4 AVF SWITCH: Switching to R{alternative[0]} with lower AVF risk ({features[alternative[0]]['risk_score_ema']:.1f})")
            return alternative[0], "SUPERIOR_DEVIL_V4_AVF_SAFE"

    log_debug(f"V4 FINAL CHOICE: Room {best_cand[0]} (Score: {best_cand[1]:.3f}, AVF Risk: {best_risk:.1f})")
    return best_cand[0], "SUPERIOR_DEVIL_V4_AVF"

# -------------------- BETTING HELPERS --------------------

def api_headers() -> Dict[str, str]:
    """Tạo header chuẩn cho API đặt cược."""
    return {
        "content-type": "application/json",
        "user-agent": "Mozilla/5.0",
        "user-id": str(USER_ID) if USER_ID else "",
        "user-secret-key": SECRET_KEY if SECRET_KEY else ""
    }


def place_bet_http(issue: int, room_id: int, amount: float) -> dict:
    """Gửi yêu cầu đặt cược qua HTTP POST."""
    payload = {"asset_type": "BUILD", "user_id": USER_ID, "room_id": int(room_id), "bet_amount": float(amount)}
    try:
        r = HTTP.post(BET_API_URL, headers=api_headers(), json=payload, timeout=6)
        try:
            return r.json()
        except Exception:
            return {"raw": r.text, "http_status": r.status_code}
    except Exception as e:
        return {"error": str(e)}


def record_bet(issue: int, room_id: int, amount: float, resp: dict, algo_used: Optional[str] = None) -> dict:
    """Ghi lại lịch sử đặt cược."""
    now = datetime.now(tz).strftime("%H:%M:%S")
    rec = {
        "issue": issue, "room": room_id, "amount": float(amount), 
        "time": now, "resp": resp, "result": "Đang", 
        "algo": algo_used, "delta": 0.0, "win_streak": win_streak, 
        "lose_streak": lose_streak,
        "killed_room_id": None
    }
    bet_history.append(rec)
    return rec


def place_bet_async(issue: int, room_id: int, amount: float, algo_used: Optional[str] = None) -> None:
    """Đặt cược không đồng bộ (non-blocking) trong một thread mới."""
    def worker():
        console.print(f"[{PENDING_COLOR}]Đang đặt {amount:,.4f} BUILD -> PHÒNG_{room_id} (v{issue}) — Thuật toán: {algo_used}[/]")
        time.sleep(random.uniform(0.02, 0.25))
        res = place_bet_http(issue_id, room_id, amount)
        rec = record_bet(issue_id, room_id, amount, res, algo_used=algo_used)
        
        if isinstance(res, dict) and (res.get("msg") == "ok" or res.get("code") == 0 or res.get("status") in ("ok", 1) or "success" in str(res).lower()):
            bet_sent_for_issue.add(issue_id)
            console.print(f"[{SUCCESS_COLOR}]✅ Đặt thành công {amount:,.4f} BUILD vào PHÒNG_{room_id} (v{issue_id}).[/]")
        else:
            console.print(f"[{FAILURE_COLOR}]❌ Đặt lỗi v{issue_id}: {res}[/]")
            
    threading.Thread(target=worker, daemon=True).start()

# -------------------- LOCK & AUTO-BET --------------------

def lock_prediction_if_needed(force: bool = False) -> None:
    """
    Thực hiện khóa dự đoán và đặt cược tự động nếu điều kiện cho phép.
    """
    global prediction_locked, predicted_room, ui_state, current_bet, _rounds_placed_since_skip, skip_next_round_flag, _skip_rounds_remaining, win_streak, lose_streak
    global current_build 
    global auto_bet_enabled
    
    if stop_flag:
        return
    if prediction_locked and not force:
        return
    if issue_id is None:
        return
        
    prediction_locked = True
    ui_state = "PREDICTED"
    
    chosen, algo_used = choose_room_devilmode()
    predicted_room = chosen
    
    if _skip_rounds_remaining > 0:
        console.print(f"[{ACCENT_COLOR}]⏸️ Đang nghỉ sau khi thua... Còn lại {_skip_rounds_remaining} ván.[/]")
        _skip_rounds_remaining -= 1
        prediction_locked = True 
        return
        
    if run_mode == "AUTO" and not skip_next_round_flag:
        
        if not auto_bet_enabled:
            record_bet(issue_id, predicted_room, 0.0, {"msg": "simulation"}, algo_used=algo_used)
            console.print(f"[{PENDING_COLOR}]ℹ️ AI DỰ ĐOÁN: PHÒNG {predicted_room} (Chế độ OFF - Mô phỏng kết quả)[/]")
            return

        bld, _, _ = fetch_balances_3games(params={"userId": str(USER_ID)} if USER_ID else None)
        if bld is None:
            console.print(f"[{ACCENT_COLOR}]⚠️ Không lấy được số dư trước khi đặt — bỏ qua đặt ván này.[/]")
            prediction_locked = False
            return
            
        if current_bet is None:
            current_bet = base_bet
        
        strategy = SELECTION_CONFIG.get("bet_management_strategy", "MARTINGALE")
        if strategy == "ANTI-MARTINGALE":
            if win_streak > 0:
                current_bet = base_bet + (base_bet * 0.1 * win_streak) 
            else:
                current_bet = base_bet
                
        if current_bet < base_bet:
            current_bet = base_bet

        amt = float(current_bet)
        
        if amt <= 0 or amt > current_build:
            console.print(f"[{FAILURE_COLOR}]⚠️ Số tiền đặt không hợp lệ ({amt:,.4f} > {current_build:,.4f}). Bỏ qua.[/]")
            prediction_locked = False
            return
        
        place_bet_async(issue_id, predicted_room, amt, algo_used=algo_used)
        _rounds_placed_since_skip += 1
        
        if bet_rounds_before_skip > 0 and _rounds_placed_since_skip >= bet_rounds_before_skip:
            skip_next_round_flag = True
            _rounds_placed_since_skip = 0
            
    elif skip_next_round_flag:
        console.print(f"[{ACCENT_COLOR}]⏸️ TẠM DỪNG THEO DÕI SÁT THỦ (Cấu hình SKIP: Chống soi)[/]")
        skip_next_round_flag = False
        prediction_locked = True 
        return

# -------------------- WEBSOCKET HANDLERS --------------------

def safe_send_enter_game(ws: Optional[websocket.WebSocketApp]) -> None:
    """Gửi yêu cầu tham gia game qua WebSocket."""
    if not ws:
        log_debug("safe_send_enter_game: ws None")
        return
    try:
        payload = {"msg_type": "handle_enter_game", "asset_type": "BUILD", "user_id": USER_ID, "user_secret_key": SECRET_KEY}
        ws.send(json.dumps(payload))
        log_debug("Sent enter_game")
    except Exception as e:
        log_debug(f"safe_send_enter_game err: {e}")


def _extract_issue_id(d: Dict[str, Any]) -> Optional[int]:
    """Trích xuất issue ID từ payload WS."""
    if not isinstance(d, dict):
        return None
    possible = []
    for key in ("issue_id", "issueId", "issue", "id"):
        v = d.get(key)
        if v is not None:
            possible.append(v)
    if isinstance(d.get("data"), dict):
        for key in ("issue_id", "issueId", "issue", "id"):
            v = d["data"].get(key)
            if v is not None:
                possible.append(v)
    for p in possible:
        try:
            return int(p)
        except Exception:
            try:
                return int(str(p))
            except Exception:
                continue
    return None


def on_open(ws: websocket.WebSocketApp) -> None:
    """Xử lý khi kết nối WS được mở."""
    _ws["ws"] = ws
    console.print(f"[{SUCCESS_COLOR}]ĐANG TRUY CẬP DỮ LIỆU GAME (SUPERIOR DEVIL AVF MODE ON)[/]")
    safe_send_enter_game(ws)


def _background_fetch_balance_after_result() -> None:
    """Fetch số dư trong background sau khi có kết quả ván."""
    try:
        fetch_balances_3games()
    except Exception:
        pass


def _mark_bet_result_from_issue(res_issue: Optional[int], krid: int) -> None:
    """
    Đánh dấu kết quả cược ngay lập tức trong lịch sử cược (local).
    """
    global current_bet, win_streak, lose_streak, max_win_streak, max_lose_streak, _skip_rounds_remaining, stop_flag, multiplier, base_bet
    if res_issue is None:
        return
        
    rec = None
    for b in reversed(list(bet_history)):
        if b.get("issue") == res_issue:
            rec = b
            break
            
    if rec is None:
        return
        
    try:
        rec["killed_room_id"] = int(krid)
        
        placed_room = int(rec.get("room"))
        placed_amount = float(rec.get("amount"))
        is_win = (placed_room != int(krid))
        
        delta = 0.0
        if is_win:
            rec["result"] = "Thắng"
            delta = placed_amount 
            
            if SELECTION_CONFIG.get("bet_management_strategy") == "MARTINGALE":
                 current_bet = base_bet 
            
            win_streak += 1
            lose_streak = 0
            if win_streak > max_win_streak:
                max_win_streak = win_streak
                
        else:
            rec["result"] = "Thua"
            delta = -placed_amount
            
            if SELECTION_CONFIG.get("bet_management_strategy") == "MARTINGALE":
                try:
                    current_bet = placed_amount * float(multiplier)
                except Exception:
                    current_bet = base_bet
            else:
                 current_bet = base_bet
                 
            lose_streak += 1
            win_streak = 0
            if lose_streak > max_lose_streak:
                max_lose_streak = lose_streak
                
            if pause_after_losses > 0:
                _skip_rounds_remaining = pause_after_losses
                
        rec["delta"] = delta
        
    except Exception as e:
        log_debug(f"_mark_bet_result_from_issue err: {e}")


def on_message(ws: websocket.WebSocketApp, message: Union[str, bytes]) -> None:
    """Xử lý các tin nhắn nhận được từ WebSocket."""
    global issue_id, count_down, killed_room, round_index, ui_state, analysis_start_ts, issue_start_ts
    global prediction_locked, predicted_room, last_killed_room, last_msg_ts, current_bet
    global win_streak, lose_streak, max_win_streak, max_lose_streak, cumulative_profit, _skip_rounds_remaining, stop_flag, analysis_blur
    global game_kill_history, game_kill_pattern_tracker, room_stats
    
    last_msg_ts = time.time()
    try:
        if isinstance(message, bytes):
            try:
                message = message.decode("utf-8", errors="replace")
            except Exception:
                message = str(message)
        
        data = None
        try:
            data = json.loads(message)
        except Exception:
            try:
                data = json.loads(message.replace("'", '"'))
            except Exception:
                log_debug(f"on_message non-json: {str(message)[:200]}")
                return

        if isinstance(data, dict) and isinstance(data.get("data"), str):
            try:
                inner = json.loads(data.get("data"))
                merged = dict(data)
                merged.update(inner)
                data = merged
            except Exception:
                pass

        msg_type = data.get("msg_type") or data.get("type") or ""
        msg_type = str(msg_type)
        new_issue = _extract_issue_id(data)

        # 1. Thông báo thống kê ván (issue stat / rooms update)
        if msg_type == "notify_issue_stat" or "issue_stat" in msg_type:
            rooms = data.get("rooms") or []
            if not rooms and isinstance(data.get("data"), dict):
                rooms = data["data"].get("rooms", [])
                
            for rm in (rooms or []):
                try:
                    rid = int(rm.get("room_id") or rm.get("roomId") or rm.get("id"))
                except Exception:
                    continue
                players = int(rm.get("user_cnt") or rm.get("userCount") or 0) or 0
                bet = float(rm.get("total_bet_amount") or rm.get("totalBet") or rm.get("bet") or 0) or 0
                
                room_state[rid] = {"players": players, "bet": bet}
                
                room_stats[rid]["last_players"] = players
                room_stats[rid]["last_bet"] = bet
                
                bpp = bet / players if players > 0 else 0.0
                if bpp > 0:
                     stats = room_stats.get(rid)
                     if stats and isinstance(stats.get("historical_bpp"), deque):
                          stats["historical_bpp"].append(bpp)
                          
            if new_issue is not None and new_issue != issue_id:
                log_debug(f"New issue: {issue_id} -> {new_issue}")
                issue_id = new_issue
                issue_start_ts = time.time()
                killed_room = None
                prediction_locked = False
                predicted_room = None
                
                if ui_state == "RESULT":
                     round_index += 1
                
                ui_state = "ANALYZING"
                analysis_start_ts = time.time()

        # 2. Thông báo đếm ngược (countdown)
        elif msg_type == "notify_count_down" or "count_down" in msg_type:
            count_down_val = data.get("count_down") or data.get("countDown") or data.get("count") or count_down
            try:
                count_val = int(count_down_val)
                count_down = count_val
            except Exception:
                count_val = None
                
            if count_val is not None:
                try:
                    if count_val <= 5 and not prediction_locked:
                        analysis_blur = False
                        lock_prediction_if_needed()
                    elif count_val <= 45:
                        ui_state = "ANALYZING"
                        analysis_start_ts = time.time()
                        analysis_blur = True
                except Exception as e:
                    log_debug(f"Countdown logic error: {e}")

        # 3. Thông báo kết quả (result)
        elif msg_type == "notify_result" or "result" in msg_type:
            kr = data.get("killed_room") if data.get("killed_room") is not None else data.get("killed_room_id")
            if kr is None and isinstance(data.get("data"), dict):
                kr = data["data"].get("killed_room") or data["data"].get("killed_room_id")
                
            if kr is not None:
                try:
                    krid = int(kr)
                except Exception:
                    krid = kr
                killed_room = krid
                last_killed_room = krid
                
                game_kill_history.append(krid)
                game_kill_pattern_tracker["kill_seq"].append(krid)
                game_kill_pattern_tracker["kill_counts"][krid] += 1
                game_kill_pattern_tracker["last_kill_ts"] = time.time()
                
                for rid in ROOM_ORDER:
                    if rid == krid:
                        room_stats[rid]["kills"] += 1
                        room_stats[rid]["last_kill_round"] = round_index
                    else:
                        room_stats[rid]["survives"] += 1

                res_issue = new_issue if new_issue is not None else issue_id
                _mark_bet_result_from_issue(res_issue, krid)
                
                threading.Thread(target=_background_fetch_balance_after_result, daemon=True).start()

            ui_state = "RESULT"

            def _check_stop_conditions():
                global stop_flag, current_build, profit_target, stop_loss_target
                try:
                    if stop_when_profit_reached and profit_target is not None and isinstance(current_build, (int, float)) and current_build >= profit_target:
                        console.print(f"[{SUCCESS_COLOR} on {MAIN_COLOR}]🎉 MỤC TIÊU LÃI ĐẠT: {current_build:,.4f} >= {profit_target:,.4f}. Dừng tool.[/]")
                        stop_flag = True
                        try:
                            wsobj = _ws.get("ws")
                            if wsobj: wsobj.close()
                        except Exception:
                            pass
                    if stop_when_loss_reached and stop_loss_target is not None and isinstance(current_build, (int, float)) and current_build <= stop_loss_target:
                        console.print(f"[{FAILURE_COLOR} on {MAIN_COLOR}]⚠️ STOP-LOSS TRIGGED: {current_build:,.4f} <= {stop_loss_target:,.4f}. Dừng tool.[/]")
                        stop_flag = True
                        try:
                            wsobj = _ws.get("ws")
                            if wsobj: wsobj.close()
                        except Exception:
                            pass
                except Exception as e:
                    log_debug(f"Stop conditions check error: {e}")
                    
            threading.Timer(1.2, _check_stop_conditions).start()

    except Exception as e:
        log_debug(f"on_message err: {e}")
    
    # *** ADVANCED AVF RISK ASSESSMENT: Cập nhật đánh giá rủi ro sau mỗi tin nhắn ***
    try:
        update_all_room_risks()
    except Exception as e:
        log_debug(f"Risk assessment update error: {e}")


def on_close(ws: websocket.WebSocketApp, code: int, reason: str) -> None:
    """Xử lý khi kết nối WS bị đóng."""
    log_debug(f"WS closed: {code} {reason}")


def on_error(ws: websocket.WebSocketApp, err: Union[Exception, str]) -> None:
    """Xử lý lỗi WebSocket."""
    log_debug(f"WS error: {err}")


def start_ws() -> None:
    """Khởi động và duy trì kết nối WebSocket (với logic tự động reconnect)."""
    backoff = 0.6
    while not stop_flag:
        try:
            ws_app = websocket.WebSocketApp(WS_URL, on_open=on_open, on_message=on_message, on_close=on_close, on_error=on_error)
            _ws["ws"] = ws_app
            ws_app.run_forever(ping_interval=12, ping_timeout=6)
        except Exception as e:
            log_debug(f"start_ws exception: {e}")
        
        t = min(backoff + random.random() * 0.5, 30)
        log_debug(f"Reconnect WS after {t}s")
        console.print(f"[{ACCENT_COLOR}]Đã mất kết nối WS. Đang thử kết nối lại sau {t:.1f}s...[/]")
        time.sleep(t)
        backoff = min(backoff * 1.5, 30)

# -------------------- BALANCE POLLER THREAD --------------------

class BalancePoller(threading.Thread):
    """
    Thread chạy ngầm để định kỳ fetch số dư người dùng.
    """
    def __init__(self, uid: Optional[int], secret: Optional[str], poll_seconds: int = 2, on_balance=None, on_error=None, on_status=None):
        super().__init__(daemon=True)
        self.uid = uid
        self.secret = secret
        self.poll_seconds = max(1, int(poll_seconds))
        self._running = True
        self._last_balance_local: Optional[float] = None
        self.on_balance = on_balance
        self.on_error = on_error
        self.on_status = on_status

    def stop(self) -> None:
        """Dừng thread poller."""
        self._running = False

    def run(self) -> None:
        """Logic chính của thread: Định kỳ fetch số dư."""
        if self.on_status:
            self.on_status("Kết nối...")
            
        while self._running and not stop_flag:
            try:
                build, world, usdt = fetch_balances_3games(params={"userId": str(self.uid)} if self.uid else None, uid=self.uid, secret=self.secret)
                
                if build is None:
                    raise RuntimeError("Không đọc được balance từ response")
                    
                delta = 0.0 if self._last_balance_local is None else (build - self._last_balance_local)
                first_time = (self._last_balance_local is None)
                
                if first_time or abs(delta) > 0.000001:
                    self._last_balance_local = build
                    if self.on_balance:
                        self.on_balance(float(build), float(delta), {"ts": human_ts()})
                    if self.on_status:
                        self.on_status("Đang theo dõi")
                else:
                    if self.on_status:
                        self.on_status("Đang theo dõi (không đổi)")
            
            except Exception as e:
                if self.on_error:
                    self.on_error(str(e))
                if self.on_status:
                    self.on_status("Lỗi kết nối (thử lại...)")
            
            for _ in range(max(1, int(self.poll_seconds * 5))):
                if not self._running or stop_flag:
                    break
                time.sleep(0.2)
                
        if self.on_status:
            self.on_status("Đã dừng")

# -------------------- MONITOR --------------------

def monitor_loop() -> None:
    """
    Thread giám sát sức khỏe của kết nối WS và fetch số dư dự phòng.
    """
    global last_balance_fetch_ts, last_msg_ts, stop_flag
    while not stop_flag:
        now = time.time()
        
        if now - last_balance_fetch_ts >= BALANCE_POLL_INTERVAL * 2:
            last_balance_fetch_ts = now
            try:
                fetch_balances_3games(params={"userId": str(USER_ID)} if USER_ID else None)
            except Exception as e:
                log_debug(f"monitor fetch err: {e}")
        
        if now - last_msg_ts > 8:
            log_debug("No ws msg >8s, send enter_game to keep alive")
            try:
                safe_send_enter_game(_ws.get("ws"))
            except Exception as e:
                log_debug(f"monitor send err: {e}")
                
        if now - last_msg_ts > 20:
            log_debug("No ws msg >20s, force reconnect")
            try:
                wsobj = _ws.get("ws")
                if wsobj:
                    try:
                        wsobj.close()
                    except Exception:
                        pass
            except Exception:
                pass
                
        time.sleep(0.6)

# -------------------- UI (RICH) - OPTIMIZED FOR PERFORMANCE --------------------

def _spinner_char() -> str:
    """Lấy ký tự spinner Blue mode hiện tại."""
    return _spinner[int(time.time() * 4) % len(_spinner)]

def _blue_border_style() -> str:
    """Tạo style viền nhấp nháy Xanh/Xanh Đậm."""
    idx = int(time.time() * 2) % 2
    return MAIN_COLOR if idx == 0 else ACCENT_COLOR

def build_header(border_color: Optional[str] = None) -> Panel:
    """
    Xây dựng Panel Header (Thông tin tài khoản, Lãi/Lỗ, Cấu hình).
    OPTIMIZED: Giảm số lượng tính toán và text operations.
    """
    global auto_bet_enabled

    # Sử dụng cached values để giảm tính toán
    current_time = datetime.now(tz)
    ab_status = "ON" if auto_bet_enabled else "OFF"
    ab_color = SUCCESS_COLOR if auto_bet_enabled else FAILURE_COLOR
    
    # Build header với ít operations hơn
    header_table = Table.grid(expand=True, padding=(0, 1))
    header_table.add_column(ratio=2)
    header_table.add_column(ratio=1)

    # Left side - Title
    left_title = Text.assemble(
        (f"[{MAIN_COLOR} bold]🌐 SUPERIOR DEVIL AVF V4.0 [/]"), 
        (f"[{ACCENT_COLOR}] - {SELECTION_MODES.get(settings.get('algo', ''), settings.get('algo'))}[/]")
    )
    
    # Right side - Time and status
    right_time = Text.assemble(
        (f"[{TEXT_COLOR}]{current_time.strftime('%Y/%m/%d %H:%M:%S')}  •  {_spinner_char()}[/]", "dim"),
        (f"  |  Auto Bet: ", "dim"),
        (f"{ab_status}", f"bold {ab_color}")
    )
    
    header_table.add_row(Align.left(left_title), Align.right(right_time))

    # Balance information - simplified
    b = f"{current_build:,.4f}" if isinstance(current_build, (int, float)) else (str(current_build) if current_build is not None else "-")
    pnl_val = cumulative_profit if cumulative_profit is not None else 0.0
    pnl_str = f"{pnl_val:+,.4f}"
    pnl_style = SUCCESS_COLOR if pnl_val > 0 else (FAILURE_COLOR if pnl_val < 0 else PENDING_COLOR)
    
    balance_text = Text.assemble(
         (f"[{TEXT_COLOR}]BUILD: [/{TEXT_COLOR}]",), (f"[{MAIN_COLOR} bold]{b}[/]",), 
         (f"  |  PnL: ",), (f"[{pnl_style}]{pnl_str}[/]",)
    )
    
    header_table.add_row(Align.left(balance_text), Text(""))  # Empty right cell

    panel = Panel(
        header_table, 
        box=box.HEAVY_HEAD, 
        padding=(0,1), 
        border_style=(border_color or _blue_border_style())
    )
    return panel

def build_rooms_table(border_color: Optional[str] = None) -> Panel:
    """
    Xây dựng Panel hiển thị dữ liệu thời gian thực của các phòng.
    OPTIMIZED: Giảm số lượng tính toán và string operations.
    """
    # Sử dụng table đơn giản hơn
    t = Table(box=box.SIMPLE, expand=True, title=Text("📊 DỮ LIỆU PHÒNG", style=f"bold {MAIN_COLOR}"))
    t.add_column("ID", justify="center", width=3, style=PENDING_COLOR)
    t.add_column("Phòng", width=16, style=TEXT_COLOR)
    t.add_column("Players", justify="right", style=ACCENT_COLOR, width=8)
    t.add_column("Risk", justify="center", style=TEXT_COLOR, width=12)
    t.add_column("Status", justify="center", style=TEXT_COLOR, width=12)
    
    for r in ROOM_ORDER:
        st = room_state.get(r, {})
        
        players = st.get("players", 0)
        status = ""
        row_style = ""
        
        # Risk display - simplified
        risk_data = room_risk_assessment.get(r, {})
        risk_score = risk_data.get("risk_score", 50.0)
        risk_icon = risk_data.get("risk_icon", "🟡")
        
        risk_display = f"{risk_icon} {risk_score:.0f}%"
        
        # Status determination
        is_last_kill = False
        try:
            if killed_room is not None and int(r) == int(killed_room):
                status = f"[{FAILURE_COLOR}]☠[/]"
                row_style = FAILURE_COLOR
                is_last_kill = True
        except Exception:
            pass
            
        try:
            if predicted_room is not None and int(r) == int(predicted_room):
                status = f"[{SUCCESS_COLOR}]✓[/]" if not is_last_kill else f"[{FAILURE_COLOR}]☠[/] [{SUCCESS_COLOR}]✓[/]"
                if not is_last_kill:
                    row_style = SUCCESS_COLOR 
        except Exception:
            pass
            
        t.add_row(
            str(r), 
            ROOM_NAMES.get(r, f"P {r}"), 
            str(players), 
            risk_display,
            status, 
            style=row_style
        )
        
    return Panel(t, title_align="left", border_style=(border_color or _blue_border_style()), padding=(0, 1))

def build_mid(border_color: Optional[str] = None) -> Panel:
    """Xây dựng Panel giữa (Trạng thái hiện tại). OPTIMIZED: Giảm tính toán phức tạp."""
    global analysis_start_ts, analysis_blur
    
    current_border = border_color or _blue_border_style()
    
    if ui_state == "ANALYZING":
        lines = []
        lines.append(f"[{PENDING_COLOR} bold]ĐANG PHÂN TÍCH AVF {_spinner_char()}[/]")
        
        cd_val = int(count_down) if count_down is not None else None
        
        if cd_val is not None:
            lines.append(f"[{TEXT_COLOR}]Đếm ngược: [/{TEXT_COLOR}][{MAIN_COLOR} bold]{cd_val}s[/]")
        else:
            lines.append(f"[{ACCENT_COLOR}]Chờ dữ liệu...[/]")

        if analysis_blur:
            # Simplified loading bar
            bar_len = 20
            tbase = int(time.time() * 3)
            bar = "".join(["█" if (tbase + i) % 3 == 0 else "░" for i in range(bar_len)])
            lines.append(f"[{MAIN_COLOR}]{bar}[/]")
        else:
            lines.append(f"[{TEXT_COLOR}]Chờ cửa sổ 10s...[/]")
            
        lines.append(f"[{TEXT_COLOR}]Sát thủ trước: [/{TEXT_COLOR}][{FAILURE_COLOR}]{ROOM_NAMES.get(last_killed_room, '-')}[/]")
        
        # Simplified risk overview
        risk_counts = {RISK_LEVEL_CRITICAL: 0, RISK_LEVEL_HIGH: 0, RISK_LEVEL_MEDIUM: 0, RISK_LEVEL_LOW: 0, RISK_LEVEL_SAFE: 0}
        for room_id in ROOM_ORDER:
            risk_data = room_risk_assessment.get(room_id, {})
            risk_level = risk_data.get("risk_level", RISK_LEVEL_SAFE)
            risk_counts[risk_level] += 1
        
        risk_summary = []
        if risk_counts[RISK_LEVEL_CRITICAL] > 0:
            risk_summary.append(f"[{FAILURE_COLOR}]{risk_counts[RISK_LEVEL_CRITICAL]}🔴[/]")
        if risk_counts[RISK_LEVEL_HIGH] > 0:
            risk_summary.append(f"[{FAILURE_COLOR}]{risk_counts[RISK_LEVEL_HIGH]}🟠[/]")
        if risk_counts[RISK_LEVEL_MEDIUM] > 0:
            risk_summary.append(f"[{WARNING_COLOR}]{risk_counts[RISK_LEVEL_MEDIUM]}🟡[/]")
        if risk_counts[RISK_LEVEL_LOW] > 0:
            risk_summary.append(f"[{PENDING_COLOR}]{risk_counts[RISK_LEVEL_LOW]}🔵[/]")
        if risk_counts[RISK_LEVEL_SAFE] > 0:
            risk_summary.append(f"[{SUCCESS_COLOR}]{risk_counts[RISK_LEVEL_SAFE]}🟢[/]")
            
        if risk_summary:
            lines.append(f"[{TEXT_COLOR}]Phân bố rủi ro: [/{TEXT_COLOR}]" + " ".join(risk_summary))
        
        txt = "\n".join(lines)
        return Panel(
            Align.center(Text.from_markup(txt), vertical="middle"), 
            title=Text("🔥 PHÂN TÍCH AVF", style=f"bold {MAIN_COLOR}"), 
            border_style=current_border, 
            height=10,  # Reduced height
            padding=(0, 1)
        )

    elif ui_state == "PREDICTED":
        name = ROOM_NAMES.get(predicted_room, f"P{predicted_room}") if predicted_room else '-'
        
        last_bet_amt_display = f"{current_bet:,.4f}" if isinstance(current_bet, (int, float)) and current_bet is not None else '-'
        
        lines = []
        lines.append(f"[{ACCENT_COLOR} bold]🌐 AI CHỌN: [/][{SUCCESS_COLOR} bold]{name}[/]")
        lines.append(f"[{TEXT_COLOR}]Cược: [/{TEXT_COLOR}][{MAIN_COLOR} bold]{last_bet_amt_display} BUILD[/]")
        lines.append(f"[{TEXT_COLOR}]Sát thủ trước: [/{TEXT_COLOR}][{FAILURE_COLOR}]{ROOM_NAMES.get(last_killed_room, '-')}[/]")
        lines.append(f"[{TEXT_COLOR}]Chuỗi: [/{TEXT_COLOR}][{SUCCESS_COLOR}]W={win_streak}[/] | [{FAILURE_COLOR}]L={lose_streak}[/]")
        
        cd_val = int(count_down) if count_down is not None else None
        if cd_val is not None:
            lines.append(f"[{TEXT_COLOR}]Đếm ngược: [/{TEXT_COLOR}][{MAIN_COLOR} bold]{cd_val}s[/]")
        
        lines.append(f"[{PENDING_COLOR}]Chờ kết quả {_spinner_char()}[/]")
        
        # Simplified risk info for predicted room
        if predicted_room is not None:
            risk_data = room_risk_assessment.get(predicted_room, {})
            risk_score = risk_data.get("risk_score", 50.0)
            risk_color = risk_data.get("risk_color", SUCCESS_COLOR)
            
            lines.append("")
            lines.append(f"[{TEXT_COLOR}]Đánh giá AVF: [/{TEXT_COLOR}][{risk_color}]{risk_score:.1f}%[/]")
        
        txt = "\n".join(lines)
        
        return Panel(
            Align.center(Text.from_markup(txt)), 
            title=Text("🎯 DỰ ĐOÁN AVF", style=f"bold {MAIN_COLOR}"), 
            border_style=current_border, 
            height=10,  # Reduced height
            padding=(0, 1)
        )

    elif ui_state == "RESULT":
        k = ROOM_NAMES.get(killed_room, "-") if killed_room else "-"
        
        border = current_border
        last_result_rec = bet_history[-1] if bet_history else None
        last_result = last_result_rec.get('result') if last_result_rec else None
        
        if last_result == 'Thắng':
            border = SUCCESS_COLOR
            result_line = f"[{SUCCESS_COLOR} bold]✅ THẮNG! PnL: {cumulative_profit:+.4f} BUILD[/]"
        elif last_result == 'Thua':
            border = FAILURE_COLOR
            result_line = f"[{FAILURE_COLOR} bold]❌ THUA! PnL: {cumulative_profit:+.4f} BUILD[/]"
        else:
            result_line = f"[{PENDING_COLOR} bold]Đang chờ kết quả...[/]"

        lines = []
        lines.append(f"[{FAILURE_COLOR} bold]⚔️ SÁT THỦ: [/][{PENDING_COLOR} bold]{k}[/]")
        lines.append(result_line)
        lines.append(f"[{TEXT_COLOR}]Chuỗi: [/{TEXT_COLOR}][{SUCCESS_COLOR}]W={win_streak}[/] | [{FAILURE_COLOR}]L={lose_streak}[/]")
        lines.append(f"[{TEXT_COLOR}]Cược tiếp: [/{TEXT_COLOR}][{MAIN_COLOR} bold]{current_bet:,.4f} BUILD[/]")
        lines.append(f"[{TEXT_COLOR}]Ván tiếp: [/{TEXT_COLOR}][{PENDING_COLOR} bold]{(issue_id or 0) + 1}[/]")
        
        txt = "\n".join(lines)
        
        return Panel(
            Align.center(Text.from_markup(txt)), 
            title=Text("🔔 KẾT QUẢ", style=f"bold {MAIN_COLOR}"), 
            border_style=border, 
            height=10,  # Reduced height
            padding=(0, 1)
        )
    
    else:
        lines = []
        lines.append(f"[{PENDING_COLOR} bold]--- HỆ THỐNG AVF ĐANG KHỞI ĐỘNG ---[/]")
        lines.append(f"[{TEXT_COLOR}]Chờ ván mới...[/]")
        lines.append(f"[{TEXT_COLOR}]Sát thủ trước: [/{TEXT_COLOR}][{FAILURE_COLOR}]{ROOM_NAMES.get(last_killed_room, '-')}[/]")
        profit_style = SUCCESS_COLOR if cumulative_profit >= 0 else FAILURE_COLOR
        lines.append(f"[{TEXT_COLOR}]PnL: [/{TEXT_COLOR}][{profit_style} bold]{cumulative_profit:+.4f} BUILD[/]")
        
        txt = "\n".join(lines)
        return Panel(
            Align.center(Text.from_markup(txt)), 
            title=Text("⚙️ TRẠNG THÁI", style=f"bold {MAIN_COLOR}"), 
            border_style=current_border, 
            height=10,  # Reduced height
            padding=(0, 1)
        )

def build_bet_table(border_color: Optional[str] = None) -> Panel:
    """
    Xây dựng Panel hiển thị lịch sử cược 8 ván gần nhất.
    OPTIMIZED: Giảm số lượng hàng và cột.
    """
    global auto_bet_enabled

    t = Table(title=Text("📜 LỊCH SỬ CƯỢC", style=f"bold {MAIN_COLOR}"), box=box.SIMPLE, expand=True)

    if not auto_bet_enabled:
        t.add_column("Ván", justify="center", no_wrap=True, style=PENDING_COLOR, width=6)
        t.add_column("Dự đoán", justify="center", no_wrap=True, style=TEXT_COLOR, width=8)
        t.add_column("Kill", justify="center", no_wrap=True, style=ACCENT_COLOR, width=8)
        t.add_column("KQ", justify="center", no_wrap=True, width=4)
    else:
        t.add_column("Ván", justify="center", no_wrap=True, style=PENDING_COLOR, width=6)
        t.add_column("Đặt", justify="center", no_wrap=True, style=TEXT_COLOR, width=4)
        t.add_column("Số tiền", justify="right", no_wrap=True, style=MAIN_COLOR, width=10)
        t.add_column("KQ", justify="center", no_wrap=True, width=4)
        t.add_column("Kill", justify="center", no_wrap=True, style=ACCENT_COLOR, width=6) 
    
    last8 = list(bet_history)[-8:]  # Reduced from 10 to 8
    
    for b in reversed(last8):
        issue = str(b.get('issue') or '-')
        placed_room = str(b.get('room') or '-')
        
        res = str(b.get('result') or '-')
        
        killed_id = b.get("killed_room_id")
        killed_room_display = "-"
        
        if killed_id is not None:
             killed_room_display = str(killed_id)
             if placed_room.isdigit() and int(placed_room) == killed_id:
                  kill_style = FAILURE_COLOR
             else:
                  kill_style = SUCCESS_COLOR 
        else:
            kill_style = ACCENT_COLOR

        if res.lower().startswith('thắng'):
            res_text = Text("W", style=SUCCESS_COLOR)
        elif res.lower().startswith('thua'):
            res_text = Text("L", style=FAILURE_COLOR)
        else:
            res_text = Text("-", style=PENDING_COLOR)
            
        if not auto_bet_enabled:
            t.add_row(
                issue,
                placed_room,
                Text(killed_room_display, style=kill_style),
                res_text
            )
        else:
            amt = b.get('amount') or 0
            amt_fmt = f"{float(amt):.2f}"
            t.add_row(
                issue, 
                placed_room, 
                amt_fmt, 
                res_text, 
                Text(killed_room_display, style=kill_style)
            )
        
    return Panel(t, border_style=(border_color or _blue_border_style()), padding=(0, 1))
def build_stat_table(border_color: Optional[str] = None) -> Panel:
    """
    Xây dựng Panel hiển thị thống kê hoạt động.
    Hiển thị khác nhau khi auto-bet on/off.
    """
    global auto_bet_enabled, current_build, issue_id, round_index, cumulative_profit
    global win_streak, lose_streak, max_win_streak, max_lose_streak
    
    # Tính toán thống kê
    total_wins = sum(1 for b in bet_history if b.get('result') == 'Thắng')
    total_losses = sum(1 for b in bet_history if b.get('result') == 'Thua')
    total_settled_rounds = total_wins + total_losses
    win_rate = (total_wins / total_settled_rounds) * 100 if total_settled_rounds > 0 else 0.0
    
    # Định dạng số dư BUILD
    current_build_fmt = f"{current_build:,.4f}" if isinstance(current_build, (int, float)) else '-'
    
    # Tạo bảng thống kê
    stat_table = Table.grid(padding=(0, 1))
    stat_table.add_column(justify="left")
    stat_table.add_column(justify="right")
    
    if not auto_bet_enabled:
        # Khi auto-bet OFF
        stat_lines = [
            ("Số dư BUILD:", f"[{MAIN_COLOR} bold]{current_build_fmt} BUILD[/]"),
            ("Phiên hiện tại:", f"[{PENDING_COLOR}]{issue_id or '-'}[/]"),
            ("Tổng ván chơi:", f"[{ACCENT_COLOR} bold]{round_index}[/]"),
            ("Tổng W/L:", f"[{SUCCESS_COLOR}]{total_wins}[/]/[{FAILURE_COLOR}]{total_losses}[/]"),
            ("Tỷ lệ Win:", f"[{MAIN_COLOR} bold]{win_rate:.2f}%[/]"),
            ("MAX W/L:", f"[{SUCCESS_COLOR}]{max_win_streak}[/]/[{FAILURE_COLOR}]{max_lose_streak}[/]"),
        ]
    else:
        # Khi auto-bet ON
        pnl_val = cumulative_profit if cumulative_profit is not None else 0.0
        pnl_style = SUCCESS_COLOR if pnl_val > 0 else (FAILURE_COLOR if pnl_val < 0 else PENDING_COLOR)
        
        stat_lines = [
            ("Số dư BUILD:", f"[{MAIN_COLOR} bold]{current_build_fmt} BUILD[/]"),
            ("Phiên hiện tại:", f"[{PENDING_COLOR}]{issue_id or '-'}[/]"),
            ("Tổng ván chơi:", f"[{ACCENT_COLOR} bold]{round_index}[/]"),
            ("Lãi/Lỗ:", f"[{pnl_style} bold]{pnl_val:+.4f} BUILD[/]"),
            ("Tổng W/L:", f"[{SUCCESS_COLOR}]{total_wins}[/]/[{FAILURE_COLOR}]{total_losses}[/]"),
            ("Tỷ lệ Win:", f"[{MAIN_COLOR} bold]{win_rate:.2f}%[/]"),
            ("MAX W/L:", f"[{SUCCESS_COLOR}]{max_win_streak}[/]/[{FAILURE_COLOR}]{max_lose_streak}[/]"),
        ]
    
    # Thêm các dòng vào bảng
    for label, value in stat_lines:
        stat_table.add_row(
            Text.from_markup(f"[{TEXT_COLOR}]{label}[/]"),
            Text.from_markup(value)
        )
    
    # Tiêu đề panel
    title_text = "📈 THỐNG KÊ HOẠT ĐỘNG"
    if auto_bet_enabled:
        title_text += " (AUTO)"
    else:
        title_text += " (MANUAL)"
    
    return Panel(
        stat_table,
        title=Text(title_text, style=f"bold {ACCENT_COLOR}"),
        border_style=(border_color or _blue_border_style()),
        padding=(0, 1)
    )
def make_layout() -> Layout:
    """Tạo bố cục màn hình chính với bảng thống kê."""
    layout = Layout(name="root")

    layout.split_column(
        Layout(name="header", size=4), 
        Layout(name="content", ratio=4),
        Layout(name="footer", ratio=2) 
    )

    layout["content"].split_row(
        Layout(name="content.left", ratio=3),
        Layout(name="content.right", ratio=2)
    )

    # THÊM DÒNG NÀY - chia phần right thành mid và stat
    layout["content.right"].split_column(
        Layout(name="content.right.mid", size=14),
        Layout(name="content.right.stat", ratio=1)  # Phần cho bảng thống kê
    )
    
    return layout

def update_layout(layout: Layout) -> None:
    """
    Cập nhật nội dung cho bố cục. OPTIMIZED: Giảm tính toán phức tạp.
    """
    global max_lose_streak, auto_bet_enabled
    
    # Simplified statistics
    total_wins = sum(1 for b in bet_history if b.get('result') == 'Thắng')
    total_losses = sum(1 for b in bet_history if b.get('result') == 'Thua')
    total_settled_rounds = total_wins + total_losses
    win_rate = (total_wins / total_settled_rounds) * 100 if total_settled_rounds > 0 else 0.0
    
    # Các panel hiện tại
    header_panel = build_header(border_color=_blue_border_style())
    layout["header"].update(header_panel)
    
    rooms_panel = build_rooms_table(border_color=_blue_border_style())
    layout["content.left"].update(rooms_panel)

    mid_panel = build_mid(border_color=_blue_border_style())
    layout["content.right.mid"].update(mid_panel)
    
    # THÊM DÒNG NÀY - hiển thị bảng thống kê
    stat_panel = build_stat_table(border_color=_blue_border_style())
    layout["content.right.stat"].update(stat_panel)
    
    bet_history_panel = build_bet_table(border_color=_blue_border_style())
    layout["footer"].update(bet_history_panel)

def prompt_settings() -> None:
    """Hiển thị và nhận cấu hình người dùng trước khi bắt đầu. OPTIMIZED: Simplified prompts."""
    global base_bet, multiplier, run_mode, bet_rounds_before_skip, current_bet, pause_after_losses, profit_target, stop_when_profit_reached, stop_loss_target, stop_when_loss_reached, settings
    global SELECTION_CONFIG, auto_bet_enabled
    
    console.print(Rule(f"[bold {MAIN_COLOR}]CẤU HÌNH SUPERIOR DEVIL AVF V4.0[/]", style=MAIN_COLOR))
    
    ab = safe_input(f"[{TEXT_COLOR}]Auto-bet (on/off) [ON]: [/{TEXT_COLOR}]", default="on")
    auto_bet_enabled = str(ab).lower() != "off"
    
    base = safe_input(f"[{TEXT_COLOR}]Số BUILD đặt mỗi ván [1.0]: [/{TEXT_COLOR}]", default="1.0", cast=float)
    base_bet = float(base) if base else 1.0
    current_bet = base_bet

    console.print(f"\n[{TEXT_COLOR}]Chiến lược cược:[/{TEXT_COLOR}]")
    console.print(f"[{ACCENT_COLOR}]1) MARTINGALE (Mặc định)[/{ACCENT_COLOR}]")
    console.print(f"[{ACCENT_COLOR}]2) ANTI-MARTINGALE[/{ACCENT_COLOR}]")
    strategy_choice = safe_input(f"[{TEXT_COLOR}]Chọn [1]: [/{TEXT_COLOR}]", default="1")
    SELECTION_CONFIG["bet_management_strategy"] = "MARTINGALE" if str(strategy_choice).strip() != "2" else "ANTI-MARTINGALE"
    
    m = safe_input(f"[{TEXT_COLOR}]Hệ số nhân [2.0]: [/{TEXT_COLOR}]", default="2.0", cast=float)
    multiplier = float(m) if m else 2.0
    
    settings["algo"] = "DEVILMODE"
    console.print(f"\n[{ACCENT_COLOR} bold]✅ Thuật toán: SUPERIOR DEVIL AVF - SÓNG THẦN (v4.0)[/]")

    s = safe_input(f"[{TEXT_COLOR}]Chống soi (0=tắt) [0]: [/{TEXT_COLOR}]", default="0", cast=int)
    bet_rounds_before_skip = int(s) if s else 0
    
    pl = safe_input(f"[{TEXT_COLOR}]Nghỉ sau thua (0=tắt) [0]: [/{TEXT_COLOR}]", default="0", cast=int)
    pause_after_losses = int(pl) if pl else 0
    
    pt = safe_input(f"[{TEXT_COLOR}]Chốt lỗi (BUILD, enter=bỏ qua): [/{TEXT_COLOR}]", default="")
    if pt and pt.strip():
        profit_target = float(pt)
        stop_when_profit_reached = True
    else:
        profit_target = None
        stop_when_profit_reached = False
        
    sl = safe_input(f"[{TEXT_COLOR}]Cắt lỗ (BUILD, enter=bỏ qua): [/{TEXT_COLOR}]", default="")
    if sl and sl.strip():
        stop_loss_target = float(sl)
        stop_when_loss_reached = True
    else:
        stop_loss_target = None
        stop_when_loss_reached = False

    safe_input(f"[{MAIN_COLOR} bold]Nhấn Enter để bắt đầu...[/{MAIN_COLOR}]", default="")
    run_mode = "AUTO"

def start_threads() -> None:
    """Khởi động các thread WS và Monitor."""
    threading.Thread(target=start_ws, daemon=True).start()
    threading.Thread(target=monitor_loop, daemon=True).start()

def parse_login() -> None:
    """Yêu cầu và phân tích link game để lấy USER_ID và SECRET_KEY."""
    global USER_ID, SECRET_KEY
    console.print(Rule(f"[bold {MAIN_COLOR}]ĐĂNG NHẬP[/]", style=MAIN_COLOR))
    link = safe_input(f"[{TEXT_COLOR}]Dán link trò chơi > [/{TEXT_COLOR}]", default=None)
    
    if not link:
        console.print(f"[{FAILURE_COLOR}]Không nhập link. Thoát.[/]")
        sys.exit(1)
        
    try:
        parsed = urlparse(link)
        params = parse_qs(parsed.query)
        
        temp_uid = params.get('userId', [None])[0] or params.get('uid', [None])[0]
        temp_secret = params.get('secretKey', [None])[0] or params.get('secret', [None])[0]
        
        if temp_uid:
            USER_ID = int(temp_uid)
        SECRET_KEY = temp_secret
        
        if USER_ID is None or SECRET_KEY is None:
             raise ValueError("Missing USER_ID or SECRET_KEY")
             
        console.print(f"[{SUCCESS_COLOR}]✅ Đã đọc: userId={USER_ID}[/]")
    except Exception as e:
        console.print(f"[{FAILURE_COLOR}]Link không hợp lệ. Thoát.[/]")
        log_debug(f"parse_login err: {e}")
        sys.exit(1)

def initialize_risk_assessment() -> None:
    """
    Khởi tạo hệ thống đánh giá rủi ro AVF.
    """
    global room_risk_ema, room_risk_raw, room_risk_assessment
    
    console.print(f"[{PENDING_COLOR}]🔄 Đang khởi tạo hệ thống AVF Risk Assessment...[/]")
    
    # Cập nhật risk assessment ban đầu
    update_all_room_risks()
    
    console.print(f"[{SUCCESS_COLOR}]✅ Hệ thống AVF đã được khởi tạo[/]")

def main() -> None:
    """Hàm chính khởi chạy toàn bộ chương trình. OPTIMIZED: Better performance management."""
    global last_ui_update, last_risk_update, UI_REFRESH_INTERVAL, RISK_UPDATE_INTERVAL
    
    parse_login()
    console.print(f"[{MAIN_COLOR} bold]Loading...[/]")
    prompt_settings()
    console.print(f"[{SUCCESS_COLOR} bold]Bắt đầu kết nối (SUPERIOR DEVIL AVF V4.0)...[/]")

    # Khởi tạo hệ thống đánh giá rủi ro AVF
    initialize_risk_assessment()

    def on_balance_changed(bal, delta, info):
        """Callback khi số dư thay đổi."""
        color = SUCCESS_COLOR if delta >= 0 else FAILURE_COLOR
        console.print(f"[{SUCCESS_COLOR}]⤴️ Balance: [/{SUCCESS_COLOR}][{MAIN_COLOR}]{bal:,.4f}[/] (Δ [{color}]{delta:+.4f}[/])")

    def on_error(msg):
        """Callback khi Balance Poller gặp lỗi."""
        console.print(f"[{FAILURE_COLOR}]Balance error: {msg}[/]")

    # Khởi động Balance Poller
    poller = BalancePoller(
        USER_ID, SECRET_KEY, 
        poll_seconds=max(1, int(BALANCE_POLL_INTERVAL)), 
        on_balance=on_balance_changed, 
        on_error=on_error, 
        on_status=None
    )
    poller.start()
    
    # Khởi động các thread khác
    start_threads()

    # Vòng lặp chính cập nhật UI với refresh rate được tối ưu
    main_layout = make_layout()
    
    # Khởi tạo thời gian cập nhật
    last_ui_update = time.time()
    last_risk_update = time.time()

    with Live(
        main_layout, 
        refresh_per_second=3,  # Further reduced from 4 to 3 FPS
        console=console, 
        screen=True
    ) as live:
        try:
            while not stop_flag:
                current_time = time.time()
                
                # Cập nhật risk assessment mỗi RISK_UPDATE_INTERVAL giây
                if current_time - last_risk_update >= RISK_UPDATE_INTERVAL:
                    update_all_room_risks()
                    last_risk_update = current_time
                
                # Cập nhật UI mỗi UI_REFRESH_INTERVAL giây
                if current_time - last_ui_update >= UI_REFRESH_INTERVAL:
                    update_layout(main_layout)
                    last_ui_update = current_time
                
                time.sleep(0.15)  # Increased sleep to reduce CPU usage
                
            console.print(f"[{MAIN_COLOR} bold]Tool đã dừng.[/]")
        except KeyboardInterrupt:
            console.print(f"[{ACCENT_COLOR}]Thoát bằng người dùng.[/]")
            poller.stop()
            sys.exit(0)
        except Exception as e:
            console.print(f"[{FAILURE_COLOR}]Lỗi: {e}[/]")
            log_debug(f"Main loop error: {e}")
            poller.stop()

if __name__ == "__main__":
    main()