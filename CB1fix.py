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
from datetime import datetime
from urllib.parse import urlparse, parse_qs
from typing import Any, Dict, Tuple, Optional, List, Union

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
base_bet: float = 1.0 # Tiền cược cơ sở
multiplier: float = 2.0 # Hệ số nhân khi Martingale
current_bet: Optional[float] = None # Tiền cược hiện tại
run_mode: str = "AUTO" # Chế độ chạy: AUTO hoặc STAT

# Cấu hình bỏ qua ván
bet_rounds_before_skip: int = 0
_rounds_placed_since_skip: int = 0
skip_next_round_flag: bool = False

bet_history: deque = deque(maxlen=500) # Lịch sử cược (lưu trữ 500 ván)
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

# *** SUPERIOR DEVIL UPGRADE: Change logic name ***
SELECTION_MODES = {
    "DEVILMODE": "SUPERIOR DEVIL - LÁ CHẮN TITAN (v3.0)" # New label
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
            # log_debug(f"Cast error for input '{s}' with type {cast}")
            return default
    return s

# -------------------- BALANCE PARSING & FETCH --------------------
def _parse_balance_from_json(j: Dict[str, Any]) -> Tuple[Optional[float], Optional[float], Optional[float]]:
    """
    Phân tích JSON response từ API ví (wallet) để trích xuất số dư BUILD, WORLD, USDT.
    Hỗ trợ nhiều cấu trúc JSON khác nhau.

    Args:
        j: Dữ liệu JSON từ response API.

    Returns:
        Tuple chứa (build, world, usdt) hoặc None cho các giá trị không tìm thấy.
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
            # Thử các khóa thường là BUILD/Ctoken
            for key in ("ctoken_contribute", "ctoken", "build", "balance", "amount"):
                if key in cwallet and build is None:
                    build = _parse_number(cwallet.get(key))
        # Thử các khóa cấp cao nhất cho BUILD
        for k in ("build", "ctoken", "ctoken_contribute"):
            if build is None and k in data:
                build = _parse_number(data.get(k))
        # Thử các khóa cho USDT
        for k in ("usdt", "kusdt", "usdt_balance"):
            if usdt is None and k in data:
                usdt = _parse_number(data.get(k))
        # Thử các khóa cho WORLD
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

    # Sử dụng kết quả quét để điền vào các giá trị còn thiếu
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
    # Cấu trúc payload chuẩn cho API 3games
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

            # Phân tích số dư
            build, world, usdt = _parse_balance_from_json(j)

            if build is not None:
                if last_balance_val is None:
                    # Thiết lập số dư ban đầu
                    starting_balance = build
                    last_balance_val = build
                else:
                    # Tính toán lợi nhuận tích lũy
                    delta = float(build) - float(last_balance_val)
                    if abs(delta) > 0.000001: # Ngưỡng tối thiểu để ghi nhận thay đổi
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


# -------------------- SUPERIOR DEVIL ENSEMBLE SELECTION --------------------

def _room_features(rid: int) -> Dict[str, float]:
    """
    Tính toán các đặc trưng (features) chi tiết của một phòng để đưa vào mô hình dự đoán.
    Bao gồm các chỉ số thống kê, trạng thái cược, và phân tích bẫy (trap analysis).
    """
    global game_kill_history, round_index, room_state, room_stats, last_killed_room, game_kill_pattern_tracker
    
    st = room_state.get(rid, {})
    stats = room_stats.get(rid, {})
    
    # 1. Dữ liệu thời gian thực (Real-time Data)
    players = float(st.get("players", 0))
    bet = float(st.get("bet", 0))
    bet_per_player = (bet / players) if players > 0 else 0.0 # BPP (Bet Per Player)

    # 2. Dữ liệu lịch sử (Historical Stats)
    kill_count = float(stats.get("kills", 0))
    survive_count = float(stats.get("survives", 0))
    
    # Tránh chia cho 0, làm mượt dữ liệu (Laplace smoothing)
    total_rounds = kill_count + survive_count
    kill_rate = (kill_count + 1.0) / (total_rounds + 2.0) if total_rounds > 0 else 0.5
    survive_score = 1.0 - kill_rate # Tỷ lệ sống lịch sử

    # 3. Phân tích trạng thái thị trường (Market State Analysis)
    all_players = sum(r.get("players", 0) for r in room_state.values())
    all_bet = sum(r.get("bet", 0) for r in room_state.values())
    
    # Chuẩn hóa động (Dynamic Normalization)
    players_norm = players / max(1.0, all_players) # Chuẩn hóa theo tổng người chơi
    bet_norm = bet / max(1.0, all_bet) # Chuẩn hóa theo tổng tiền cược

    # SUPERIOR DEVIL: Contrarian Score (Ưu tiên phòng ít người/cược)
    contrarian_score = 1.0 - (players_norm + bet_norm) / 2.0 

    # 4. Phân tích bẫy (Trap Analysis)
    
    # Recent Kill Penalty (Last 10 rounds of game results) - Phạt phòng ta đã thua gần đây
    recent_pen = 0.0
    for i, rec in enumerate(reversed(list(bet_history))):
        if i >= 10: break
        if rec.get("room") == rid and rec.get("result") == "Thua":
            # Nếu ta cược R và R bị tiêu diệt (thua cược), phạt R
            recent_pen += 0.15 * (1.0 / (i + 1)) # Phạt nặng hơn nếu thua gần hơn
    
    # Last Kill Penalty - Phạt phòng vừa bị tiêu diệt
    last_pen = 0.0
    if last_killed_room == rid and SELECTION_CONFIG.get("avoid_last_kill", True):
        last_pen = 0.45 

    # Safety Score - Điểm an toàn tương đối (không bị tiêu diệt quá nhiều so với các phòng khác)
    total_rounds_stats = sum(r['kills'] + r['survives'] for r in room_stats.values())
    safety_score = 0.5
    if total_rounds_stats > 0:
        safety_score = 1.0 - (kill_count / max(1, total_rounds_stats / 8)) # Chuẩn hóa theo số vòng và số phòng

    # 5. DEVIL Features (Cold, Frequency, BPP Health)
    
    # Cold Room Score (Bonus for not being killed recently)
    last_kill_round = stats.get("last_kill_round")
    cold_room_score = 0.0
    min_rounds_safe = 10.0 # Cần 10 ván để được coi là "lạnh" hoàn toàn
    if last_kill_round is None:
        cold_room_score = 1.0
    else:
        delta = round_index - last_kill_round
        cold_room_score = min(1.0, delta / min_rounds_safe) # Scale 0.0 -> 1.0

    # Recent Kill Frequency Penalty (Penalty for being killed often in last 20 kills)
    recent_kills = game_kill_history.count(rid)
    freq_penalty = min(1.0, recent_kills / SELECTION_CONFIG.get("max_recent_kills", 3.0)) # Phạt max nếu vượt ngưỡng cấu hình

    # BPP Health Score (Bonus for being in a "healthy" BPP range, avoid traps)
    bpp_score = 0.0
    min_h = SELECTION_CONFIG.get("bpp_trap_low", 500.0)
    max_h = SELECTION_CONFIG.get("bpp_trap_high", 4000.0)
    
    if bet_per_player < min_h:
        bpp_score = max(0.0, bet_per_player / min_h) # Tăng từ 0 đến 1.0
    elif bet_per_player > max_h:
        # Giảm từ 1.0 về 0 (ví dụ: max_h = 4000, về 0 ở 8000)
        bpp_score = max(0.0, 1.0 - (bet_per_player - max_h) / max_h) 
    else:
        bpp_score = 1.0 # Vùng khỏe mạnh
        
    # SUPERIOR DEVIL: BPP Deviation (Phạt phòng có BPP quá xa mức trung bình lịch sử)
    historical_bpp_deq = stats.get("historical_bpp")
    bpp_deviation_penalty = 0.0
    if historical_bpp_deq and len(historical_bpp_deq) >= 5:
        avg_bpp = sum(historical_bpp_deq) / len(historical_bpp_deq)
        # Chỉ quan tâm nếu BPP hiện tại cao hơn 2 lần độ lệch chuẩn (hoặc cố định 50%) so với trung bình
        if avg_bpp > 100 and bet_per_player > avg_bpp * 1.5:
             bpp_deviation_penalty = min(1.0, (bet_per_player - avg_bpp * 1.5) / avg_bpp)
        elif avg_bpp > 100 and bet_per_player < avg_bpp * 0.5:
             bpp_deviation_penalty = min(1.0, (avg_bpp * 0.5 - bet_per_player) / avg_bpp)
             
    # SUPERIOR DEVIL: Pattern Avoidance (Phạt phòng vừa bị tiêu diệt hoặc là phòng lặp lại)
    pattern_penalty = 0.0
    kill_seq = game_kill_pattern_tracker.get("kill_seq", deque())
    
    if len(kill_seq) >= 3:
        # Phát hiện mô hình A-B-A hoặc A-B-C-A
        # Ví dụ: 1-2-1 -> nếu phòng là 1, phạt
        if rid == kill_seq[-3] and rid != kill_seq[-2]:
             pattern_penalty = max(pattern_penalty, 0.6) # Phạt nặng cho mô hình lặp 2 ván
        
        # Phát hiện mô hình 1-1-1 (không xảy ra, nhưng nếu có)
        if len(kill_seq) == 5 and all(r == rid for r in kill_seq):
             pattern_penalty = max(pattern_penalty, 0.9) # Siêu nặng

    # 6. Trạng thái cược (Betting State)
    # Tỷ lệ cược/người so với trung bình các phòng
    avg_bpp_all = all_bet / max(1.0, all_players)
    bpp_relative_score = 1.0 - abs(bet_per_player - avg_bpp_all) / max(1.0, avg_bpp_all * 2) # Gần mức trung bình là tốt (score 1.0)
        
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
        "bpp_score": bpp_score, # BPP Health (range check)
        "bpp_deviation_penalty": bpp_deviation_penalty, # BPP quá xa lịch sử
        "pattern_penalty": pattern_penalty, # Tránh mô hình lặp lại
        "bpp_relative_score": bpp_relative_score, # Gần BPP trung bình
    }


def choose_room_devilmode() -> Tuple[int, str]:
    """
    SUPERIOR DEVIL MODE (v3.0) - LÁ CHẮN TITAN
    Logic phòng thủ tiên tiến, tập trung vào việc tính điểm An Toàn (Safety)
    và điểm Bẫy (Trap) một cách rõ ràng để đưa ra quyết định.
    Nó thay thế mô hình ensemble ngẫu nhiên của V2 bằng một mô hình quyết định.
    """
    global game_kill_history, round_index, room_state, room_stats, last_killed_room
    
    # --- V3 PRE-COMPUTATION & FEATURE ENGINEERING ---
    # Giai đoạn này tính toán tất cả các đặc trưng V2 và V3 cho mọi phòng
    # trước khi lọc hoặc tính điểm.
    # -------------------------------------------------
    log_debug("--- SUPERIOR DEVIL V3 PRE-COMPUTATION ---")
    features = {}
    
    # 1. Tính toán trạng thái thị trường chung
    all_players = sum(r.get("players", 0) for r in room_state.values())
    all_bet = sum(r.get("bet", 0) for r in room_state.values())
    avg_players = all_players / max(1, len(ROOM_ORDER))
    avg_bet = all_bet / max(1, len(ROOM_ORDER))
    avg_bpp_all = all_bet / max(1, all_players) # BPP trung bình toàn thị trường

    # 2. Lấy Xếp hạng (Rank) (1 = cao nhất/phổ biến nhất, 8 = thấp nhất)
    player_ranks_sorted = sorted(ROOM_ORDER, key=lambda r: room_state[r].get("players", 0), reverse=True)
    bet_ranks_sorted = sorted(ROOM_ORDER, key=lambda r: room_state[r].get("bet", 0), reverse=True)
    
    # 3. Lấy Thống kê Vùng (Zone Stats) - Phân tích 10 ván giết gần nhất
    recent_10_kills = list(game_kill_history)[-10:]
    low_zone_kills = sum(1 for k in recent_10_kills if k in [1, 2, 3, 4])
    high_zone_kills = sum(1 for k in recent_10_kills if k in [5, 6, 7, 8])

    # 4. Xây dựng bộ đặc trưng (features) cho mỗi phòng
    for r in ROOM_ORDER:
        f = _room_features(r) # Lấy tất cả đặc trưng của V2

        # --- Thêm Đặc trưng V3 ---
        f['player_rank'] = player_ranks_sorted.index(r) + 1
        f['bet_rank'] = bet_ranks_sorted.index(r) + 1
        
        # V3 - Bẫy Cá Voi (Whale Trap)
        # Định nghĩa: <= 3 người chơi VÀ BPP cao gấp 5 lần BPP trung bình (hoặc tối thiểu 3000)
        whale_bpp_threshold = max(3000.0, avg_bpp_all * 5.0)
        f['whale_trap_score'] = 0.0
        if 0 < f['players'] <= 3 and f['bet_per_player'] > whale_bpp_threshold:
            f['whale_trap_score'] = 1.0 # Bẫy cá voi 100%
        
        # V3 - Bẫy Chim Mồi (Decoy Trap)
        # Định nghĩa: Phòng phổ biến thứ 2 hoặc 3 (mục tiêu phổ biến của sát thủ)
        f['decoy_trap_score'] = 1.0 if f['player_rank'] in [2, 3] else 0.0
        
        # V3 - Phạt Vùng Nóng (Zone Penalty)
        # Phạt nếu phòng nằm trong vùng (1-4 hoặc 5-8) đang bị giết nhiều
        f['zone_penalty'] = 0.0
        my_zone = 'low' if r <= 4 else 'high'
        if my_zone == 'low' and low_zone_kills > high_zone_kills:
            # Vùng thấp đang nóng, phạt phòng 1-4
            f['zone_penalty'] = min(1.0, (low_zone_kills - high_zone_kills) / 5.0) # Scale: 5 lần chênh lệch = 1.0
        elif my_zone == 'high' and high_zone_kills > low_zone_kills:
            # Vùng cao đang nóng, phạt phòng 5-8
            f['zone_penalty'] = min(1.0, (high_zone_kills - low_zone_kills) / 5.0)

        features[r] = f
        log_debug(f"V3 Features R{r}: Whale={f['whale_trap_score']:.2f}, Decoy={f['decoy_trap_score']:.2f}, ZonePen={f['zone_penalty']:.2f}")

    # --- PHASE 1: SUPERIOR TITANIUM FILTERING (V3) ---
    # Lọc bỏ các ứng viên không an toàn một cách tuyệt đối
    # -------------------------------------------------
    filtered_cand = []
    
    for r in ROOM_ORDER:
        f = features[r] # Sử dụng bộ đặc trưng đã tính toán
        
        # F1 (V2): Né phòng vừa bị giết
        if SELECTION_CONFIG.get("avoid_last_kill", True) and last_killed_room == r:
            log_debug(f"Filter R{r}: Last killed (F1).")
            continue
        
        # F2 (V2): Tỷ lệ sống tối thiểu
        if f["survive_score"] < SELECTION_CONFIG.get("min_survive_rate", 0.55):
            log_debug(f"Filter R{r}: Low survive rate ({f['survive_score']:.2f}) (F2).")
            continue
        
        # F3 (V2): Bẫy quá đông/cược cao (Dynamic)
        if (f["players"] > avg_players * 1.8) and (f["bet"] > avg_bet * 1.8):
            log_debug(f"Filter R{r}: Overcrowded/High bet (Dynamic Trap F3).")
            continue

        # F4 (V2): Tần suất bị giết gần đây (Hot kill target)
        if f["freq_penalty"] > 0.8: # Bị giết > 4 lần trong 20 ván
            log_debug(f"Filter R{r}: High recent kill freq ({f['freq_penalty']:.2f}) (F4).")
            continue
            
        # F5 (V2): Bẫy BPP (Nằm ngoài vùng BPP khỏe mạnh)
        if f["bpp_score"] < 0.3: 
            log_debug(f"Filter R{r}: Extreme BPP score ({f['bpp_score']:.2f}) (F5).")
            continue

        # F6 (V2): Bẫy BPP Lệch (BPP quá xa lịch sử của chính nó)
        if f["bpp_deviation_penalty"] > 0.5: 
            log_debug(f"Filter R{r}: High BPP Deviation Penalty ({f['bpp_deviation_penalty']:.2f}) (F6).")
            continue
            
        # F7 (V2): Bẫy Mô hình (Tránh lặp lại A-B-A)
        if f["pattern_penalty"] > 0.5: 
            log_debug(f"Filter R{r}: High Pattern Penalty ({f['pattern_penalty']:.2f}) (F7).")
            continue

        # --- V3 ADVANCED FILTERS ---
        # F8 (V3): Lọc Bẫy Cá Voi
        if f['whale_trap_score'] > 0.5:
            log_debug(f"Filter R{r}: Whale Trap detected (F8).")
            continue
        
        # F9 (V3): Lọc Vùng Cực Nóng
        if f['zone_penalty'] > 0.8: # Chỉ lọc nếu vùng đó *cực kỳ* nóng
            log_debug(f"Filter R{r}: Extreme Hot Zone Penalty ({f['zone_penalty']:.2f}) (F9).")
            continue

        filtered_cand.append(r)

    # Fallback: Nếu tất cả đều bị lọc, chọn phòng có Kill Rate thấp nhất
    if not filtered_cand:
        log_debug("All rooms filtered. Fallback to lowest kill rate (excl. last kill).")
        fallback_scores = {r: _room_features(r)["kill_rate"] for r in ROOM_ORDER if r != last_killed_room}
        if not fallback_scores:
             fallback_scores = {r: _room_features(r)["kill_rate"] for r in ROOM_ORDER}
             
        best_room = min(fallback_scores.items(), key=lambda x: x[1])[0]
        return best_room, "SUPERIOR_DEVIL_V3_FALLBACK"

    # --- PHASE 2: Deterministic Scoring (SUPERIOR DEVIL V3) ---
    # Tính điểm các ứng viên còn lại dựa trên mô hình Safety vs Trap
    # Final Score = SafetyScore - TrapScore
    # -----------------------------------------------------------

    agg_scores = {r: 0.0 for r in filtered_cand}
    
    # Trọng số V3 (Có thể điều chỉnh)
    WEIGHTS = {
        # YẾU TỐ AN TOÀN (Càng cao càng tốt)
        "safety_contrarian": 1.5,  # V3: Thưởng mạnh cho việc chống đám đông
        "safety_bpp_health": 1.2,  # V2: Thưởng cho BPP trong vùng khỏe mạnh
        "safety_cold_room": 1.0,   # V2: Thưởng cho phòng "lạnh" (lâu chưa bị giết)
        "safety_survive_hist": 0.5,  # V2: Thưởng cho tỷ lệ sống lịch sử
        "safety_bpp_relative": 0.3,  # V2: Thưởng vì BPP gần mức trung bình thị trường
        
        # YẾU TỐ BẪY (Càng cao càng tệ)
        "trap_decoy": 2.5,       # V3: Phạt nặng bẫy chim mồi (RẤT QUAN TRỌNG)
        "trap_whale": 2.5,       # V3: Phạt nặng bẫy cá voi (RẤT QUAN TRỌNG)
        "trap_bpp_dev": 1.5,     # V2: Phạt nặng BPP lệch khỏi lịch sử của nó
        "trap_freq": 1.5,        # V2: Phạt nặng tần suất bị giết gần đây
        "trap_pattern": 1.2,     # V2: Phạt mô hình lặp lại (A-B-A)
        "trap_zone": 1.0,        # V3: Phạt vì nằm trong vùng nóng
        "trap_last_kill": 0.8,   # V2: Phạt phòng vừa bị giết (nhẹ, vì F1 đã lọc)
    }
    
    log_debug(f"--- SUPERIOR DEVIL V3 Scoring (Candidates: {filtered_cand}) ---")
    
    for r in filtered_cand:
        f = features[r]
        
        # --- Tính Điểm An Toàn ---
        safety_score = 0.0
        safety_score += WEIGHTS["safety_contrarian"] * f["contrarian_score"]
        safety_score += WEIGHTS["safety_bpp_health"] * f["bpp_score"]
        safety_score += WEIGHTS["safety_cold_room"] * f["cold_room_score"]
        safety_score += WEIGHTS["safety_survive_hist"] * f["survive_score"]
        safety_score += WEIGHTS["safety_bpp_relative"] * f["bpp_relative_score"]
        
        # --- Tính Điểm Bẫy ---
        trap_score = 0.0
        trap_score += WEIGHTS["trap_decoy"] * f["decoy_trap_score"]
        trap_score += WEIGHTS["trap_whale"] * f["whale_trap_score"]
        trap_score += WEIGHTS["trap_bpp_dev"] * f["bpp_deviation_penalty"]
        trap_score += WEIGHTS["trap_freq"] * f["freq_penalty"]
        trap_score += WEIGHTS["trap_pattern"] * f["pattern_penalty"]
        trap_score += WEIGHTS["trap_zone"] * f["zone_penalty"]
        trap_score += WEIGHTS["trap_last_kill"] * f["last_pen"]

        # Điểm cuối cùng = An Toàn - Bẫy
        final_score = safety_score - trap_score
        agg_scores[r] = final_score
        
        log_debug(f"Room {r}: Safety={safety_score:.3f}, Trap={trap_score:.3f} -> FINAL={final_score:.3f}")

    # Xếp hạng: điểm cao nhất (An Toàn > Bẫy) là tốt nhất
    ranked = sorted(agg_scores.items(), key=lambda kv: (-kv[1], kv[0]))
    best_room = ranked[0][0]
    
    log_debug(f"V3 FINAL CHOICE: Room {best_room} (Score: {ranked[0][1]:.3f})")
    return best_room, "SUPERIOR_DEVIL_V3"


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
        "killed_room_id": None # THÊM TRƯỜNG LƯU TRỮ PHÒNG BỊ GIẾT
    }
    bet_history.append(rec)
    return rec


def place_bet_async(issue: int, room_id: int, amount: float, algo_used: Optional[str] = None) -> None:
    """Đặt cược không đồng bộ (non-blocking) trong một thread mới."""
    def worker():
        console.print(f"[{PENDING_COLOR}]Đang đặt {amount:,.4f} BUILD -> PHÒNG_{room_id} (v{issue}) — Thuật toán: {algo_used}[/]")
        time.sleep(random.uniform(0.02, 0.25)) # Độ trễ ngẫu nhiên để tránh bị phát hiện
        res = place_bet_http(issue_id, room_id, amount)
        rec = record_bet(issue_id, room_id, amount, res, algo_used=algo_used)
        
        # Kiểm tra response thành công
        if isinstance(res, dict) and (res.get("msg") == "ok" or res.get("code") == 0 or res.get("status") in ("ok", 1) or "success" in str(res).lower()):
            bet_sent_for_issue.add(issue_id)
            console.print(f"[{SUCCESS_COLOR}]✅ Đặt thành công {amount:,.4f} BUILD vào PHÒNG_{room_id} (v{issue_id}).[/]")
        else:
            # Ghi lại lỗi nếu đặt thất bại
            console.print(f"[{FAILURE_COLOR}]❌ Đặt lỗi v{issue_id}: {res}[/]")
            
    threading.Thread(target=worker, daemon=True).start()

# -------------------- LOCK & AUTO-BET (FIXED) --------------------

def lock_prediction_if_needed(force: bool = False) -> None:
    """
    Thực hiện khóa dự đoán và đặt cược tự động nếu điều kiện cho phép.
    Hàm này được gọi khi đếm ngược về ngưỡng đặt cược (<= 10s).
    ĐÃ SỬA: Logic nghỉ sau khi thua và logic chống soi (skip round).
    """
    global prediction_locked, predicted_room, ui_state, current_bet, _rounds_placed_since_skip, skip_next_round_flag, _skip_rounds_remaining, win_streak, lose_streak
    global current_build 
    
    if stop_flag:
        return
    if prediction_locked and not force:
        return
    if issue_id is None:
        return
        
    # --- SỬA LỖI: Ưu tiên xử lý các trạng thái nghỉ (Pause/Skip) và KHÓA ngay ---
    # 1. Xử lý chế độ nghỉ sau khi thua (Pause after losses)
    if _skip_rounds_remaining > 0:
        prediction_locked = True # Khóa lại ngay để không chạy lại logic này trong cùng 1 giây
        ui_state = "IDLE" # Đặt trạng thái UI
        console.print(f"[{ACCENT_COLOR}]⏸️ Đang nghỉ sau khi thua (Còn lại {_skip_rounds_remaining} ván).[/]")
        _skip_rounds_remaining -= 1 # Trừ số ván nghỉ
        return

    # 2. Xử lý chế độ chống soi (Skip next round)
    if skip_next_round_flag:
        prediction_locked = True # Khóa lại ngay
        ui_state = "IDLE"
        console.print(f"[{ACCENT_COLOR}]⏸️ TẠM DỪNG THEO DÕI SÁT THỦ (Cấu hình SKIP 1 ván).[/]")
        skip_next_round_flag = False # Reset cờ skip
        return
    # ---------------------------------------------------------------------------
        
    prediction_locked = True
    ui_state = "PREDICTED"
    
    # *** SUPERIOR DEVIL UPGRADE: Call new logic ***
    chosen, algo_used = choose_room_devilmode()
    predicted_room = chosen
    
    # Đặt cược nếu chế độ AUTO
    if run_mode == "AUTO":
        # Lấy số dư trước khi đặt (non-blocking friendly)
        bld, _, _ = fetch_balances_3games(params={"userId": str(USER_ID)} if USER_ID else None)
        if bld is None:
            console.print(f"[{ACCENT_COLOR}]⚠️ Không lấy được số dư trước khi đặt — bỏ qua đặt ván này.[/]")
            prediction_locked = False
            return
            
        
        # === BET MANAGEMENT LOGIC (MARTINGALE / ANTI-MARTINGALE) ===
        if current_bet is None:
            current_bet = base_bet
        
        # Nếu đang ở chế độ ANTI-MARTINGALE, tăng cược nhẹ sau khi thắng
        strategy = SELECTION_CONFIG.get("bet_management_strategy", "MARTINGALE")
        if strategy == "ANTI-MARTINGALE":
            if win_streak > 0:
                # Tăng cược lũy tiến nhỏ (ví dụ: 10% base_bet cho mỗi chuỗi thắng)
                current_bet = base_bet + (base_bet * 0.1 * win_streak) 
            else:
                current_bet = base_bet
                
        # Đảm bảo cược không nhỏ hơn cược cơ sở
        if current_bet < base_bet:
            current_bet = base_bet

        amt = float(current_bet)
        
        # Kiểm tra số tiền đặt hợp lệ và không vượt quá số dư
        if amt <= 0 or amt > current_build:
            console.print(f"[{FAILURE_COLOR}]⚠️ Số tiền đặt không hợp lệ ({amt:,.4f} > {current_build:,.4f}). Bỏ qua.[/]")
            prediction_locked = False
            return
        
        place_bet_async(issue_id, predicted_room, amt, algo_used=algo_used)
        _rounds_placed_since_skip += 1
        
        # Cập nhật cờ SKIP cho ván *TIẾP THEO*
        if bet_rounds_before_skip > 0 and _rounds_placed_since_skip >= bet_rounds_before_skip:
            skip_next_round_flag = True
            _rounds_placed_since_skip = 0

# -------------------- WEBSOCKET HANDLERS --------------------

def safe_send_enter_game(ws: Optional[websocket.WebSocketApp]) -> None:
    """Gửi yêu cầu tham gia game qua WebSocket."""
    if not ws:
        log_debug("safe_send_enter_game: ws None")
        return
    try:
        # Cấu trúc payload chuẩn
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
    # Thử nhiều khóa khác nhau
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
    console.print(f"[{SUCCESS_COLOR}]ĐANG TRUY CẬP DỮ LIỆU GAME (SUPERIOR DEVIL MODE ON)[/]")
    safe_send_enter_game(ws)


def _background_fetch_balance_after_result() -> None:
    """Fetch số dư trong background sau khi có kết quả ván."""
    try:
        # Cập nhật số dư một lần sau khi có kết quả để tính lại Cumulative Profit
        fetch_balances_3games()
    except Exception:
        pass


def _mark_bet_result_from_issue(res_issue: Optional[int], krid: int) -> None:
    """
    Đánh dấu kết quả cược ngay lập tức trong lịch sử cược (local).
    Cập nhật chuỗi thắng/thua và tiền cược tiếp theo (Martingale/Anti-Martingale).
    
    ĐÃ SỬA: Loại bỏ cập nhật cumulative_profit để ưu tiên Poller.
    """
    global current_bet, win_streak, lose_streak, max_win_streak, max_lose_streak, _skip_rounds_remaining, stop_flag, multiplier, base_bet
    if res_issue is None:
        return
        
    # Tìm cược ta đã đặt trong ván này
    rec = None
    for b in reversed(list(bet_history)):
        if b.get("issue") == res_issue:
            rec = b
            break
            
    if rec is None:
        return
        
    try:
        # --- SỬA LỖI: LƯU TRỮ PHÒNG BỊ GIẾT ---
        rec["killed_room_id"] = int(krid)
        # -------------------------------------
        
        placed_room = int(rec.get("room"))
        placed_amount = float(rec.get("amount"))
        is_win = (placed_room != int(krid)) # Thắng nếu phòng ta đặt không phải phòng bị giết (krid)
        
        # === TÍNH TOÁN LÃI/LỖ (DELTA) ===
        delta = 0.0
        if is_win:
            rec["result"] = "Thắng"
            # Thắng 1:1 -> Lãi ròng = Tiền cược
            delta = placed_amount 
            
            # Cập nhật tiền cược: Martingale -> Reset, Anti-Martingale -> Logic ở lock_prediction_if_needed
            if SELECTION_CONFIG.get("bet_management_strategy") == "MARTINGALE":
                 current_bet = base_bet 
            
            win_streak += 1
            lose_streak = 0
            if win_streak > max_win_streak:
                max_win_streak = win_streak
                
        else:
            rec["result"] = "Thua"
            # Thua -> Lỗ ròng = -Tiền cược
            delta = -placed_amount
            
            # Cập nhật tiền cược: Martingale -> Nhân, Anti-Martingale -> Reset
            if SELECTION_CONFIG.get("bet_management_strategy") == "MARTINGALE":
                try:
                    # Tiền cược tiếp theo = Tiền cược ván này * Hệ số nhân
                    current_bet = placed_amount * float(multiplier)
                except Exception:
                    current_bet = base_bet # Fallback
            else:
                 current_bet = base_bet
                 
            lose_streak += 1
            win_streak = 0
            # FIX: Cập nhật max_lose_streak khi chuỗi thua tăng
            if lose_streak > max_lose_streak:
                max_lose_streak = lose_streak
                
            # Kích hoạt nghỉ sau khi thua (Pause after losses)
            if pause_after_losses > 0:
                _skip_rounds_remaining = pause_after_losses
                
        # Cập nhật delta vào lịch sử cược (Không cập nhật cumulative_profit ở đây)
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
        # Xử lý decode nếu là bytes
        if isinstance(message, bytes):
            try:
                message = message.decode("utf-8", errors="replace")
            except Exception:
                message = str(message)
        
        # Phân tích JSON
        data = None
        try:
            data = json.loads(message)
        except Exception:
            try:
                data = json.loads(message.replace("'", '"'))
            except Exception:
                log_debug(f"on_message non-json: {str(message)[:200]}")
                return

        # Xử lý trường hợp JSON lồng nhau trong khóa 'data'
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
                
            # Cập nhật trạng thái phòng (players, bet)
            for rm in (rooms or []):
                try:
                    rid = int(rm.get("room_id") or rm.get("roomId") or rm.get("id"))
                except Exception:
                    continue
                players = int(rm.get("user_cnt") or rm.get("userCount") or 0) or 0
                bet = float(rm.get("total_bet_amount") or rm.get("totalBet") or rm.get("bet") or 0) or 0
                
                # Cập nhật trạng thái hiện tại
                room_state[rid] = {"players": players, "bet": bet}
                
                # Cập nhật trạng thái trước đó
                room_stats[rid]["last_players"] = players
                room_stats[rid]["last_bet"] = bet
                
                # SUPERIOR DEVIL: Cập nhật BPP lịch sử
                bpp = bet / players if players > 0 else 0.0
                if bpp > 0:
                     stats = room_stats.get(rid)
                     if stats and isinstance(stats.get("historical_bpp"), deque):
                          stats["historical_bpp"].append(bpp)
                          
            if new_issue is not None and new_issue != issue_id:
                # Ván mới bắt đầu -> Chuẩn bị cho dự đoán mới
                log_debug(f"New issue: {issue_id} -> {new_issue}")
                issue_id = new_issue
                issue_start_ts = time.time()
                killed_room = None
                prediction_locked = False
                predicted_room = None
                
                if ui_state == "RESULT":
                     round_index += 1 # Tăng chỉ số ván nếu ván trước đã kết thúc
                
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
                    # Khi <=10s, khóa và đặt cược
                    if count_val <= 10 and not prediction_locked:
                        analysis_blur = False
                        lock_prediction_if_needed()
                    elif count_val <= 45:
                        # Bắt đầu cửa sổ phân tích (45s -> 10s)
                        ui_state = "ANALYZING"
                        analysis_start_ts = time.time()
                        analysis_blur = True # Kích hoạt hiệu ứng "blur"
                except Exception as e:
                    log_debug(f"Countdown logic error: {e}")

        # 3. Thông báo kết quả (result)
        elif msg_type == "notify_result" or "result" in msg_type:
            # Lấy phòng bị tiêu diệt
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
                
                # *** SUPERIOR DEVIL UPGRADE: Store kill history & pattern ***
                game_kill_history.append(krid)
                game_kill_pattern_tracker["kill_seq"].append(krid)
                game_kill_pattern_tracker["kill_counts"][krid] += 1
                game_kill_pattern_tracker["last_kill_ts"] = time.time()
                
                # Cập nhật thống kê kills/survives
                for rid in ROOM_ORDER:
                    if rid == krid:
                        room_stats[rid]["kills"] += 1
                        room_stats[rid]["last_kill_round"] = round_index
                    else:
                        room_stats[rid]["survives"] += 1

                # Đánh dấu kết quả cược local (nhanh chóng)
                res_issue = new_issue if new_issue is not None else issue_id
                _mark_bet_result_from_issue(res_issue, krid)
                
                # Kích hoạt background balance refresh để tính delta & cumulative profit thực tế
                threading.Thread(target=_background_fetch_balance_after_result, daemon=True).start()

            ui_state = "RESULT"

            # Kiểm tra các điều kiện dừng (Take Profit / Stop Loss)
            def _check_stop_conditions():
                global stop_flag, current_build, profit_target, stop_loss_target
                try:
                    # Kiểm tra Take Profit
                    if stop_when_profit_reached and profit_target is not None and isinstance(current_build, (int, float)) and current_build >= profit_target:
                        console.print(f"[{SUCCESS_COLOR} on {MAIN_COLOR}]🎉 MỤC TIÊU LÃI ĐẠT: {current_build:,.4f} >= {profit_target:,.4f}. Dừng tool.[/]")
                        stop_flag = True
                        try:
                            wsobj = _ws.get("ws")
                            if wsobj: wsobj.close()
                        except Exception:
                            pass
                    # Kiểm tra Stop Loss
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
                    
            # Chạy kiểm tra sau 1.2s để đảm bảo thread cập nhật số dư đã hoàn thành
            threading.Timer(1.2, _check_stop_conditions).start()

    except Exception as e:
        log_debug(f"on_message err: {e}")


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
            # Chạy mãi mãi, ping/pong để duy trì kết nối
            ws_app.run_forever(ping_interval=12, ping_timeout=6)
        except Exception as e:
            log_debug(f"start_ws exception: {e}")
        
        # Backoff logic trước khi reconnect
        t = min(backoff + random.random() * 0.5, 30)
        log_debug(f"Reconnect WS after {t}s")
        console.print(f"[{ACCENT_COLOR}]Đã mất kết nối WS. Đang thử kết nối lại sau {t:.1f}s...[/]")
        time.sleep(t)
        backoff = min(backoff * 1.5, 30)

# -------------------- BALANCE POLLER THREAD --------------------

class BalancePoller(threading.Thread):
    """
    Thread chạy ngầm để định kỳ fetch số dư người dùng, đảm bảo số liệu BUILD luôn được cập nhật.
    """
    def __init__(self, uid: Optional[int], secret: Optional[str], poll_seconds: int = 2, on_balance=None, on_error=None, on_status=None):
        super().__init__(daemon=True)
        self.uid = uid
        self.secret = secret
        self.poll_seconds = max(1, int(poll_seconds))
        self._running = True
        self._last_balance_local: Optional[float] = None
        self.on_balance = on_balance # Callback khi số dư thay đổi
        self.on_error = on_error # Callback khi có lỗi fetch
        self.on_status = on_status # Callback cập nhật trạng thái

    def stop(self) -> None:
        """Dừng thread poller."""
        self._running = False

    def run(self) -> None:
        """Logic chính của thread: Định kỳ fetch số dư."""
        if self.on_status:
            self.on_status("Kết nối...")
            
        while self._running and not stop_flag:
            try:
                # Gọi hàm fetch balance
                build, world, usdt = fetch_balances_3games(params={"userId": str(self.uid)} if self.uid else None, uid=self.uid, secret=self.secret)
                
                if build is None:
                    raise RuntimeError("Không đọc được balance từ response")
                    
                delta = 0.0 if self._last_balance_local is None else (build - self._last_balance_local)
                first_time = (self._last_balance_local is None)
                
                # Chỉ kích hoạt callback nếu là lần đầu hoặc số dư thay đổi
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
            
            # Tạm dừng trước khi fetch tiếp
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
        
        # Polling balance dự phòng (ít thường xuyên hơn poller chính)
        if now - last_balance_fetch_ts >= BALANCE_POLL_INTERVAL * 2:
            last_balance_fetch_ts = now
            try:
                fetch_balances_3games(params={"userId": str(USER_ID)} if USER_ID else None)
            except Exception as e:
                log_debug(f"monitor fetch err: {e}")
        
        # Kiểm tra sức khỏe kết nối WS
        if now - last_msg_ts > 8:
            log_debug("No ws msg >8s, send enter_game to keep alive")
            try:
                safe_send_enter_game(_ws.get("ws"))
            except Exception as e:
                log_debug(f"monitor send err: {e}")
                
        if now - last_msg_ts > 20: # Nếu không có tin nhắn trong 20s, buộc reconnect
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

# -------------------- UI (RICH) - BLUE THEME --------------------

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
    """
    tbl = Table.grid(expand=True, padding=(0, 1))
    tbl.add_column(ratio=2)
    tbl.add_column(ratio=1)

    # Dòng 1: Tiêu đề và Thời gian
    left_title = Text.assemble(
        (f"[{MAIN_COLOR} bold]🌐 SUPERIOR DEVIL V3.0 [/]"), 
        (f"[{ACCENT_COLOR}] - {SELECTION_MODES.get(settings.get('algo', ''), settings.get('algo'))}[/]")
    )
    right_time = Text(f"[{TEXT_COLOR}]{datetime.now(tz).strftime('%Y/%m/%d %H:%M:%S')}  •  {_spinner_char()}[/]", style="dim")
    tbl.add_row(Align.left(left_title), Align.right(right_time))

    # Dòng 2: Số dư và Cấu hình
    b = f"{current_build:,.4f}" if isinstance(current_build, (int, float)) else (str(current_build) if current_build is not None else "-")
    u = f"{current_usdt:,.4f}" if isinstance(current_usdt, (int, float)) else (str(current_usdt) if current_usdt is not None else "-")

    # Định dạng Lãi/Lỗ
    pnl_val = cumulative_profit if cumulative_profit is not None else 0.0
    pnl_str = f"{pnl_val:+,.4f}"
    pnl_style = SUCCESS_COLOR if pnl_val > 0 else (FAILURE_COLOR if pnl_val < 0 else PENDING_COLOR)
    
    # Text Lãi/Lỗ và Target
    pnl_text = Text.assemble(
        (f"[{TEXT_COLOR}]Lãi/lỗ tích lũy: [/{TEXT_COLOR}]",), 
        (f"[{pnl_style} bold]{pnl_str}[/]",)
    )
    
    targets = []
    if stop_when_profit_reached and profit_target is not None:
         targets.append(f"[{SUCCESS_COLOR}]🏆 TP@{profit_target:,.2f}[/]")
    if stop_when_loss_reached and stop_loss_target is not None:
         targets.append(f"[{FAILURE_COLOR}]🛡️ SL@{stop_loss_target:,.2f}[/]")
    
    target_text = Text.from_markup(" | ".join(targets))

    # Số dư (FIXED: Hiển thị số dư)
    balance_text = Text.assemble(
         (f"[{TEXT_COLOR}]BUILD: [/{TEXT_COLOR}]",), (f"[{MAIN_COLOR} bold]{b} | [/]",), 
         (f"[{TEXT_COLOR}]USDT: [/{TEXT_COLOR}]",), (f"[{PENDING_COLOR}]{u}[/]")
    )
    
    # Bên phải: PNL và Target
    right_info = Table.grid(padding=(0, 0))
    right_info.add_row(Align.right(pnl_text))
    if targets:
        right_info.add_row(Align.right(target_text))
    
    tbl.add_row(
        Align.left(balance_text), 
        Align.right(right_info)
    )

    panel = Panel(
        tbl, 
        box=box.HEAVY_HEAD, 
        padding=(0,1), 
        border_style=(border_color or _blue_border_style())
    )
    return panel

def build_rooms_table(border_color: Optional[str] = None) -> Panel:
    """
    Xây dựng Panel hiển thị dữ liệu thời gian thực của các phòng.
    """
    t = Table(box=box.MINIMAL_DOUBLE_HEAD, expand=True, title=Text("📊 DỮ LIỆU PHÒNG QUỶ", style=f"bold {MAIN_COLOR}"))
    t.add_column("[#ffffff]ID[/]", justify="center", width=3, style=PENDING_COLOR)
    t.add_column("[#ffffff]Phòng[/]", width=18, style=TEXT_COLOR)
    t.add_column("[#ffffff]Players[/]", justify="right", style=ACCENT_COLOR)
    # CỘT NÀY HIỂN THỊ TỔNG TIỀN CƯỢC (TOTAL BET)
    t.add_column("[#ffffff]Total Bet[/]", justify="right", style=MAIN_COLOR, min_width=12) 
    t.add_column("[#ffffff]Status[/]", justify="center", style=TEXT_COLOR)
    
    # Tính toán trạng thái chung để so sánh (cho BPP Highlight)
    # (Vẫn cần tính toán cho logic AI)
    all_players = sum(r.get("players", 0) for r in room_state.values())
    all_bet = sum(r.get("bet", 0) for r in room_state.values())
    avg_bpp_all = all_bet / max(1.0, all_players)

    for r in ROOM_ORDER:
        st = room_state.get(r, {})
        
        players = st.get("players", 0)
        bet_val = st.get('bet', 0) or 0
        status = ""
        row_style = ""
        
        # Định dạng bet có dấu phẩy để dễ đọc
        bet_fmt = f"{bet_val:,.4f}" 
        
        # Trạng thái
        is_last_kill = False
        try:
            if killed_room is not None and int(r) == int(killed_room):
                status = f"[{FAILURE_COLOR}]☠ KILL[/]"
                row_style = FAILURE_COLOR
                is_last_kill = True
        except Exception:
            pass
            
        try:
            if predicted_room is not None and int(r) == int(predicted_room):
                status = (status + f" [dim]|[/] [{SUCCESS_COLOR}]✓ DỰ ĐOÁN[/]") if status else f"[{SUCCESS_COLOR}]✓ DỰ ĐOÁN[/]"
                if not is_last_kill:
                    row_style = SUCCESS_COLOR 
        except Exception:
            pass
            
        t.add_row(
            str(r), 
            ROOM_NAMES.get(r, f"Phòng {r}"), 
            str(players), 
            bet_fmt, 
            status, 
            style=row_style
        )
        
    return Panel(t, title_align="left", border_style=(border_color or _blue_border_style()), padding=(0, 1))

def build_mid(border_color: Optional[str] = None) -> Panel:
    """Xây dựng Panel giữa (Trạng thái hiện tại: ANALYZING, PREDICTED, RESULT, IDLE)."""
    global analysis_start_ts, analysis_blur
    
    current_border = border_color or _blue_border_style()
    
    if ui_state == "ANALYZING":
        # ------------------ TRẠNG THÁI PHÂN TÍCH ------------------
        lines = []
        lines.append(f"[{PENDING_COLOR} bold]ĐANG PHÂN TÍCH BẪY SÁT THỦ {_spinner_char()}[/]")
        
        cd_val = int(count_down) if count_down is not None else None
        
        if cd_val is not None:
            lines.append(f"[{TEXT_COLOR}]Đếm ngược tới kết quả: [/{TEXT_COLOR}][{MAIN_COLOR} bold]{cd_val}s[/]")
        else:
            lines.append(f"[{ACCENT_COLOR}]Chưa nhận được dữ liệu đếm ngược...[/]")

        if analysis_blur:
            # Animated blocks with Blue/Dark (Hiệu ứng Loading)
            bar_len = 36
            blocks = []
            tbase = int(time.time() * 5)
            for i in range(bar_len):
                val = (tbase + i) % 7
                ch = "█" if val in (0, 1, 2, 3) else "░"
                color = MAIN_COLOR if val % 2 == 0 else ACCENT_COLOR
                blocks.append(f"[{color}]{ch}[/{color}]")
            lines.append("".join(blocks))
            lines.append("")
            lines.append(f"[{MAIN_COLOR} bold]AI ĐANG TÍNH TOÁN 10S CUỐI VÀO BUID (SUPERIOR LOGIC)[/]")
        else:
            lines.append(f"[{TEXT_COLOR}]Waiting for 10s window...[/]")
            
        lines.append(f"[{TEXT_COLOR}]Phòng sát thủ ván trước: [/{TEXT_COLOR}][{FAILURE_COLOR}]{ROOM_NAMES.get(last_killed_room, '-')}[/]")
        
        txt = "\n".join(lines)
        return Panel(
            Align.center(Text.from_markup(txt), vertical="middle"), 
            title=Text("🔥 PHÂN TÍCH SUPERIOR DEVIL", style=f"bold {MAIN_COLOR}"), 
            border_style=current_border, 
            height=9,
            padding=(0, 1)
        )

    elif ui_state == "PREDICTED":
        # ------------------ TRẠNG THÁT DỰ ĐOÁN ------------------
        name = ROOM_NAMES.get(predicted_room, f"Phòng {predicted_room}") if predicted_room else '-'
        
        last_bet_amt_display = f"{current_bet:,.4f}" if isinstance(current_bet, (int, float)) and current_bet is not None else '-'
        
        lines = []
        lines.append(f"[{ACCENT_COLOR} bold]🌐 AI CHỌN: [/][{SUCCESS_COLOR} bold]{name}[/] - KẾT QUẢ DỰ ĐOÁN")
        lines.append(f"[{TEXT_COLOR}]Số đặt: [/{TEXT_COLOR}][{MAIN_COLOR} bold]{last_bet_amt_display} BUILD[/]")
        lines.append(f"[{TEXT_COLOR}]Phòng sát thủ ván trước: [/{TEXT_COLOR}][{FAILURE_COLOR}]{ROOM_NAMES.get(last_killed_room, '-')}[/]")
        lines.append(f"[{TEXT_COLOR}]Chuỗi: [/{TEXT_COLOR}][{SUCCESS_COLOR}]W={win_streak}[/] | [{FAILURE_COLOR}]L={lose_streak}[/]")
        
        cd_val = int(count_down) if count_down is not None else None
        if cd_val is not None:
            lines.append(f"[{TEXT_COLOR}]Đếm ngược tới kết quả: [/{TEXT_COLOR}][{MAIN_COLOR} bold]{cd_val}s[/]")
        
        lines.append(f"[{PENDING_COLOR}]Đang chờ sát thủ ra tay {_spinner_char()}[/]")
        
        txt = "\n".join(lines)
        
        return Panel(
            Align.center(Text.from_markup(txt)), 
            title=Text("🎯 DỰ ĐOÁN SUPERIOR DEVIL", style=f"bold {MAIN_COLOR}"), 
            border_style=current_border, 
            height=9,
            padding=(0, 1)
        )

    elif ui_state == "RESULT":
        # ------------------ TRẠNG THÁI KẾT QUẢ ------------------
        k = ROOM_NAMES.get(killed_room, "-") if killed_room else "-"
        
        # Màu viền phản ánh kết quả cược ván cuối
        border = current_border
        last_result_rec = bet_history[-1] if bet_history else None
        last_result = last_result_rec.get('result') if last_result_rec else None
        
        if last_result == 'Thắng':
            border = SUCCESS_COLOR
            result_line = f"[{SUCCESS_COLOR} bold]✅ THẮNG CƯỢC! Lợi nhuận tích lũy: {cumulative_profit:+.4f} BUILD[/]"
        elif last_result == 'Thua':
            border = FAILURE_COLOR
            result_line = f"[{FAILURE_COLOR} bold]❌ THUA CƯỢC! Lỗ tích lũy: {cumulative_profit:+.4f} BUILD[/]"
        else:
            result_line = f"[{PENDING_COLOR} bold]Kết quả chưa xác định (Ván {issue_id}).[/]"

        lines = []
        lines.append(f"[{FAILURE_COLOR} bold]⚔️ SÁT THỦ ĐÃ VÀO: [/][{PENDING_COLOR} bold]{k}[/]")
        lines.append(result_line)
        lines.append(f"[{TEXT_COLOR}]Chuỗi hiện tại: [/{TEXT_COLOR}][{SUCCESS_COLOR}]W={win_streak}[/] | [{FAILURE_COLOR}]L={lose_streak}[/]")
        lines.append(f"[{TEXT_COLOR}]Cược tiếp theo: [/{TEXT_COLOR}][{MAIN_COLOR} bold]{current_bet:,.4f} BUILD[/]")
        lines.append(f"[{TEXT_COLOR}]Ván chơi tiếp theo: [/{TEXT_COLOR}][{PENDING_COLOR} bold]{(issue_id or 0) + 1}[/]")
        
        txt = "\n".join(lines)
        
        return Panel(
            Align.center(Text.from_markup(txt)), 
            title=Text("🔔 KẾT QUẢ VÁN", style=f"bold {MAIN_COLOR}"), 
            border_style=border, 
            height=9,
            padding=(0, 1)
        )
    
    else:
        # ------------------ TRẠNG THÁI IDLE/KHỞI ĐỘNG ------------------
        lines = []
        if _skip_rounds_remaining > 0:
             lines.append(f"[{ACCENT_COLOR} bold]⏸️ ĐANG NGHỈ SAU THUA ({_skip_rounds_remaining} ván)[/]")
        elif skip_next_round_flag:
             lines.append(f"[{ACCENT_COLOR} bold]⏸️ ĐANG NGHỈ CHỐNG SOI (1 ván)[/]")
        else:
             lines.append(f"[{PENDING_COLOR} bold]--- HỆ THỐNG SUPERIOR DEVIL ĐANG KHỞI ĐỘNG ---[/]")
             
        lines.append(f"[{TEXT_COLOR}]Chờ ván mới...[/]")
        lines.append(f"[{TEXT_COLOR}]Phòng sát thủ ván trước: [/{TEXT_COLOR}][{FAILURE_COLOR}]{ROOM_NAMES.get(last_killed_room, '-')}[/]")
        lines.append(f"[{TEXT_COLOR}]AI chọn: [/{TEXT_COLOR}][{PENDING_COLOR}]{ROOM_NAMES.get(predicted_room, '-') if predicted_room else '-'}[/]")
        # Hiển thị Lãi/Lỗ ngay cả khi IDLE
        profit_style = SUCCESS_COLOR if cumulative_profit >= 0 else FAILURE_COLOR
        lines.append(f"[{TEXT_COLOR}]Lãi/lỗ tích lũy: [/{TEXT_COLOR}][{profit_style} bold]{cumulative_profit:+.4f} BUILD[/]")
        
        txt = "\n".join(lines)
        return Panel(
            Align.center(Text.from_markup(txt)), 
            title=Text("⚙️ TRẠNG THÁI HỆ THỐNG", style=f"bold {MAIN_COLOR}"), 
            border_style=current_border, 
            height=9,
            padding=(0, 1)
        )

def build_bet_table(border_color: Optional[str] = None) -> Panel:
    """
    Xây dựng Panel hiển thị lịch sử cược 10 ván gần nhất.
    ĐÃ SỬA LỖI HIỂN THỊ PHÒNG KILL.
    """
    t = Table(title=Text("📜 LỊCH SỬ CƯỢC (10 VÁN SUPERIOR DEVIL)", style=f"bold {MAIN_COLOR}"), box=box.HEAVY_EDGE, expand=True)
    t.add_column("[#ffffff]Ván[/]", justify="center", no_wrap=True, style=PENDING_COLOR)
    t.add_column("[#ffffff]Phòng Đặt[/]", justify="center", no_wrap=True, style=TEXT_COLOR)
    t.add_column("[#ffffff]Tiền Đặt[/]", justify="right", no_wrap=True, style=MAIN_COLOR)
    t.add_column("[#ffffff]K Q[/]", justify="center", no_wrap=True)
    t.add_column("[#ffffff]Phòng KILL[/]", justify="center", no_wrap=True, style=ACCENT_COLOR) # CỘT SỬA ĐỔI
    t.add_column("[#ffffff]Thuật toán[/]", no_wrap=True, style="dim")
    
    last10 = list(bet_history)[-10:]
    
    for b in reversed(last10):
        issue = str(b.get('issue') or '-')
        placed_room = str(b.get('room') or '-')
        amt = b.get('amount') or 0
        
        amt_fmt = f"{float(amt):,.4f}"
             
        res = str(b.get('result') or '-')
        algo = str(b.get('algo') or '-')
        
        # --- LOGIC SỬA ĐỔI ĐỂ HIỂN THỊ PHÒNG KILL CHÍNH XÁC ---
        killed_id = b.get("killed_room_id")
        killed_room_display = "-"
        kr_style = ACCENT_COLOR # Default color (Xanh Đậm)
        
        if killed_id is not None:
             killed_room_display = ROOM_NAMES.get(killed_id, str(killed_id))
             # Nếu phòng đặt BỊ GIẾT, tô màu đỏ
             if placed_room.isdigit() and int(placed_room) == killed_id:
                  kr_style = FAILURE_COLOR
             else:
                  kr_style = SUCCESS_COLOR # Nếu phòng đặt KHÔNG BỊ GIẾT (Thắng), tô màu xanh

        # 1. Nếu ván HIỆN TẠI đang có kết quả (RESULT UI state)
        if b.get('issue') == issue_id and killed_room is not None and killed_id is None:
             # Đây là ván vừa kết thúc nhưng dữ liệu chưa kịp cập nhật (rất hiếm)
             killed_room_display = ROOM_NAMES.get(killed_room, str(killed_room))
             if placed_room.isdigit() and int(placed_room) == killed_room:
                 kr_style = FAILURE_COLOR
             else:
                 kr_style = SUCCESS_COLOR
        # --- END LOGIC SỬA LỖI ---
        
        # --- ĐỊNH DẠNG KẾT QUẢ ---
        if res.lower().startswith('thắng') or res.lower().startswith('win'):
            res_text = Text(res, style=SUCCESS_COLOR)
        elif res.lower().startswith('thua') or res.lower().startswith('lose'):
            res_text = Text(res, style=FAILURE_COLOR)
        else:
            res_text = Text(res, style=PENDING_COLOR)
            
        t.add_row(
            issue, 
            placed_room, 
            amt_fmt, 
            res_text, 
            Text(killed_room_display, style=kr_style),
            algo
        )
        
    return Panel(t, border_style=(border_color or _blue_border_style()), padding=(0, 1))

def make_layout() -> Layout:
    """Tạo bố cục màn hình chính theo phong cách của ảnh."""
    layout = Layout(name="root")

    # Chia bố cục chính thành 3 hàng: Header, Content, Footer (Bet History)
    layout.split_column(
        Layout(name="header", size=4), 
        Layout(name="content", ratio=4),
        Layout(name="footer", ratio=2) 
    )

    # Chia Content thành 2 cột: Left (Rooms Table) và Right (Mid Panel & Stat)
    # FIX: Tăng ratio cho content.left (Rooms Table) từ 2 lên 3
    layout["content"].split_row(
        Layout(name="content.left", ratio=3), # Rooms Table (RỘNG HƠN)
        Layout(name="content.right", ratio=2) # Hẹp hơn
    )

    # Chia Content Right thành 2 hàng: Mid Panel và Stat Placeholder
    layout["content.right"].split_column(
        Layout(name="content.right.mid", size=9), # Kích thước cố định cho Mid Panel
        Layout(name="content.right.stat_placeholder", ratio=1) # Phần thống kê
    )
    return layout

def update_layout(layout: Layout) -> None:
    """
    Cập nhật nội dung cho bố cục, BAO GỒM THỐNG KÊ MỚI: Tổng W/L và Tỷ lệ Win.
    """
    global max_lose_streak # Đảm bảo biến được sử dụng là global
    
    # --- PHÂN TÍCH THỐNG KÊ MỚI ---
    total_wins = sum(1 for b in bet_history if b.get('result') == 'Thắng')
    total_losses = sum(1 for b in bet_history if b.get('result') == 'Thua')
    total_settled_rounds = total_wins + total_losses
    win_rate = (total_wins / total_settled_rounds) * 100 if total_settled_rounds > 0 else 0.0
    # -------------------------------
    
    # 1. HEADER
    header_panel = build_header(border_color=_blue_border_style())
    layout["header"].update(header_panel)
    
    # 2. CONTENT LEFT (Rooms Table)
    rooms_panel = build_rooms_table(border_color=_blue_border_style())
    layout["content.left"].update(rooms_panel)

    # 3. CONTENT RIGHT MID (Current State/Countdown)
    mid_panel = build_mid(border_color=_blue_border_style())
    layout["content.right.mid"].update(mid_panel)
    
    # 4. FOOTER (Bet History)
    bet_history_panel = build_bet_table(border_color=_blue_border_style())
    layout["footer"].update(bet_history_panel)
    
    # 5. CONTENT RIGHT STAT PLACEHOLDER (Thống kê phụ/Trống)
    pnl_val = cumulative_profit if cumulative_profit is not None else 0.0
    pnl_style = SUCCESS_COLOR if pnl_val > 0 else (FAILURE_COLOR if pnl_val < 0 else PENDING_COLOR)
    
    stat_content = Table.grid(padding=(0,1))
    stat_content.add_column()
    
    # Lấy số dư BUILD hiện tại
    current_build_fmt = f"{current_build:,.4f}" if isinstance(current_build, (int, float)) else '-'
    
    # Hiển thị thông tin chuỗi/rounds
    stat_lines = [
        # THAY ĐỔI: DÒNG THÊM SỐ DƯ BUILD HIỆN TẠI
        f"[{TEXT_COLOR}]Số dư BUILD: [/{TEXT_COLOR}][{TEXT_COLOR} bold]{current_build_fmt} BUILD[/]",
        # --- THÔNG TIN KHÁC ---
        f"[{TEXT_COLOR}]Phiên hiện tại: [/{TEXT_COLOR}][{PENDING_COLOR}]{issue_id or '-'}[/]",
        f"[{TEXT_COLOR}]Tổng ván chơi: [/{TEXT_COLOR}][{MAIN_COLOR} bold]{round_index}[/]",
        f"[{TEXT_COLOR}]Lãi/Lỗ Tích Lũy: [/{TEXT_COLOR}][{pnl_style} bold]{pnl_val:+.4f} BUILD[/]",
        f"[{TEXT_COLOR}]Tổng W/L: [/{TEXT_COLOR}][{SUCCESS_COLOR}]{total_wins}[/]/[{FAILURE_COLOR}]{total_losses}[/]",
        f"[{TEXT_COLOR}]Tỷ lệ Win: [/{TEXT_COLOR}][{MAIN_COLOR} bold]{win_rate:.2f}%[/]",
        # DÒNG ĐÃ THAY THẾ (GỘP MAX W/L)
        f"[{TEXT_COLOR}]MAX W/L: [/{TEXT_COLOR}][{SUCCESS_COLOR}]{max_win_streak}[/]/[{FAILURE_COLOR}]{max_lose_streak}[/]",
    ]
    stat_content.add_row(Align.left(Text.from_markup("\n".join(stat_lines))))

    layout["content.right.stat_placeholder"].update(Panel(
        stat_content,
        title=Text("📈 THỐNG KÊ HOẠT ĐỘNG", style=f"bold {ACCENT_COLOR}"),
        height=9, 
        border_style=_blue_border_style(),
        padding=(0, 1)
    ))


# -------------------- SETTINGS & START --------------------

def prompt_settings() -> None:
    """Hiển thị và nhận cấu hình người dùng trước khi bắt đầu."""
    global base_bet, multiplier, run_mode, bet_rounds_before_skip, current_bet, pause_after_losses, profit_target, stop_when_profit_reached, stop_loss_target, stop_when_loss_reached, settings
    global SELECTION_CONFIG
    
    console.print(Rule(f"[bold {MAIN_COLOR}]CẤU HÌNH SUPERIOR DEVIL (V3.0)[/]", style=MAIN_COLOR))
    
    # 1. Cược cơ sở
    base = safe_input(f"[{TEXT_COLOR}]Số BUILD đặt mỗi ván (>=1.0): [/{TEXT_COLOR}]", default="1.0", cast=float)
    try:
        base_bet = float(base)
    except Exception:
        base_bet = 1.0
    current_bet = base_bet

    # 2. Chiến lược cược
    console.print(f"\n[{TEXT_COLOR} bold]Chọn Chiến lược Quản lý Cược:[/{TEXT_COLOR}]")
    console.print(f"[{ACCENT_COLOR}]1) MARTINGALE (Mặc định):[/{ACCENT_COLOR}] Nhân tiền khi thua (hạn chế chuỗi thua).")
    console.print(f"[{ACCENT_COLOR}]2) ANTI-MARTINGALE:[/{ACCENT_COLOR}] Tăng nhẹ tiền khi thắng (tối đa hóa lợi nhuận).")
    strategy_choice = safe_input(f"[{TEXT_COLOR}]Chọn (1/2): [/{TEXT_COLOR}]", default="1")
    if str(strategy_choice).strip() == "2":
        SELECTION_CONFIG["bet_management_strategy"] = "ANTI-MARTINGALE"
    else:
        SELECTION_CONFIG["bet_management_strategy"] = "MARTINGALE"
    
    # 3. Hệ số nhân Martingale
    m = safe_input(f"[{TEXT_COLOR}]Nhập 1 số nhân sau khi thua (ổn định thì 2): [/{TEXT_COLOR}]", default="2.0", cast=float)
    try:
        multiplier = float(m)
    except Exception:
        multiplier = 2.0
    
    # 4. Thuật toán (Đã cố định)
    settings["algo"] = "DEVILMODE"
    console.print(f"\n[{ACCENT_COLOR} bold]✅ Thuật toán: SUPERIOR DEVIL - LÁ CHẮN TITAN (v3.0) (Cố định)[/]")

    # 5. Skip rounds (Chống soi)
    s = safe_input(f"[{TEXT_COLOR}]Chống soi: sau bao nhiêu ván đặt thì nghỉ 1 ván: [/{TEXT_COLOR}]", default="0", cast=int)
    try:
        bet_rounds_before_skip = int(s)
    except Exception:
        bet_rounds_before_skip = 0
    
    # 6. Pause after losses (Nghỉ sau khi thua)
    pl = safe_input(f"[{TEXT_COLOR}]Nếu thua thì nghỉ bao nhiêu tay trước khi cược lại (ví dụ 2): [/{TEXT_COLOR}]", default="0", cast=int)
    try:
        pause_after_losses = int(pl)
    except Exception:
        pause_after_losses = 0
    
    # 7. Take Profit
    pt = safe_input(f"[{TEXT_COLOR}]Lãi bao nhiêu thì chốt (BUILD, không dùng enter để bỏ qua): [/{TEXT_COLOR}]", default="")
    try:
        if pt and pt.strip() != "":
            profit_target = float(pt)
            stop_when_profit_reached = True
        else:
            profit_target = None
            stop_when_profit_reached = False
    except Exception:
        profit_target = None
        stop_when_profit_reached = False
        
    # 8. Stop Loss
    sl = safe_input(f"[{TEXT_COLOR}]Lỗ bao nhiêu thì chốt (BUILD, không dùng enter để bỏ qua): [/{TEXT_COLOR}]", default="")
    try:
        if sl and sl.strip() != "":
            stop_loss_target = float(sl)
            stop_when_loss_reached = True
        else:
            stop_loss_target = None
            stop_when_loss_reached = False
    except Exception:
        stop_loss_target = None
        stop_when_loss_reached = False

    # 9. Chế độ chạy
    runm = safe_input(f"[{MAIN_COLOR} bold]💯bạn đã sẵn sàng hãy nhấn enter để bắt đầu💯: [/{MAIN_COLOR}]", default="AUTO")
    run_mode = str(runm).upper()

def start_threads() -> None:
    """Khởi động các thread WS và Monitor."""
    threading.Thread(target=start_ws, daemon=True).start()
    threading.Thread(target=monitor_loop, daemon=True).start()

def parse_login() -> None:
    """Yêu cầu và phân tích link game để lấy USER_ID và SECRET_KEY."""
    global USER_ID, SECRET_KEY
    console.print(Rule(f"[bold {MAIN_COLOR}]ĐĂNG NHẬP[/]", style=MAIN_COLOR))
    link = safe_input(f"[{TEXT_COLOR}]Dán link trò chơi (từ xworld.info) tại đây (ví dụ chứa userId & secretKey) > [/{TEXT_COLOR}]", default=None)
    
    if not link:
        console.print(f"[{FAILURE_COLOR}]Không nhập link. Thoát.[/]")
        sys.exit(1)
        
    try:
        parsed = urlparse(link)
        params = parse_qs(parsed.query)
        
        # Thử tìm ID/Key từ các khóa phổ biến
        temp_uid = params.get('userId', [None])[0] or params.get('uid', [None])[0]
        temp_secret = params.get('secretKey', [None])[0] or params.get('secret', [None])[0]
        
        if temp_uid:
            USER_ID = int(temp_uid)
        SECRET_KEY = temp_secret
        
        if USER_ID is None or SECRET_KEY is None:
             raise ValueError("Missing USER_ID or SECRET_KEY")
             
        console.print(f"[{SUCCESS_COLOR}]✅ Đã đọc: userId={USER_ID}[/]")
    except Exception as e:
        console.print(f"[{FAILURE_COLOR}]Link không hợp lệ. Vui lòng kiểm tra lại link đã dán có chứa userId và secretKey. Thoát.[/]")
        log_debug(f"parse_login err: {e}")
        sys.exit(1)

def main() -> None:
    """Hàm chính khởi chạy toàn bộ chương trình."""
    parse_login()
    console.print(f"[{MAIN_COLOR} bold]Loading...[/]")
    prompt_settings()
    console.print(f"[{SUCCESS_COLOR} bold]Bắt đầu kết nối dữ liệu (SUPERIOR DEVIL V3.0)...[/]")

    def on_balance_changed(bal, delta, info):
        """Callback khi số dư thay đổi."""
        color = SUCCESS_COLOR if delta >= 0 else FAILURE_COLOR
        console.print(f"[{SUCCESS_COLOR}]⤴️ cập nhật số dư: [/{SUCCESS_COLOR}][{MAIN_COLOR}]{bal:,.4f}[/] (Δ [{color}]{delta:+.4f}[/]) — [{PENDING_COLOR}]{info.get('ts')}[/]")

    def on_error(msg):
        """Callback khi Balance Poller gặp lỗi."""
        console.print(f"[{FAILURE_COLOR}]Balance poll lỗi: {msg}[/]")

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

    # Vòng lặp chính cập nhật UI
    main_layout = make_layout()

    with Live(
        main_layout, 
        refresh_per_second=8, 
        console=console, 
        screen=True # Rất quan trọng để hiển thị Layout đúng
    ) as live:
        try:
            while not stop_flag:
                update_layout(main_layout)
                time.sleep(0.12) # Cập nhật UI khoảng 8 lần/giây
            console.print(f"[{MAIN_COLOR} bold]Tool đã dừng theo yêu cầu hoặc đạt mục tiêu.[/]")
        except KeyboardInterrupt:
            console.print(f"[{ACCENT_COLOR}]Thoát bằng người dùng.[/]")
            poller.stop()
            sys.exit(0) # Thoát hẳn chương trình
        except Exception as e:
            console.print(f"[{FAILURE_COLOR}]Lỗi nghiêm trọng trong vòng lặp chính: {e}[/]")
            log_debug(f"Main loop error: {e}")
            poller.stop()

if __name__ == "__main__":
    main()
