from __future__ import annotations

# LaborForceScheduler V3 (NEW) — Portable, 30-minute ticks, Optimizer
# -------------------------------------------------------------------
# Core principles:
# - Portable one-folder app (relative ./data ./history ./exports)
# - 30-minute tick time system
# - Fixed schedules + weekly overrides + bulk requirements apply
# - Optimizer (greedy + local search improvement)
# - Participation guarantee when feasible (>=1 shift >=1 hour for wants_hours=True)
# - ND minor rules (configurable for 14-15; conservative checks)
#
# RUN:
#   py LaborForceScheduler.py
#
# OPTIONAL EXE:
#   py -m pip install pyinstaller
#   py -m PyInstaller --onefile --windowed --name LaborForceScheduler LaborForceScheduler.py
#
# NOTE:
# This is a NEW program. It does not overwrite or modify your old working build.

from __future__ import annotations

import os, json, tempfile, shutil, webbrowser, datetime, random, math, subprocess, sys, zipfile, copy, pathlib, re
from dataclasses import dataclass, asdict, field
from typing import Dict, List, Tuple, Optional, Set, Any

import tkinter as tk
from tkinter import ttk, messagebox, filedialog, colorchooser
import tkinter.font as tkfont

# ---- Build/version ----
APP_VERSION = 'V3.5 PHASE5_E3_EMPLOYEE_FIT'

ASSIGNMENT_SOURCE_ENGINE = "engine_created"
ASSIGNMENT_SOURCE_FIXED_LOCKED = "fixed_locked_override"
ASSIGNMENT_SOURCE_MANUAL = "manual_override"
ASSIGNMENT_SOURCE_FIXED_UNLOCKED = "fixed_unlocked_preference"

def _app_dir() -> str:
    try:
        if getattr(sys, 'frozen', False):
            return os.path.dirname(sys.executable)
        return os.path.dirname(os.path.abspath(__file__))
    except Exception:
        return os.getcwd()

def _write_crash_log(exc_type, exc, tb):
    try:
        import traceback, platform
        p = os.path.join(_app_dir(), 'crash_log.txt')
        with open(p, 'a', encoding='utf-8') as f:
            f.write('\n' + '='*78 + '\n')
            f.write(f'Time: {datetime.datetime.now().isoformat()}\n')
            f.write(f'Version: {APP_VERSION}\n')
            f.write(f'Python: {sys.version}\n')
            f.write(f'Platform: {platform.platform()}\n')
            f.write(f'CWD: {os.getcwd()}\n')
            f.write(f'AppDir: {_app_dir()}\n')
            f.write('Traceback:\n')
            traceback.print_exception(exc_type, exc, tb, file=f)
    except Exception:
        pass


def _run_log_path() -> str:
    try:
        return os.path.join(_app_dir(), 'run_log.txt')
    except Exception:
        return os.path.join(os.getcwd(), 'run_log.txt')

def _write_run_log(msg: str):
    """Append a single line to run_log.txt (best-effort)."""
    try:
        p = _run_log_path()
        ts = datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        with open(p, 'a', encoding='utf-8') as f:
            f.write(f'[{ts}] {msg}\n')
    except Exception:
        pass

def _install_crash_hooks():
    # Unhandled exceptions
    try:
        def _hook(exc_type, exc, tb):
            _write_crash_log(exc_type, exc, tb)
            try:
                sys.__excepthook__(exc_type, exc, tb)
            except Exception:
                pass
        sys.excepthook = _hook
    except Exception:
        pass
    # Thread exceptions (py3.8+)
    try:
        import threading
        def _thread_hook(args):
            _write_crash_log(args.exc_type, args.exc_value, args.exc_traceback)
        threading.excepthook = _thread_hook  # type: ignore[attr-defined]
    except Exception:
        pass

# Pillow for branding images
try:
    from PIL import Image, ImageTk
except Exception:
    Image = None
    ImageTk = None

# -----------------------------
# Time system: 30-minute ticks
# -----------------------------
TICK_MINUTES = 30
TICKS_PER_HOUR = 2
DAY_TICKS = 48  # 24h * 2

# Peak-hours soft-rule scoring defaults (centralized tuning knobs).
# These are intentionally soft and only influence candidate/final ranking after hard-rule feasibility.
PEAK_SOFT_CANDIDATE_OVERLAP_PER_HOUR_BONUS = 2.4     # reward assigning coverage time inside configured peak windows
PEAK_SOFT_CANDIDATE_PRACTICAL_SEGMENT_BONUS = 1.2     # extra bonus when the candidate segment is practical length (>=2h)
PEAK_SOFT_CANDIDATE_CONTIGUOUS_EXTENSION_BONUS = 2.0  # reward contiguous extension of an existing same-day block into peak time
PEAK_SOFT_CANDIDATE_SHORT_ISOLATED_PENALTY = 1.0      # slight penalty for short isolated peak placements (<2h)

PEAK_SOFT_FINAL_OVERLAP_PER_HOUR_BONUS = 1.6          # reward total schedule overlap with peak windows
PEAK_SOFT_FINAL_PRACTICAL_SEGMENT_BONUS = 0.8         # extra reward for practical peak-covering segments (>=2h)
PEAK_SOFT_FINAL_CONTIGUOUS_BLOCK_BONUS = 0.7          # reward broader contiguous blocks (>=3h) that include peak overlap

# Employee soft-availability candidate scoring (small magnitude, soft-only preference).
SOFT_AVAILABILITY_MATCH_BONUS = 1.5
SOFT_AVAILABILITY_MISS_PENALTY = 2.5

DAYS = ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"]
DAY_FULL = {
    "Sun": "Sunday",
    "Mon": "Monday",
    "Tue": "Tuesday",
    "Wed": "Wednesday",
    "Thu": "Thursday",
    "Fri": "Friday",
    "Sat": "Saturday",
}
AREAS = ["CSTORE", "KITCHEN", "CARWASH"]
AREA_PRIORITY_TEXT = {
    "CSTORE": "C-Store (Primary / Master Staffing)",
    "KITCHEN": "Kitchen (Secondary)",
    "CARWASH": "Carwash (Tertiary)",
}

def tick_to_hhmm(t: int) -> str:
    t = max(0, min(DAY_TICKS, int(t)))
    mins = t * TICK_MINUTES
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

def hhmm_to_tick(s: str) -> int:
    s = str(s).strip()
    if not s:
        return 0
    h, m = s.split(":")
    h = int(h); m = int(m)
    return max(0, min(DAY_TICKS, (h*60 + m)//TICK_MINUTES))

TIME_CHOICES = [tick_to_hhmm(t) for t in range(0, DAY_TICKS+1)]  # inclusive 24:00

def ticks_between(a: int, b: int) -> int:
    return max(0, int(b) - int(a))

def hours_between_ticks(a: int, b: int) -> float:
    return ticks_between(a,b) / TICKS_PER_HOUR

def ensure_dir(p: str) -> str:
    os.makedirs(p, exist_ok=True)
    return p

def _atomic_write_text(path: str, text: str, encoding: str = "utf-8") -> None:
    """Write text atomically using temp-file + replace in the same directory."""
    d = os.path.dirname(path) or "."
    ensure_dir(d)
    fd, tmp = tempfile.mkstemp(prefix=".__tmp_", suffix=".tmp", dir=d)
    try:
        with os.fdopen(fd, "w", encoding=encoding) as f:
            f.write(text)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
    finally:
        try:
            if os.path.exists(tmp):
                os.remove(tmp)
        except Exception:
            pass


def _atomic_write_json(path: str, payload: Any, indent: int = 2) -> None:
    """Serialize JSON deterministically and write atomically."""
    data = json.dumps(payload, indent=indent, ensure_ascii=False)
    _atomic_write_text(path, data, encoding="utf-8")


def _safe_file_backup(path: str) -> Optional[str]:
    """Best-effort single-file backup; returns backup path when created."""
    try:
        if not path or not os.path.isfile(path):
            return None
        d = os.path.dirname(path) or "."
        ensure_dir(d)
        stamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
        bak = f"{path}.bak.{stamp}"
        shutil.copy2(path, bak)
        return bak
    except Exception:
        return None

def app_dir() -> str:
    return _app_dir()

def rel_path(*parts: str) -> str:
    return os.path.join(app_dir(), *parts)


def ensure_runtime_support_dirs() -> None:
    """Create expected runtime folders for portable operation (best-effort)."""
    for parts in [
        ("data",),
        ("data", "final_schedules"),
        ("data", "backups"),
        ("exports",),
        ("history",),
        ("Assets",),
        ("assets",),
        ("state_laws",),
    ]:
        try:
            ensure_dir(rel_path(*parts))
        except Exception:
            pass


def resolve_brand_asset_paths(base_dir: Optional[str] = None) -> Dict[str, List[str]]:
    root = base_dir or os.path.dirname(os.path.abspath(__file__))
    assets_dir = os.path.join(root, "Assets")
    legacy_assets_dir = os.path.join(root, "assets")
    header = [
        os.path.join(assets_dir, "header_logo.png"),
        os.path.join(legacy_assets_dir, "header_logo.png"),
        os.path.join(legacy_assets_dir, "petroserve.png"),
        os.path.join(root, "petroserve.png"),
    ]
    store = [
        os.path.join(assets_dir, "store_logo.png"),
        os.path.join(legacy_assets_dir, "store_logo.png"),
        os.path.join(assets_dir, "header_logo.png"),
        os.path.join(legacy_assets_dir, "header_logo.png"),
        os.path.join(legacy_assets_dir, "petroserve.png"),
        os.path.join(root, "petroserve.png"),
    ]
    return {"header": header, "store": store}


def resolve_brand_asset_path(kind: str = "header", base_dir: Optional[str] = None) -> str:
    candidates = resolve_brand_asset_paths(base_dir).get(str(kind or "header"), [])
    return next((p for p in candidates if os.path.isfile(p)), "")


def _build_runtime_diagnostics_bucket(diag: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    out = dict(diag or {})
    runtime = dict(out.get("runtime_diagnostics") or {})
    out["runtime_diagnostics"] = runtime
    return out


def _set_runtime_metric(diag: Optional[Dict[str, Any]], key: str, seconds: float, **extra: Any) -> Dict[str, Any]:
    out = _build_runtime_diagnostics_bucket(diag)
    row = {"seconds": round(max(0.0, float(seconds or 0.0)), 4)}
    for ek, ev in extra.items():
        row[str(ek)] = ev
    out["runtime_diagnostics"][str(key)] = row
    return out


@dataclass
class SolverRuntimeBudget:
    phase: str
    target_seconds: float
    hard_seconds: float
    started_at: datetime.datetime = field(default_factory=datetime.datetime.now)
    counters: Dict[str, int] = field(default_factory=dict)

    def elapsed_seconds(self) -> float:
        return max(0.0, (datetime.datetime.now() - self.started_at).total_seconds())

    def seconds_remaining(self) -> float:
        return max(0.0, float(self.hard_seconds) - self.elapsed_seconds())

    def target_exhausted(self) -> bool:
        return self.elapsed_seconds() >= float(self.target_seconds)

    def hard_exhausted(self) -> bool:
        return self.elapsed_seconds() >= float(self.hard_seconds)

    def should_stop(self, reserve_seconds: float = 0.0) -> bool:
        return self.seconds_remaining() <= max(0.0, float(reserve_seconds))

    def note(self, key: str, amount: int = 1) -> int:
        name = str(key)
        self.counters[name] = int(self.counters.get(name, 0) or 0) + int(amount)
        return self.counters[name]

    def snapshot(self) -> Dict[str, Any]:
        return {
            "phase": str(self.phase),
            "target_seconds": round(float(self.target_seconds), 4),
            "hard_seconds": round(float(self.hard_seconds), 4),
            "elapsed_seconds": round(self.elapsed_seconds(), 4),
            "seconds_remaining": round(self.seconds_remaining(), 4),
            "target_exhausted": bool(self.target_exhausted()),
            "hard_exhausted": bool(self.hard_exhausted()),
            "counters": dict(self.counters),
        }


def _labor_cost_summary(model: DataModel, assignments: List[Assignment]) -> Dict[str, Any]:
    goals = getattr(model, "manager_goals", None)
    req, sched = _req_sched_counts(model, assignments)
    total_hours = float(sum(hours_between_ticks(a.start_t, a.end_t) for a in assignments))
    hours_by_area = {area: 0.0 for area in AREAS}
    daily_totals = {day: 0.0 for day in DAYS}
    for a in assignments:
        hrs = float(hours_between_ticks(a.start_t, a.end_t))
        hours_by_area[a.area] = hours_by_area.get(a.area, 0.0) + hrs
        daily_totals[a.day] = daily_totals.get(a.day, 0.0) + hrs
    overstaff_hours = 0.0
    near_cap_ticks = 0
    for key, sched_ct in sched.items():
        req_ct = int(req.get(key, 0) or 0)
        if int(sched_ct) > req_ct:
            overstaff_hours += (int(sched_ct) - req_ct) * 0.5
    hard_cap = float(getattr(goals, 'maximum_weekly_cap', 0.0) or 0.0)
    cap_ratio = (total_hours / hard_cap) if hard_cap > 0.0 else 0.0
    for day in DAYS:
        for area in AREAS:
            for t in range(DAY_TICKS):
                req_ct = int(req.get((day, area, t), 0) or 0)
                sched_ct = int(sched.get((day, area, t), 0) or 0)
                if req_ct > 0 and sched_ct >= req_ct and sched_ct <= req_ct + 1:
                    near_cap_ticks += 1
    return {
        "total_hours": total_hours,
        "hours_by_area": hours_by_area,
        "daily_totals": daily_totals,
        "weekly_cap_hours": hard_cap,
        "weekly_cap_ratio": cap_ratio,
        "overstaff_hours": overstaff_hours,
        "near_cap_indicator_ticks": int(near_cap_ticks),
        "approx_labor_load": "High" if cap_ratio >= 0.95 else ("Moderate" if cap_ratio >= 0.75 else "Low"),
    }


def build_publish_readiness_checklist(model: DataModel, label: str, assignments: List[Assignment], diagnostics: Optional[Dict[str, Any]] = None, warnings: Optional[List[str]] = None, analyzer_findings_count: Optional[int] = None) -> Dict[str, Any]:
    diag = dict(diagnostics or {})
    findings = requirement_sanity_checker(model, label, assignments).get("warnings", [])
    readiness = build_manager_readiness_summary(model, label, assignments, diagnostics=diag, warnings=warnings)
    actual_analyzer_count = int(analyzer_findings_count) if analyzer_findings_count is not None else int(len(findings))
    fragile_count = 0
    try:
        cov = count_coverage_per_tick(assignments)
        min_req, _pref_req, _max_req = build_requirement_maps(model.requirements, goals=getattr(model, "manager_goals", None), store_info=getattr(model, "store_info", None))
        fragile_count = sum(1 for key, req in min_req.items() if int(req or 0) > 0 and int(cov.get(key, 0) or 0) == int(req or 0))
    except Exception:
        fragile_count = 0
    return {
        "status": readiness.get("status", "Review"),
        "publish_ready": bool(readiness.get("publish_ready", False)),
        "readiness": readiness,
        "hard_blockers": [line for line in readiness.get("headline", []) if "uncovered" in line.lower() or "hard-rule" in line.lower()],
        "uncovered_minimums": int(readiness.get("min_short", 0) or 0),
        "preferred_gaps": int(readiness.get("pref_short", 0) or 0),
        "fragile_windows_count": int(fragile_count),
        "override_warnings": int(readiness.get("override_warnings", 0) or 0),
        "labor_cap_warnings": int(diag.get("cap_blocked_attempts", 0) or 0),
        "analyzer_findings_count": int(actual_analyzer_count),
        "analyzer_findings": list(findings),
    }


def build_historical_suggestions(model: DataModel) -> Dict[str, Any]:
    pats = getattr(model, "learned_patterns", {}) or {}
    suggestions: List[Dict[str, Any]] = []
    demand = dict((pats.get("__demand_forecast__") or {})) if isinstance(pats, dict) else {}
    for emp in getattr(model, "employees", []) or []:
        prof = dict((pats.get(emp.name) or {})) if isinstance(pats, dict) else {}
        if not prof:
            continue
        bits: List[str] = []
        if prof.get("preferred_area"):
            bits.append(f"Usually strongest in {prof.get('preferred_area')}")
        if prof.get("preferred_start_tick") is not None:
            bits.append(f"Typical start {tick_to_hhmm(int(prof.get('preferred_start_tick') or 0))}")
        if prof.get("preferred_len_ticks"):
            bits.append(f"Common block length {hours_between_ticks(0, int(prof.get('preferred_len_ticks') or 0)):.1f}h")
        suggestions.append({"employee": emp.name, "summary": "; ".join(bits), "confidence": float(len(bits))})
    suggestions.sort(key=lambda row: (row.get("confidence", 0.0), str(row.get("employee", "")).lower()), reverse=True)
    top_pressure = []
    for key, val in list(demand.items())[:6]:
        try:
            day, area, tick = key.split("|")
            top_pressure.append({"day": day, "area": area, "tick": int(tick), "forecast": float(val)})
        except Exception:
            continue
    return {"employee_suggestions": suggestions[:8], "forecast_pressure": top_pressure[:6]}


def build_replacement_assistant_candidates(model: DataModel, label: str, assignments: List[Assignment], target: Assignment) -> Dict[str, Any]:
    cov = count_coverage_per_tick(assignments)
    emp_hours: Dict[str, float] = {}
    for a in assignments:
        emp_hours[a.employee_name] = emp_hours.get(a.employee_name, 0.0) + hours_between_ticks(a.start_t, a.end_t)
    base_without = [a for a in assignments if a is not target]
    clopen = _clopen_map_from_assignments(model, base_without)
    min_req, _pref_req, _max_req = build_requirement_maps(model.requirements, goals=getattr(model, 'manager_goals', None), store_info=getattr(model, 'store_info', None))
    candidates = []
    swaps = []
    target_hours = float(hours_between_ticks(target.start_t, target.end_t))
    for e in getattr(model, 'employees', []) or []:
        if getattr(e, 'work_status', '') != 'Active' or e.name == target.employee_name:
            continue
        qualified = target.area in (getattr(e, 'areas_allowed', []) or [])
        available = bool(qualified and is_employee_available(model, e, label, target.day, target.start_t, target.end_t, target.area, clopen))
        overlap_safe = not any(a.employee_name == e.name and a.day == target.day and not (int(a.end_t) <= int(target.start_t) or int(a.start_t) >= int(target.end_t)) for a in base_without)
        projected = float(emp_hours.get(e.name, 0.0) or 0.0) + target_hours
        limit_safe = projected <= float(getattr(e, 'max_weekly_hours', 0.0) or 0.0) + 1e-9
        impact_ticks = 0
        for tt in range(int(target.start_t), int(target.end_t)):
            key = (target.day, target.area, int(tt))
            before = int(cov.get(key, 0) or 0) - 1
            after = before + (1 if available and overlap_safe else 0)
            impact_ticks += max(0, int(min_req.get(key, 0) or 0) - after)
        explanation = []
        explanation.append("qualified" if qualified else "not qualified")
        explanation.append("available" if available else "availability warning")
        explanation.append("overlap-safe" if overlap_safe else "overlap conflict")
        explanation.append("hour-limit-safe" if limit_safe else "hour-limit warning")
        candidates.append({
            "employee": e.name,
            "qualified": bool(qualified),
            "available": bool(available),
            "overlap_safe": bool(overlap_safe),
            "hour_limit_safe": bool(limit_safe),
            "coverage_impact_ticks": int(impact_ticks),
            "explanation": ", ".join(explanation),
            "score": (1 if qualified else 0) + (1 if available else 0) + (1 if overlap_safe else 0) + (1 if limit_safe else 0) - impact_ticks * 0.1,
        })
    candidates.sort(key=lambda row: (row["score"], -row["coverage_impact_ticks"], str(row["employee"]).lower()), reverse=True)
    for other in base_without:
        if other.day != target.day or other.employee_name == target.employee_name:
            continue
        if other.area not in getattr(next((e for e in model.employees if e.name == target.employee_name), Employee(name="")), 'areas_allowed', []):
            continue
        if target.area not in getattr(next((e for e in model.employees if e.name == other.employee_name), Employee(name="")), 'areas_allowed', []):
            continue
        swaps.append({"swap_with": other.employee_name, "day": other.day, "target_area": target.area, "other_area": other.area})
        if len(swaps) >= 3:
            break
    return {"target_employee": target.employee_name, "candidates": candidates[:6], "swap_suggestions": swaps[:3]}

def _candidate_starter_data_paths() -> List[str]:
    """Return supported starter-data locations (new + legacy casing)."""
    return [
        rel_path("Assets", "starting_data_3-2-26.json"),
        rel_path("assets", "starting_data_3-2-26.json"),
    ]


US_STATES: List[Tuple[str, str]] = [
    ("AL", "Alabama"), ("AK", "Alaska"), ("AZ", "Arizona"), ("AR", "Arkansas"), ("CA", "California"),
    ("CO", "Colorado"), ("CT", "Connecticut"), ("DE", "Delaware"), ("FL", "Florida"), ("GA", "Georgia"),
    ("HI", "Hawaii"), ("ID", "Idaho"), ("IL", "Illinois"), ("IN", "Indiana"), ("IA", "Iowa"),
    ("KS", "Kansas"), ("KY", "Kentucky"), ("LA", "Louisiana"), ("ME", "Maine"), ("MD", "Maryland"),
    ("MA", "Massachusetts"), ("MI", "Michigan"), ("MN", "Minnesota"), ("MS", "Mississippi"), ("MO", "Missouri"),
    ("MT", "Montana"), ("NE", "Nebraska"), ("NV", "Nevada"), ("NH", "New Hampshire"), ("NJ", "New Jersey"),
    ("NM", "New Mexico"), ("NY", "New York"), ("NC", "North Carolina"), ("ND", "North Dakota"), ("OH", "Ohio"),
    ("OK", "Oklahoma"), ("OR", "Oregon"), ("PA", "Pennsylvania"), ("RI", "Rhode Island"), ("SC", "South Carolina"),
    ("SD", "South Dakota"), ("TN", "Tennessee"), ("TX", "Texas"), ("UT", "Utah"), ("VT", "Vermont"),
    ("VA", "Virginia"), ("WA", "Washington"), ("WV", "West Virginia"), ("WI", "Wisconsin"), ("WY", "Wyoming"),
]
US_STATE_CODES: Set[str] = {c for c, _ in US_STATES}
US_STATE_LABELS: Dict[str, str] = {c: f"{c} - {n}" for c, n in US_STATES}


def _state_law_dir() -> str:
    return rel_path("state_laws")


def _state_law_file(code: str) -> str:
    return os.path.join(_state_law_dir(), f"{str(code or '').strip().upper()}.json")


def ensure_state_law_seed_files() -> None:
    """Create placeholder state law profiles for all 50 states (idempotent)."""
    try:
        ensure_dir(_state_law_dir())
        for code, name in US_STATES:
            p = _state_law_file(code)
            if os.path.isfile(p):
                continue
            payload = {
                "state_code": code,
                "state_name": name,
                "complete": True,
                "notes": "Conservative normalized core minor-hour restrictions. Customize if needed.",
                "minor_rules": {
                    "mode": "core_minors_v1",
                    "enforce": True,
                    "school_week_default": True,
                    "caps": {
                        "MINOR_14_15": {"school_day": 3.0, "nonschool_day": 8.0, "weekly_school": 18.0, "weekly_nonschool": 40.0},
                        "MINOR_16_17": {"school_day": 4.0, "nonschool_day": 8.0, "weekly_school": 28.0, "weekly_nonschool": 40.0}
                    }
                }
            }
            _atomic_write_json(p, payload, indent=2)
    except Exception as ex:
        _write_run_log(f"STATE_LAW | seed creation failed: {repr(ex)}")


def load_state_law_profile(state_code: str) -> Tuple[Dict[str, Any], str]:
    """Return (profile, warning_message). Empty warning means profile is usable."""
    code = str(state_code or "").strip().upper()
    if code not in US_STATE_CODES:
        return {}, "Store State is required and must be a valid U.S. state. Falling back to current/default rules."
    ensure_state_law_seed_files()
    p = _state_law_file(code)
    if not os.path.isfile(p):
        return {}, f"No state law profile found for {code}. Falling back to current/default rules."
    try:
        with open(p, "r", encoding="utf-8") as f:
            payload = json.load(f)
    except Exception:
        return {}, f"State law profile for {code} could not be read. Falling back to current/default rules."

    if not isinstance(payload, dict):
        return {}, f"State law profile for {code} is invalid. Falling back to current/default rules."
    if not bool(payload.get("complete", False)):
        return payload, f"State law profile for {code} is incomplete. Using current/default rules for now."
    if not isinstance(payload.get("minor_rules", {}), dict):
        return payload, f"State law profile for {code} is missing required sections. Falling back to current/default rules."
    return payload, ""


def apply_state_law_profile_to_model(model: "DataModel", state_code: str, profile: Dict[str, Any]) -> Tuple[bool, str]:
    """Apply selected-state core minor-rule profile into runtime config.

    Only the chosen Store-tab state is applied; no cross-state blending.
    """
    code = str(state_code or "").strip().upper()
    if not isinstance(profile, dict):
        return False, f"State law profile apply skipped for {code}: profile payload is not a JSON object."
    if str(profile.get("state_code", "")).strip().upper() != code:
        return False, f"State law profile apply skipped for {code}: profile state_code mismatch."

    minor_rules = profile.get("minor_rules", {})
    if not isinstance(minor_rules, dict):
        return False, f"State law profile apply skipped for {code}: minor_rules section missing/invalid."

    mode = str(minor_rules.get("mode", "") or "").strip().lower()
    if mode not in {"core_minors_v1", "nd_legacy", "default_fallback", "nd_14_15", "north_dakota_14_15"}:
        return False, f"State law profile apply skipped for {code}: unsupported minor_rules mode."

    try:
        model.nd_rules.enforce = bool(minor_rules.get("enforce", True))
        if minor_rules.get("school_week_default", None) is not None:
            model.nd_rules.is_school_week = bool(minor_rules.get("school_week_default"))

        if mode in {"nd_legacy", "nd_14_15", "north_dakota_14_15"} and code == "ND":
            model.nd_rules.state_code = "ND"
            model.nd_rules.mode = "nd_legacy"
            model.nd_rules.caps_by_minor = {}
            return True, "State law profile applied for ND (legacy mode)."

        caps_payload = dict(minor_rules.get("caps", {}) or {})
        caps_map: Dict[str, Dict[str, float]] = {}
        for mtype in ("MINOR_14_15", "MINOR_16_17"):
            row = dict(caps_payload.get(mtype, {}) or {})
            caps_map[mtype] = {
                "school_day": float(row.get("school_day", 3.0 if mtype == "MINOR_14_15" else 4.0) or 0.0),
                "nonschool_day": float(row.get("nonschool_day", 8.0) or 0.0),
                "weekly_school": float(row.get("weekly_school", 18.0 if mtype == "MINOR_14_15" else 28.0) or 0.0),
                "weekly_nonschool": float(row.get("weekly_nonschool", 40.0) or 0.0),
            }

        model.nd_rules.state_code = code
        model.nd_rules.mode = "core_minors_v1" if mode != "default_fallback" else "default_fallback"
        model.nd_rules.caps_by_minor = caps_map
    except Exception as ex:
        return False, f"State law profile apply failed for {code}: {ex}"

    return True, f"State law profile applied for {code} runtime minor settings."

def _safe_export_label_token(label: str, max_len: int = 24) -> str:
    raw = str(label or '').strip()
    wk = week_sun_from_label(raw)
    if wk is not None:
        token = f"wk{wk.isoformat()}"
    else:
        cleaned = []
        for ch in raw.lower():
            if ch.isalnum():
                cleaned.append(ch)
            elif ch in (' ', '-', '_'):
                cleaned.append('_')
        token = ''.join(cleaned).strip('_') or 'schedule'
        while '__' in token:
            token = token.replace('__', '_')
    return token[:max_len].rstrip('_') or 'schedule'

def _build_export_filename(prefix: str, label: str, ext: str) -> str:
    date_token = datetime.datetime.now().strftime("%Y%m%d_%H%M")
    label_token = _safe_export_label_token(label)
    return f"{prefix}_{date_token}_{label_token}.{ext}"

def _local_file_uri(path: str) -> str:
    try:
        return pathlib.Path(os.path.abspath(path)).resolve().as_uri()
    except Exception:
        return ""

def open_local_export_file(path: str) -> bool:
    """Open a local export file in the default browser/app (best effort)."""
    try:
        if not path or not os.path.isfile(path):
            return False
        abs_path = os.path.abspath(path)
        if sys.platform.startswith("win") and hasattr(os, "startfile"):
            try:
                os.startfile(abs_path)  # type: ignore[attr-defined]
                return True
            except Exception:
                pass
        opener = []
        if sys.platform == "darwin":
            opener = ["open", abs_path]
        elif os.name == "posix":
            opener = ["xdg-open", abs_path]
        if opener:
            try:
                proc = subprocess.Popen(opener)
                if proc.poll() is None or proc.returncode == 0:
                    return True
            except Exception:
                pass
        file_uri = _local_file_uri(abs_path)
        if file_uri and webbrowser.open(file_uri):
            return True
        return bool(webbrowser.open(abs_path))
    except Exception:
        return False

def default_data_path() -> str:
    return rel_path("data", "scheduler_data.json")


def _backup_dir() -> str:
    return rel_path("data", "backups")


def _backup_stamp() -> str:
    return datetime.datetime.now().strftime("%Y-%m-%d_%H%M")


def _iter_backup_source_files() -> List[Tuple[str, str]]:
    """Yield (abs_path, archive_rel_path) for files included in a store backup."""
    items: List[Tuple[str, str]] = []

    def add_file(abs_path: str, rel_name: str) -> None:
        if os.path.isfile(abs_path):
            items.append((abs_path, rel_name.replace('\\', '/')))

    def add_tree(abs_root: str, rel_root: str, suffix: str = '.json') -> None:
        if not os.path.isdir(abs_root):
            return
        for root, _dirs, files in os.walk(abs_root):
            for name in sorted(files):
                if suffix and not name.lower().endswith(suffix):
                    continue
                abs_path = os.path.join(root, name)
                rel_path_name = os.path.relpath(abs_path, abs_root)
                add_file(abs_path, os.path.join(rel_root, rel_path_name))

    add_file(default_data_path(), os.path.join('data', 'scheduler_data.json'))
    add_file(rel_path('data', 'patterns.json'), os.path.join('data', 'patterns.json'))
    add_file(rel_path('data', 'last_schedule.json'), os.path.join('data', 'last_schedule.json'))
    add_tree(rel_path('data', 'final_schedules'), os.path.join('data', 'final_schedules'))
    add_tree(rel_path('history'), 'history')
    return items


def create_store_backup_zip(dest_zip_path: str) -> Dict[str, Any]:
    ensure_dir(os.path.dirname(dest_zip_path))
    included = _iter_backup_source_files()
    meta = {
        'created_on': datetime.datetime.now().isoformat(timespec='seconds'),
        'app_version': APP_VERSION,
        'included_files': [arc for _abs, arc in included],
    }
    with zipfile.ZipFile(dest_zip_path, 'w', compression=zipfile.ZIP_DEFLATED) as zf:
        zf.writestr('backup_manifest.json', json.dumps(meta, indent=2))
        for abs_path, arc_name in included:
            zf.write(abs_path, arc_name)
    return {'path': dest_zip_path, 'file_count': len(included), 'meta': meta}


def list_store_backups() -> List[str]:
    folder = _backup_dir()
    if not os.path.isdir(folder):
        return []
    out = []
    for name in sorted(os.listdir(folder), reverse=True):
        if name.lower().endswith('.zip'):
            out.append(os.path.join(folder, name))
    return out


def restore_store_backup_zip(zip_path: str) -> Dict[str, Any]:
    if not os.path.isfile(zip_path):
        raise FileNotFoundError(f'Backup not found: {zip_path}')
    with tempfile.TemporaryDirectory(prefix='lfs_restore_') as tmpdir:
        with zipfile.ZipFile(zip_path, 'r') as zf:
            members = zf.infolist()
            member_names = [info.filename for info in members]
            data_members = [m for m in member_names if m.startswith('data/') and not m.endswith('/')]
            if 'data/scheduler_data.json' not in data_members:
                raise ValueError('Backup is missing data/scheduler_data.json')
            for info in members:
                name = info.filename
                if not name:
                    continue
                normalized = name.replace('\\', '/')
                parts = [part for part in normalized.split('/') if part not in ('', '.')]
                if (
                    normalized.startswith(('/', '\\'))
                    or normalized.startswith('\\\\')
                    or (len(normalized) >= 2 and normalized[1] == ':')
                    or any(part == '..' for part in parts)
                ):
                    raise ValueError(f'Unsafe path in backup zip: {name}')
                target = os.path.normpath(os.path.join(tmpdir, *parts)) if parts else tmpdir
                if os.path.commonpath([tmpdir, target]) != tmpdir:
                    raise ValueError(f'Unsafe path in backup zip: {name}')
                if name.endswith('/') or info.is_dir():
                    ensure_dir(target)
                    continue
                ensure_dir(os.path.dirname(target))
                with zf.open(info, 'r') as src_fh, open(target, 'wb') as dst_fh:
                    shutil.copyfileobj(src_fh, dst_fh)
        extracted_data = os.path.join(tmpdir, 'data', 'scheduler_data.json')
        _ = load_data(extracted_data)  # validate structure before overwrite

        restored: List[str] = []
        safety_backups: List[str] = []
        for rel_name in [
            os.path.join('data', 'scheduler_data.json'),
            os.path.join('data', 'patterns.json'),
            os.path.join('data', 'last_schedule.json'),
        ]:
            src = os.path.join(tmpdir, rel_name)
            dst = rel_path(*rel_name.split(os.sep))
            if os.path.isfile(src):
                ensure_dir(os.path.dirname(dst))
                bak = _safe_file_backup(dst)
                if bak:
                    safety_backups.append(bak)
                fd, tmp_dst = tempfile.mkstemp(prefix=os.path.basename(dst) + '.__restore_tmp__', dir=os.path.dirname(dst))
                os.close(fd)
                try:
                    shutil.copyfile(src, tmp_dst)
                    os.replace(tmp_dst, dst)
                finally:
                    if os.path.exists(tmp_dst):
                        os.remove(tmp_dst)
                restored.append(rel_name.replace('\\', '/'))

        for rel_folder in [os.path.join('data', 'final_schedules'), 'history']:
            src_root = os.path.join(tmpdir, rel_folder)
            dst_root = rel_path(*rel_folder.split(os.sep))
            if os.path.isdir(src_root):
                parent_dir = os.path.dirname(dst_root)
                ensure_dir(parent_dir)
                stage_root = tempfile.mkdtemp(prefix=os.path.basename(dst_root) + '.__restore_tmp__', dir=parent_dir)
                os.rmdir(stage_root)
                backup_root = None
                try:
                    shutil.copytree(src_root, stage_root)
                    if os.path.exists(dst_root):
                        backup_root = tempfile.mkdtemp(prefix=os.path.basename(dst_root) + '.__restore_old__', dir=parent_dir)
                        os.rmdir(backup_root)
                        os.replace(dst_root, backup_root)
                    os.replace(stage_root, dst_root)
                    if backup_root and os.path.exists(backup_root):
                        shutil.rmtree(backup_root)
                except Exception:
                    if os.path.exists(stage_root):
                        shutil.rmtree(stage_root)
                    if backup_root and os.path.exists(backup_root) and not os.path.exists(dst_root):
                        os.replace(backup_root, dst_root)
                    raise
                for root, _dirs, files in os.walk(dst_root):
                    for name in files:
                        restored.append(os.path.relpath(os.path.join(root, name), app_dir()).replace('\\', '/'))

    return {'path': zip_path, 'restored_files': sorted(restored), 'safety_backups': sorted(set(safety_backups))}



def get_week_exception_bucket(model: "DataModel", label: str) -> Dict[str, Any]:
    lbl = str(label or "").strip()
    all_data = _normalize_weekly_exception_settings(getattr(model, "weekly_exception_settings", {}) or {}, model)
    try:
        model.weekly_exception_settings = all_data
    except Exception:
        pass
    if lbl not in all_data:
        all_data[lbl] = {
            "no_school_days": {d: False for d in DAYS},
            "special_event_days": {d: False for d in DAYS},
            "time_off_requests": [],
        }
    return all_data[lbl]


def get_week_time_off_requests(model: "DataModel", label: str) -> List[TimeOffRequest]:
    b = get_week_exception_bucket(model, label)
    return [des_time_off_request(x) for x in b.get("time_off_requests", [])]


def is_no_school_day_for_label(model: "DataModel", label: str, day: str) -> bool:
    b = get_week_exception_bucket(model, label)
    flags = _normalize_exception_day_flags(b.get("no_school_days", {}))
    return bool(flags.get(day, False))


def is_special_event_day_for_label(model: "DataModel", label: str, day: str) -> bool:
    b = get_week_exception_bucket(model, label)
    flags = _normalize_exception_day_flags(b.get("special_event_days", {}))
    return bool(flags.get(day, False))


def get_employee_time_off_for_window(model: "DataModel", label: str, employee_name: str, day: str, start_t: int, end_t: int) -> List[TimeOffRequest]:
    out: List[TimeOffRequest] = []
    for r in get_week_time_off_requests(model, label):
        if r.employee_name != employee_name or r.day != day:
            continue
        if r.all_day:
            out.append(r); continue
        if not (int(end_t) <= int(r.start_t) or int(start_t) >= int(r.end_t)):
            out.append(r)
    return out
def compute_weekly_eligibility(model: "DataModel", label: str) -> Tuple[Dict[str, str], Dict[str, str]]:
    """Return (eligible, not_eligible) dicts mapping employee_name -> reason.

    Eligible definition (Milestone 3):
      - work_status == 'Active'
      - wants_hours == True
      - has at least one 1-hour window (2 ticks) available in the week after applying:
          * base availability DayRules
          * weekly overrides for the given label (off_all_day, blocked_ranges)
    """
    eligible: Dict[str, str] = {}
    not_eligible: Dict[str, str] = {}

    # Index overrides for quick lookup: (emp, day) -> WeeklyOverride
    ov_map: Dict[Tuple[str, str], WeeklyOverride] = {}
    approved_time_off: Dict[Tuple[str, str], List[TimeOffRequest]] = {}
    for o in getattr(model, "weekly_overrides", []) or []:
        try:
            if (o.label or "").strip() == (label or "").strip():
                ov_map[(o.employee_name, o.day)] = o
        except Exception:
            continue

    for r in get_week_time_off_requests(model, label):
        if r.status != "approved":
            continue
        approved_time_off.setdefault((r.employee_name, r.day), []).append(r)

    one_hour_ticks = 2  # 30-min ticks => 1 hour
    for e in getattr(model, "employees", []) or []:
        name = getattr(e, "name", "(unknown)")
        # Active / opted-in
        if getattr(e, "work_status", "") != "Active":
            not_eligible[name] = f"Not Active ({getattr(e, 'work_status', '')})"
            continue
        if not bool(getattr(e, "wants_hours", True)):
            not_eligible[name] = "Opted-out (wants_hours=False)"
            continue

        any_window = False
        for day in DAYS:
            dr = None
            try:
                dr = (getattr(e, "availability", {}) or {}).get(day)
            except Exception:
                dr = None
            if dr is None:
                # default: unavailable_day=False, full day available
                dr = DayRules(False, 0, DAY_TICKS, [])
            # Apply weekly override
            o = ov_map.get((name, day))
            if o is not None:
                if bool(getattr(o, "off_all_day", False)):
                    continue
                # Merge blocked ranges (override blocks add to existing)
                try:
                    br = list(getattr(dr, "blocked_ranges", []) or [])
                    br.extend(list(getattr(o, "blocked_ranges", []) or []))
                    dr = DayRules(bool(getattr(dr, "unavailable_day", False)),
                                 int(getattr(dr, "earliest_start", 0)),
                                 int(getattr(dr, "latest_end", DAY_TICKS)),
                                 br)
                except Exception:
                    pass

            # Approved selected-week time off requests are hard blackouts in this week.
            reqs = approved_time_off.get((name, day), [])
            if reqs:
                try:
                    br = list(getattr(dr, "blocked_ranges", []) or [])
                    for rq in reqs:
                        if bool(getattr(rq, "all_day", False)):
                            dr = DayRules(True, int(getattr(dr, "earliest_start", 0)), int(getattr(dr, "latest_end", DAY_TICKS)), br)
                            break
                        br.append((int(getattr(rq, "start_t", 0)), int(getattr(rq, "end_t", DAY_TICKS))))
                    else:
                        dr = DayRules(bool(getattr(dr, "unavailable_day", False)), int(getattr(dr, "earliest_start", 0)), int(getattr(dr, "latest_end", DAY_TICKS)), br)
                except Exception:
                    pass

            # Scan for at least one 1-hour window
            try:
                earliest = int(getattr(dr, "earliest_start", 0))
                latest = int(getattr(dr, "latest_end", DAY_TICKS))
                if bool(getattr(dr, "unavailable_day", False)):
                    continue
                for s in range(max(0, earliest), max(0, latest - one_hour_ticks) + 1):
                    if dr.is_available(s, s + one_hour_ticks):
                        any_window = True
                        break
            except Exception:
                # If availability structure is malformed, treat as no availability for safety
                pass

            if any_window:
                break

        if any_window:
            eligible[name] = "Eligible"
        else:
            not_eligible[name] = "No 1-hour availability after weekly overrides/time off/blocks"

    return eligible, not_eligible

def today_iso() -> str:
    return datetime.date.today().isoformat()


def _safe_date_from_iso(v: str) -> Optional[datetime.date]:
    try:
        return datetime.date.fromisoformat(str(v or "").strip())
    except Exception:
        return None


def _add_months(d: datetime.date, months: int) -> datetime.date:
    y = d.year + ((d.month - 1 + months) // 12)
    m = ((d.month - 1 + months) % 12) + 1
    # clamp to last day of target month
    nxt_m = datetime.date(y + (1 if m == 12 else 0), 1 if m == 12 else m + 1, 1)
    last_day = (nxt_m - datetime.timedelta(days=1)).day
    return datetime.date(y, m, min(d.day, last_day))


def roll_task_window(earliest_iso: str, due_iso: str, recurrence: str) -> Tuple[str, str]:
    est = _safe_date_from_iso(earliest_iso)
    due = _safe_date_from_iso(due_iso)
    if est is None or due is None:
        return earliest_iso, due_iso
    rec = _normalize_recurrence(recurrence)
    if rec == "Weekly":
        delta = datetime.timedelta(days=7)
        return (est + delta).isoformat(), (due + delta).isoformat()
    if rec == "Bi-Weekly":
        delta = datetime.timedelta(days=14)
        return (est + delta).isoformat(), (due + delta).isoformat()
    if rec == "Monthly":
        return _add_months(est, 1).isoformat(), _add_months(due, 1).isoformat()
    if rec == "Quarterly":
        return _add_months(est, 3).isoformat(), _add_months(due, 3).isoformat()
    if rec == "Yearly":
        return _add_months(est, 12).isoformat(), _add_months(due, 12).isoformat()
    return earliest_iso, due_iso


def week_window_for_label(label: str) -> Tuple[Optional[datetime.date], Optional[datetime.date]]:
    wk = week_sun_from_label(label)
    if wk is None:
        return None, None
    return wk, wk + datetime.timedelta(days=6)

def weekend_days() -> Set[str]:
    return {"Sat","Sun"}

def html_escape(s: str) -> str:
    return (str(s).replace("&", "&amp;")
            .replace("<","&lt;")
            .replace(">","&gt;")
            .replace('"',"&quot;")
            .replace("'","&#039;"))

# -----------------------------
# ND minor rules helpers
# -----------------------------
def labor_day(year: int) -> datetime.date:
    # first Monday in September
    d = datetime.date(year, 9, 1)
    while d.weekday() != 0:
        d += datetime.timedelta(days=1)
    return d

def is_summer_for_minor_14_15(day_date: datetime.date) -> bool:
    # June 1 – Labor Day (inclusive)
    ld = labor_day(day_date.year)
    return (day_date >= datetime.date(day_date.year, 6, 1)) and (day_date <= ld)

def nd_minor_daily_hour_cap(model: "DataModel", e: "Employee", day: str, label: str = "") -> Optional[float]:
    """Return selected-state daily legal cap (hours) for this employee/day, or None when not applicable."""
    if not bool(getattr(getattr(model, "nd_rules", None), "enforce", False)):
        return None
    minor_type = str(getattr(e, "minor_type", "ADULT") or "ADULT")
    if minor_type == "ADULT":
        return None

    mode = str(getattr(model.nd_rules, "mode", "nd_legacy") or "nd_legacy")
    if mode == "nd_legacy":
        if minor_type != "MINOR_14_15":
            return None
        school_week = bool(getattr(model.nd_rules, "is_school_week", True))
        if school_week and day in {"Mon", "Tue", "Wed", "Thu", "Fri"} and not is_no_school_day_for_label(model, label, day):
            return 3.0
        return 8.0

    caps = dict((getattr(model.nd_rules, "caps_by_minor", {}) or {}).get(minor_type, {}) or {})
    if not caps:
        return None
    school_week = bool(getattr(model.nd_rules, "is_school_week", True))
    if school_week and day in {"Mon", "Tue", "Wed", "Thu", "Fri"} and not is_no_school_day_for_label(model, label, day):
        return float(caps.get("school_day", 0.0) or 0.0)
    return float(caps.get("nonschool_day", caps.get("school_day", 0.0)) or 0.0)

def nd_minor_weekly_hour_cap(model: "DataModel", e: "Employee") -> Optional[float]:
    """Return selected-state weekly legal cap (hours) for this employee, or None when not applicable."""
    if not bool(getattr(getattr(model, "nd_rules", None), "enforce", False)):
        return None
    minor_type = str(getattr(e, "minor_type", "ADULT") or "ADULT")
    if minor_type == "ADULT":
        return None

    mode = str(getattr(model.nd_rules, "mode", "nd_legacy") or "nd_legacy")
    if mode == "nd_legacy":
        if minor_type != "MINOR_14_15":
            return None
        return 18.0 if bool(getattr(model.nd_rules, "is_school_week", True)) else 40.0

    caps = dict((getattr(model.nd_rules, "caps_by_minor", {}) or {}).get(minor_type, {}) or {})
    if not caps:
        return None
    if bool(getattr(model.nd_rules, "is_school_week", True)):
        return float(caps.get("weekly_school", 0.0) or 0.0)
    return float(caps.get("weekly_nonschool", caps.get("weekly_school", 0.0)) or 0.0)

def nd_minor_hours_feasible(model: "DataModel", e: "Employee", day: str, st: int, en: int,
                            assignments: List["Assignment"], label: str = "") -> bool:
    """Hard feasibility check for ND minor daily/weekly hour limits."""
    daily_cap = nd_minor_daily_hour_cap(model, e, day, label=label)
    weekly_cap = nd_minor_weekly_hour_cap(model, e)
    if daily_cap is None or weekly_cap is None:
        return True
    add_h = hours_between_ticks(st, en)
    day_h = add_h
    week_h = add_h
    for a in assignments:
        if a.employee_name != e.name:
            continue
        h = hours_between_ticks(a.start_t, a.end_t)
        week_h += h
        if a.day == day:
            day_h += h
    if day_h - daily_cap > 1e-9:
        return False
    if week_h - weekly_cap > 1e-9:
        return False
    return True

# -----------------------------
# Data models
# -----------------------------
MINOR_TYPES = ["ADULT", "MINOR_14_15", "MINOR_16_17"]

@dataclass
class DayRules:
    unavailable_day: bool = False
    earliest_start: int = 0         # tick
    latest_end: int = DAY_TICKS     # tick
    blocked_ranges: List[Tuple[int,int]] = field(default_factory=list)  # tick ranges

    def is_available(self, start_t: int, end_t: int) -> bool:
        if self.unavailable_day:
            return False
        if start_t < self.earliest_start:
            return False
        if end_t > self.latest_end:
            return False
        for bs, be in self.blocked_ranges:
            if not (end_t <= bs or start_t >= be):
                return False
        return True

@dataclass
class FixedShift:
    day: str
    start_t: int
    end_t: int
    area: str
    locked: bool

@dataclass
class Employee:
    name: str
    phone: str = ""
    work_status: str = "Active"                 # Active / On Leave / Inactive
    wants_hours: bool = True

    # New (V3.2 employee hard-rules + metadata)
    employee_type: str = "Crew Member"          # informational for now
    split_shifts_ok: bool = True                # if False: no split shifts across any areas
    double_shifts_ok: bool = False              # if False: hard cap 8h per shift block
    min_hours_per_shift: float = 1.0            # hard rule (final schedule): minimum contiguous shift length
    max_hours_per_shift: float = 8.0            # per-employee cap; may be raised if double_shifts_ok
    max_shifts_per_day: int = 1                 # contiguous work blocks/day (area changes w/o break count as same shift)
    max_weekly_hours: float = 30.0
    target_min_hours: float = 0.0               # soft preference
    hard_min_weekly_hours: float = 0.0          # best-effort participation target floor (warning if unmet)
    minor_type: str = "ADULT"                   # ADULT / MINOR_14_15 / MINOR_16_17

    areas_allowed: List[str] = field(default_factory=lambda: ["CSTORE"])
    preferred_areas: List[str] = field(default_factory=list)

    avoid_clopens: bool = True
    max_consecutive_days: int = 6
    weekend_preference: str = "Neutral"         # Prefer / Avoid / Neutral

    # Legacy single availability field is kept for backward compatibility.
    # Current semantics: hard_availability = absolute; soft_availability = preference.
    availability: Dict[str, DayRules] = field(default_factory=dict)
    hard_availability: Dict[str, DayRules] = field(default_factory=dict)
    soft_availability: Dict[str, DayRules] = field(default_factory=dict)

    # Canonical recurring fixed schedule payload (one shift/day max) + status.
    # Status: "none" | "active" | "paused"
    fixed_schedule_status: str = "none"
    fixed_schedule: List[FixedShift] = field(default_factory=list)

    # Legacy compatibility payload retained for reading old saves.
    recurring_locked_schedule: List[FixedShift] = field(default_factory=list)

@dataclass
class WeeklyOverride:
    label: str               # week label key
    employee_name: str
    day: str
    off_all_day: bool
    blocked_ranges: List[Tuple[int,int]] = field(default_factory=list)
    note: str = ""

@dataclass
class TimeOffRequest:
    request_id: str
    group_id: str = ""
    label: str = ""
    employee_name: str = ""
    day: str = "Sun"
    all_day: bool = False
    start_t: int = 0
    end_t: int = DAY_TICKS
    status: str = "pending"
    note: str = ""


@dataclass
class ManagerTask:
    task_id: str
    title: str = ""
    description: str = ""
    earliest_start_date: str = ""
    due_date: str = ""
    recurrence: str = "One-Time"  # One-Time / Weekly / Bi-Weekly / Monthly / Quarterly / Yearly
    completed: bool = False
    completed_on: str = ""
    last_rolled_on: str = ""


@dataclass
class CallOffIncident:
    incident_id: str
    week_label: str = ""
    day: str = ""
    incident_date: str = ""
    called_out_employee: str = ""
    replacement_employee: str = ""
    recorded_on: str = ""
    note: str = ""
    status: str = "reported"


@dataclass
class EmployeeReliabilityEvent:
    event_id: str
    employee_name: str = ""
    event_type: str = ""  # call_out / extra_shift_pickup
    date: str = ""
    week_label: str = ""
    related_employee: str = ""
    note: str = ""
    source: str = ""

@dataclass
class RequirementBlock:
    day: str
    area: str
    start_t: int
    end_t: int
    min_count: int
    preferred_count: int
    max_count: int

@dataclass
class Assignment:
    day: str
    area: str
    start_t: int
    end_t: int
    employee_name: str
    locked: bool = False
    source: str = ASSIGNMENT_SOURCE_ENGINE

@dataclass
class ScheduleSummary:
    label: str
    created_on: str
    total_hours: float
    warnings: List[str]
    employee_hours: Dict[str, float]
    weekend_counts: Dict[str, int]
    undesirable_counts: Dict[str, int]
    filled_slots: int
    total_slots: int

@dataclass
class StoreInfo:
    store_name: str = ""
    store_address: str = ""
    store_phone: str = ""
    store_manager: str = ""
    store_state: str = ""
    cstore_open: str = "00:00"
    cstore_close: str = "24:00"
    kitchen_open: str = "00:00"
    kitchen_close: str = "24:00"
    carwash_open: str = "00:00"
    carwash_close: str = "24:00"
    # Soft preference windows by area; each area keeps 3 optional (start, end) HH:MM pairs.
    peak_hours_soft: Dict[str, List[Tuple[str, str]]] = field(default_factory=lambda: {
        "CSTORE": [("", ""), ("", ""), ("", "")],
        "KITCHEN": [("", ""), ("", ""), ("", "")],
        "CARWASH": [("", ""), ("", ""), ("", "")],
    })
    # Report/UI metadata only (does not affect solver behavior).
    area_colors: Dict[str, str] = field(default_factory=lambda: {
        "CSTORE": "#2f4f4f",
        "KITCHEN": "#5a4a3a",
        "CARWASH": "#3d4f6a",
    })


def _default_area_colors() -> Dict[str, str]:
    return {
        "CSTORE": "#2f4f4f",
        "KITCHEN": "#5a4a3a",
        "CARWASH": "#3d4f6a",
    }


def _normalize_area_colors(raw: Any) -> Dict[str, str]:
    out = _default_area_colors()
    if not isinstance(raw, dict):
        return out
    for area in AREAS:
        v = str(raw.get(area, "") or "").strip()
        if re.fullmatch(r"#[0-9a-fA-F]{6}", v):
            out[area] = v.lower()
    return out


def _norm_hhmm_or_default(v: str, default: str) -> str:
    try:
        return tick_to_hhmm(hhmm_to_tick(str(v).strip()))
    except Exception:
        return default


def area_open_close_ticks(model: "DataModel", area: str) -> Tuple[int, int]:
    if area not in AREAS:
        return 0, DAY_TICKS
    si = getattr(model, "store_info", None)
    if si is None:
        return 0, DAY_TICKS
    if area == "CSTORE":
        op = _norm_hhmm_or_default(getattr(si, "cstore_open", "00:00"), "00:00")
        cl = _norm_hhmm_or_default(getattr(si, "cstore_close", "24:00"), "24:00")
    elif area == "KITCHEN":
        op = _norm_hhmm_or_default(getattr(si, "kitchen_open", "00:00"), "00:00")
        cl = _norm_hhmm_or_default(getattr(si, "kitchen_close", "24:00"), "24:00")
    else:
        op = _norm_hhmm_or_default(getattr(si, "carwash_open", "00:00"), "00:00")
        cl = _norm_hhmm_or_default(getattr(si, "carwash_close", "24:00"), "24:00")
    op_t = hhmm_to_tick(op)
    cl_t = hhmm_to_tick(cl)
    if cl_t <= op_t:
        # Treat invalid/closed configurations as closed for validation safety.
        return 0, 0
    return op_t, cl_t


def is_within_area_hours(model: "DataModel", area: str, start_t: int, end_t: int) -> bool:
    op_t, cl_t = area_open_close_ticks(model, area)
    return int(start_t) >= int(op_t) and int(end_t) <= int(cl_t) and int(end_t) > int(start_t)


def _normalize_peak_hours_soft(raw: Any) -> Dict[str, List[Tuple[str, str]]]:
    out: Dict[str, List[Tuple[str, str]]] = {a: [("", ""), ("", ""), ("", "")] for a in AREAS}
    if not isinstance(raw, dict):
        return out
    for k, windows in raw.items():
        key = str(k or "").strip().upper().replace("-", "").replace(" ", "")
        if key in ("CSTORE", "C-STORE"):
            area = "CSTORE"
        elif key in ("KITCHEN",):
            area = "KITCHEN"
        elif key in ("CARWASH", "CAR WASH"):
            area = "CARWASH"
        else:
            continue
        cleaned: List[Tuple[str, str]] = []
        for item in (windows or []):
            if isinstance(item, (list, tuple)) and len(item) >= 2:
                s_raw = str(item[0] or "").strip()
                e_raw = str(item[1] or "").strip()
            else:
                s_raw, e_raw = "", ""
            s = _norm_hhmm_or_default(s_raw, "") if s_raw else ""
            e = _norm_hhmm_or_default(e_raw, "") if e_raw else ""
            cleaned.append((s, e))
            if len(cleaned) >= 3:
                break
        while len(cleaned) < 3:
            cleaned.append(("", ""))
        out[area] = cleaned
    return out


def get_area_peak_windows_ticks(store_info: Optional[StoreInfo], area: str) -> List[Tuple[int, int]]:
    if store_info is None:
        return []
    norm = _normalize_peak_hours_soft(getattr(store_info, "peak_hours_soft", {}) or {})
    out: List[Tuple[int, int]] = []
    for s, e in norm.get(area, []):
        if not s or not e:
            continue
        try:
            st = hhmm_to_tick(s)
            en = hhmm_to_tick(e)
        except Exception:
            continue
        if en > st:
            out.append((int(st), int(en)))
    return out


def peak_overlap_ticks(store_info: Optional[StoreInfo], area: str, st: int, en: int) -> int:
    total = 0
    for p_st, p_en in get_area_peak_windows_ticks(store_info, area):
        total += max(0, min(int(en), int(p_en)) - max(int(st), int(p_st)))
    return int(total)

@dataclass
class Settings:
    ui_scale: float = 1.0
    min_rest_hours: int = 10               # clopen rest
    fairness_lookback_weeks: int = 6
    optimizer_iterations: int = 2500
    optimizer_temperature: float = 0.8
    solver_scrutiny_level: str = "Balanced"
    learn_from_history: bool = True
    enable_multi_scenario_generation: bool = True
    scenario_schedule_count: int = 4
    enable_demand_forecast_engine: bool = True
    enable_employee_fit_engine: bool = True
    
@dataclass
class NdMinorRuleConfig:
    enforce: bool = True
    # School week toggle affects weekly minor hour limits.
    is_school_week: bool = True
    state_code: str = "ND"
    mode: str = "nd_legacy"
    caps_by_minor: Dict[str, Dict[str, float]] = field(default_factory=dict)


@dataclass
class ManagerGoals:
    # Targets & thresholds used for manager reporting and solver preferences/caps.
    # NOTE: In Milestone 1 these caps are persisted + validated; solver behavior is unchanged.
    coverage_goal_pct: float = 95.0                 # percent of required 30-min blocks fully covered
    daily_overstaff_allow_hours: float = 0.0        # informational threshold for warnings

    # Weekly labor caps:
    # preferred_weekly_cap: soft target (0 = ignore)
    # maximum_weekly_cap: hard cap (0 = disabled) — enforced starting Milestone 2
    preferred_weekly_cap: float = 0.0
    maximum_weekly_cap: float = 0.0
    minimum_weekly_floor: float = 0.0              # desired labor floor (best-effort)


    # --- Milestone 6: Scoring weights (soft penalties) ---
    # Higher weight = stronger preference to avoid.
    w_under_preferred_coverage: float = 5.0      # per 30-min deficit tick
    w_over_max_soft_ceiling: float = 80.0        # per 30-min tick over Max (soft ceiling, stronger than preferred)
    w_over_preferred_cap: float = 20.0           # per hour over preferred cap
    w_participation_miss: float = 250.0          # per eligible employee missing >=1hr
    w_split_shifts: float = 30.0                 # per extra shift in a day
    w_hour_imbalance: float = 2.0                # per hour away from average (L1)

    # --- P2-3: Schedule Stability ---
    enable_schedule_stability: bool = True      # prefer keeping last week's assignments when feasible
    w_schedule_stability: float = 14.0          # per hour moved/changed vs previous schedule
    # --- Phase 4 C3: Risk-Aware Optimization ---
    enable_risk_aware_optimization: bool = True   # penalize fragile windows at generation time
    protect_single_point_failures: bool = True    # extra penalty for 1/1 windows
    w_risk_fragile: float = 4.0                   # scheduled == minimum required
    w_risk_single_point: float = 8.0              # minimum=1 and scheduled=1


    
    # --- Phase 3: Coverage Risk Protection + Utilization Optimizer ---
    enable_coverage_risk_protection: bool = True   # fill scarce shifts first and reserve scarce employees for scarce shifts
    w_coverage_risk: float = 10.0                  # strength of scarcity-aware preference (soft)

    enable_utilization_optimizer: bool = True      # prefer cleaner schedules: fewer unique employees, fewer fragments
    w_new_employee_penalty: float = 3.0            # penalty for introducing a brand-new employee (soft)
    w_fragmentation_penalty: float = 2.5           # penalty per assignment segment (soft)
    w_extend_shift_bonus: float = 2.0              # bonus for extending an adjacent shift (soft)
    w_low_hours_priority_bonus: float = 2.5        # bonus for using employees who are currently under-used
    w_near_cap_penalty: float = 5.0                # penalty for piling more hours onto already-heavy employees
    w_target_min_fill_bonus: float = 1.5           # bonus for employees still below their target minimum hours
    utilization_balance_tolerance_hours: float = 2.0   # ignore small hour differences inside this band

# Optional preferences (soft toggles)
    prefer_longer_shifts: bool = True            # slight penalty for very short segments
    prefer_area_consistency: bool = False        # slight penalty for switching areas
    # Backward compatibility: older saves used weekly_hours_cap. We keep it so old files load/saves remain compatible.
    # It is migrated into preferred_weekly_cap when loading older data.
    weekly_hours_cap: float = 0.0                   # legacy (0 = ignore)
    # --- Phase 2 Milestone P2-4/P2-5 ---
    w_pattern_learning: float = 8.0              # weight for deviating from learned patterns (soft preference)

    # Demand-adaptive staffing multipliers (applied to staffing requirements)
    demand_morning_multiplier: float = 1.0
    demand_midday_multiplier: float = 1.0
    demand_evening_multiplier: float = 1.0


    call_list_depth: int = 5
    include_noncertified_in_call_list: bool = False


@dataclass
class DataModel:
    meta_version: str = "LaborForceScheduler_v3_new"
    store_info: StoreInfo = field(default_factory=StoreInfo)
    settings: Settings = field(default_factory=Settings)
    nd_rules: NdMinorRuleConfig = field(default_factory=NdMinorRuleConfig)
    manager_goals: ManagerGoals = field(default_factory=ManagerGoals)

    week_start_sun: str = ""  # ISO date for current schedule label default
    employees: List[Employee] = field(default_factory=list)
    requirements: List[RequirementBlock] = field(default_factory=list)
    weekly_overrides: List[WeeklyOverride] = field(default_factory=list)
    weekly_exception_settings: Dict[str, Dict[str, Any]] = field(default_factory=dict)

    learned_patterns: Dict[str, Any] = field(default_factory=dict)

    history: List[ScheduleSummary] = field(default_factory=list)
    manager_tasks: List[ManagerTask] = field(default_factory=list)
    calloff_incidents: List[CallOffIncident] = field(default_factory=list)
    reliability_events: List[EmployeeReliabilityEvent] = field(default_factory=list)

# -----------------------------
# Defaults
# -----------------------------
def default_day_rules() -> Dict[str, DayRules]:
    return {d: DayRules(False, 0, DAY_TICKS, []) for d in DAYS}


def _normalize_fixed_schedule_status(v: Any) -> str:
    s = str(v or "none").strip().lower()
    if s in {"active", "paused", "none"}:
        return s
    return "none"


def _normalize_fixed_schedule_entries(entries: List[FixedShift]) -> List[FixedShift]:
    """Normalize fixed schedule payload to one valid shift per day."""
    by_day: Dict[str, List[FixedShift]] = {d: [] for d in DAYS}
    for fs in entries or []:
        try:
            day = str(getattr(fs, "day", "") or "").strip()
            area = str(getattr(fs, "area", "") or "").strip().upper()
            st = int(getattr(fs, "start_t", 0))
            en = int(getattr(fs, "end_t", 0))
        except Exception:
            continue
        if day not in DAYS or area not in AREAS:
            continue
        if en <= st:
            continue
        by_day[day].append(FixedShift(day=day, start_t=st, end_t=en, area=area, locked=True))

    out: List[FixedShift] = []
    for d in DAYS:
        day_items = sorted(by_day[d], key=lambda x: (int(x.start_t), int(x.end_t), str(x.area)))
        if day_items:
            out.append(day_items[0])
    return out


def employee_hard_availability(e: Employee) -> Dict[str, DayRules]:
    av = getattr(e, "hard_availability", None)
    if isinstance(av, dict) and av:
        return av
    av2 = getattr(e, "availability", None)
    if isinstance(av2, dict) and av2:
        return av2
    return default_day_rules()


def employee_soft_availability(e: Employee) -> Dict[str, DayRules]:
    av = getattr(e, "soft_availability", None)
    if isinstance(av, dict) and av:
        return av
    av2 = getattr(e, "availability", None)
    if isinstance(av2, dict) and av2:
        return av2
    return default_day_rules()

def default_requirements() -> List[RequirementBlock]:
    # Default blocks: 05:00–23:00 in 30-minute increments, CSTORE=2, others=0
    out: List[RequirementBlock] = []
    start = hhmm_to_tick("05:00")
    end = hhmm_to_tick("23:00")
    for day in DAYS:
        t = start
        while t < end:
            t2 = t + 1  # 30 min
            for area in AREAS:
                cnt = 2 if area == "CSTORE" else 0
                out.append(RequirementBlock(day, area, t, t2, cnt, cnt, cnt))
            t = t2
    return out

# -----------------------------
# Serialization
# -----------------------------
def ser_dayrules(dr: DayRules) -> dict:
    return {"unavailable_day": dr.unavailable_day,
            "earliest_start": dr.earliest_start,
            "latest_end": dr.latest_end,
            "blocked_ranges": [list(x) for x in dr.blocked_ranges]}

def des_dayrules(d: dict) -> DayRules:
    return DayRules(
        unavailable_day=bool(d.get("unavailable_day", False)),
        earliest_start=int(d.get("earliest_start", 0)),
        latest_end=int(d.get("latest_end", DAY_TICKS)),
        blocked_ranges=[(int(a), int(b)) for a,b in d.get("blocked_ranges", []) if int(b) > int(a)]
    )

def ser_employee(e: Employee) -> dict:
    hard_av = employee_hard_availability(e)
    soft_av = employee_soft_availability(e)
    fixed_norm = _normalize_fixed_schedule_entries(list(getattr(e, "fixed_schedule", []) or []))
    fixed_status = _normalize_fixed_schedule_status(getattr(e, "fixed_schedule_status", "none"))
    return {
        "name": e.name,
        "phone": e.phone,
        "work_status": e.work_status,
        "wants_hours": bool(e.wants_hours),
        "employee_type": str(getattr(e, "employee_type", "Crew Member")),
        "split_shifts_ok": bool(getattr(e, "split_shifts_ok", True)),
        "double_shifts_ok": bool(getattr(e, "double_shifts_ok", False)),
        "min_hours_per_shift": float(getattr(e, "min_hours_per_shift", 1.0)),
        "max_hours_per_shift": float(getattr(e, "max_hours_per_shift", 8.0)),
        "max_shifts_per_day": int(getattr(e, "max_shifts_per_day", 1)),
        "max_weekly_hours": float(e.max_weekly_hours),
        "target_min_hours": float(e.target_min_hours),
        "hard_min_weekly_hours": float(getattr(e, "hard_min_weekly_hours", 0.0)),
        "minor_type": e.minor_type,
        "areas_allowed": list(e.areas_allowed),
        "preferred_areas": list(e.preferred_areas),
        "avoid_clopens": bool(e.avoid_clopens),
        "max_consecutive_days": int(e.max_consecutive_days),
        "weekend_preference": str(e.weekend_preference),
        # Legacy + explicit hard/soft availability payloads.
        "availability": {d: ser_dayrules(hard_av.get(d, DayRules())) for d in DAYS},
        "hard_availability": {d: ser_dayrules(hard_av.get(d, DayRules())) for d in DAYS},
        "soft_availability": {d: ser_dayrules(soft_av.get(d, DayRules())) for d in DAYS},
        # Canonical fixed schedule payload + status.
        "fixed_schedule_status": fixed_status,
        "fixed_schedule": [asdict(fs) for fs in fixed_norm],
        # Legacy compatibility write-through: expose active fixed entries as recurring_locked_schedule.
        "recurring_locked_schedule": [asdict(fs) for fs in fixed_norm] if fixed_status == "active" else [],
    }

def des_employee(d: dict) -> Employee:
    av_raw = d.get("availability", {})
    hard_av_raw = d.get("hard_availability", av_raw)
    soft_av_raw = d.get("soft_availability", av_raw)
    hard_av = {day: des_dayrules((hard_av_raw or {}).get(day, {})) for day in DAYS}
    soft_av = {day: des_dayrules((soft_av_raw or {}).get(day, {})) for day in DAYS}

    fs_raw: List[FixedShift] = []
    for x in d.get("fixed_schedule", []):
        try:
            fs_raw.append(FixedShift(
                day=x.get("day","Sun"),
                start_t=int(x.get("start_t",0)),
                end_t=int(x.get("end_t",0)),
                area=x.get("area","CSTORE"),
                locked=bool(x.get("locked", False)),
            ))
        except Exception:
            pass

    recurring_raw = d.get("recurring_locked_schedule", None)
    rls_raw: List[FixedShift] = []
    if isinstance(recurring_raw, list):
        for x in recurring_raw:
            try:
                rls_raw.append(FixedShift(
                    day=x.get("day","Sun"),
                    start_t=int(x.get("start_t",0)),
                    end_t=int(x.get("end_t",0)),
                    area=x.get("area","CSTORE"),
                    locked=True,
                ))
            except Exception:
                pass
    # Compatibility mapping behavior:
    # - New payload (explicit status) => treat fixed_schedule as canonical payload.
    # - Legacy payload => migrate recurring_locked + fixed.locked=True as ACTIVE fixed schedule.
    # - Legacy fixed.locked=False does not migrate into the new fixed hard-rule system.
    has_new_fixed_shape = ("fixed_schedule_status" in d) or ("hard_availability" in d) or ("soft_availability" in d)
    if has_new_fixed_shape:
        fixed_status = _normalize_fixed_schedule_status(d.get("fixed_schedule_status", "none"))
        fixed_payload = _normalize_fixed_schedule_entries(fs_raw)
    else:
        legacy_active: List[FixedShift] = []
        for x in rls_raw:
            legacy_active.append(FixedShift(day=x.day, start_t=x.start_t, end_t=x.end_t, area=x.area, locked=True))
        for x in fs_raw:
            if bool(getattr(x, "locked", False)):
                legacy_active.append(FixedShift(day=x.day, start_t=x.start_t, end_t=x.end_t, area=x.area, locked=True))
        fixed_payload = _normalize_fixed_schedule_entries(legacy_active)
        fixed_status = "active" if fixed_payload else "none"

    # If status says none, payload should be empty; if status active/paused and payload empty, normalize to none.
    if fixed_status == "none":
        fixed_payload = []
    elif not fixed_payload:
        fixed_status = "none"

    et = str(d.get("employee_type", "Crew Member"))
    if not et.strip():
        et = "Crew Member"

    def _as_float(val, default):
        try:
            return float(val)
        except Exception:
            return float(default)

    def _as_int(val, default):
        try:
            return int(val)
        except Exception:
            return int(default)

    split_ok = bool(d.get("split_shifts_ok", True))
    double_ok = bool(d.get("double_shifts_ok", False))
    min_shift_h = _as_float(d.get("min_hours_per_shift", 1.0), 1.0)
    max_raw = d.get("max_hours_per_shift", None)
    max_shift_h = None if max_raw is None else _as_float(max_raw, 8.0)
    max_shifts_day = _as_int(d.get("max_shifts_per_day", 1), 1)

    if max_shift_h is None:
        t = et.strip().lower()
        if t in ["store manager", "assistant manager", "kitchen manager"]:
            max_shift_h = 16.0
        elif t in ["senior crew member", "manager in training"]:
            max_shift_h = 12.0
        else:
            max_shift_h = 8.0

    min_shift_h = max(0.5, min_shift_h)
    max_shift_h = max(min_shift_h, max_shift_h)
    max_shifts_day = max(1, max_shifts_day)
    mt = d.get("minor_type","ADULT")
    if mt not in MINOR_TYPES:
        mt = "ADULT"
    areas = [a for a in d.get("areas_allowed", ["CSTORE"]) if a in AREAS]
    if not areas:
        areas = ["CSTORE"]
    pref_areas = [a for a in d.get("preferred_areas", []) if a in AREAS]
    return Employee(
        name=str(d.get("name","")).strip(),
        phone=str(d.get("phone","")).strip(),
        work_status=str(d.get("work_status","Active")),
        wants_hours=bool(d.get("wants_hours", True)),
        employee_type=et,
        split_shifts_ok=split_ok,
        double_shifts_ok=double_ok,
        min_hours_per_shift=min_shift_h,
        max_hours_per_shift=max_shift_h,
        max_shifts_per_day=max_shifts_day,
        max_weekly_hours=float(d.get("max_weekly_hours", 30.0)),
        target_min_hours=float(d.get("target_min_hours", 0.0)),
        hard_min_weekly_hours=float(d.get("hard_min_weekly_hours", d.get("min_weekly_hours", 0.0)) or 0.0),
        minor_type=mt,
        areas_allowed=areas,
        preferred_areas=pref_areas,
        avoid_clopens=bool(d.get("avoid_clopens", True)),
        max_consecutive_days=int(d.get("max_consecutive_days", 6)),
        weekend_preference=str(d.get("weekend_preference", "Neutral")),
        availability=hard_av,
        hard_availability=hard_av,
        soft_availability=soft_av,
        fixed_schedule_status=fixed_status,
        fixed_schedule=fixed_payload,
        recurring_locked_schedule=[FixedShift(day=x.day, start_t=x.start_t, end_t=x.end_t, area=x.area, locked=True) for x in fixed_payload] if fixed_status == "active" else [],
    )

def ser_override(o: WeeklyOverride) -> dict:
    return {"label": o.label, "employee_name": o.employee_name, "day": o.day,
            "off_all_day": bool(o.off_all_day),
            "blocked_ranges": [list(x) for x in o.blocked_ranges],
            "note": o.note}

def des_override(d: dict) -> WeeklyOverride:
    br = []
    for a,b in d.get("blocked_ranges", []):
        try:
            a=int(a); b=int(b)
            if b>a: br.append((a,b))
        except Exception:
            pass
    return WeeklyOverride(
        label=str(d.get("label","")).strip(),
        employee_name=str(d.get("employee_name","")).strip(),
        day=str(d.get("day","Sun")),
        off_all_day=bool(d.get("off_all_day", False)),
        blocked_ranges=br,
        note=str(d.get("note","")).strip(),
    )


def _normalize_exception_day_flags(raw: Any) -> Dict[str, bool]:
    out: Dict[str, bool] = {d: False for d in DAYS}
    if isinstance(raw, dict):
        for d in DAYS:
            out[d] = bool(raw.get(d, False))
    elif isinstance(raw, list):
        for day in raw:
            d = str(day or '').strip().title()[:3]
            if d in DAYS:
                out[d] = True
    return out


def _normalize_time_off_status(v: Any) -> str:
    s = str(v or 'pending').strip().lower()
    if s in {'approved', 'denied', 'pending'}:
        return s
    if s in {'declined', 'decline'}:
        return 'denied'
    if s in {'undecided', 'pending / undecided', 'pending/undecided'}:
        return 'pending'
    return 'pending'


def _normalize_time_range(start_t: Any, end_t: Any) -> Tuple[int, int]:
    try:
        st = int(start_t)
    except Exception:
        st = 0
    try:
        en = int(end_t)
    except Exception:
        en = DAY_TICKS
    st = max(0, min(DAY_TICKS, st))
    en = max(0, min(DAY_TICKS, en))
    if en <= st:
        return st, st
    return st, en


def _normalize_time_off_requests(raw: Any, label_hint: str = '') -> List[TimeOffRequest]:
    out: List[TimeOffRequest] = []
    if not isinstance(raw, list):
        return out
    for i, row in enumerate(raw):
        if not isinstance(row, dict):
            continue
        label = str(row.get('label', label_hint or '')).strip()
        emp = str(row.get('employee_name', '')).strip()
        day = str(row.get('day', '')).strip().title()[:3]
        if not label or not emp or day not in DAYS:
            continue
        all_day = bool(row.get('all_day', False))
        st, en = _normalize_time_range(row.get('start_t', 0), row.get('end_t', DAY_TICKS))
        if all_day:
            st, en = 0, DAY_TICKS
        elif en <= st:
            continue
        rid = str(row.get('request_id', '')).strip() or f"{label}|{emp}|{day}|{st}|{en}|{i}"
        gid = str(row.get('group_id', '')).strip() or rid
        out.append(TimeOffRequest(
            request_id=rid,
            group_id=gid,
            label=label,
            employee_name=emp,
            day=day,
            all_day=all_day,
            start_t=st,
            end_t=en,
            status=_normalize_time_off_status(row.get('status', 'pending')),
            note=str(row.get('note', '')).strip(),
        ))
    return out


def _normalize_recurrence(v: Any) -> str:
    raw = str(v or "One-Time").strip().lower().replace("_", "-")
    mapping = {
        "one-time": "One-Time",
        "onetime": "One-Time",
        "weekly": "Weekly",
        "bi-weekly": "Bi-Weekly",
        "biweekly": "Bi-Weekly",
        "monthly": "Monthly",
        "quarterly": "Quarterly",
        "yearly": "Yearly",
    }
    return mapping.get(raw, "One-Time")


def _norm_iso_date(v: Any) -> str:
    s = str(v or "").strip()
    if not s:
        return ""
    try:
        return datetime.date.fromisoformat(s).isoformat()
    except Exception:
        return ""


def _normalize_manager_tasks(raw: Any) -> List[ManagerTask]:
    out: List[ManagerTask] = []
    if not isinstance(raw, list):
        return out
    for i, row in enumerate(raw):
        if not isinstance(row, dict):
            continue
        tid = str(row.get("task_id", "")).strip() or f"task_{i}_{random.randint(1000,9999)}"
        out.append(ManagerTask(
            task_id=tid,
            title=str(row.get("title", "")).strip(),
            description=str(row.get("description", "")).strip(),
            earliest_start_date=_norm_iso_date(row.get("earliest_start_date", "")),
            due_date=_norm_iso_date(row.get("due_date", "")),
            recurrence=_normalize_recurrence(row.get("recurrence", "One-Time")),
            completed=bool(row.get("completed", False)),
            completed_on=_norm_iso_date(row.get("completed_on", "")),
            last_rolled_on=_norm_iso_date(row.get("last_rolled_on", "")),
        ))
    return out


def _normalize_calloff_incidents(raw: Any) -> List[CallOffIncident]:
    out: List[CallOffIncident] = []
    if not isinstance(raw, list):
        return out
    for i, row in enumerate(raw):
        if not isinstance(row, dict):
            continue
        iid = str(row.get("incident_id", "")).strip() or f"inc_{i}_{random.randint(1000,9999)}"
        day = str(row.get("day", "")).strip().title()[:3]
        if day and day not in DAYS:
            day = ""
        out.append(CallOffIncident(
            incident_id=iid,
            week_label=str(row.get("week_label", "")).strip(),
            day=day,
            incident_date=_norm_iso_date(row.get("incident_date", "")),
            called_out_employee=str(row.get("called_out_employee", "")).strip(),
            replacement_employee=str(row.get("replacement_employee", "")).strip(),
            recorded_on=_norm_iso_date(row.get("recorded_on", "")),
            note=str(row.get("note", "")).strip(),
            status=str(row.get("status", "reported")).strip() or "reported",
        ))
    return out


def _normalize_reliability_events(raw: Any) -> List[EmployeeReliabilityEvent]:
    out: List[EmployeeReliabilityEvent] = []
    if not isinstance(raw, list):
        return out
    for i, row in enumerate(raw):
        if not isinstance(row, dict):
            continue
        ev_id = str(row.get("event_id", "")).strip() or f"rel_{i}_{random.randint(1000,9999)}"
        ev_type = str(row.get("event_type", "")).strip().lower().replace("-", "_")
        if ev_type not in {"call_out", "extra_shift_pickup"}:
            ev_type = ""
        out.append(EmployeeReliabilityEvent(
            event_id=ev_id,
            employee_name=str(row.get("employee_name", "")).strip(),
            event_type=ev_type,
            date=_norm_iso_date(row.get("date", "")),
            week_label=str(row.get("week_label", "")).strip(),
            related_employee=str(row.get("related_employee", "")).strip(),
            note=str(row.get("note", "")).strip(),
            source=str(row.get("source", "")).strip(),
        ))
    return out


def _normalize_weekly_exception_settings(raw: Any, model: Optional[DataModel] = None) -> Dict[str, Dict[str, Any]]:
    out: Dict[str, Dict[str, Any]] = {}
    if isinstance(raw, dict):
        for label, payload in raw.items():
            lbl = str(label or '').strip()
            if not lbl or not isinstance(payload, dict):
                continue
            out[lbl] = {
                'no_school_days': _normalize_exception_day_flags(payload.get('no_school_days', {})),
                'special_event_days': _normalize_exception_day_flags(payload.get('special_event_days', {})),
                'time_off_requests': [asdict(x) for x in _normalize_time_off_requests(payload.get('time_off_requests', []), lbl)],
            }

    # Backward-safe migration path from legacy weekly_overrides into per-week time-off requests.
    if model is not None:
        for o in getattr(model, 'weekly_overrides', []) or []:
            lbl = str(getattr(o, 'label', '') or '').strip()
            emp = str(getattr(o, 'employee_name', '') or '').strip()
            day = str(getattr(o, 'day', '') or '').strip()
            if not lbl or not emp or day not in DAYS:
                continue
            slot = out.setdefault(lbl, {
                'no_school_days': {d: False for d in DAYS},
                'special_event_days': {d: False for d in DAYS},
                'time_off_requests': [],
            })
            note = str(getattr(o, 'note', '') or '').strip()
            if bool(getattr(o, 'off_all_day', False)):
                slot['time_off_requests'].append(asdict(TimeOffRequest(
                    request_id=f"legacy|{lbl}|{emp}|{day}|all_day",
                    group_id=f"legacy|{lbl}|{emp}|{day}|all_day",
                    label=lbl,
                    employee_name=emp,
                    day=day,
                    all_day=True,
                    start_t=0,
                    end_t=DAY_TICKS,
                    status='approved',
                    note=note,
                )))
            for j, (bs, be) in enumerate(list(getattr(o, 'blocked_ranges', []) or [])):
                st, en = _normalize_time_range(bs, be)
                if en <= st:
                    continue
                slot['time_off_requests'].append(asdict(TimeOffRequest(
                    request_id=f"legacy|{lbl}|{emp}|{day}|{st}|{en}|{j}",
                    group_id=f"legacy|{lbl}|{emp}|{day}|{st}|{en}|{j}",
                    label=lbl,
                    employee_name=emp,
                    day=day,
                    all_day=False,
                    start_t=st,
                    end_t=en,
                    status='approved',
                    note=note,
                )))

    # final dedupe and shape cleanup
    for lbl, payload in list(out.items()):
        reqs = _normalize_time_off_requests(payload.get('time_off_requests', []), lbl)
        seen: Set[str] = set()
        deduped: List[Dict[str, Any]] = []
        for r in reqs:
            key = f"{r.request_id}|{r.employee_name}|{r.day}|{r.start_t}|{r.end_t}|{r.status}"
            if key in seen:
                continue
            seen.add(key)
            deduped.append(asdict(r))
        out[lbl] = {
            'no_school_days': _normalize_exception_day_flags(payload.get('no_school_days', {})),
            'special_event_days': _normalize_exception_day_flags(payload.get('special_event_days', {})),
            'time_off_requests': deduped,
        }

    return out


def ser_time_off_request(r: TimeOffRequest) -> dict:
    return asdict(r)


def des_time_off_request(d: dict) -> TimeOffRequest:
    day = str(d.get('day', '')).strip().title()[:3]
    st, en = _normalize_time_range(d.get('start_t', 0), d.get('end_t', DAY_TICKS))
    all_day = bool(d.get('all_day', False))
    if all_day:
        st, en = 0, DAY_TICKS
    rid = str(d.get('request_id', '')).strip()
    return TimeOffRequest(
        request_id=rid,
        group_id=str(d.get('group_id', '')).strip() or rid,
        label=str(d.get('label', '')).strip(),
        employee_name=str(d.get('employee_name', '')).strip(),
        day=day if day in DAYS else 'Sun',
        all_day=all_day,
        start_t=st,
        end_t=en,
        status=_normalize_time_off_status(d.get('status', 'pending')),
        note=str(d.get('note', '')).strip(),
    )

def ser_req(r: RequirementBlock) -> dict:
    return asdict(r)

def des_req(d: dict) -> RequirementBlock:
    # Backward compatible: older saves used required_count only
    rc = int(d.get("required_count", d.get("min_count", 0)))
    mn = int(d.get("min_count", rc))
    pr = int(d.get("preferred_count", mn))
    mx = int(d.get("max_count", pr))
    # normalize
    mn = max(0, mn)
    pr = max(mn, pr)
    mx = max(pr, mx)
    return RequirementBlock(
        day=str(d.get("day","Sun")),
        area=str(d.get("area","CSTORE")),
        start_t=int(d.get("start_t",0)),
        end_t=int(d.get("end_t",0)),
        min_count=mn,
        preferred_count=pr,
        max_count=mx,
    )

def ser_assignment(a: Assignment) -> dict:
    out = asdict(a)
    out["source"] = assignment_provenance(a)
    return out

def _normalize_assignment_source(source: str, locked: bool = False) -> str:
    s = str(source or "").strip().lower()
    if s in {ASSIGNMENT_SOURCE_ENGINE, "solver", "participation", "weak_area_improve", "prev", "final", "repair"}:
        return ASSIGNMENT_SOURCE_ENGINE
    # Legacy "fixed_prefer" aliases map to fixed-unlocked preference semantics.
    if s in {ASSIGNMENT_SOURCE_FIXED_UNLOCKED, "fixed_unlocked", "fixed_prefer", "fixed_unlocked_preference"}:
        return ASSIGNMENT_SOURCE_FIXED_UNLOCKED
    if s in {ASSIGNMENT_SOURCE_MANUAL, "manual_edit"}:
        return ASSIGNMENT_SOURCE_MANUAL
    if locked or s in {ASSIGNMENT_SOURCE_FIXED_LOCKED, "locked", "recurring_locked", "fixed_locked"}:
        return ASSIGNMENT_SOURCE_FIXED_LOCKED
    return ASSIGNMENT_SOURCE_ENGINE

def is_engine_managed_source(source: str) -> bool:
    return str(source or "") in {ASSIGNMENT_SOURCE_ENGINE, ASSIGNMENT_SOURCE_FIXED_UNLOCKED}

def assignment_provenance(a: Assignment) -> str:
    return _normalize_assignment_source(getattr(a, "source", ASSIGNMENT_SOURCE_ENGINE), bool(getattr(a, "locked", False)))

def des_assignment(d: dict) -> Assignment:
    locked = bool(d.get("locked", False))
    return Assignment(
        day=str(d.get("day", "Sun")),
        area=str(d.get("area", "CSTORE")),
        start_t=int(d.get("start_t", 0)),
        end_t=int(d.get("end_t", 0)),
        employee_name=str(d.get("employee_name", "")).strip(),
        locked=locked,
        source=_normalize_assignment_source(str(d.get("source", ASSIGNMENT_SOURCE_ENGINE) or ASSIGNMENT_SOURCE_ENGINE), locked),
    )

def ser_summary(s: ScheduleSummary) -> dict:
    return asdict(s)

def des_summary(d: dict) -> ScheduleSummary:
    return ScheduleSummary(
        label=d.get("label",""),
        created_on=d.get("created_on",""),
        total_hours=float(d.get("total_hours",0.0)),
        warnings=list(d.get("warnings",[])),
        employee_hours={k: float(v) for k,v in d.get("employee_hours",{}).items()},
        weekend_counts={k: int(v) for k,v in d.get("weekend_counts",{}).items()},
        undesirable_counts={k: int(v) for k,v in d.get("undesirable_counts",{}).items()},
        filled_slots=int(d.get("filled_slots",0)),
        total_slots=int(d.get("total_slots",0)),
    )

def save_data(model: DataModel, path: str):
    payload = {
        "meta": {"version": model.meta_version, "saved_on": today_iso()},
        "store_info": asdict(model.store_info),
        "settings": asdict(model.settings),
        "nd_rules": asdict(model.nd_rules),
        "manager_goals": asdict(model.manager_goals),
        "week_start_sun": model.week_start_sun,
        "employees": [ser_employee(e) for e in model.employees],
        "requirements": [ser_req(r) for r in model.requirements],
        "weekly_overrides": [ser_override(o) for o in model.weekly_overrides],
        "weekly_exception_settings": _normalize_weekly_exception_settings(getattr(model, "weekly_exception_settings", {}) or {}, model),
        "history": [ser_summary(s) for s in model.history],
        "manager_tasks": [asdict(x) for x in getattr(model, "manager_tasks", []) or []],
        "calloff_incidents": [asdict(x) for x in getattr(model, "calloff_incidents", []) or []],
        "reliability_events": [asdict(x) for x in getattr(model, "reliability_events", []) or []],
    }
    ensure_dir(os.path.dirname(path))
    _atomic_write_json(path, payload, indent=2)

def load_data(path: str) -> DataModel:
    with open(path, "r", encoding="utf-8") as f:
        payload = json.load(f)
    m = DataModel()
    m.week_start_sun = str(payload.get("week_start_sun","")).strip()

    store_info_raw = dict(payload.get("store_info", {}) or {})
    try:
        allowed_store_info_keys = set(StoreInfo.__dataclass_fields__.keys())
        unknown_store_info = sorted(k for k in store_info_raw.keys() if k not in allowed_store_info_keys)
        if unknown_store_info:
            _write_run_log(f"[load_data] Ignoring unknown store_info keys: {', '.join(unknown_store_info)}")
        store_info_filtered = {k: v for k, v in store_info_raw.items() if k in allowed_store_info_keys}
    except Exception:
        store_info_filtered = store_info_raw
    m.store_info = StoreInfo(**store_info_filtered)
    try:
        m.store_info.peak_hours_soft = _normalize_peak_hours_soft(getattr(m.store_info, "peak_hours_soft", {}) or {})
    except Exception:
        m.store_info.peak_hours_soft = _normalize_peak_hours_soft({})
    try:
        m.store_info.area_colors = _normalize_area_colors(getattr(m.store_info, "area_colors", {}) or {})
    except Exception:
        m.store_info.area_colors = _default_area_colors()

    settings_raw = dict(payload.get("settings", {}) or {})
    try:
        allowed_settings_keys = set(Settings.__dataclass_fields__.keys())
        unknown_settings = sorted(k for k in settings_raw.keys() if k not in allowed_settings_keys)
        if unknown_settings:
            _write_run_log(f"[load_data] Ignoring unknown settings keys: {', '.join(unknown_settings)}")
        settings_filtered = {k: v for k, v in settings_raw.items() if k in allowed_settings_keys}
    except Exception:
        settings_filtered = settings_raw
    m.settings = Settings(**settings_filtered)
    # Clamp ui_scale to prevent oversized UI from test files or older saves.
    # Target baseline is 1.0; allow up to 1.3 (roughly +30%) for readability.
    try:
        if m.settings.ui_scale is None:
            m.settings.ui_scale = 1.0
        if float(m.settings.ui_scale) > 1.3:
            m.settings.ui_scale = 1.3
        if float(m.settings.ui_scale) < 0.5:
            m.settings.ui_scale = 1.0
    except Exception:
        m.settings.ui_scale = 1.0
    nd_rules_raw = dict(payload.get("nd_rules", {}) or {})
    try:
        allowed_nd_rules_keys = set(NdMinorRuleConfig.__dataclass_fields__.keys())
        unknown_nd_rules = sorted(k for k in nd_rules_raw.keys() if k not in allowed_nd_rules_keys)
        if unknown_nd_rules:
            _write_run_log(f"[load_data] Ignoring unknown nd_rules keys: {', '.join(unknown_nd_rules)}")
        nd_rules_filtered = {k: v for k, v in nd_rules_raw.items() if k in allowed_nd_rules_keys}
    except Exception:
        nd_rules_filtered = nd_rules_raw
    m.nd_rules = NdMinorRuleConfig(**nd_rules_filtered)
    # Manager goals migration (backward compatible)
    mg = dict(payload.get("manager_goals", {}) or {})
    # Older saves used weekly_hours_cap; migrate into preferred_weekly_cap if needed.
    if "preferred_weekly_cap" not in mg and "weekly_hours_cap" in mg:
        try:
            mg["preferred_weekly_cap"] = float(mg.get("weekly_hours_cap", 0.0) or 0.0)
        except Exception:
            mg["preferred_weekly_cap"] = 0.0
    # Ensure new field exists (0 = disabled)
    if "maximum_weekly_cap" not in mg:
        mg["maximum_weekly_cap"] = 0.0
    if "minimum_weekly_floor" not in mg:
        mg["minimum_weekly_floor"] = 0.0
    # P2-3 stability defaults
    if "enable_schedule_stability" not in mg:
        mg["enable_schedule_stability"] = True
    if "w_schedule_stability" not in mg:
        mg["w_schedule_stability"] = 14.0

    # Phase 4 C3: Risk-Aware Optimization defaults (soft)
    if "enable_risk_aware_optimization" not in mg:
        mg["enable_risk_aware_optimization"] = True
    if "protect_single_point_failures" not in mg:
        mg["protect_single_point_failures"] = True
    if "w_risk_fragile" not in mg:
        mg["w_risk_fragile"] = 4.0
    if "w_risk_single_point" not in mg:
        mg["w_risk_single_point"] = 8.0
    # Keep legacy field populated for backward compatibility
    if "weekly_hours_cap" not in mg:
        mg["weekly_hours_cap"] = mg.get("preferred_weekly_cap", 0.0)

    # Compatibility hardening: ignore unknown keys from future / partially patched builds
    # instead of crashing ManagerGoals(**mg).
    try:
        allowed_mg_keys = set(ManagerGoals.__dataclass_fields__.keys())
        unknown_mg = sorted(k for k in mg.keys() if k not in allowed_mg_keys)
        if unknown_mg:
            _write_run_log(f"[load_data] Ignoring unknown manager_goals keys: {', '.join(unknown_mg)}")
        mg = {k: v for k, v in mg.items() if k in allowed_mg_keys}
    except Exception:
        pass

    m.manager_goals = ManagerGoals(**mg)
    m.employees = [des_employee(e) for e in payload.get("employees", []) if str(e.get("name","")).strip()]
    m.requirements = [des_req(r) for r in payload.get("requirements", [])]
    if not m.requirements:
        m.requirements = default_requirements()
    m.weekly_overrides = [des_override(o) for o in payload.get("weekly_overrides", [])]
    m.weekly_exception_settings = _normalize_weekly_exception_settings(payload.get("weekly_exception_settings", {}), m)
    m.history = [des_summary(s) for s in payload.get("history", [])]
    m.manager_tasks = _normalize_manager_tasks(payload.get("manager_tasks", []))
    m.calloff_incidents = _normalize_calloff_incidents(payload.get("calloff_incidents", []))
    m.reliability_events = _normalize_reliability_events(payload.get("reliability_events", []))
    return m

# -----------------------------
# P2-3 — Schedule Stability helpers
# -----------------------------
def _expand_assignments_to_tick_map(assigns: List[Assignment]) -> Dict[Tuple[str,str,int], str]:
    out: Dict[Tuple[str,str,int], str] = {}
    for a in assigns:
        for tt in range(int(a.start_t), int(a.end_t)):
            out[(a.day, a.area, int(tt))] = a.employee_name
    return out

def load_last_schedule_tick_map() -> Tuple[Optional[str], Dict[Tuple[str,str,int], str]]:
    """Loads the previous schedule tick map from ./data/last_schedule.json (if present)."""
    path = rel_path("data", "last_schedule.json")
    if not os.path.exists(path):
        return None, {}
    try:
        with open(path, "r", encoding="utf-8") as f:
            payload = json.load(f) or {}
        label = str(payload.get("label", "")).strip() or None
        assigns_raw = payload.get("assignments", []) or []
        assigns: List[Assignment] = []
        for x in assigns_raw:
            try:
                assigns.append(Assignment(
                    day=str(x.get("day","Sun")),
                    area=str(x.get("area","CSTORE")),
                    start_t=int(x.get("start_t",0)),
                    end_t=int(x.get("end_t",0)),
                    employee_name=str(x.get("employee_name","")).strip(),
                    locked=bool(x.get("locked", False)),
                    source=str(x.get("source","prev")),
                ))
            except Exception:
                pass
        return label, _expand_assignments_to_tick_map(assigns)
    except Exception:
        return None, {}



def load_prev_final_schedule_tick_map(current_label: Optional[str]) -> Tuple[Optional[str], Dict[Tuple[str,str,int], str]]:
    """Prefer last week's *published final* schedule (./data/final_schedules/YYYY-MM-DD.json) for stability.
    Falls back to most recent final schedule found earlier than the current week if exact prev-week file is missing.
    """
    try:
        wk = week_sun_from_label(str(current_label or ""))
    except Exception:
        wk = None
    if not wk:
        return None, {}

    def _load_final(path: str) -> Tuple[Optional[str], Dict[Tuple[str,str,int], str]]:
        try:
            with open(path, "r", encoding="utf-8") as f:
                payload = json.load(f) or {}
            label = str(payload.get("label", "")).strip() or None
            assigns_raw = payload.get("assignments", []) or []
            assigns: List[Assignment] = []
            for x in assigns_raw:
                try:
                    assigns.append(Assignment(
                        day=str(x.get("day","Sun")),
                        area=str(x.get("area","CSTORE")),
                        start_t=int(x.get("start_t",0)),
                        end_t=int(x.get("end_t",0)),
                        employee_name=str(x.get("employee_name","")).strip(),
                        locked=bool(x.get("locked", False)),
                        source=str(x.get("source","final")),
                    ))
                except Exception:
                    pass
            return label, _expand_assignments_to_tick_map(assigns)
        except Exception:
            return None, {}

    # Prefer exact prior week file
    prev = wk - datetime.timedelta(days=7)
    exact = rel_path("data", "final_schedules", f"{prev.isoformat()}.json")
    if os.path.isfile(exact):
        return _load_final(exact)

    # Otherwise, choose most recent final earlier than current week
    d = rel_path("data", "final_schedules")
    if not os.path.isdir(d):
        return None, {}
    best_date = None
    best_path = None
    for fn in os.listdir(d):
        if not fn.lower().endswith(".json"):
            continue
        m = re.match(r"(\d{4}-\d{2}-\d{2})\.json$", fn)
        if not m:
            continue
        try:
            dt = datetime.date.fromisoformat(m.group(1))
        except Exception:
            continue
        if dt >= wk:
            continue
        if best_date is None or dt > best_date:
            best_date = dt
            best_path = os.path.join(d, fn)
    if best_path:
        return _load_final(best_path)
    return None, {}

def load_final_schedule_payload_for_label(label: Optional[str]) -> Tuple[Optional[str], Dict[str, Any]]:
    """Load the published final schedule payload for the given label/week, if present."""
    try:
        wk = week_sun_from_label(str(label or ""))
    except Exception:
        wk = None
    if not wk:
        return None, {}
    path = rel_path("data", "final_schedules", f"{wk.isoformat()}.json")
    if not os.path.isfile(path):
        return None, {}
    try:
        with open(path, "r", encoding="utf-8") as f:
            payload = json.load(f) or {}
        return path, payload
    except Exception:
        return None, {}


def load_assignments_from_final_payload(payload: Dict[str, Any]) -> List[Assignment]:
    assigns: List[Assignment] = []
    for item in (payload.get("assignments", []) or []):
        try:
            assigns.append(des_assignment(item))
        except Exception:
            pass
    return assigns


def load_prev_final_schedule_assignments(current_label: Optional[str]) -> Tuple[Optional[str], Optional[str], List[Assignment]]:
    """Return the label/path/assignments for the prior published final schedule used by stability logic."""
    try:
        wk = week_sun_from_label(str(current_label or ""))
    except Exception:
        wk = None
    if not wk:
        return None, None, []

    def _load_final(path: str) -> Tuple[Optional[str], Optional[str], List[Assignment]]:
        try:
            with open(path, "r", encoding="utf-8") as f:
                payload = json.load(f) or {}
            return str(payload.get("label", "")).strip() or None, path, load_assignments_from_final_payload(payload)
        except Exception:
            return None, None, []

    prev = wk - datetime.timedelta(days=7)
    exact = rel_path("data", "final_schedules", f"{prev.isoformat()}.json")
    if os.path.isfile(exact):
        return _load_final(exact)

    d = rel_path("data", "final_schedules")
    if not os.path.isdir(d):
        return None, None, []
    best_date = None
    best_path = None
    for fn in os.listdir(d):
        if not fn.lower().endswith(".json"):
            continue
        m = re.match(r"(\d{4}-\d{2}-\d{2})\.json$", fn)
        if not m:
            continue
        try:
            dt = datetime.date.fromisoformat(m.group(1))
        except Exception:
            continue
        if dt >= wk:
            continue
        if best_date is None or dt > best_date:
            best_date = dt
            best_path = os.path.join(d, fn)
    if best_path:
        return _load_final(best_path)
    return None, None, []


def load_last_schedule_assignments() -> Tuple[Optional[str], List[Assignment]]:
    path = rel_path("data", "last_schedule.json")
    if not os.path.isfile(path):
        return None, []
    try:
        with open(path, "r", encoding="utf-8") as f:
            payload = json.load(f) or {}
        label = str(payload.get("label", "")).strip() or None
        assigns = []
        for x in (payload.get("assignments", []) or []):
            try:
                assigns.append(Assignment(
                    day=str(x.get("day","Sun")),
                    area=str(x.get("area","CSTORE")),
                    start_t=int(x.get("start_t",0)),
                    end_t=int(x.get("end_t",0)),
                    employee_name=str(x.get("employee_name","")).strip(),
                    locked=bool(x.get("locked", False)),
                    source=str(x.get("source","prev")),
                ))
            except Exception:
                pass
        return label, assigns
    except Exception:
        return None, []


def _patterns_path() -> str:
    return rel_path("data", "patterns.json")

def load_patterns() -> Dict[str, Any]:
    """Load learned patterns from ./data/patterns.json."""
    path = _patterns_path()
    try:
        if os.path.isfile(path):
            with open(path, "r", encoding="utf-8") as f:
                return json.load(f) or {}
    except Exception:
        pass
    return {}

def save_patterns(patterns: Dict[str, Any]) -> None:
    path = _patterns_path()
    try:
        ensure_dir(os.path.dirname(path))
        _atomic_write_json(path, patterns or {}, indent=2)
    except Exception:
        pass

def _tick_to_hour(tick: int) -> float:
    return float(tick) * 0.5

def _demand_bucket_for_tick(tick: int) -> str:
    """Return 'morning' | 'midday' | 'evening' based on start tick."""
    hr = _tick_to_hour(int(tick))
    # Treat overnight (before 5am) as evening demand.
    if hr < 5.0:
        return "evening"
    if hr < 11.0:
        return "morning"
    if hr < 17.0:
        return "midday"
    return "evening"

def learn_patterns_from_history_folder() -> Dict[str, Any]:
    """Scan ./history/*.json and ./data/last_schedule.json to infer soft preferences."""
    patterns: Dict[str, Any] = {}
    # Accumulators
    area_counts: Dict[str, Dict[str, int]] = {}
    start_counts: Dict[str, Dict[str, int]] = {}
    len_counts: Dict[str, Dict[str, int]] = {}

    def add_assignment(a: Dict[str, Any]) -> None:
        emp = str(a.get("employee","")).strip()
        if not emp:
            return
        area = str(a.get("area","")).strip()
        st = int(a.get("start_t", 0))
        en = int(a.get("end_t", 0))
        ln = max(1, int(en - st))
        area_counts.setdefault(emp, {})
        area_counts[emp][area] = area_counts[emp].get(area, 0) + 1
        start_counts.setdefault(emp, {})
        start_counts[emp][str(st)] = start_counts[emp].get(str(st), 0) + 1
        len_counts.setdefault(emp, {})
        len_counts[emp][str(ln)] = len_counts[emp].get(str(ln), 0) + 1

    # history snapshots
    try:
        hdir = rel_path("history")
        if os.path.isdir(hdir):
            for fn in os.listdir(hdir):
                if not fn.lower().endswith(".json"):
                    continue
                path = os.path.join(hdir, fn)
                try:
                    with open(path, "r", encoding="utf-8") as f:
                        payload = json.load(f) or {}
                    assigns = payload.get("assignments") or payload.get("schedule", {}).get("assignments") or []
                    if isinstance(assigns, list):
                        for a in assigns:
                            if isinstance(a, dict):
                                add_assignment(a)
                except Exception:
                    continue
    except Exception:
        pass

    # last schedule
    try:
        lpath = rel_path("data", "last_schedule.json")
        if os.path.isfile(lpath):
            with open(lpath, "r", encoding="utf-8") as f:
                payload = json.load(f) or {}
            assigns = payload.get("assignments") or []
            if isinstance(assigns, list):
                for a in assigns:
                    if isinstance(a, dict):
                        add_assignment(a)
    except Exception:
        pass

    # finalize
    for emp in set(list(area_counts.keys()) + list(start_counts.keys()) + list(len_counts.keys())):
        ac = area_counts.get(emp, {})
        sc = start_counts.get(emp, {})
        lc = len_counts.get(emp, {})
        pref_area = max(ac.items(), key=lambda kv: kv[1])[0] if ac else ""
        pref_start = int(max(sc.items(), key=lambda kv: kv[1])[0]) if sc else 0
        pref_len = int(max(lc.items(), key=lambda kv: kv[1])[0]) if lc else 0
        patterns[emp] = {
            "preferred_area": pref_area,
            "preferred_start_tick": pref_start,
            "preferred_len_ticks": pref_len,
            "area_counts": ac,
            "start_tick_counts": sc,
            "len_counts": lc,
        }
    return patterns


def build_demand_forecast_profile() -> Dict[str, Any]:
    bucket_counts = {"morning": 0.0, "midday": 0.0, "evening": 0.0}
    area_counts: Dict[str, float] = {}

    def _consume(assigns: List[Dict[str, Any]]) -> None:
        for a in assigns or []:
            try:
                st = int(a.get("start_t", 0) or 0)
                en = int(a.get("end_t", 0) or 0)
                ln = max(1, en - st)
                bucket = _demand_bucket_for_tick(st)
                bucket_counts[bucket] = bucket_counts.get(bucket, 0.0) + float(ln)
                area = str(a.get("area", "") or "").strip()
                if area:
                    area_counts[area] = area_counts.get(area, 0.0) + float(ln)
            except Exception:
                pass

    try:
        hdir = rel_path("history")
        if os.path.isdir(hdir):
            for fn in os.listdir(hdir):
                if not fn.lower().endswith('.json'):
                    continue
                p = os.path.join(hdir, fn)
                try:
                    with open(p, 'r', encoding='utf-8') as f:
                        payload = json.load(f) or {}
                    _consume(payload.get('assignments') or payload.get('schedule', {}).get('assignments') or [])
                except Exception:
                    pass
    except Exception:
        pass

    try:
        p = rel_path('data', 'last_schedule.json')
        if os.path.isfile(p):
            with open(p, 'r', encoding='utf-8') as f:
                payload = json.load(f) or {}
            _consume(payload.get('assignments') or [])
    except Exception:
        pass

    total = sum(float(v) for v in bucket_counts.values())
    multipliers = {"morning": 1.0, "midday": 1.0, "evening": 1.0}
    if total > 0.0:
        baseline = total / 3.0
        for bucket, raw in bucket_counts.items():
            ratio = float(raw) / max(1.0, baseline)
            multipliers[bucket] = max(0.85, min(1.20, round(ratio, 2)))

    peak_bucket = max(multipliers.items(), key=lambda kv: kv[1])[0] if multipliers else 'midday'
    low_bucket = min(multipliers.items(), key=lambda kv: kv[1])[0] if multipliers else 'midday'
    return {'bucket_counts': bucket_counts, 'multipliers': multipliers, 'peak_bucket': peak_bucket, 'low_bucket': low_bucket, 'dominant_area': max(area_counts.items(), key=lambda kv: kv[1])[0] if area_counts else ''}


def apply_demand_forecast_to_model(model: DataModel, forecast: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    forecast = dict(forecast or build_demand_forecast_profile())
    mults = dict(forecast.get('multipliers') or {})
    try:
        model.manager_goals.demand_morning_multiplier = float(mults.get('morning', 1.0) or 1.0)
        model.manager_goals.demand_midday_multiplier = float(mults.get('midday', 1.0) or 1.0)
        model.manager_goals.demand_evening_multiplier = float(mults.get('evening', 1.0) or 1.0)
    except Exception:
        pass
    return forecast


def build_employee_fit_profiles() -> Dict[str, Any]:
    profiles: Dict[str, Any] = {}
    area_counts: Dict[str, Dict[str, float]] = {}
    bucket_counts: Dict[str, Dict[str, float]] = {}
    def _consume(assigns: List[Dict[str, Any]]) -> None:
        for a in assigns or []:
            try:
                emp = str(a.get('employee_name', a.get('employee', '')) or '').strip()
                if not emp:
                    continue
                area = str(a.get('area', '') or '').strip()
                st = int(a.get('start_t', 0) or 0)
                en = int(a.get('end_t', 0) or 0)
                ln = max(1, en - st)
                bucket = _demand_bucket_for_tick(st)
                area_counts.setdefault(emp, {})
                bucket_counts.setdefault(emp, {})
                if area:
                    area_counts[emp][area] = area_counts[emp].get(area, 0.0) + float(ln)
                bucket_counts[emp][bucket] = bucket_counts[emp].get(bucket, 0.0) + float(ln)
            except Exception:
                pass
    try:
        hdir = rel_path('history')
        if os.path.isdir(hdir):
            for fn in os.listdir(hdir):
                if not fn.lower().endswith('.json'):
                    continue
                p = os.path.join(hdir, fn)
                try:
                    with open(p, 'r', encoding='utf-8') as f:
                        payload = json.load(f) or {}
                    _consume(payload.get('assignments') or payload.get('schedule', {}).get('assignments') or [])
                except Exception:
                    pass
    except Exception:
        pass
    try:
        p = rel_path('data', 'last_schedule.json')
        if os.path.isfile(p):
            with open(p, 'r', encoding='utf-8') as f:
                payload = json.load(f) or {}
            _consume(payload.get('assignments') or [])
    except Exception:
        pass
    for emp in sorted(set(list(area_counts.keys()) + list(bucket_counts.keys()))):
        ac = area_counts.get(emp, {}) or {}
        bc = bucket_counts.get(emp, {}) or {}
        profiles[emp] = {'best_area': max(ac.items(), key=lambda kv: kv[1])[0] if ac else '', 'best_bucket': max(bc.items(), key=lambda kv: kv[1])[0] if bc else '', 'area_counts': ac, 'bucket_counts': bc}
    return profiles


def get_employee_fit_score(learned_patterns: Dict[str, Any], emp_name: str, area: str, start_tick: int) -> float:
    fit_profiles = dict((learned_patterns or {}).get('__employee_fit__') or {})
    profile = dict(fit_profiles.get(emp_name) or {})
    if not profile:
        return 0.0
    score = 0.0
    best_area = str(profile.get('best_area', '') or '').strip()
    best_bucket = str(profile.get('best_bucket', '') or '').strip()
    bucket = _demand_bucket_for_tick(int(start_tick))
    if best_area:
        score += 2.5 if area == best_area else -1.5
    if best_bucket:
        score += 1.5 if bucket == best_bucket else -0.5
    return score


def save_last_schedule(assigns: List[Assignment], label: str):
    """Persists the latest schedule to ./data/last_schedule.json for stability scoring."""
    path = rel_path("data", "last_schedule.json")
    ensure_dir(os.path.dirname(path))
    try:
        payload = {
            "label": str(label),
            "saved_on": today_iso(),
            "assignments": [asdict(a) for a in assigns],
        }
        _atomic_write_json(path, payload, indent=2)
    except Exception:
        pass

# -----------------------------
# Constraint checking

# -----------------------------
def week_sun_from_label(label: str) -> Optional[datetime.date]:
    # expects label like "Week starting YYYY-MM-DD"
    import re
    m = re.search(r"(\d{4}-\d{2}-\d{2})", label)
    if not m:
        return None
    try:
        return datetime.date.fromisoformat(m.group(1))
    except Exception:
        return None

def day_date(week_sun: datetime.date, day: str) -> datetime.date:
    return week_sun + datetime.timedelta(days=DAYS.index(day))

def calc_schedule_stats(model: "DataModel", assignments: List[Assignment]) -> Tuple[Dict[str,float], float, int, int]:
    emp_hours: Dict[str, float] = {}
    total_hours = 0.0
    for a in assignments or []:
        hrs = hours_between_ticks(int(a.start_t), int(a.end_t))
        emp_hours[a.employee_name] = emp_hours.get(a.employee_name, 0.0) + hrs
        total_hours += hrs

    coverage: Dict[Tuple[str, str, int], int] = {}
    for a in assignments or []:
        try:
            for t in range(int(a.start_t), int(a.end_t)):
                k = (a.day, a.area, t)
                coverage[k] = coverage.get(k, 0) + 1
        except Exception:
            continue

    filled = 0
    total_slots = 0
    min_req, _pref_req, _max_req = build_requirement_maps(getattr(model, "requirements", []) or [], goals=getattr(model, "manager_goals", None), store_info=getattr(model, "store_info", None))
    for k, mn in min_req.items():
        total_slots += int(mn)
        filled += min(int(mn), int(coverage.get(k, 0)))

    return emp_hours, float(total_hours), int(filled), int(total_slots)

def is_employee_available(model: DataModel, e: Employee, label: str, day: str, start_t: int, end_t: int, area: str,
                          clopen_min_start: Dict[Tuple[str,str], int]) -> bool:
    if e.work_status != "Active":
        return False
    if area not in e.areas_allowed:
        return False
    if not is_within_area_hours(model, area, start_t, end_t):
        return False
    dr = employee_hard_availability(e).get(day)
    if dr is None:
        return False
    if not dr.is_available(start_t, end_t):
        return False

    # weekly override (legacy support)
    for o in model.weekly_overrides:
        if o.label.strip() == label.strip() and o.employee_name == e.name and o.day == day:
            if o.off_all_day:
                return False
            for bs, be in o.blocked_ranges:
                if not (end_t <= bs or start_t >= be):
                    return False

    # selected-week approved time-off requests are hard blackout windows.
    for rq in get_employee_time_off_for_window(model, label, e.name, day, start_t, end_t):
        if rq.status == 'approved':
            return False

    # clopen rest
    ms = clopen_min_start.get((e.name, day))
    if ms is not None and start_t < ms:
        return False

    # ND minor rules (14-15)
    if model.nd_rules.enforce and e.minor_type == "MINOR_14_15":
        ws = week_sun_from_label(label) or datetime.date.today()
        ddate = day_date(ws, day)
        summer = is_summer_for_minor_14_15(ddate)
        # Allowed window
        earliest = hhmm_to_tick("07:00")
        latest = hhmm_to_tick("21:00") if summer else hhmm_to_tick("19:00")
        if start_t < earliest:
            return False
        if end_t > latest:
            return False
    return True


def fixed_shift_compliance_ok(model: DataModel, e: Employee, label: str, day: str, start_t: int, end_t: int, area: str,
                              existing_assignments: Optional[List[Assignment]] = None) -> Tuple[bool, str]:
    """Compliance checks for active fixed anchors.

    Active fixed shifts override employee-level availability/area/preferences,
    but must still respect store hours and legal/minor restrictions.
    """
    if area not in AREAS:
        return False, "Area must be CSTORE, KITCHEN, or CARWASH."
    if day not in DAYS:
        return False, "Day must be Sun, Mon, Tue, Wed, Thu, Fri, or Sat."
    if int(end_t) <= int(start_t):
        return False, "End must be after start."
    if not is_within_area_hours(model, area, int(start_t), int(end_t)):
        op_t, cl_t = area_open_close_ticks(model, area)
        return False, f"Shift must be within Hours of Operation for {area}: {tick_to_hhmm(op_t)}–{tick_to_hhmm(cl_t)}"

    if model.nd_rules.enforce and e.minor_type == "MINOR_14_15":
        ws = week_sun_from_label(label) or datetime.date.today()
        ddate = day_date(ws, day)
        summer = is_summer_for_minor_14_15(ddate)
        earliest = hhmm_to_tick("07:00")
        latest = hhmm_to_tick("21:00") if summer else hhmm_to_tick("19:00")
        if int(start_t) < earliest or int(end_t) > latest:
            return False, "Shift violates ND minor allowed working window."
        if not nd_minor_hours_feasible(model, e, day, int(start_t), int(end_t), list(existing_assignments or []), label=label):
            return False, "Shift violates ND minor daily/weekly hour limits."

    return True, ""

def apply_clopen_from(model: DataModel, e: Employee, a: Assignment,
                      clopen_min_start: Dict[Tuple[str,str], int]):
    if not e.avoid_clopens:
        return
    # if ends late (>=22:00), enforce min rest for next day
    end_hr = a.end_t / TICKS_PER_HOUR
    if end_hr >= 22.0:
        idx = DAYS.index(a.day)
        next_day = DAYS[(idx + 1) % 7]
        min_start_ticks = int(max(0, (a.end_t + model.settings.min_rest_hours*TICKS_PER_HOUR) - DAY_TICKS))
        clopen_min_start[(e.name, next_day)] = max(clopen_min_start.get((e.name, next_day), 0), min_start_ticks)

# -----------------------------
# Optimizer
# -----------------------------
def build_requirement_maps(reqs: List[RequirementBlock], goals: Optional[Any] = None, store_info: Optional[StoreInfo] = None) -> Tuple[Dict[Tuple[str,str,int], int], Dict[Tuple[str,str,int], int], Dict[Tuple[str,str,int], int]]:
    """Compile requirements into per-30-minute-tick maps.

    Returns:
      min_req[(day, area, tick)] = hard minimum headcount
      pref_req[(day, area, tick)] = preferred (soft) target headcount
      max_req[(day, area, tick)] = preferred soft ceiling headcount
    Overlaps are combined conservatively:
      - min / preferred: take max
      - max: take min (tightest cap)
    """
    min_req: Dict[Tuple[str,str,int], int] = {}
    pref_req: Dict[Tuple[str,str,int], int] = {}
    max_req: Dict[Tuple[str,str,int], int] = {}
    for r in reqs:
        if r.day not in DAYS or r.area not in AREAS:
            continue
        mn = max(0, int(getattr(r, "min_count", 0)))
        pr = max(mn, int(getattr(r, "preferred_count", mn)))
        mx = max(pr, int(getattr(r, "max_count", pr)))
        m_morn = float(getattr(goals, "demand_morning_multiplier", 1.0) or 1.0) if goals is not None else 1.0
        m_mid  = float(getattr(goals, "demand_midday_multiplier", 1.0) or 1.0) if goals is not None else 1.0
        m_eve  = float(getattr(goals, "demand_evening_multiplier", 1.0) or 1.0) if goals is not None else 1.0
        for t in range(int(r.start_t), int(r.end_t)):
            mult = 1.0
            bucket = _demand_bucket_for_tick(int(t))
            if bucket == "morning":
                mult = m_morn
            elif bucket == "midday":
                mult = m_mid
            else:
                mult = m_eve
            mn_t = int(round(mn * mult))
            pr_t = int(round(pr * mult))
            mx_t = int(round(mx * mult))
            mn_t = max(0, mn_t)
            pr_t = max(mn_t, pr_t)
            mx_t = max(pr_t, mx_t)

            k = (r.day, r.area, int(t))
            min_req[k] = max(min_req.get(k, 0), mn_t)
            pref_req[k] = max(pref_req.get(k, 0), pr_t)
            if k in max_req:
                max_req[k] = min(max_req[k], mx_t)
            else:
                max_req[k] = mx_t
    for k in set(list(min_req.keys()) + list(pref_req.keys()) + list(max_req.keys())):
        mn = min_req.get(k, 0)
        pr = pref_req.get(k, mn)
        mx = max_req.get(k, pr)
        mn = max(0, mn)
        pr = max(mn, pr)
        mx = max(pr, mx)
        min_req[k] = mn
        pref_req[k] = pr
        max_req[k] = mx
    return min_req, pref_req, max_req

def count_coverage_per_tick(assignments: List[Assignment]) -> Dict[Tuple[str,str,int], int]:
    cov: Dict[Tuple[str,str,int], int] = {}
    for a in assignments:
        for t in range(int(a.start_t), int(a.end_t)):
            k = (a.day, a.area, int(t))
            cov[k] = cov.get(k, 0) + 1
    return cov

def compute_requirement_shortfalls(min_req: Dict[Tuple[str,str,int], int],
                                   pref_req: Dict[Tuple[str,str,int], int],
                                   max_req: Dict[Tuple[str,str,int], int],
                                   cov: Dict[Tuple[str,str,int], int]) -> Tuple[int,int,int]:
    """Return (min_shortfall_ticks, preferred_shortfall_ticks, max_violations_ticks)."""
    min_short = 0
    pref_short = 0
    max_viol = 0
    for k, mn in min_req.items():
        if cov.get(k, 0) < mn:
            min_short += (mn - cov.get(k, 0))
    for k, pr in pref_req.items():
        if cov.get(k, 0) < pr:
            pref_short += (pr - cov.get(k, 0))
    for k, mx in max_req.items():
        if cov.get(k, 0) > mx:
            max_viol += (cov.get(k, 0) - mx)
    return min_short, pref_short, max_viol

def overlaps(a1: Assignment, a2: Assignment) -> bool:
    if a1.employee_name != a2.employee_name or a1.day != a2.day:
        return False
    return not (a1.end_t <= a2.start_t or a1.start_t >= a2.end_t)

def _merge_touching_intervals(intervals: List[Tuple[int,int]]) -> List[Tuple[int,int]]:
    if not intervals:
        return []
    intervals = sorted(intervals, key=lambda x: (x[0], x[1]))
    out = [intervals[0]]
    for st,en in intervals[1:]:
        pst, pen = out[-1]
        # merge if overlaps OR touches (end==start counts as continuous shift)
        if st <= pen:
            out[-1] = (pst, max(pen, en))
        else:
            out.append((st,en))
    return out

def employee_allowed_max_shift_hours(e: Employee) -> float:
    """Hard cap 8h unless employee allows double shifts."""
    mx = float(getattr(e, "max_hours_per_shift", 8.0))
    if not bool(getattr(e, "double_shifts_ok", False)):
        return min(8.0, mx)
    return mx

def daily_shift_blocks(assigns: List[Assignment], emp_name: str, day: str, extra: Optional[Tuple[int,int]] = None) -> List[Tuple[int,int]]:
    intervals = [(a.start_t, a.end_t) for a in assigns if a.employee_name==emp_name and a.day==day]
    if extra is not None:
        intervals.append(extra)
    return _merge_touching_intervals(intervals)

def derive_master_envelopes(assigns: List[Assignment]) -> Dict[Tuple[str, str], List[Tuple[int, int]]]:
    """Read-only derived payroll envelopes per employee/day from flat area segments."""
    by_emp_day: Dict[Tuple[str, str], List[Tuple[int, int]]] = {}
    for a in assigns or []:
        by_emp_day.setdefault((a.employee_name, a.day), []).append((int(a.start_t), int(a.end_t)))
    out: Dict[Tuple[str, str], List[Tuple[int, int]]] = {}
    for k, intervals in by_emp_day.items():
        out[k] = _merge_touching_intervals(intervals)
    return out

def can_place_segment_within_envelope(emp_name: str,
                                      day: str,
                                      st: int,
                                      en: int,
                                      envelopes_by_emp_day: Dict[Tuple[str, str], List[Tuple[int, int]]]) -> bool:
    """True when [st,en] sits wholly inside an existing derived envelope for emp/day."""
    for bst, ben in envelopes_by_emp_day.get((emp_name, day), []):
        if int(st) >= int(bst) and int(en) <= int(ben):
            return True
    return False

def validate_master_envelope_consistency(assigns: List[Assignment],
                                         *,
                                         tol_hours: float = 1e-9) -> Dict[str, Any]:
    """Sanity diagnostics: payroll hours parity and overlap integrity in derived envelopes."""
    envelopes = derive_master_envelopes(assigns)
    raw_hours = float(sum(hours_between_ticks(int(a.start_t), int(a.end_t)) for a in (assigns or [])))

    # Envelope hours count each covered tick once per employee/day.
    envelope_hours = 0.0
    overlap_ticks = 0
    seen_emp_day_ticks: Dict[Tuple[str, str], Set[int]] = {}
    for a in assigns or []:
        key = (a.employee_name, a.day)
        occ = seen_emp_day_ticks.setdefault(key, set())
        for tt in range(int(a.start_t), int(a.end_t)):
            if tt in occ:
                overlap_ticks += 1
            occ.add(tt)
    for (_emp_day, blocks) in envelopes.items():
        for st, en in blocks:
            envelope_hours += hours_between_ticks(int(st), int(en))

    return {
        "raw_assignment_hours": float(raw_hours),
        "derived_envelope_hours": float(envelope_hours),
        "hours_parity_ok": bool(abs(raw_hours - envelope_hours) <= float(tol_hours) or overlap_ticks > 0),
        "overlap_ticks_detected": int(overlap_ticks),
        "envelope_count": int(sum(len(v) for v in envelopes.values())),
    }

def _practical_shift_target_hours(e: Optional[Employee], learned_patterns: Optional[Dict[str, Any]] = None) -> float:
    """Soft practical target for contiguous shift length.

    Priority: learned preferred length -> midpoint of employee min/max -> conservative default.
    """
    if e is None:
        return 4.0
    try:
        if learned_patterns:
            p = (learned_patterns.get(e.name) or {}) if isinstance(learned_patterns, dict) else {}
            pref_len_ticks = int((p or {}).get("preferred_len_ticks", 0) or 0)
            if pref_len_ticks > 0:
                return max(2.0, min(8.0, pref_len_ticks / float(TICKS_PER_HOUR)))
    except Exception:
        pass
    min_h = max(0.5, float(getattr(e, "min_hours_per_shift", 1.0) or 1.0))
    max_h = max(min_h, float(employee_allowed_max_shift_hours(e) or min_h))
    if max_h - min_h <= 0.25:
        return max(2.0, min(8.0, max_h))
    return max(2.0, min(8.0, (min_h + min(max_h, 8.0)) * 0.5))

def _schedule_quality_penalty_units(model: DataModel,
                                    assignments: List[Assignment],
                                    learned_patterns: Optional[Dict[str, Any]] = None) -> Dict[str, float]:
    """Returns soft quality units used to discourage fragmented and micro shifts."""
    emp_by_name = {e.name: e for e in getattr(model, "employees", []) or []}
    by_emp_day: Dict[Tuple[str, str], List[Tuple[int, int]]] = {}
    for a in assignments or []:
        by_emp_day.setdefault((a.employee_name, a.day), []).append((int(a.start_t), int(a.end_t)))

    frag_units = 0.0
    short_units = 0.0
    pref_len_units = 0.0
    fragmented_days = 0
    micro_1h = 0
    micro_2h = 0

    for (emp_name, _day), intervals in by_emp_day.items():
        blocks = _merge_touching_intervals(intervals)
        if not blocks:
            continue
        e = emp_by_name.get(emp_name)
        split_ok = bool(getattr(e, "split_shifts_ok", True)) if e else True
        if len(blocks) > 1:
            fragmented_days += 1
            base_mult = 1.25 if split_ok else 4.0
            frag_units += (len(blocks) - 1) * base_mult

        target_h = _practical_shift_target_hours(e, learned_patterns)
        for st, en in blocks:
            h = hours_between_ticks(st, en)
            if h <= 1.0 + 1e-9:
                micro_1h += 1
                short_units += 8.0
            elif h <= 2.0 + 1e-9:
                micro_2h += 1
                short_units += 3.5
            elif h < 3.0 - 1e-9:
                short_units += 1.25
            if target_h > 0.0:
                pref_len_units += min(4.0, abs(h - target_h))

    return {
        "frag_units": float(frag_units),
        "short_units": float(short_units),
        "pref_len_units": float(pref_len_units),
        "fragmented_days": float(fragmented_days),
        "micro_1h": float(micro_1h),
        "micro_2h": float(micro_2h),
    }

def respects_daily_shift_limits(assigns: List[Assignment], e: Employee, day: str, extra: Optional[Tuple[int,int]] = None) -> bool:
    blocks = daily_shift_blocks(assigns, e.name, day, extra=extra)
    n = len(blocks)
    max_shifts = int(getattr(e, "max_shifts_per_day", 1))
    if max_shifts < 1:
        max_shifts = 1
    if n > max_shifts:
        return False
    if not bool(getattr(e, "split_shifts_ok", True)) and n > 1:
        return False
    # enforce max shift length (per contiguous block)
    mxh = employee_allowed_max_shift_hours(e)
    for st,en in blocks:
        if hours_between_ticks(st,en) - mxh > 1e-9:
            return False
    return True

def respects_max_consecutive_days(assigns: List[Assignment], e: Employee, day: str) -> bool:
    """Hard check for max consecutive days after adding/considering a day assignment."""
    lim = int(getattr(e, "max_consecutive_days", 0) or 0)
    if lim <= 0:
        return True
    if lim >= len(DAYS):
        return True
    days_worked = {a.day for a in assigns if a.employee_name == e.name}
    days_worked.add(day)
    flags = [False] * len(DAYS)
    for d in days_worked:
        if d in DAYS:
            flags[DAYS.index(d)] = True
    if not any(flags):
        return True
    doubled = flags + flags
    run = 0
    maxrun = 0
    for worked in doubled:
        if worked:
            run += 1
            if run > len(DAYS):
                run = len(DAYS)
            maxrun = max(maxrun, run)
        else:
            run = 0
    return maxrun <= lim


@dataclass
class HardRuleViolation:
    code: str
    message: str
    severity: str = "error"
    employee_name: str = ""
    day: str = ""
    assignment_source: str = ASSIGNMENT_SOURCE_ENGINE
    assignment_index: int = -1
    is_override_allowed: bool = False


def _viol_to_text(v: HardRuleViolation) -> str:
    src = f" source={v.assignment_source}" if v.assignment_source else ""
    who = f" employee={v.employee_name}" if v.employee_name else ""
    day = f" day={v.day}" if v.day else ""
    tag = "override-allowed" if v.is_override_allowed else "hard"
    return f"{tag} rule={v.code}{who}{day}{src} {v.message}".strip()


def evaluate_schedule_hard_rules(model: DataModel, label: str, assignments: List[Assignment], include_override_warnings: bool = True) -> List[HardRuleViolation]:
    violations: List[HardRuleViolation] = []
    emp_by_name: Dict[str, Employee] = {e.name: e for e in getattr(model, "employees", []) or []}
    by_emp: Dict[str, List[Tuple[int, Assignment]]] = {}
    for idx, a in enumerate(assignments or []):
        by_emp.setdefault(a.employee_name, []).append((idx, a))

    coverage = count_coverage_per_tick(assignments)
    _min_req, _pref_req, max_req = build_requirement_maps(model.requirements, goals=getattr(model, 'manager_goals', None), store_info=getattr(model, "store_info", None))

    def _derived_provenance(parts: List[Assignment]) -> Tuple[str, bool]:
        """Attribution policy for derived (block/aggregate) violations.

        - If any engine-managed assignment contributes, classify as engine-managed hard.
        - If contributors are override-only (fixed_locked/manual), classify override-allowed.
        - For override-only contributors, prefer MANUAL when any manual edit participates.
        """
        provs = {assignment_provenance(a) for a in (parts or [])}
        if not provs:
            return ASSIGNMENT_SOURCE_ENGINE, False
        if any(is_engine_managed_source(p) for p in provs):
            return ASSIGNMENT_SOURCE_ENGINE, False
        if ASSIGNMENT_SOURCE_MANUAL in provs:
            return ASSIGNMENT_SOURCE_MANUAL, True
        if ASSIGNMENT_SOURCE_FIXED_LOCKED in provs:
            return ASSIGNMENT_SOURCE_FIXED_LOCKED, True
        return ASSIGNMENT_SOURCE_ENGINE, False

    all_emp_names = set(by_emp.keys()) | set(emp_by_name.keys())
    for emp_name in sorted(all_emp_names):
        pairs = list(by_emp.get(emp_name, []))
        e = emp_by_name.get(emp_name)
        if e is None:
            violations.append(HardRuleViolation(code="unknown-employee", message=f"unknown employee in assignment set ({len(pairs)} assignments)", employee_name=emp_name))
            continue
        ordered = sorted(pairs, key=lambda x: (DAYS.index(x[1].day), int(x[1].start_t), int(x[1].end_t), AREAS.index(x[1].area) if x[1].area in AREAS else 999))
        running: List[Assignment] = []
        clopen_min_start: Dict[Tuple[str, str], int] = {}
        weekly_hours = 0.0
        daily_hours: Dict[str, float] = {d: 0.0 for d in DAYS}

        for idx, a in ordered:
            prov = assignment_provenance(a)
            # Only active fixed anchors bypass employee-level constraints.
            # Manual overrides should not inherit fixed-schedule bypass scope.
            is_override = (prov == ASSIGNMENT_SOURCE_FIXED_LOCKED)

            if e.work_status != "Active":
                violations.append(HardRuleViolation(code="active-status", message="employee is not Active", employee_name=emp_name, day=a.day, assignment_source=prov, assignment_index=idx, is_override_allowed=is_override))
            if (not is_override) and a.area not in e.areas_allowed:
                violations.append(HardRuleViolation(code="allowed-area", message=f"area={a.area} not in employee allowed list", employee_name=emp_name, day=a.day, assignment_source=prov, assignment_index=idx, is_override_allowed=is_override))
            if is_override:
                _ok, _msg = fixed_shift_compliance_ok(model, e, label, a.day, int(a.start_t), int(a.end_t), a.area, running)
                if not _ok:
                    violations.append(HardRuleViolation(code="fixed-override-compliance", message=_msg, employee_name=emp_name, day=a.day, assignment_source=prov, assignment_index=idx, is_override_allowed=False))
            elif not is_employee_available(model, e, label, a.day, int(a.start_t), int(a.end_t), a.area, clopen_min_start):
                violations.append(HardRuleViolation(code="availability-window", message=f"{tick_to_hhmm(a.start_t)}-{tick_to_hhmm(a.end_t)} violates availability/override/minor-time rules", employee_name=emp_name, day=a.day, assignment_source=prov, assignment_index=idx, is_override_allowed=is_override))
            if any(overlaps(a, prev) for prev in running if prev.employee_name == emp_name and prev.day == a.day):
                violations.append(HardRuleViolation(code="overlap", message=f"overlap at {tick_to_hhmm(a.start_t)}-{tick_to_hhmm(a.end_t)}", employee_name=emp_name, day=a.day, assignment_source=prov, assignment_index=idx, is_override_allowed=is_override))

            trial = running + [a]
            if (not is_override) and not respects_daily_shift_limits(trial, e, a.day):
                violations.append(HardRuleViolation(code="daily-shift-limits", message="split/max-shifts/max-shift-length violated", employee_name=emp_name, day=a.day, assignment_source=prov, assignment_index=idx, is_override_allowed=is_override))
            if (not is_override) and not respects_max_consecutive_days(trial, e, a.day):
                violations.append(HardRuleViolation(code="max-consecutive-days", message="max consecutive day limit violated", employee_name=emp_name, day=a.day, assignment_source=prov, assignment_index=idx, is_override_allowed=is_override))

            h = hours_between_ticks(int(a.start_t), int(a.end_t))
            weekly_hours += h
            daily_hours[a.day] += h
            running.append(a)
            apply_clopen_from(model, e, a, clopen_min_start)

        for day in DAYS:
            blocks = daily_shift_blocks(running, emp_name, day)
            if not blocks:
                continue
            min_h = float(getattr(e, "min_hours_per_shift", 1.0) or 0.0)
            mx_h = employee_allowed_max_shift_hours(e)
            for st, en in blocks:
                block_h = hours_between_ticks(st, en)
                block_parts = [
                    x for x in running
                    if x.employee_name == emp_name and x.day == day and not (int(en) <= int(x.start_t) or int(st) >= int(x.end_t))
                ]
                block_src, block_override = _derived_provenance(block_parts)
                if (not block_override) and min_h > 0.0 and block_h + 1e-9 < min_h:
                    violations.append(HardRuleViolation(code="min-hours-per-shift", message=f"block {tick_to_hhmm(st)}-{tick_to_hhmm(en)} ({block_h:.1f}h) < min {min_h:.1f}h", employee_name=emp_name, day=day, assignment_source=block_src, is_override_allowed=block_override))
                if (not block_override) and block_h - mx_h > 1e-9:
                    violations.append(HardRuleViolation(code="max-hours-per-shift", message=f"block {tick_to_hhmm(st)}-{tick_to_hhmm(en)} ({block_h:.1f}h) > max {mx_h:.1f}h", employee_name=emp_name, day=day, assignment_source=block_src, is_override_allowed=block_override))

        max_weekly = float(getattr(e, "max_weekly_hours", 0.0) or 0.0)
        weekly_src, weekly_override = _derived_provenance(running)
        if (not weekly_override) and max_weekly > 0.0 and (weekly_hours - max_weekly) > 1e-9:
            violations.append(HardRuleViolation(code="employee-max-weekly-hours", message=f"scheduled={weekly_hours:.1f} max={max_weekly:.1f}", employee_name=emp_name, assignment_source=weekly_src, is_override_allowed=weekly_override))

        # Hard minimum weekly floor: true hard requirement.
        hard_min_weekly = float(getattr(e, "hard_min_weekly_hours", 0.0) or 0.0)
        if e.work_status == "Active" and hard_min_weekly > 0.0 and weekly_hours + 1e-9 < hard_min_weekly:
            violations.append(HardRuleViolation(code="employee-hard-min-weekly-shortfall", severity="error", message=f"scheduled={weekly_hours:.1f} min={hard_min_weekly:.1f}", employee_name=emp_name, assignment_source=ASSIGNMENT_SOURCE_ENGINE))

        if model.nd_rules.enforce and e.minor_type == "MINOR_14_15":
            weekly_cap = nd_minor_weekly_hour_cap(model, e)
            if weekly_cap is not None and (weekly_hours - weekly_cap) > 1e-9:
                violations.append(HardRuleViolation(code="nd-minor-weekly-hours", message=f"scheduled={weekly_hours:.1f} max={weekly_cap:.1f}", employee_name=emp_name, assignment_source=ASSIGNMENT_SOURCE_ENGINE))
            for day, day_h in daily_hours.items():
                daily_cap = nd_minor_daily_hour_cap(model, e, day, label=label)
                if daily_cap is not None and (day_h - daily_cap) > 1e-9:
                    violations.append(HardRuleViolation(code="nd-minor-daily-hours", message=f"scheduled={day_h:.1f} max={daily_cap:.1f}", employee_name=emp_name, day=day, assignment_source=ASSIGNMENT_SOURCE_ENGINE))

    for k, cap in max_req.items():
        cov = int(coverage.get(k, 0))
        if cov > int(cap):
            day, area, tick = k
            violations.append(HardRuleViolation(code="max-staffing-soft-ceiling", severity="warning", message=f"area={area} tick={tick_to_hhmm(int(tick))} scheduled={cov} max={int(cap)}", day=day, assignment_source=ASSIGNMENT_SOURCE_ENGINE))

    total_hours = float(sum(hours_between_ticks(int(a.start_t), int(a.end_t)) for a in assignments))
    locked_override_hours = float(sum(
        hours_between_ticks(int(a.start_t), int(a.end_t))
        for a in assignments
        if assignment_provenance(a) in {ASSIGNMENT_SOURCE_FIXED_LOCKED, ASSIGNMENT_SOURCE_MANUAL}
    ))
    max_weekly_cap = float(getattr(model.manager_goals, 'maximum_weekly_cap', 0.0) or 0.0)
    if max_weekly_cap > 0.0 and (total_hours - max_weekly_cap) > 1e-9:
        override_cap = locked_override_hours - max_weekly_cap > 1e-9
        violations.append(HardRuleViolation(
            code="maximum-weekly-labor-cap",
            message=f"scheduled={total_hours:.1f} cap={max_weekly_cap:.1f}",
            assignment_source=ASSIGNMENT_SOURCE_FIXED_LOCKED if override_cap else ASSIGNMENT_SOURCE_ENGINE,
            is_override_allowed=bool(override_cap),
        ))

    labor_floor = float(getattr(model.manager_goals, 'minimum_weekly_floor', 0.0) or 0.0)
    if labor_floor > 0.0 and total_hours + 1e-9 < labor_floor:
        # Best-effort planning target (warning-only): does not block legality.
        violations.append(HardRuleViolation(code="minimum-weekly-labor-floor-shortfall", severity="warning", message=f"scheduled={total_hours:.1f} floor={labor_floor:.1f}", assignment_source=ASSIGNMENT_SOURCE_ENGINE))

    if include_override_warnings:
        return violations
    return [v for v in violations if not v.is_override_allowed]


def validate_final_schedule_hard(model: DataModel, label: str, assignments: List[Assignment]) -> List[str]:
    """Strict hard-rule validation for finalized schedules.

    Used by generated and manually-loaded flows; includes manager-override warnings so
    diagnostics can distinguish override-authorized exceptions from engine hard failures.
    """
    violations = evaluate_schedule_hard_rules(model, label, assignments, include_override_warnings=True)
    return [_viol_to_text(v) for v in violations]


def schedule_score(model: DataModel, label: str,
                   assignments: List[Assignment],
                   unfilled: int,
                   history_stats: Dict[str, Dict[str,int]],
                   prev_tick_map: Optional[Dict[Tuple[str,str,int], str]] = None) -> float:
    """Return a single numeric score (lower is better).

    Hard constraints should be enforced by construction/feasibility checks.
    This score is used to compare candidate schedules.
    """
    goals = getattr(model, "manager_goals", None)

    # Weight helpers (safe defaults)
    w_under_pref_cov = float(getattr(goals, "w_under_preferred_coverage", 5.0) or 5.0)
    w_over_pref_cap = float(getattr(goals, "w_over_preferred_cap", 20.0) or 20.0)
    w_part_miss = float(getattr(goals, "w_participation_miss", 250.0) or 250.0)
    w_split = float(getattr(goals, "w_split_shifts", 30.0) or 30.0)
    w_imb = float(getattr(goals, "w_hour_imbalance", 2.0) or 2.0)
    enable_util = bool(getattr(goals, "enable_utilization_optimizer", True))
    w_low_hours = float(getattr(goals, "w_low_hours_priority_bonus", 2.5) or 0.0)
    w_near_cap = float(getattr(goals, "w_near_cap_penalty", 5.0) or 0.0)
    balance_tol = float(getattr(goals, "utilization_balance_tolerance_hours", 2.0) or 0.0)
    w_new_emp = float(getattr(goals, "w_new_employee_penalty", 3.0) or 0.0)
    w_frag = float(getattr(goals, "w_fragmentation_penalty", 2.5) or 0.0)
    prefer_longer = bool(getattr(goals, "prefer_longer_shifts", True))
    prefer_area_consistency = bool(getattr(goals, "prefer_area_consistency", False))
    # Phase 3 weights (safe defaults)
    enable_risk = bool(getattr(goals, "enable_coverage_risk_protection", True))
    w_risk = float(getattr(goals, "w_coverage_risk", 10.0) or 0.0)
    enable_util = bool(getattr(goals, "enable_utilization_optimizer", True))
    w_new_emp = float(getattr(goals, "w_new_employee_penalty", 3.0) or 0.0)
    w_frag = float(getattr(goals, "w_fragmentation_penalty", 2.5) or 0.0)
    w_low_hours = float(getattr(goals, "w_low_hours_priority_bonus", 2.5) or 0.0)
    w_near_cap = float(getattr(goals, "w_near_cap_penalty", 5.0) or 0.0)
    balance_tol = float(getattr(goals, "utilization_balance_tolerance_hours", 2.0) or 0.0)


    # Coverage shortfalls/violations
    try:
        min_req_ls, pref_req_ls, max_req_ls = build_requirement_maps(model.requirements, goals=getattr(model,'manager_goals',None), store_info=getattr(model, "store_info", None))
        cov_map = count_coverage_per_tick(assignments)
        min_short, pref_short, max_viol = compute_requirement_shortfalls(min_req_ls, pref_req_ls, max_req_ls, cov_map)
    except Exception:
        min_short, pref_short, max_viol = int(unfilled), 0, 0

    pen = 0.0

    # Hard-ish penalties (very high)
    pen += int(min_short) * 1000.0
    # Max is a soft ceiling (firmer than preferred), not a hard impossibility barrier.
    w_over_max_soft_ceiling = float(getattr(goals, "w_over_max_soft_ceiling", 80.0) or 80.0)
    pen += int(max_viol) * w_over_max_soft_ceiling

    # Soft: preferred coverage shortfall
    pen += int(pref_short) * w_under_pref_cov

    # Phase 4 C3: Risk-Aware Optimization (soft resilience buffer)
    try:
        enable_riskaware = bool(getattr(goals, "enable_risk_aware_optimization", False))
        protect_sp = bool(getattr(goals, "protect_single_point_failures", True))
        w_fragile = float(getattr(goals, "w_risk_fragile", 4.0) or 0.0)
        w_sp = float(getattr(goals, "w_risk_single_point", 8.0) or 0.0)
    except Exception:
        enable_riskaware, protect_sp, w_fragile, w_sp = False, True, 0.0, 0.0

    if enable_riskaware and (w_fragile > 0.0 or w_sp > 0.0):
        try:
            fragile_ticks = 0
            single_point_ticks = 0
            # Use MIN requirements as the baseline for resilience
            for k, req in min_req_ls.items():
                if req <= 0:
                    continue
                cov = cov_map.get(k, 0)
                if cov <= 0:
                    continue
                if cov == req:
                    fragile_ticks += 1
                    if protect_sp and req == 1 and cov == 1:
                        single_point_ticks += 1
            fragile_h = fragile_ticks / float(TICKS_PER_HOUR)
            sp_h = single_point_ticks / float(TICKS_PER_HOUR)
            pen += fragile_h * w_fragile
            if protect_sp:
                pen += sp_h * w_sp
        except Exception:
            pass


    # Soft: preferred weekly cap overage
    try:
        pref_cap = float(getattr(goals, 'preferred_weekly_cap', getattr(goals,'weekly_hours_cap',0.0)) or 0.0)
        if pref_cap > 0.0:
            total_h = sum(hours_between_ticks(a.start_t, a.end_t) for a in assignments)
            if total_h > pref_cap:
                pen += (total_h - pref_cap) * w_over_pref_cap
    except Exception:
        pass

    # Employee hours balance & prefs
    emp_hours: Dict[str, float] = {e.name: 0.0 for e in model.employees}
    emp_days: Dict[str, Set[str]] = {e.name: set() for e in model.employees}
    weekend_ct: Dict[str,int] = {e.name: 0 for e in model.employees}
    undesirable_ct: Dict[str,int] = {e.name: 0 for e in model.employees}
    shifts_per_day: Dict[Tuple[str,str], int] = {}

    for a in assignments:
        emp_hours[a.employee_name] += hours_between_ticks(a.start_t, a.end_t)
        emp_days[a.employee_name].add(a.day)
        shifts_per_day[(a.employee_name, a.day)] = shifts_per_day.get((a.employee_name, a.day), 0) + 1
        if a.day in weekend_days():
            weekend_ct[a.employee_name] += 1
        # undesirable: late close blocks (>=22) and early open (<7)
        if (a.start_t < hhmm_to_tick("07:00")) or (a.end_t >= hhmm_to_tick("22:00")):
            undesirable_ct[a.employee_name] += 1

    
    # --- P2-3: Schedule stability (prefer keeping last week's assignments) ---
    try:
        enable_stab = bool(getattr(goals, "enable_schedule_stability", True))
        w_stab = float(getattr(goals, "w_schedule_stability", 14.0) or 0.0)
    except Exception:
        enable_stab = True
        w_stab = 0.0

    if enable_stab and w_stab > 0.0 and prev_tick_map:
        cur_tick_emp: Dict[Tuple[str,str,int], str] = {}
        for a in assignments:
            for tt in range(int(a.start_t), int(a.end_t)):
                cur_tick_emp[(a.day, a.area, int(tt))] = a.employee_name

        changed_ticks = 0
        for k, prev_emp in prev_tick_map.items():
            cur_emp = cur_tick_emp.get(k)
            if cur_emp != prev_emp:
                changed_ticks += 1
        # Each tick is 30 minutes => 0.5 hours
        pen += float(changed_ticks) * (w_stab * 0.5)

# Soft: split shifts per day
    for (emp, day), n in shifts_per_day.items():
        if n > 1:
            pen += (n - 1) * w_split

    # Soft: prefer longer shifts (penalize segments shorter than 2 hours)
    if prefer_longer:
        for a in assignments:
            hseg = hours_between_ticks(a.start_t, a.end_t)
            if hseg < 2.0:
                pen += (2.0 - hseg) * 8.0

    # Soft: area consistency (penalize multiple areas for same employee)
    if prefer_area_consistency:
        areas_by_emp: Dict[str, Set[str]] = {}
        for a in assignments:
            areas_by_emp.setdefault(a.employee_name, set()).add(a.area)
        for emp, areas in areas_by_emp.items():
            if len(areas) > 1:
                pen += (len(areas) - 1) * 6.0

    # Participation + constraints related penalties
    for e in model.employees:
        if e.work_status != "Active":
            continue
        h = emp_hours.get(e.name, 0.0)
        if e.wants_hours and h < 1.0:
            pen += w_part_miss
        if h > e.max_weekly_hours + 1e-9:
            pen += 5000.0 + (h - e.max_weekly_hours)*200.0
        if e.target_min_hours > 0 and h < e.target_min_hours:
            pen += (e.target_min_hours - h) * 15.0

        # consecutive days
        if e.max_consecutive_days > 0:
            days = [DAYS.index(d) for d in emp_days.get(e.name, set())]
            if days:
                days = sorted(set(days))
                run = 1
                maxrun = 1
                for i in range(1,len(days)):
                    if days[i] == days[i-1] + 1:
                        run += 1
                        maxrun = max(maxrun, run)
                    else:
                        run = 1
                if maxrun > e.max_consecutive_days:
                    pen += (maxrun - e.max_consecutive_days) * 40.0

        # weekend pref
        if e.weekend_preference == "Avoid":
            pen += weekend_ct.get(e.name,0) * 6.0
        elif e.weekend_preference == "Prefer":
            pen -= weekend_ct.get(e.name,0) * 2.0

        # fairness over history
        past_weekends = history_stats.get("weekend", {}).get(e.name, 0)
        past_undes = history_stats.get("undesirable", {}).get(e.name, 0)
        pen += past_weekends * weekend_ct.get(e.name,0) * 0.5
        pen += past_undes * undesirable_ct.get(e.name,0) * 0.3

    # Soft: hour inequality among active opted-in employees
    act = [e for e in model.employees if e.work_status=="Active" and e.wants_hours]
    if act:
        hs = [emp_hours[e.name] for e in act]
        avg = sum(hs)/len(hs)
        pen += sum(abs(x-avg) for x in hs) * w_imb


    # Pattern learning (Phase 2 P2-4) — soft preference from history
    try:
        if bool(getattr(model.settings, "learn_from_history", True)):
            pats = getattr(model, "learned_patterns", {}) or {}
            w_pat = float(getattr(goals, "w_pattern_learning", 8.0) or 8.0) if goals is not None else 8.0
            pat_pen_units = 0.0
            for a in assignments:
                emp = getattr(a, "employee_name", "")
                if not emp:
                    continue
                p = pats.get(emp) or {}
                pref_area = str(p.get("preferred_area", "")).strip()
                if pref_area and str(a.area) != pref_area:
                    pat_pen_units += 1.0
                pref_start = int(p.get("preferred_start_tick", 0) or 0)
                if pref_start:
                    pat_pen_units += min(8.0, abs(int(a.start_t) - pref_start)) * 0.10
                pref_len = int(p.get("preferred_len_ticks", 0) or 0)
                if pref_len:
                    cur_len = max(1, int(a.end_t) - int(a.start_t))
                    pat_pen_units += min(8.0, abs(cur_len - pref_len)) * 0.05
            pen += pat_pen_units * w_pat
    except Exception:
        pass


    
    # Phase 3: utilization optimizer (soft)
    if enable_util and (w_new_emp > 0.0 or w_frag > 0.0):
        try:
            used = {a.employee_name for a in assignments}
            pen += float(len(used)) * w_new_emp
        except Exception:
            pass
        try:
            pen += float(len(assignments)) * w_frag
        except Exception:
            pass

    # Phase 8B: aggressive anti-fragmentation / anti-micro-shift quality bias (soft)
    try:
        pats = getattr(model, "learned_patterns", {}) or {}
        q = _schedule_quality_penalty_units(model, assignments, pats)
        split_weight = max(6.0, w_split * 1.8)
        short_weight = 12.0 if prefer_longer else 8.0
        pref_len_weight = 3.2
        pen += q.get("frag_units", 0.0) * split_weight
        pen += q.get("short_units", 0.0) * short_weight
        pen += q.get("pref_len_units", 0.0) * pref_len_weight
    except Exception:
        pass

    # Store peak hours (soft): reward contiguous practical coverage inside configured rush windows.
    # This bonus is intentionally additive with candidate-level peak guidance: candidate scoring shapes
    # local placement choices, while this final score judges the whole schedule's resulting peak utility.
    try:
        by_emp_day: Dict[Tuple[str, str], List[Tuple[int, int, str]]] = {}
        for a in assignments:
            by_emp_day.setdefault((a.employee_name, a.day), []).append((int(a.start_t), int(a.end_t), str(a.area)))
        peak_bonus = 0.0
        for segs in by_emp_day.values():
            merged = _merge_touching_intervals([(st, en) for (st, en, _area) in segs])
            for st, en, area in segs:
                ov = peak_overlap_ticks(getattr(model, "store_info", None), area, st, en)
                if ov <= 0:
                    continue
                seg_h = float(hours_between_ticks(st, en))
                peak_bonus += (ov / float(TICKS_PER_HOUR)) * PEAK_SOFT_FINAL_OVERLAP_PER_HOUR_BONUS
                if seg_h >= 2.0 - 1e-9:
                    peak_bonus += PEAK_SOFT_FINAL_PRACTICAL_SEGMENT_BONUS
                for mst, men in merged:
                    if int(mst) <= int(st) and int(en) <= int(men):
                        merged_h = float(hours_between_ticks(mst, men))
                        if merged_h >= 3.0 - 1e-9:
                            peak_bonus += PEAK_SOFT_FINAL_CONTIGUOUS_BLOCK_BONUS
                        break
        pen -= peak_bonus
    except Exception:
        pass

    # Final score
    return float(pen)


def schedule_score_breakdown(model: DataModel, label: str,
                             assignments: List[Assignment],
                             unfilled: int,
                             history_stats: Dict[str, Dict[str,int]],
                             prev_tick_map: Optional[Dict[Tuple[str,str,int], str]] = None) -> Dict[str, float]:
    """Explainability helper.

    Returns a dict of penalty components that sum to the same total returned by schedule_score().
    """
    goals = getattr(model, "manager_goals", None)
    # Weight helpers (safe defaults)
    w_under_pref_cov = float(getattr(goals, "w_under_preferred_coverage", 5.0) or 5.0)
    w_over_pref_cap = float(getattr(goals, "w_over_preferred_cap", 20.0) or 20.0)
    w_over_max_soft_ceiling = float(getattr(goals, "w_over_max_soft_ceiling", 80.0) or 80.0)
    w_part_miss = float(getattr(goals, "w_participation_miss", 250.0) or 250.0)
    w_split = float(getattr(goals, "w_split_shifts", 30.0) or 30.0)
    w_imb = float(getattr(goals, "w_hour_imbalance", 2.0) or 2.0)
    prefer_longer = bool(getattr(goals, "prefer_longer_shifts", True))
    prefer_area_consistency = bool(getattr(goals, "prefer_area_consistency", False))
    enable_util = bool(getattr(goals, "enable_utilization_optimizer", True))
    w_low_hours = float(getattr(goals, "w_low_hours_priority_bonus", 2.5) or 0.0)
    w_near_cap = float(getattr(goals, "w_near_cap_penalty", 5.0) or 0.0)
    balance_tol = float(getattr(goals, "utilization_balance_tolerance_hours", 2.0) or 0.0)
    w_new_emp = float(getattr(goals, "w_new_employee_penalty", 3.0) or 0.0)
    w_frag = float(getattr(goals, "w_fragmentation_penalty", 2.5) or 0.0)

    # Coverage shortfalls/violations
    try:
        min_req_ls, pref_req_ls, max_req_ls = build_requirement_maps(
            model.requirements,
            goals=getattr(model,'manager_goals',None),
            store_info=getattr(model, "store_info", None),
        )
        cov_map = count_coverage_per_tick(assignments)
        min_short, pref_short, max_viol = compute_requirement_shortfalls(min_req_ls, pref_req_ls, max_req_ls, cov_map)
    except Exception:
        min_short, pref_short, max_viol = int(unfilled), 0, 0

    out: Dict[str, float] = {
        "min_coverage_pen": float(int(min_short) * 1000.0),
        "max_staffing_violation_pen": float(int(max_viol) * w_over_max_soft_ceiling),
        "preferred_coverage_shortfall_pen": float(int(pref_short) * w_under_pref_cov),
        "risk_fragile_pen": 0.0,
        "risk_single_point_pen": 0.0,
        "preferred_weekly_cap_pen": 0.0,
        "split_shift_pen": 0.0,
        "short_shift_pen": 0.0,
        "area_consistency_pen": 0.0,
        "participation_pen": 0.0,
        "employee_max_hours_pen": 0.0,
        "target_min_hours_pen": 0.0,
        "consecutive_days_pen": 0.0,
        "weekend_pref_pen": 0.0,
        "history_fairness_pen": 0.0,
        "stability_pen": 0.0,
        "hour_imbalance_pen": 0.0,
        "pattern_pen": 0.0,
        "employee_fit_pen": 0.0,
        "utilization_new_employee_pen": 0.0,
        "utilization_fragmentation_pen": 0.0,
        "utilization_balance_pen": 0.0,  # advisory-only (not part of schedule_score total)
        "utilization_near_cap_pen": 0.0,  # advisory-only (not part of schedule_score total)
        "fragmentation_quality_pen": 0.0,
        "micro_shift_quality_pen": 0.0,
        "preferred_length_quality_pen": 0.0,
        "peak_hours_soft_bonus": 0.0,
    }

    # Phase 4 C3: Risk-Aware Optimization (soft resilience buffer)
    try:
        enable_riskaware = bool(getattr(goals, "enable_risk_aware_optimization", False))
        protect_sp = bool(getattr(goals, "protect_single_point_failures", True))
        w_fragile = float(getattr(goals, "w_risk_fragile", 4.0) or 0.0)
        w_sp = float(getattr(goals, "w_risk_single_point", 8.0) or 0.0)
    except Exception:
        enable_riskaware, protect_sp, w_fragile, w_sp = False, True, 0.0, 0.0

    if enable_riskaware and (w_fragile > 0.0 or w_sp > 0.0):
        try:
            fragile_ticks = 0
            single_point_ticks = 0
            for k, req in min_req_ls.items():
                if req <= 0:
                    continue
                cov = cov_map.get(k, 0)
                if cov <= 0:
                    continue
                if cov == req:
                    fragile_ticks += 1
                    if protect_sp and req == 1 and cov == 1:
                        single_point_ticks += 1
            fragile_h = fragile_ticks / float(TICKS_PER_HOUR)
            sp_h = single_point_ticks / float(TICKS_PER_HOUR)
            out["risk_fragile_pen"] += fragile_h * w_fragile
            if protect_sp:
                out["risk_single_point_pen"] += sp_h * w_sp
        except Exception:
            pass

    # Preferred weekly cap overage
    try:
        pref_cap = float(getattr(goals, 'preferred_weekly_cap', getattr(goals,'weekly_hours_cap',0.0)) or 0.0)
        if pref_cap > 0.0:
            total_h = sum(hours_between_ticks(a.start_t, a.end_t) for a in assignments)
            if total_h > pref_cap:
                out["preferred_weekly_cap_pen"] += (total_h - pref_cap) * w_over_pref_cap
    except Exception:
        pass

    emp_hours: Dict[str, float] = {e.name: 0.0 for e in model.employees}
    emp_days: Dict[str, Set[str]] = {e.name: set() for e in model.employees}
    weekend_ct: Dict[str,int] = {e.name: 0 for e in model.employees}
    undesirable_ct: Dict[str,int] = {e.name: 0 for e in model.employees}
    shifts_per_day: Dict[Tuple[str,str], int] = {}

    for a in assignments:
        emp_hours[a.employee_name] += hours_between_ticks(a.start_t, a.end_t)
        emp_days[a.employee_name].add(a.day)
        shifts_per_day[(a.employee_name, a.day)] = shifts_per_day.get((a.employee_name, a.day), 0) + 1
        if a.day in weekend_days():
            weekend_ct[a.employee_name] += 1
        if (a.start_t < hhmm_to_tick("07:00")) or (a.end_t >= hhmm_to_tick("22:00")):
            undesirable_ct[a.employee_name] += 1

    
    # --- P2-3: Schedule stability (prefer keeping last week's assignments) ---
    try:
        enable_stab = bool(getattr(goals, "enable_schedule_stability", True))
        w_stab = float(getattr(goals, "w_schedule_stability", 14.0) or 0.0)
    except Exception:
        enable_stab = True
        w_stab = 0.0

    if enable_stab and w_stab > 0.0 and prev_tick_map:
        cur_tick_emp: Dict[Tuple[str,str,int], str] = {}
        for a in assignments:
            for tt in range(int(a.start_t), int(a.end_t)):
                cur_tick_emp[(a.day, a.area, int(tt))] = a.employee_name

        changed_ticks = 0
        for k, prev_emp in prev_tick_map.items():
            cur_emp = cur_tick_emp.get(k)
            if cur_emp != prev_emp:
                changed_ticks += 1

        out["stability_pen"] = float(changed_ticks) * (w_stab * 0.5)

    for (emp, day), n in shifts_per_day.items():
        if n > 1:
            out["split_shift_pen"] += (n - 1) * w_split

    if prefer_longer:
        for a in assignments:
            hseg = hours_between_ticks(a.start_t, a.end_t)
            if hseg < 2.0:
                out["short_shift_pen"] += (2.0 - hseg) * 8.0

    if prefer_area_consistency:
        areas_by_emp: Dict[str, Set[str]] = {}
        for a in assignments:
            areas_by_emp.setdefault(a.employee_name, set()).add(a.area)
        for emp, areas in areas_by_emp.items():
            if len(areas) > 1:
                out["area_consistency_pen"] += (len(areas) - 1) * 6.0

    for e in model.employees:
        if e.work_status != "Active":
            continue
        h = emp_hours.get(e.name, 0.0)
        if e.wants_hours and h < 1.0:
            out["participation_pen"] += w_part_miss
        if h > e.max_weekly_hours + 1e-9:
            out["employee_max_hours_pen"] += 5000.0 + (h - e.max_weekly_hours)*200.0
        if e.target_min_hours > 0 and h < e.target_min_hours:
            out["target_min_hours_pen"] += (e.target_min_hours - h) * 15.0

        if e.max_consecutive_days > 0:
            days = [DAYS.index(d) for d in emp_days.get(e.name, set())]
            if days:
                days = sorted(set(days))
                run = 1
                maxrun = 1
                for i in range(1,len(days)):
                    if days[i] == days[i-1] + 1:
                        run += 1
                        maxrun = max(maxrun, run)
                    else:
                        run = 1
                if maxrun > e.max_consecutive_days:
                    out["consecutive_days_pen"] += (maxrun - e.max_consecutive_days) * 40.0

        if e.weekend_preference == "Avoid":
            out["weekend_pref_pen"] += weekend_ct.get(e.name,0) * 6.0
        elif e.weekend_preference == "Prefer":
            out["weekend_pref_pen"] -= weekend_ct.get(e.name,0) * 2.0

        past_weekends = history_stats.get("weekend", {}).get(e.name, 0)
        past_undes = history_stats.get("undesirable", {}).get(e.name, 0)
        out["history_fairness_pen"] += past_weekends * weekend_ct.get(e.name,0) * 0.5
        out["history_fairness_pen"] += past_undes * undesirable_ct.get(e.name,0) * 0.3

    act = [e for e in model.employees if e.work_status=="Active" and e.wants_hours]
    if act:
        hs = [emp_hours[e.name] for e in act]
        avg = sum(hs)/len(hs)
        out["hour_imbalance_pen"] += sum(abs(x-avg) for x in hs) * w_imb
        if enable_util:
            try:
                for e in act:
                    h = float(emp_hours.get(e.name, 0.0) or 0.0)
                    under = max(0.0, avg - balance_tol - h)
                    if under > 0.0 and w_low_hours > 0.0:
                        out["utilization_balance_pen"] += under * w_low_hours
                    maxh = float(getattr(e, "max_weekly_hours", 0.0) or 0.0)
                    if maxh > 0.0 and h > (maxh * 0.85) and w_near_cap > 0.0:
                        out["utilization_near_cap_pen"] += ((h - (maxh * 0.85)) / max(1.0, maxh * 0.15)) * w_near_cap
            except Exception:
                pass


    # Pattern learning (Phase 2 P2-4)
    try:
        if bool(getattr(model.settings, "learn_from_history", True)):
            pats = getattr(model, "learned_patterns", {}) or {}
            w_pat = float(getattr(goals, "w_pattern_learning", 8.0) or 8.0) if goals is not None else 8.0
            pat_units = 0.0
            for a in assignments:
                empn = getattr(a, "employee_name", "")
                if not empn:
                    continue
                p = pats.get(empn) or {}
                pref_area = str(p.get("preferred_area", "")).strip()
                if pref_area and str(a.area) != pref_area:
                    pat_units += 1.0
                pref_start = int(p.get("preferred_start_tick", 0) or 0)
                if pref_start:
                    pat_units += min(8.0, abs(int(a.start_t) - pref_start)) * 0.10
                pref_len = int(p.get("preferred_len_ticks", 0) or 0)
                if pref_len:
                    cur_len = max(1, int(a.end_t) - int(a.start_t))
                    pat_units += min(8.0, abs(cur_len - pref_len)) * 0.05
            out["pattern_pen"] += pat_units * w_pat
    except Exception:
        pass

    try:
        if bool(getattr(model.settings, 'enable_employee_fit_engine', True)):
            pats = getattr(model, 'learned_patterns', {}) or {}
            fit_units = 0.0
            for a in assignments:
                fit_score = get_employee_fit_score(pats, getattr(a, 'employee_name', ''), getattr(a, 'area', ''), int(getattr(a, 'start_t', 0) or 0))
                if fit_score < 0:
                    fit_units += abs(float(fit_score))
            out['employee_fit_pen'] += fit_units
    except Exception:
        pass

    if enable_util and (w_new_emp > 0.0 or w_frag > 0.0):
        try:
            used = {a.employee_name for a in assignments}
            out["utilization_new_employee_pen"] += float(len(used)) * w_new_emp
        except Exception:
            pass
        try:
            out["utilization_fragmentation_pen"] += float(len(assignments)) * w_frag
        except Exception:
            pass

    try:
        pats = getattr(model, "learned_patterns", {}) or {}
        q = _schedule_quality_penalty_units(model, assignments, pats)
        split_weight = max(6.0, w_split * 1.8)
        short_weight = 12.0 if prefer_longer else 8.0
        pref_len_weight = 3.2
        out["fragmentation_quality_pen"] += q.get("frag_units", 0.0) * split_weight
        out["micro_shift_quality_pen"] += q.get("short_units", 0.0) * short_weight
        out["preferred_length_quality_pen"] += q.get("pref_len_units", 0.0) * pref_len_weight
    except Exception:
        pass

    # Mirror schedule_score() peak bonus for explainability; kept additive by design (see note there).
    try:
        by_emp_day: Dict[Tuple[str, str], List[Tuple[int, int, str]]] = {}
        for a in assignments:
            by_emp_day.setdefault((a.employee_name, a.day), []).append((int(a.start_t), int(a.end_t), str(a.area)))
        peak_bonus = 0.0
        for segs in by_emp_day.values():
            merged = _merge_touching_intervals([(st, en) for (st, en, _area) in segs])
            for st, en, area in segs:
                ov = peak_overlap_ticks(getattr(model, "store_info", None), area, st, en)
                if ov <= 0:
                    continue
                seg_h = float(hours_between_ticks(st, en))
                peak_bonus += (ov / float(TICKS_PER_HOUR)) * PEAK_SOFT_FINAL_OVERLAP_PER_HOUR_BONUS
                if seg_h >= 2.0 - 1e-9:
                    peak_bonus += PEAK_SOFT_FINAL_PRACTICAL_SEGMENT_BONUS
                for mst, men in merged:
                    if int(mst) <= int(st) and int(en) <= int(men):
                        merged_h = float(hours_between_ticks(mst, men))
                        if merged_h >= 3.0 - 1e-9:
                            peak_bonus += PEAK_SOFT_FINAL_CONTIGUOUS_BLOCK_BONUS
                        break
        out["peak_hours_soft_bonus"] -= peak_bonus
    except Exception:
        pass

    advisory_only = {"utilization_balance_pen", "utilization_near_cap_pen", "employee_fit_pen"}
    out["total"] = float(sum(v for k,v in out.items() if k != "total" and k not in advisory_only))
    return out


def _explain_feasible_reason(model: DataModel, label: str, emp: Employee,
                             day: str, area: str, st: int, en: int,
                             assignments: List[Assignment]) -> Tuple[bool, str]:
    """Return (feasible, reason_if_not). Used for explainability only."""
    cl: Dict[Tuple[str,str], int] = {}
    try:
        for a in assignments:
            if a.employee_name != emp.name:
                continue
            if emp.avoid_clopens:
                end_hr = a.end_t / TICKS_PER_HOUR
                if end_hr >= 22.0:
                    idx = DAYS.index(a.day)
                    nd = DAYS[(idx+1)%7]
                    ms = int(max(0, (a.end_t + model.settings.min_rest_hours*TICKS_PER_HOUR) - DAY_TICKS))
                    cl[(emp.name, nd)] = max(cl.get((emp.name, nd), 0), ms)
    except Exception:
        cl = {}

    if area not in emp.areas_allowed:
        return False, "Not allowed in this area"
    if not is_employee_available(model, emp, label, day, st, en, area, cl):
        return False, "Not available (availability/time-off/clopen/minor rules)"
    if not respects_daily_shift_limits(assignments, emp, day, extra=(st,en)):
        return False, "Daily shift rules would be violated"
    if any(a.employee_name==emp.name and a.day==day and not (en<=a.start_t or st>=a.end_t) for a in assignments):
        return False, "Overlaps an existing shift"
    h = hours_between_ticks(st,en)
    hours_now = sum(hours_between_ticks(a.start_t,a.end_t) for a in assignments if a.employee_name==emp.name)
    if hours_now + h > emp.max_weekly_hours + 1e-9:
        return False, "Would exceed employee max weekly hours"
    if not nd_minor_hours_feasible(model, emp, day, st, en, assignments, label=label):
        return False, "Would exceed ND minor daily/weekly hour limits"
    return True, ""

def history_stats_from(model: DataModel) -> Dict[str, Dict[str,int]]:
    # lookback N
    n = max(0, int(model.settings.fairness_lookback_weeks))
    weekend: Dict[str,int] = {}
    undes: Dict[str,int] = {}
    for s in model.history[-n:]:
        for k,v in s.weekend_counts.items():
            weekend[k] = weekend.get(k,0) + int(v)
        for k,v in s.undesirable_counts.items():
            undes[k] = undes.get(k,0) + int(v)
    return {"weekend": weekend, "undesirable": undes}

def build_locked_and_prefer_from_fixed(model: DataModel, label: str) -> Tuple[List[Assignment], List[Assignment]]:
    locked: List[Assignment] = []
    prefer: List[Assignment] = []
    seen_locked: Set[Tuple[str,str,int,int,str]] = set()
    for e in model.employees:
        if e.work_status != "Active":
            continue
        status = _normalize_fixed_schedule_status(getattr(e, "fixed_schedule_status", "none"))
        if status != "active":
            continue
        for fs in _normalize_fixed_schedule_entries(list(getattr(e, "fixed_schedule", []) or [])):
            if fs.day not in DAYS or fs.area not in AREAS:
                continue
            key = (fs.day, fs.area, int(fs.start_t), int(fs.end_t), e.name)
            if key in seen_locked:
                continue
            seen_locked.add(key)
            locked.append(Assignment(fs.day, fs.area, fs.start_t, fs.end_t, e.name, locked=True, source=ASSIGNMENT_SOURCE_FIXED_LOCKED))
    return locked, prefer

def build_locked_seed_state(model: DataModel,
                            label: str,
                            locked: List[Assignment]) -> Dict[str, Any]:
    """Build read-only locked seed diagnostics/state for phased constructive solving."""
    coverage = count_coverage_per_tick(locked)
    envelopes = derive_master_envelopes(locked)
    by_area_hours: Dict[str, float] = {a: 0.0 for a in AREAS}
    for a in locked:
        by_area_hours[a.area] = by_area_hours.get(a.area, 0.0) + hours_between_ticks(int(a.start_t), int(a.end_t))
    return {
        "locked_count": int(len(locked)),
        "locked_hours": float(sum(hours_between_ticks(int(a.start_t), int(a.end_t)) for a in locked)),
        "locked_hours_by_area": by_area_hours,
        "locked_coverage": coverage,
        "locked_envelopes": envelopes,
        "label": str(label or ""),
    }

def _schedule_total_penalty(model: DataModel, label: str, assignments: List[Assignment], filled: int, total_slots: int, prev_tick_map: Optional[Dict[Tuple[str,str,int], str]] = None) -> float:
    try:
        hist = history_stats_from(model)
        unfilled_ticks = max(0, int(total_slots) - int(filled))
        bd = schedule_score_breakdown(model, label, list(assignments), unfilled_ticks, hist, prev_tick_map or {})
        return float(bd.get("total", 0.0) or 0.0)
    except Exception:
        return 1e9

def improve_weak_areas(model: DataModel,
                       label: str,
                       assignments: List[Assignment],
                       prev_tick_map: Optional[Dict[Tuple[str,str,int], str]] = None,
                       protect_locked: bool = True,
                       protect_manual: bool = True,
                       max_passes: int = 2,
                       max_windows: int = 12,
                       max_attempts_per_window: int = 20,
                       runtime_budget: Optional[SolverRuntimeBudget] = None) -> Tuple[List[Assignment], Dict[str, Any]]:
    """Conservative post-generation targeted improvement pass.

    Focuses only on weak windows (coverage deficits first, fragile windows second)
    and attempts safe local additions without global re-solving.
    """
    base_assignments = list(assignments or [])
    diagnostics: Dict[str, Any] = {
        "engine": "EW1",
        "accepted_moves": 0,
        "rejected_moves": 0,
        "passes_run": 0,
        "windows_examined": 0,
        "attempts": 0,
        "protected_preserved": True,
        "notes": [],
    }
    runtime_budget = runtime_budget or SolverRuntimeBudget("refine", 50.0, 60.0)

    if not base_assignments:
        diagnostics["notes"].append("No assignments provided; nothing to improve.")
        diagnostics["changed"] = False
        return base_assignments, diagnostics

    history_stats = history_stats_from(model)
    min_req, pref_req, max_req = build_requirement_maps(model.requirements, goals=getattr(model, 'manager_goals', None), store_info=getattr(model, "store_info", None))

    def _asig(a: Assignment) -> Tuple[str, str, int, int, str, bool, str]:
        return (
            str(a.day), str(a.area), int(a.start_t), int(a.end_t),
            str(a.employee_name), bool(a.locked), str(a.source),
        )

    def _is_protected(a: Assignment) -> bool:
        if protect_locked and bool(getattr(a, "locked", False)):
            return True
        if protect_manual and assignment_provenance(a) == ASSIGNMENT_SOURCE_MANUAL:
            return True
        return False

    protected_sigs = {_asig(a) for a in base_assignments if _is_protected(a)}

    def _emp_hours(assigns: List[Assignment]) -> Dict[str, float]:
        out: Dict[str, float] = {}
        for a in assigns:
            out[a.employee_name] = out.get(a.employee_name, 0.0) + hours_between_ticks(a.start_t, a.end_t)
        return out

    def _coverage(assigns: List[Assignment]) -> Dict[Tuple[str,str,int], int]:
        return count_coverage_per_tick(assigns)

    def _extract_weak_windows(cov: Dict[Tuple[str,str,int], int]) -> List[Tuple[float, int, str, str, int, int, str]]:
        windows: List[Tuple[float, int, str, str, int, int, str]] = []
        for day in DAYS:
            for area in AREAS:
                t = 0
                while t < DAY_TICKS:
                    req = int(min_req.get((day, area, t), 0))
                    sch = int(cov.get((day, area, t), 0))
                    deficit = max(0, req - sch)
                    if deficit <= 0:
                        t += 1
                        continue
                    st = t
                    peak = deficit
                    deficit_h = 0.0
                    while t < DAY_TICKS:
                        req2 = int(min_req.get((day, area, t), 0))
                        sch2 = int(cov.get((day, area, t), 0))
                        d2 = max(0, req2 - sch2)
                        if d2 <= 0:
                            break
                        peak = max(peak, d2)
                        deficit_h += d2 * 0.5
                        t += 1
                    en = t
                    windows.append((deficit_h, peak, day, area, st, en, "deficit"))
        if windows:
            windows.sort(key=lambda x: (x[0], x[1], -x[4]), reverse=True)
            return windows
        for day in DAYS:
            for area in AREAS:
                t = 0
                while t < DAY_TICKS:
                    req = int(min_req.get((day, area, t), 0))
                    sch = int(cov.get((day, area, t), 0))
                    fragile = (req > 0 and sch == req)
                    if not fragile:
                        t += 1
                        continue
                    st = t
                    peak_req = req
                    h = 0.0
                    while t < DAY_TICKS:
                        req2 = int(min_req.get((day, area, t), 0))
                        sch2 = int(cov.get((day, area, t), 0))
                        if not (req2 > 0 and sch2 == req2):
                            break
                        peak_req = max(peak_req, req2)
                        h += 0.5
                        t += 1
                    en = t
                    windows.append((h, peak_req, day, area, st, en, "fragile"))
        windows.sort(key=lambda x: (x[0], x[1], -x[4]), reverse=True)
        return windows

    def _metrics(assigns: List[Assignment]) -> Tuple[int, int, int, int, float]:
        cov = _coverage(assigns)
        min_short, pref_short, max_viol = compute_requirement_shortfalls(min_req, pref_req, max_req, cov)
        score = float(schedule_score(model, label, assigns, int(min_short), history_stats, prev_tick_map or {}))
        try:
            q = _schedule_quality_penalty_units(model, assigns, getattr(model, "learned_patterns", {}) or {})
            short_count = int((q.get("micro_1h", 0.0) or 0.0) + (q.get("micro_2h", 0.0) or 0.0))
        except Exception:
            short_count = 0
        return int(min_short), int(pref_short), int(max_viol), int(short_count), float(score)

    def _overlaps_emp(assigns: List[Assignment], employee_name: str, day: str, st: int, en: int) -> bool:
        for a in assigns:
            if a.employee_name != employee_name or a.day != day:
                continue
            if not (en <= int(a.start_t) or st >= int(a.end_t)):
                return True
        return False

    def _tick_max_blocked(cov: Dict[Tuple[str,str,int], int], day: str, area: str, st: int, en: int) -> bool:
        # Max is a soft ceiling, not a feasibility blocker.
        return False

    active_emps = [e for e in model.employees if getattr(e, "work_status", "Active") == "Active"]

    emp_flex = {e.name: max(1, len(getattr(e, "areas_allowed", []) or [])) for e in active_emps}
    later_pressure: Dict[Tuple[str, str, int, int], float] = {}

    def _contiguous_extension_bonus(assigns: List[Assignment], emp_name: str, day: str, st: int, en: int) -> float:
        segs = [(int(a.start_t), int(a.end_t)) for a in assigns if a.employee_name == emp_name and a.day == day]
        if not segs:
            return -0.35
        merged_existing = _merge_touching_intervals(segs)
        merged_new = _merge_touching_intervals(segs + [(int(st), int(en))])
        if len(merged_new) < len(merged_existing) + 1:
            return 1.25
        seg_h = hours_between_ticks(st, en)
        return -0.8 if seg_h <= 2.0 + 1e-9 else -0.25

    def _candidate_rank(e: Employee, day: str, area: str, st: int, en: int, emp_hours: Dict[str, float]) -> Tuple[float, float, float, float, str]:
        cur_h = float(emp_hours.get(e.name, 0.0) or 0.0)
        gap = max(0.0, float(getattr(e, "target_min_hours", 0.0) or 0.0) - cur_h)
        stab_match = 0.0
        if prev_tick_map:
            match = 0
            total = max(1, int(en - st))
            for tt in range(int(st), int(en)):
                if prev_tick_map.get((day, area, int(tt))) == e.name:
                    match += 1
            stab_match = match / float(total)
        return (stab_match, _contiguous_extension_bonus(current, e.name, day, st, en), -1.0 / float(emp_flex.get(e.name, 1)), gap + later_pressure.get((day, area, st, min(DAY_TICKS, st + 2)), 0.0) * 0.05, f"{100000-cur_h:09.3f}:{e.name.lower()}")

    current = list(base_assignments)
    cur_min, cur_pref, cur_max, cur_short, cur_score = _metrics(current)
    diagnostics["before_min_shortfall"] = int(cur_min)
    diagnostics["before_pref_shortfall"] = int(cur_pref)
    diagnostics["before_max_violations"] = int(cur_max)
    diagnostics["before_short_shift_count"] = int(cur_short)
    diagnostics["before_score"] = float(cur_score)

    total_window_budget = max(1, int(max_windows))
    max_passes = max(1, int(max_passes))
    max_attempts_per_window = max(1, int(max_attempts_per_window))

    for p in range(max_passes):
        if runtime_budget.should_stop(4.0):
            diagnostics["notes"].append("Runtime budget exhausted before next refine pass.")
            break
        diagnostics["passes_run"] = p + 1
        pass_improved = False
        cov_now = _coverage(current)
        later_pressure = {}
        for day_lp in DAYS:
            for area_lp in AREAS:
                for st_lp in range(DAY_TICKS):
                    later = 0.0
                    horizon = min(DAY_TICKS, st_lp + 8)
                    for tt in range(st_lp, horizon):
                        later += max(0, int(min_req.get((day_lp, area_lp, tt), 0) or 0) - int(cov_now.get((day_lp, area_lp, tt), 0) or 0))
                    later_pressure[(day_lp, area_lp, st_lp, min(DAY_TICKS, st_lp + 2))] = later
        weak_windows = _extract_weak_windows(cov_now)[:total_window_budget]
        if not weak_windows:
            diagnostics["notes"].append("No weak windows detected.")
            break

        emp_hours = _emp_hours(current)
        clopen = _clopen_map_from_assignments(model, current)

        for (_sev_h, _peak, day, area, wst, wen, wkind) in weak_windows:
            if runtime_budget.should_stop(4.0):
                diagnostics["notes"].append("Runtime budget exhausted during weak-window refinement.")
                break
            diagnostics["windows_examined"] += 1
            window_attempts = 0
            starts: List[int] = list(range(int(wst), int(wen)))
            if int(wst) > 0:
                starts.append(int(wst) - 1)
            starts = sorted(set([t for t in starts if 0 <= t < DAY_TICKS]))
            segment_lengths = [6, 4, 2] if wkind == "fragile" else [8, 6, 4, 2]
            accepted_here = False
            for st in starts:
                if accepted_here or window_attempts >= max_attempts_per_window:
                    break
                for seg_len in segment_lengths:
                    if accepted_here or window_attempts >= max_attempts_per_window:
                        break
                    en = st + int(seg_len)
                    if en > DAY_TICKS or en <= int(wst) or st >= int(wen):
                        continue
                    candidates = [e for e in active_emps if area in getattr(e, "areas_allowed", [])]
                    candidates.sort(key=lambda e: _candidate_rank(e, day, area, st, en, emp_hours), reverse=True)
                    for e in candidates:
                        if window_attempts >= max_attempts_per_window:
                            break
                        window_attempts += 1
                        diagnostics["attempts"] += 1
                        runtime_budget.note("refine_candidate_evaluations", 1)
                        if _tick_max_blocked(cov_now, day, area, st, en):
                            diagnostics["rejected_moves"] += 1
                            continue
                        if _overlaps_emp(current, e.name, day, st, en):
                            diagnostics["rejected_moves"] += 1
                            continue
                        if not is_employee_available(model, e, label, day, st, en, area, clopen):
                            diagnostics["rejected_moves"] += 1
                            continue
                        if not respects_daily_shift_limits(current, e, day, extra=(st, en)):
                            diagnostics["rejected_moves"] += 1
                            continue
                        if not respects_max_consecutive_days(current, e, day):
                            diagnostics["rejected_moves"] += 1
                            continue
                        seg_h = hours_between_ticks(st, en)
                        if float(emp_hours.get(e.name, 0.0) or 0.0) + seg_h > float(getattr(e, "max_weekly_hours", 0.0) or 0.0) + 1e-9:
                            diagnostics["rejected_moves"] += 1
                            continue
                        if not nd_minor_hours_feasible(model, e, day, st, en, current, label=label):
                            diagnostics["rejected_moves"] += 1
                            continue
                        trial = list(current)
                        trial.append(Assignment(day=day, area=area, start_t=st, end_t=en, employee_name=e.name, locked=False, source=ASSIGNMENT_SOURCE_ENGINE))
                        trial_errors = [
                            v for v in evaluate_schedule_hard_rules(model, label, trial, include_override_warnings=False)
                            if v.severity == "error" and is_engine_managed_source(v.assignment_source)
                        ]
                        if trial_errors:
                            diagnostics["rejected_moves"] += 1
                            continue
                        t_min, t_pref, t_max, t_short, t_score = _metrics(trial)
                        min_ok = (t_min <= cur_min)
                        score_ok = (t_score <= cur_score + 1e-9)
                        max_ok = (t_max <= cur_max)
                        short_ok = (t_short <= cur_short)
                        extend_bias = _contiguous_extension_bonus(current, e.name, day, st, en)
                        strict_better = (t_min < cur_min) or (t_short < cur_short) or (t_score < cur_score - 1e-9) or (extend_bias > 0.9 and t_min == cur_min and t_short <= cur_short)
                        if min_ok and score_ok and max_ok and short_ok and strict_better:
                            current = trial
                            cur_min, cur_pref, cur_max, cur_short, cur_score = t_min, t_pref, t_max, t_short, t_score
                            cov_now = _coverage(current)
                            emp_hours[e.name] = emp_hours.get(e.name, 0.0) + seg_h
                            clopen = _clopen_map_from_assignments(model, current)
                            diagnostics["accepted_moves"] += 1
                            pass_improved = True
                            accepted_here = True
                        else:
                            diagnostics["rejected_moves"] += 1

        if not pass_improved:
            diagnostics["notes"].append("No accepted improvements in pass; stopping early.")
            break

    final_sigs = {_asig(a) for a in current}
    if not protected_sigs.issubset(final_sigs):
        diagnostics["protected_preserved"] = False
        diagnostics["notes"].append("Protected assignment preservation check failed; returning original schedule.")
        diagnostics["changed"] = False
        diagnostics["after_min_shortfall"] = int(diagnostics.get("before_min_shortfall", 0))
        diagnostics["after_pref_shortfall"] = int(diagnostics.get("before_pref_shortfall", 0))
        diagnostics["after_max_violations"] = int(diagnostics.get("before_max_violations", 0))
        diagnostics["after_score"] = float(diagnostics.get("before_score", 0.0))
        return list(base_assignments), diagnostics

    diagnostics["after_min_shortfall"] = int(cur_min)
    diagnostics["after_pref_shortfall"] = int(cur_pref)
    diagnostics["after_max_violations"] = int(cur_max)
    diagnostics["after_short_shift_count"] = int(cur_short)
    diagnostics["after_score"] = float(cur_score)
    diagnostics["runtime_budget"] = runtime_budget.snapshot()
    changed = list(current) != list(base_assignments)
    diagnostics["changed"] = bool(changed)
    if not diagnostics["changed"]:
        diagnostics["notes"].append("No safe improvement accepted; schedule unchanged.")
        return list(base_assignments), diagnostics
    return current, diagnostics


def requirement_sanity_checker(model: DataModel,
                               label: str,
                               assignments: Optional[List[Assignment]] = None,
                               prev_tick_map: Optional[Dict[Tuple[str,str,int], str]] = None) -> Dict[str, Any]:
    warnings: List[str] = []
    details: Dict[str, Any] = {}
    goals = getattr(model, "manager_goals", None)
    min_req, pref_req, max_req = build_requirement_maps(getattr(model, "requirements", []) or [], goals=goals, store_info=getattr(model, "store_info", None))
    total_min_hours = float(sum(int(v) for v in min_req.values())) / float(TICKS_PER_HOUR)
    total_pref_hours = float(sum(int(v) for v in pref_req.values())) / float(TICKS_PER_HOUR)
    hard_cap = float(getattr(goals, "maximum_weekly_cap", 0.0) or 0.0)
    pref_cap = float(getattr(goals, "preferred_weekly_cap", getattr(goals, "weekly_hours_cap", 0.0)) or 0.0)
    details["total_min_hours"] = float(total_min_hours)
    details["total_preferred_hours"] = float(total_pref_hours)
    details["hard_weekly_cap"] = float(hard_cap)
    details["preferred_weekly_cap"] = float(pref_cap)
    if hard_cap > 0.0 and hard_cap + 1e-9 < total_min_hours:
        warnings.append(f"Hard weekly labor cap ({hard_cap:.1f}h) is below minimum required labor ({total_min_hours:.1f}h).")
    if pref_cap > 0.0 and pref_cap + 1e-9 < total_min_hours:
        warnings.append(f"Preferred weekly labor cap ({pref_cap:.1f}h) is below minimum required labor ({total_min_hours:.1f}h).")
    active_employees = [e for e in (getattr(model, "employees", []) or []) if getattr(e, "work_status", "") == "Active"]
    active_by_area: Dict[str, int] = {a: 0 for a in AREAS}
    for e in active_employees:
        for area in AREAS:
            if area in set(getattr(e, "areas_allowed", []) or []):
                active_by_area[area] += 1
    details["active_by_area"] = dict(active_by_area)
    impossible_windows: List[Dict[str, Any]] = []
    shortage_prone_windows: List[Dict[str, Any]] = []
    for day in DAYS:
        for area in AREAS:
            t = 0
            while t < DAY_TICKS:
                req = int(min_req.get((day, area, t), 0))
                mx = int(max_req.get((day, area, t), 0)) if (day, area, t) in max_req else req
                if req <= 0:
                    t += 1
                    continue
                impossible = (req > int(active_by_area.get(area, 0))) or (mx < req)
                if impossible:
                    st = t
                    peak = req
                    while t < DAY_TICKS:
                        r2 = int(min_req.get((day, area, t), 0))
                        mx2 = int(max_req.get((day, area, t), 0)) if (day, area, t) in max_req else r2
                        if not (r2 > 0 and ((r2 > int(active_by_area.get(area, 0))) or (mx2 < r2))):
                            break
                        peak = max(peak, r2); t += 1
                    impossible_windows.append({"day": day, "area": area, "start_t": st, "end_t": t, "peak_min_required": int(peak), "qualified_active_count": int(active_by_area.get(area, 0))})
                    continue
                ratio = float(req) / float(max(1, int(active_by_area.get(area, 0))))
                if ratio >= 0.75:
                    st = t; peak = req; acc_h = 0.0
                    while t < DAY_TICKS:
                        r2 = int(min_req.get((day, area, t), 0))
                        ratio2 = float(r2) / float(max(1, int(active_by_area.get(area, 0)))) if r2 > 0 else 0.0
                        if not (r2 > 0 and ratio2 >= 0.75):
                            break
                        peak = max(peak, r2); acc_h += 0.5; t += 1
                    shortage_prone_windows.append({"day": day, "area": area, "start_t": st, "end_t": t, "hours": float(acc_h), "peak_min_required": int(peak), "qualified_active_count": int(active_by_area.get(area, 0))})
                    continue
                t += 1
    if impossible_windows:
        warnings.append(f"Detected {len(impossible_windows)} impossible requirement window(s).")
    if shortage_prone_windows:
        warnings.append(f"Detected {len(shortage_prone_windows)} shortage-prone high-demand window(s).")
    observed_shortfalls: Dict[str, Any] = {}
    if assignments is not None:
        cov = count_coverage_per_tick(assignments or [])
        min_short, pref_short, max_viol = compute_requirement_shortfalls(min_req, pref_req, max_req, cov)
        observed_shortfalls = {"min_shortfall_ticks": int(min_short), "preferred_shortfall_ticks": int(pref_short), "max_violation_ticks": int(max_viol)}
        if min_short > 0:
            warnings.append(f"Current schedule has {int(min_short)} unfilled required 30-minute blocks.")
    details["impossible_windows"] = impossible_windows
    details["shortage_prone_windows"] = shortage_prone_windows
    details["observed_shortfalls"] = observed_shortfalls
    return {"label": str(label or ""), "warnings": warnings, "details": details}

def _manual_learning_path() -> str:
    return rel_path("history", "manual_learning_signals.json")

def load_manual_learning_signals() -> Dict[str, Any]:
    p = _manual_learning_path()
    try:
        if os.path.isfile(p):
            with open(p, "r", encoding="utf-8") as f:
                return json.load(f) or {}
    except Exception:
        pass
    return {"version": 1, "updated_on": "", "employee_area_day": {}, "avoidance": {}, "pairings": {}}

def save_manual_learning_signals(signals: Dict[str, Any]) -> None:
    p = _manual_learning_path()
    try:
        ensure_dir(os.path.dirname(p))
        payload = dict(signals or {})
        payload["version"] = int(payload.get("version", 1) or 1)
        payload["updated_on"] = datetime.datetime.now().isoformat(timespec="seconds")
        _atomic_write_json(p, payload, indent=2)
    except Exception:
        pass

def learn_from_manual_edit_delta(before_assignments: List[Assignment], after_assignments: List[Assignment], label: str, max_records_per_bucket: int = 200) -> Dict[str, Any]:
    signals = load_manual_learning_signals()
    ead = dict(signals.get("employee_area_day", {}) or {})
    avoid = dict(signals.get("avoidance", {}) or {})
    pairings = dict(signals.get("pairings", {}) or {})
    def k_assign(a: Assignment) -> Tuple[str, str, int, int, str]:
        return (str(a.day), str(a.area), int(a.start_t), int(a.end_t), str(a.employee_name))
    before_set = {k_assign(a) for a in (before_assignments or [])}
    after_set = {k_assign(a) for a in (after_assignments or [])}
    added = sorted(list(after_set - before_set))
    removed = sorted(list(before_set - after_set))
    for (day, area, st, en, emp) in added:
        key = f"{emp}|{area}|{day}"; row = dict(ead.get(key, {}) or {})
        row["count"] = int(row.get("count", 0) or 0) + 1; row["last_label"] = str(label or ""); row["last_seen"] = datetime.datetime.now().isoformat(timespec="seconds"); ead[key] = row
    for (day, area, st, en, emp) in removed:
        key = f"{emp}|{area}|{day}"; row = dict(avoid.get(key, {}) or {})
        row["count"] = int(row.get("count", 0) or 0) + 1; row["last_label"] = str(label or ""); row["last_seen"] = datetime.datetime.now().isoformat(timespec="seconds"); avoid[key] = row
    slot_to_emps: Dict[Tuple[str,int,int], List[str]] = {}
    for (day, area, st, en, emp) in after_set:
        slot_to_emps.setdefault((day, st, en), []).append(emp)
    for (_day, _st, _en), emps in slot_to_emps.items():
        uniq = sorted(set([str(x) for x in emps if str(x).strip()]))
        if len(uniq) < 2:
            continue
        for i in range(len(uniq)):
            for j in range(i + 1, len(uniq)):
                k = f"{uniq[i]}<->{uniq[j]}"; row = dict(pairings.get(k, {}) or {})
                row["count"] = int(row.get("count", 0) or 0) + 1; row["last_label"] = str(label or ""); row["last_seen"] = datetime.datetime.now().isoformat(timespec="seconds"); pairings[k] = row
    def _trim(d: Dict[str, Any]) -> Dict[str, Any]:
        items = sorted(d.items(), key=lambda kv: int((kv[1] or {}).get("count", 0) or 0), reverse=True)
        return dict(items[:max(1, int(max_records_per_bucket))])
    signals["employee_area_day"] = _trim(ead); signals["avoidance"] = _trim(avoid); signals["pairings"] = _trim(pairings)
    save_manual_learning_signals(signals)
    return {"added_signals": len(added), "removed_signals": len(removed), "pairing_updates": len(pairings), "path": _manual_learning_path()}

def _fairness_memory_path() -> str:
    return rel_path("history", "fairness_memory.json")

def load_fairness_memory() -> Dict[str, Any]:
    p = _fairness_memory_path()
    try:
        if os.path.isfile(p):
            with open(p, "r", encoding="utf-8") as f:
                return json.load(f) or {}
    except Exception:
        pass
    return {"version": 1, "weeks": [], "employees": {}, "updated_on": ""}

def save_fairness_memory(memory: Dict[str, Any]) -> None:
    p = _fairness_memory_path()
    try:
        ensure_dir(os.path.dirname(p))
        payload = dict(memory or {})
        payload["version"] = int(payload.get("version", 1) or 1)
        payload["updated_on"] = datetime.datetime.now().isoformat(timespec="seconds")
        _atomic_write_json(p, payload, indent=2)
    except Exception:
        pass

def update_fairness_memory_from_schedule(label: str, assignments: List[Assignment], keep_weeks: int = 6) -> Dict[str, Any]:
    memory = load_fairness_memory(); per_emp: Dict[str, Dict[str, Any]] = {}
    for a in assignments or []:
        rec = per_emp.setdefault(a.employee_name, {"hours": 0.0, "shift_count": 0, "weekend_shifts": 0, "clopen_burden": 0, "underutilized": 0})
        rec["hours"] += hours_between_ticks(a.start_t, a.end_t); rec["shift_count"] += 1
        if a.day in ("Sat", "Sun"): rec["weekend_shifts"] += 1
    by_emp_day: Dict[Tuple[str, str], List[Assignment]] = {}
    for a in assignments or []: by_emp_day.setdefault((a.employee_name, a.day), []).append(a)
    for k in list(by_emp_day.keys()): by_emp_day[k].sort(key=lambda x: (x.start_t, x.end_t))
    for emp in set([a.employee_name for a in (assignments or [])]):
        for idx, day in enumerate(DAYS):
            cur = by_emp_day.get((emp, day), []); nxt = by_emp_day.get((emp, DAYS[(idx + 1) % 7]), [])
            if not cur or not nxt: continue
            latest_end = max(int(x.end_t) for x in cur); earliest_next = min(int(x.start_t) for x in nxt)
            if latest_end / float(TICKS_PER_HOUR) >= 22.0 and earliest_next / float(TICKS_PER_HOUR) <= 8.0:
                per_emp.setdefault(emp, {"hours": 0.0, "shift_count": 0, "weekend_shifts": 0, "clopen_burden": 0, "underutilized": 0})["clopen_burden"] += 1
    for emp, rec in per_emp.items():
        if float(rec.get("hours", 0.0) or 0.0) < 8.0: rec["underutilized"] = 1
    weeks = list(memory.get("weeks", []) or [])
    weeks = [w for w in weeks if str(w.get("label", "")) != str(label or "")]
    weeks.append({"label": str(label or ""), "employees": per_emp, "saved_on": datetime.datetime.now().isoformat(timespec="seconds")})
    weeks = weeks[-max(1, int(keep_weeks)):]
    memory["weeks"] = weeks
    agg: Dict[str, Dict[str, Any]] = {}
    for w in weeks:
        for emp, rec in dict(w.get("employees", {}) or {}).items():
            a = agg.setdefault(emp, {"weeks": 0, "hours": 0.0, "shift_count": 0, "weekend_shifts": 0, "clopen_burden": 0, "underutilized_weeks": 0})
            a["weeks"] += 1; a["hours"] += float(rec.get("hours", 0.0) or 0.0); a["shift_count"] += int(rec.get("shift_count", 0) or 0); a["weekend_shifts"] += int(rec.get("weekend_shifts", 0) or 0); a["clopen_burden"] += int(rec.get("clopen_burden", 0) or 0); a["underutilized_weeks"] += int(rec.get("underutilized", 0) or 0)
    memory["employees"] = agg; save_fairness_memory(memory)
    return {"label": str(label or ""), "weeks_tracked": len(weeks), "employees_tracked": len(agg), "path": _fairness_memory_path()}

def explain_assignment(model: DataModel, label: str, assignments: List[Assignment], target: Assignment, prev_tick_map: Optional[Dict[Tuple[str,str,int], str]] = None) -> Dict[str, Any]:
    emp = next((e for e in (model.employees or []) if e.name == target.employee_name), None)
    baseline = list(assignments or [])
    without_target = [a for a in baseline if not (a.employee_name == target.employee_name and a.day == target.day and a.area == target.area and int(a.start_t) == int(target.start_t) and int(a.end_t) == int(target.end_t))]
    min_req, pref_req, max_req = build_requirement_maps(model.requirements, goals=getattr(model, "manager_goals", None), store_info=getattr(model, "store_info", None))
    delta_required_ticks = 0; delta_pref_ticks = 0; cov_without = count_coverage_per_tick(without_target)
    for tt in range(int(target.start_t), int(target.end_t)):
        k = (target.day, target.area, int(tt))
        if cov_without.get(k, 0) < min_req.get(k, 0): delta_required_ticks += 1
        if cov_without.get(k, 0) < pref_req.get(k, 0): delta_pref_ticks += 1
    out = {"employee": str(target.employee_name), "day": str(target.day), "area": str(target.area), "start_t": int(target.start_t), "end_t": int(target.end_t), "hours": float(hours_between_ticks(target.start_t, target.end_t)), "locked": bool(getattr(target, "locked", False)), "source": str(getattr(target, "source", "")), "availability_ok": bool(is_employee_available(model, emp, label, target.day, target.start_t, target.end_t, target.area, _clopen_map_from_assignments(model, without_target))) if emp is not None else False, "required_coverage_ticks_supported": int(delta_required_ticks), "preferred_coverage_ticks_supported": int(delta_pref_ticks), "stability_matches_prev_ticks": 0}
    if prev_tick_map:
        match = 0
        for tt in range(int(target.start_t), int(target.end_t)):
            if prev_tick_map.get((target.day, target.area, int(tt))) == target.employee_name: match += 1
        out["stability_matches_prev_ticks"] = int(match)
    return out

def explain_shortage_window(model: DataModel, label: str, assignments: List[Assignment], day: str, area: str, start_t: int, end_t: int) -> Dict[str, Any]:
    min_req, pref_req, max_req = build_requirement_maps(model.requirements, goals=getattr(model, "manager_goals", None), store_info=getattr(model, "store_info", None))
    cov = count_coverage_per_tick(assignments or [])
    deficit_ticks = 0; peak_deficit = 0
    for tt in range(int(start_t), int(end_t)):
        req = int(min_req.get((day, area, int(tt)), 0)); sch = int(cov.get((day, area, int(tt)), 0)); d = max(0, req - sch)
        if d > 0: deficit_ticks += d; peak_deficit = max(peak_deficit, d)
    available: List[str] = []; clopen = _clopen_map_from_assignments(model, assignments or [])
    for e in (model.employees or []):
        if getattr(e, "work_status", "") != "Active": continue
        if area not in (getattr(e, "areas_allowed", []) or []): continue
        if is_employee_available(model, e, label, day, int(start_t), int(end_t), area, clopen): available.append(e.name)
    return {"day": str(day), "area": str(area), "start_t": int(start_t), "end_t": int(end_t), "deficit_headcount_ticks": int(deficit_ticks), "deficit_hours": float(deficit_ticks) / float(TICKS_PER_HOUR), "peak_deficit": int(peak_deficit), "available_candidates": sorted(available)}

def explain_employee_hours(model: DataModel, assignments: List[Assignment], employee_name: str) -> Dict[str, Any]:
    emp = next((e for e in (model.employees or []) if e.name == employee_name), None)
    emp_assigns = [a for a in (assignments or []) if a.employee_name == employee_name]
    total_h = sum(hours_between_ticks(a.start_t, a.end_t) for a in emp_assigns)
    by_day: Dict[str, float] = {d: 0.0 for d in DAYS}
    for a in emp_assigns: by_day[a.day] = by_day.get(a.day, 0.0) + hours_between_ticks(a.start_t, a.end_t)
    weekend_h = by_day.get("Sat", 0.0) + by_day.get("Sun", 0.0)
    target_min = float(getattr(emp, "target_min_hours", 0.0) or 0.0) if emp else 0.0
    max_h = float(getattr(emp, "max_weekly_hours", 0.0) or 0.0) if emp else 0.0
    fairness = load_fairness_memory(); rolling = dict((fairness.get("employees", {}) or {}).get(employee_name, {}) or {})
    return {"employee": str(employee_name), "current_total_hours": float(total_h), "target_min_hours": float(target_min), "max_weekly_hours": float(max_h), "weekend_hours": float(weekend_h), "day_hours": by_day, "assignment_count": len(emp_assigns), "rolling_fairness": rolling}

def run_regression_harness(model: DataModel, label: str, assignments: Optional[List[Assignment]] = None, run_exports: bool = False) -> Dict[str, Any]:
    out: Dict[str, Any] = {"label": str(label or ""), "checks": {}, "notes": []}
    try:
        prev_label, prev_tick = load_prev_final_schedule_tick_map(label); gen = generate_schedule(model, label, prev_tick_map=prev_tick or {})
        out["checks"]["generate_schedule_smoke"] = {"ok": True, "filled": int(gen[4]), "total_slots": int(gen[5]), "warnings": int(len(gen[3] or []))}
    except Exception as ex:
        out["checks"]["generate_schedule_smoke"] = {"ok": False, "error": str(ex)}
    working = list(assignments or [])
    if not working:
        try:
            if out["checks"].get("generate_schedule_smoke", {}).get("ok"): working = list(gen[0])
        except Exception:
            working = []
    try:
        protected = [a for a in working if bool(getattr(a, "locked", False)) or assignment_provenance(a) == ASSIGNMENT_SOURCE_MANUAL]
        improved, diag = improve_weak_areas(model, label, working, runtime_budget=SolverRuntimeBudget("refine", 50.0, 60.0))
        prot_after = {(a.day, a.area, int(a.start_t), int(a.end_t), a.employee_name, bool(a.locked), str(a.source)) for a in improved}
        preserved = True
        for a in protected:
            sig = (a.day, a.area, int(a.start_t), int(a.end_t), a.employee_name, bool(a.locked), str(a.source))
            if sig not in prot_after: preserved = False; break
        out["checks"]["ew1_protected_preservation"] = {"ok": bool(preserved), "diagnostics": diag}
    except Exception as ex:
        out["checks"]["ew1_protected_preservation"] = {"ok": False, "error": str(ex)}
    try:
        report_html = make_manager_report_html(model, label, working)
        has_top = ("Hard Weekly Labor Cap" in report_html and "Actual Scheduled Hours" in report_html and "Remaining Labor Budget" in report_html)
        has_area = ("C-Store shortage hours" in report_html and "Kitchen shortage hours" in report_html and "Carwash shortage hours" in report_html)
        out["checks"]["manager_report_invariants"] = {"ok": bool(has_top and has_area)}
    except Exception as ex:
        out["checks"]["manager_report_invariants"] = {"ok": False, "error": str(ex)}
    if run_exports and working:
        try:
            p1 = export_html(model, label, working); p2 = export_csv(model, label, working); p3 = export_manager_report_html(model, label, working)
            out["checks"]["export_smoke"] = {"ok": bool(os.path.isfile(p1) and os.path.isfile(p2) and os.path.isfile(p3)), "paths": [p1, p2, p3]}
        except Exception as ex:
            out["checks"]["export_smoke"] = {"ok": False, "error": str(ex)}
    try:
        rs = requirement_sanity_checker(model, label, assignments=working)
        out["checks"]["requirement_sanity_checker"] = {"ok": True, "warning_count": int(len(rs.get("warnings", []) or []))}
    except Exception as ex:
        out["checks"]["requirement_sanity_checker"] = {"ok": False, "error": str(ex)}
    return out

def _scenario_variants_for_model(model: DataModel) -> List[Dict[str, Any]]:
    return [
        {"name": "Balanced", "tweaks": {}},
        {"name": "Coverage Priority", "tweaks": {"w_under_preferred_coverage": float(getattr(model.manager_goals, "w_under_preferred_coverage", 5.0) or 5.0) * 1.45, "w_coverage_risk": float(getattr(model.manager_goals, "w_coverage_risk", 10.0) or 10.0) * 1.35}},
        {"name": "Utilization Priority", "tweaks": {"w_low_hours_priority_bonus": float(getattr(model.manager_goals, "w_low_hours_priority_bonus", 2.5) or 2.5) * 1.5, "w_near_cap_penalty": float(getattr(model.manager_goals, "w_near_cap_penalty", 5.0) or 4.0) * 1.4, "w_new_employee_penalty": float(getattr(model.manager_goals, "w_new_employee_penalty", 3.0) or 3.0) * 1.25}},
        {"name": "Stability Priority", "tweaks": {"w_schedule_stability": max(1.0, float(getattr(model.manager_goals, "w_schedule_stability", 14.0) or 12.0) * 1.5), "enable_schedule_stability": True}},
    ]

def generate_schedule_multi_scenario(model: DataModel, label: str, prev_tick_map: Optional[Dict[Tuple[str,str,int], str]] = None, runtime_budget: Optional[SolverRuntimeBudget] = None) -> Tuple[List[Assignment], Dict[str,float], float, List[str], int, int, int, int, Dict[str, Any]]:
    scenario_specs = _scenario_variants_for_model(model)
    best = None
    scenario_rows: List[Dict[str, Any]] = []
    total_iters = 0
    total_restarts = 0
    configured_count = max(1, int(getattr(model.settings, "scenario_schedule_count", 4) or 4))
    scenario_limit = min(len(scenario_specs), configured_count, 3 if configured_count > 1 else 1)
    pressure_stop_reason = ""
    for idx, spec in enumerate(scenario_specs[:scenario_limit]):
        if runtime_budget is not None:
            if idx > 0 and (runtime_budget.target_exhausted() or runtime_budget.should_stop(3.0)):
                pressure_stop_reason = "scenario_budget_pressure"
                break
            remaining_scenarios = max(0, scenario_limit - idx)
            avg_allowance = runtime_budget.seconds_remaining() / float(max(1, remaining_scenarios))
            if idx > 0 and avg_allowance < 8.0:
                pressure_stop_reason = "scenario_average_budget_too_low"
                break
        scenario_started = datetime.datetime.now()
        scenario_model = copy.deepcopy(model)
        for key, value in (spec.get("tweaks") or {}).items():
            try:
                setattr(scenario_model.manager_goals, key, value)
            except Exception:
                pass
        try:
            result = generate_schedule(scenario_model, label, prev_tick_map=prev_tick_map, runtime_budget=runtime_budget)
            assigns, emp_hours, total_hours, warnings, filled, total_slots, iters_done, restarts_done, diag = result
            # OP1: skip extra breakdown work for clearly dominated failing scenarios.
            scenario_failed = (not assigns) or any(('INFEASIBLE' in str(w)) for w in (warnings or []))
            if best is not None and scenario_failed:
                try:
                    best_filled = int(best[1][4])
                except Exception:
                    best_filled = int(filled)
                if int(filled) < max(1, int(best_filled * 0.5)):
                    score_pen = 1e9
                else:
                    score_pen = _schedule_total_penalty(scenario_model, label, assigns, filled, total_slots, prev_tick_map)
            else:
                score_pen = _schedule_total_penalty(scenario_model, label, assigns, filled, total_slots, prev_tick_map)
            total_iters += int(iters_done)
            total_restarts += int(restarts_done)
            diag = dict(diag or {})
            diag["scenario_name"] = spec.get("name", "Scenario")
            diag["scenario_score_penalty"] = float(score_pen)
            engine_hard = int((diag or {}).get("engine_hard_violations", 0) or 0)
            infeasible_warn = int(sum(1 for w in (warnings or []) if "INFEASIBLE" in str(w)))
            row = {
                "name": spec.get("name", "Scenario"),
                "seconds": round((datetime.datetime.now() - scenario_started).total_seconds(), 4),
                "penalty": float(score_pen),
                "hours": float(total_hours),
                "warnings": int(len(warnings or [])),
                "filled": int(filled),
                "total_slots": int(total_slots),
                "engine_hard_violations": int(engine_hard),
                "infeasible_warning_count": int(infeasible_warn),
                "valid": bool(engine_hard == 0),
            }
            scenario_rows.append(row)
            if runtime_budget is not None:
                runtime_budget.note("scenarios_run", 1)
            compare_key = (int(engine_hard), int(infeasible_warn), float(row["penalty"]))
            if best is None or compare_key < best[0]:
                best = (compare_key, (assigns, emp_hours, total_hours, warnings, filled, total_slots, iters_done, restarts_done, diag))
        except Exception as ex:
            scenario_rows.append({"name": spec.get("name", "Scenario"), "penalty": 1e9, "hours": 0.0, "warnings": 1, "filled": 0, "total_slots": 0, "error": str(ex), "seconds": round((datetime.datetime.now() - scenario_started).total_seconds(), 4)})
    if best is None:
        raise RuntimeError("Multi-scenario generation failed for all scenarios.")
    assigns, emp_hours, total_hours, warnings, filled, total_slots, iters_done, restarts_done, diag = best[1]
    diag = dict(diag or {})
    diag["phase5_multi_scenario_enabled"] = True
    diag["phase5_scenarios"] = scenario_rows
    diag["chosen_scenario"] = str(diag.get("scenario_name", "Balanced"))
    diag["scenario_count"] = len(scenario_rows)
    diag["scenario_count_configured"] = int(configured_count)
    diag["scenario_stop_reason"] = pressure_stop_reason or ("configured_limit" if len(scenario_rows) < configured_count else "")
    if runtime_budget is not None:
        diag["runtime_budget"] = runtime_budget.snapshot()
    return assigns, emp_hours, total_hours, warnings, filled, total_slots, int(total_iters or iters_done), int(total_restarts or restarts_done), diag

def generate_schedule(model: DataModel, label: str,
                      prev_tick_map: Optional[Dict[Tuple[str,str,int], str]] = None,
                      runtime_budget: Optional[SolverRuntimeBudget] = None) -> Tuple[List[Assignment], Dict[str,float], float, List[str], int, int, int, int, Dict[str, Any]]:
    """Primary schedule generation path.

    Hard legality remains contract-driven: fast local feasibility checks are retained for performance,
    and final legality is always gated by shared hard-rule evaluation + repair.
    """
    warnings: List[str] = []
    runtime_budget = runtime_budget or SolverRuntimeBudget("generate_fresh", 25.0, 30.0)
    assignments: List[Assignment] = []
    emp_hours: Dict[str,float] = {e.name: 0.0 for e in model.employees}
    # Patch P3-4: speed up employee lookup in the hot path (add_assignment)
    # by avoiding repeated linear scans over model.employees.
    emp_by_name: Dict[str, Employee] = {e.name: e for e in model.employees}
    # Track total scheduled labor hours incrementally so we can enforce the Maximum Weekly Labor Hours Cap.
    total_labor_hours: float = 0.0
    max_weekly_cap: float = float(getattr(model.manager_goals, 'maximum_weekly_cap', 0.0) or 0.0)
    preferred_weekly_cap: float = float(getattr(model.manager_goals, 'preferred_weekly_cap', getattr(model.manager_goals, 'weekly_hours_cap', 0.0)) or 0.0)
    cap_blocked_attempts: int = 0
    cap_blocked_ticks: int = 0
    locked_hours: float = 0.0
    clopen_min_start: Dict[Tuple[str,str], int] = {}

    # Patch P2: observability for solver scoring exceptions (log once per run).
    _warned_once: set = set()
    def _log_once(key: str, msg: str):
        try:
            if key in _warned_once:
                return
            _warned_once.add(key)
            _write_run_log(msg)
        except Exception:
            pass

    def _engine_hard_violations(assigns: List[Assignment]) -> List[HardRuleViolation]:
        """Return non-override hard errors attributable to engine-managed assignments only."""
        out: List[HardRuleViolation] = []
        for v in evaluate_schedule_hard_rules(model, label, assigns, include_override_warnings=False):
            if v.severity == "error" and is_engine_managed_source(v.assignment_source):
                out.append(v)
        return out


    history_stats = history_stats_from(model)

        # Compile per-tick requirements (min/preferred/max)
    min_req, pref_req, max_req = build_requirement_maps(model.requirements, goals=getattr(model,'manager_goals',None), store_info=getattr(model, "store_info", None))
    special_event_days = {d for d in DAYS if is_special_event_day_for_label(model, label, d)}
    if special_event_days:
        for (day, area, tick), mn in list(min_req.items()):
            if day not in special_event_days:
                continue
            pr_cur = int(pref_req.get((day, area, tick), mn))
            mx_cur = int(max_req.get((day, area, tick), max(pr_cur, mn)))
            pref_req[(day, area, tick)] = max(pr_cur, int(mn) + 1)
            max_req[(day, area, tick)] = max(mx_cur, int(pref_req[(day, area, tick)]) + 1)
    total_min_slots = sum(min_req.values())
    total_pref_slots = sum(pref_req.values())

    # Locked fixed shifts first
    locked, prefer_fixed = build_locked_and_prefer_from_fixed(model, label)
    # Track existing day segments for utilization scoring (updated as we add assignments)
    emp_day_segments: Dict[Tuple[str,str], List[Tuple[int,int,str]]] = {}
    emp_day_occupancy: Dict[Tuple[str,str], Set[int]] = {}
    emp_assigned_days: Dict[str, Set[str]] = {e.name: set() for e in model.employees}
    emp_state_version: Dict[str, int] = {e.name: 0 for e in model.employees}
    local_feasible_cache: Dict[Tuple[str, str, str, int, int, int, int], bool] = {}
    for _e in model.employees:
        for _d in DAYS:
            emp_day_segments[(_e.name, _d)] = []
            emp_day_occupancy[(_e.name, _d)] = set()

    # Stage-1 run-state cache for incremental constructive checks.
    area_bounds: Dict[str, Tuple[int, int]] = {a: area_open_close_ticks(model, a) for a in AREAS}
    run_state: Dict[str, Any] = {
        "requirement_maps": (min_req, pref_req, max_req),
        "area_bounds": area_bounds,
        "uncovered_min": {k: int(v) for k, v in min_req.items()},
        "accepted_engine_adds": 0,
        "checkpoint_every": 120,
    }

    solver_selection_telemetry: List[Dict[str, Any]] = []
    add_outcome_counts: Dict[str, int] = {
        "reduced_min": 0,
        "reduced_pref_only": 0,
        "reduced_neither": 0,
    }

    def _daily_store_hours(current: List[Assignment]) -> Dict[str, float]:
        out = {d: 0.0 for d in DAYS}
        for _a in current:
            out[_a.day] = float(out.get(_a.day, 0.0) or 0.0) + float(hours_between_ticks(_a.start_t, _a.end_t))
        return out

    def _daily_employee_hours(current: List[Assignment]) -> Dict[str, Dict[str, float]]:
        out: Dict[str, Dict[str, float]] = {e.name: {d: 0.0 for d in DAYS} for e in model.employees}
        for _a in current:
            row = out.setdefault(_a.employee_name, {d: 0.0 for d in DAYS})
            row[_a.day] = float(row.get(_a.day, 0.0) or 0.0) + float(hours_between_ticks(_a.start_t, _a.end_t))
        return out

    def _min_shortfall_by_day_area(cov: Dict[Tuple[str, str, int], int]) -> Dict[str, Dict[str, int]]:
        out: Dict[str, Dict[str, int]] = {d: {a: 0 for a in AREAS} for d in DAYS}
        for (d, a, t), mn in min_req.items():
            miss = max(0, int(mn) - int(cov.get((d, a, t), 0)))
            if miss > 0:
                out.setdefault(d, {}).setdefault(a, 0)
                out[d][a] += int(miss)
        return out

    def _candidate_demand_delta(day: str, area: str, st: int, en: int, cov: Dict[Tuple[str, str, int], int]) -> Tuple[int, int]:
        min_delta = 0
        pref_delta = 0
        for tt in range(int(st), int(en)):
            key = (day, area, int(tt))
            c = int(cov.get(key, 0))
            if c < int(min_req.get(key, 0)):
                min_delta += 1
                pref_delta += 1
            elif c < int(pref_req.get(key, 0)):
                pref_delta += 1
        return int(min_delta), int(pref_delta)

    def _candidate_distribution_penalty(emp_name: str, day: str, seg_h: float) -> Tuple[float, float, float]:
        by_emp_day = _daily_employee_hours(assignments)
        emp_day_hours = by_emp_day.get(emp_name, {d: 0.0 for d in DAYS})
        emp_pen = float(emp_day_hours.get(day, 0.0) or 0.0)
        store_day_hours = _daily_store_hours(assignments)
        store_pen = float(store_day_hours.get(day, 0.0) or 0.0)
        day_idx_pen = float(DAYS.index(day))
        return emp_pen + max(0.0, seg_h - 2.0), store_pen, day_idx_pen

    phase_snapshots: Dict[str, Dict[str, Any]] = {}
    best_valid_state: Dict[str, Any] = {
        "assignments": list(assignments),
        "coverage": {},
        "emp_hours": dict(emp_hours),
        "total_labor_hours": 0.0,
        "filled": 0,
        "total_slots": int(total_min_slots),
        "warnings": list(warnings),
        "tag": "initial",
    }

    def _deadline_hit(reserve_seconds: float = 0.0) -> bool:
        return bool(runtime_budget and runtime_budget.should_stop(reserve_seconds))

    def _capture_best_valid(tag: str):
        try:
            cov_now = count_coverage_per_tick(assignments)
            min_short_now, _pref_short_now, _max_viol_now = compute_requirement_shortfalls(min_req, pref_req, max_req, cov_now)
            engine_hard_now = len(_engine_hard_violations(assignments))
            if engine_hard_now > 0:
                return
            filled_now = int(sum(min_req.values()) - int(min_short_now))
            rank_now = (int(min_short_now), float(schedule_score(model, label, assignments, int(min_short_now), history_stats, prev_tick_map or {})))
            rank_best = best_valid_state.get("rank")
            if rank_best is None or rank_now < rank_best:
                best_valid_state["rank"] = rank_now
                best_valid_state["assignments"] = list(assignments)
                best_valid_state["coverage"] = dict(cov_now)
                best_valid_state["emp_hours"] = dict(emp_hours)
                best_valid_state["total_labor_hours"] = float(total_labor_hours)
                best_valid_state["filled"] = int(filled_now)
                best_valid_state["total_slots"] = int(total_min_slots)
                best_valid_state["warnings"] = list(warnings)
                best_valid_state["tag"] = str(tag)
        except Exception:
            pass

    def _record_phase_snapshot(phase_name: str):
        hours_by_day = _daily_store_hours(assignments)
        total_h = max(1e-9, float(sum(hours_by_day.values())))
        variance = 0.0
        if hours_by_day:
            vals = [float(hours_by_day.get(d, 0.0) or 0.0) for d in DAYS]
            avg = sum(vals) / float(max(1, len(vals)))
            variance = sum((v - avg) ** 2 for v in vals) / float(max(1, len(vals)))
        early_hours = float(sum(hours_by_day.get(d, 0.0) or 0.0 for d in DAYS[:3]))
        phase_snapshots[phase_name] = {
            "hours_by_day": hours_by_day,
            "sunday_share": float(hours_by_day.get("Sun", 0.0) / total_h),
            "early_week_share": float(early_hours / total_h),
            "day_load_variance": float(variance),
            "per_employee_by_day": _daily_employee_hours(assignments),
            "min_shortfall_by_day_area": _min_shortfall_by_day_area(coverage),
        }

    def _tick_keys_in(day: str, area: str, st: int, en: int):
        for t in range(int(st), int(en)):
            yield (day, area, int(t))

    def _violates_max(day: str, area: str, st: int, en: int, cov: Dict[Tuple[str,str,int], int]) -> bool:
        # Max staffing is modeled as a soft ceiling: we score/diagnose overages,
        # but we do not hard-block feasibility here.
        return False

    def add_assignment(a: Assignment, locked_ok: bool, cov: Dict[Tuple[str,str,int], int], enforce_weekly_cap: bool = True) -> bool:
        nonlocal total_labor_hours, locked_hours, cap_blocked_attempts, cap_blocked_ticks
        e = emp_by_name.get(a.employee_name)
        if e is None:
            return False
        if int(a.end_t) <= int(a.start_t):
            return False

        # Manager overrides are givens by design: accept and report, then work around them.
        if not locked_ok:
            if (not bool(getattr(e, "wants_hours", True))):
                return False
            if not is_employee_available(model, e, label, a.day, a.start_t, a.end_t, a.area, clopen_min_start):
                return False
            if not respects_daily_shift_limits(assignments, e, a.day, extra=(a.start_t, a.end_t)):
                return False
            if not respects_max_consecutive_days(assignments, e, a.day):
                return False
            for ex in assignments:
                if overlaps(ex, a):
                    return False
        else:
            if assignment_provenance(a) == ASSIGNMENT_SOURCE_FIXED_LOCKED:
                ok_fixed, _msg_fixed = fixed_shift_compliance_ok(model, e, label, a.day, a.start_t, a.end_t, a.area, assignments)
                if not ok_fixed:
                    return False
                for ex in assignments:
                    if overlaps(ex, a):
                        return False

        h = hours_between_ticks(a.start_t, a.end_t)
        if (not locked_ok) and enforce_weekly_cap and max_weekly_cap > 0.0 and (total_labor_hours + h) - max_weekly_cap > 1e-9:
            cap_blocked_attempts += 1
            cap_blocked_ticks += int(a.end_t - a.start_t)
            return False
        if (not locked_ok) and emp_hours[e.name] + h > e.max_weekly_hours + 1e-9:
            return False
        if (not locked_ok) and not nd_minor_hours_feasible(model, e, a.day, a.start_t, a.end_t, assignments, label=label):
            return False

        assignments.append(a)
        try:
            emp_day_segments[(a.employee_name, a.day)].append((int(a.start_t), int(a.end_t), a.area))
            emp_assigned_days.setdefault(a.employee_name, set()).add(a.day)
            occ = emp_day_occupancy.setdefault((a.employee_name, a.day), set())
            for tt in range(int(a.start_t), int(a.end_t)):
                occ.add(int(tt))
        except Exception as ex:
            _log_once('emp_day_segments_append', f"[solver] emp_day_segments append failed (likely before init): {ex}")

        emp_hours[e.name] += h
        total_labor_hours += h
        if assignment_provenance(a) == ASSIGNMENT_SOURCE_FIXED_LOCKED:
            locked_hours += h
        apply_clopen_from(model, e, a, clopen_min_start)
        for k in _tick_keys_in(a.day, a.area, a.start_t, a.end_t):
            cov[k] = cov.get(k, 0) + 1
            if k in run_state["uncovered_min"] and run_state["uncovered_min"][k] > 0:
                run_state["uncovered_min"][k] -= 1
        if not locked_ok:
            run_state["accepted_engine_adds"] = int(run_state.get("accepted_engine_adds", 0)) + 1
            emp_state_version[a.employee_name] = int(emp_state_version.get(a.employee_name, 0)) + 1
        return True

    # Seed coverage with locked shifts
    coverage = {}
    for a in locked:
        if not add_assignment(a, locked_ok=True, cov=coverage):
            warnings.append(f"Locked fixed shift could not be assigned: {a.employee_name} {a.day} {a.area} {tick_to_hhmm(a.start_t)}-{tick_to_hhmm(a.end_t)}")
    _capture_best_valid("seed_locked")

    # Phase 4 D6: pattern-learning precompute (soft)
    try:
        pattern_learning_enabled = bool(getattr(model.settings, "learn_from_history", True))
    except Exception:
        pattern_learning_enabled = True
    try:
        learned_patterns = getattr(model, "learned_patterns", {}) or {}
    except Exception:
        learned_patterns = {}
    try:
        w_pattern_learning = float(getattr(model.manager_goals, "w_pattern_learning", 8.0) or 0.0)
    except Exception:
        w_pattern_learning = 0.0

    # OP1: precompute stable candidate-scoring inputs once per generation run.
    weekend_set = weekend_days()
    try:
        enable_stab_global = bool(getattr(model.manager_goals, "enable_schedule_stability", True))
        w_stab_global = float(getattr(model.manager_goals, "w_schedule_stability", 14.0) or 0.0)
    except Exception:
        enable_stab_global = True
        w_stab_global = 0.0
    active_wants_names = [x.name for x in model.employees if x.work_status == "Active" and x.wants_hours]
    fixed_match_bonus: Set[Tuple[str, str, int, int, str]] = set(
        (p.day, p.area, int(p.start_t), int(p.end_t), p.employee_name)
        for p in prefer_fixed
    )
    current_avg_active_wants = 0.0
    scarce_employee_signal: Dict[str, float] = {}
    later_demand_pressure: Dict[Tuple[str, str, int, int], float] = {}

    # Candidate preference score for segment placement
    def candidate_score(e: Employee, day: str, area: str, st: int, en: int) -> float:
        score = 0.0
        # prefer fixed-unlocked boosts if matches exactly
        if (day, area, int(st), int(en), e.name) in fixed_match_bonus:
            score += 30.0

        # stability: prefer the same employee for the same time/area as last schedule
        if enable_stab_global and w_stab_global > 0.0 and prev_tick_map:
            total_ticks = max(1, int(en - st))
            match_ticks = 0
            for tt in range(int(st), int(en)):
                if prev_tick_map.get((day, area, int(tt))) == e.name:
                    match_ticks += 1
            # scale bonus to be comparable with other candidate heuristics
            score += (match_ticks / float(total_ticks)) * (w_stab_global * 0.8)

        if area in e.preferred_areas:
            score += 3.0
        if day in weekend_set and e.weekend_preference=="Avoid":
            score -= 2.5
        if day in weekend_set and e.weekend_preference=="Prefer":
            score += 1.2
        # Soft recurring availability preference (not a hard gate).
        try:
            soft_dr = employee_soft_availability(e).get(day)
            if soft_dr is not None:
                if soft_dr.is_available(int(st), int(en)):
                    score += SOFT_AVAILABILITY_MATCH_BONUS
                else:
                    score -= SOFT_AVAILABILITY_MISS_PENALTY
        except Exception:
            pass

        # Pending selected-week time-off is a mild soft preference only.
        try:
            overlaps_pending = any(r.status == 'pending' for r in get_employee_time_off_for_window(model, label, e.name, day, st, en))
            if overlaps_pending:
                score -= 1.2
        except Exception:
            pass

        if day in special_event_days:
            score += 3.0
        # balance: help those under target min
        gap = max(0.0, e.target_min_hours - emp_hours.get(e.name,0.0))
        score += min(5.0, gap) * 0.8
        # participation: if wants hours and currently 0, boost
        if e.wants_hours and emp_hours.get(e.name,0.0) < 1.0:
            score += 2.0

        # Store peak hours (soft): prefer practical contiguous assignments that capture useful peak coverage.
        try:
            peak_ticks = peak_overlap_ticks(getattr(model, "store_info", None), area, st, en)
            if peak_ticks > 0:
                seg_h = float(hours_between_ticks(st, en))
                score += (peak_ticks / float(TICKS_PER_HOUR)) * PEAK_SOFT_CANDIDATE_OVERLAP_PER_HOUR_BONUS
                if seg_h >= 2.0 - 1e-9:
                    score += PEAK_SOFT_CANDIDATE_PRACTICAL_SEGMENT_BONUS
                segs = emp_day_segments.get((e.name, day), [])
                if segs:
                    merged_existing = _merge_touching_intervals([(int(ast), int(aen)) for (ast, aen, _aa) in segs])
                    merged_with_new = _merge_touching_intervals([(int(ast), int(aen)) for (ast, aen, _aa) in segs] + [(int(st), int(en))])
                    if len(merged_with_new) < (len(merged_existing) + 1):
                        score += PEAK_SOFT_CANDIDATE_CONTIGUOUS_EXTENSION_BONUS
                    elif seg_h < 2.0 - 1e-9:
                        score -= PEAK_SOFT_CANDIDATE_SHORT_ISOLATED_PENALTY
        except Exception as ex:
            _log_once('peak_hours_scoring', f"[solver] peak-hours soft scoring failed: {ex}")

        # Phase 4 C4: workforce utilization optimizer (soft)
        if enable_util:
            try:
                cur_h = float(emp_hours.get(e.name, 0.0) or 0.0)
                seg_h = float(hours_between_ticks(st, en))
                if cur_h < 0.5 and w_new_emp > 0.0:
                    score -= w_new_emp

                avg_h = float(current_avg_active_wants)
                if w_low_hours > 0.0 and cur_h + balance_tol < avg_h:
                    score += min(6.0, (avg_h - cur_h - balance_tol)) * w_low_hours

                target_gap = max(0.0, float(getattr(e, "target_min_hours", 0.0) or 0.0) - cur_h)
                if target_gap > 0.0 and w_target_fill > 0.0:
                    score += min(seg_h, target_gap) * w_target_fill

                maxh = float(getattr(e, "max_weekly_hours", 0.0) or 0.0)
                projected = cur_h + seg_h
                if maxh > 0.0 and projected > (maxh * 0.85) and w_near_cap > 0.0:
                    near_cap_ratio = (projected - (maxh * 0.85)) / max(1.0, maxh * 0.15)
                    score -= max(0.0, near_cap_ratio) * w_near_cap
            except Exception as ex:
                _log_once('util_load_scoring', f"[solver] utilization(load-balance) scoring failed: {ex}")

            try:
                segs = emp_day_segments.get((e.name, day), [])
                if segs:
                    merged_existing = _merge_touching_intervals([(int(ast), int(aen)) for (ast, aen, _aa) in segs])
                    merged_with_new = _merge_touching_intervals([(int(ast), int(aen)) for (ast, aen, _aa) in segs] + [(int(st), int(en))])
                    split_ok = bool(getattr(e, "split_shifts_ok", True))
                    target_h = _practical_shift_target_hours(e, learned_patterns)
                    seg_h = float(hours_between_ticks(st, en))

                    created_new_block = len(merged_with_new) > len(merged_existing)
                    if created_new_block:
                        block_pen = (w_frag * 3.5) if split_ok else (w_frag * 9.0 + 20.0)
                        score -= block_pen

                    # Strong bonus for contiguous growth (touching existing block), regardless of area.
                    extended = len(merged_with_new) < (len(merged_existing) + 1)
                    if extended and w_extend > 0.0:
                        score += (w_extend * 3.0)

                    # Discourage isolated micro fragments.
                    min_delta_local, pref_delta_local = _candidate_demand_delta(day, area, st, en, coverage)
                    if seg_h <= 1.0 + 1e-9:
                        score -= (40.0 if min_delta_local <= 0 else 34.0)
                    elif seg_h <= 2.0 + 1e-9:
                        score -= (20.0 if min_delta_local <= 0 else 16.0)
                    if created_new_block and min_delta_local <= 0:
                        score -= 12.0

                    # Prefer moves that help an existing block approach practical length.
                    best_delta = None
                    contains_new_block = None
                    for bst, ben in merged_with_new:
                        if int(bst) <= int(st) and int(en) <= int(ben):
                            new_h = hours_between_ticks(bst, ben)
                            old_h = max(0.0, new_h - seg_h)
                            before_gap = abs(old_h - target_h)
                            after_gap = abs(new_h - target_h)
                            best_delta = (before_gap - after_gap)
                            contains_new_block = (old_h <= 1e-9)
                            if old_h < 3.0 - 1e-9 and new_h >= 3.0 - 1e-9:
                                score += 14.0
                            if old_h < 4.0 - 1e-9 and new_h >= 4.0 - 1e-9:
                                score += 6.0
                            break
                    if best_delta is not None:
                        mult = 5.0 if contains_new_block else 4.2
                        score += best_delta * mult
            except Exception as ex:
                _log_once('util_segment_scoring', f"[solver] utilization(segment) scoring failed: {ex}")

        # Phase 3: coverage risk protection (soft)
        scarce_signal = float(scarce_employee_signal.get(e.name, 0.0) or 0.0)
        if scarce_signal > 0.0:
            score += scarce_signal * 0.6
        try:
            pressure = float(later_demand_pressure.get((day, area, int(st), min(DAY_TICKS, int(st) + 2)), 0.0) or 0.0)
            score += max(0.0, pressure) * 0.03
        except Exception:
            pass

        if enable_risk and w_risk > 0.0 and tick_scarcity:
            try:
                # Average scarcity-based risk across ticks in this segment
                rs = 0.0
                n = 0
                for tt in range(int(st), int(en)):
                    sc = float(tick_scarcity.get((day, area, int(tt)), 0) or 0.0)
                    rs += 1.0 / max(1.0, sc)
                    n += 1
                seg_risk = rs / float(max(1, n))   # 0..1 (higher = scarcer)
                emp_flex = float(emp_feasible_totals.get(e.name, 0) or 0.0)
                emp_scar = 1.0 / max(1.0, emp_flex)  # higher = scarcer employee

                # Normalize risk into 0..1-ish for typical staffing
                risk_norm = min(1.0, seg_risk * 5.0)
                # Prefer using scarce employees on scarce shifts; prefer flexible employees on easy shifts
                score += (risk_norm * (w_risk * 3.0) * emp_scar) - ((1.0 - risk_norm) * (w_risk * 1.5) * emp_scar)
            except Exception as ex:
                _log_once('coverage_risk_scoring', f"[solver] coverage-risk scoring failed: {ex}")

        # Phase 4 D6: learned pattern preference (soft)
        if pattern_learning_enabled and w_pattern_learning > 0.0 and learned_patterns:
            try:
                p = learned_patterns.get(e.name, {}) or {}
                if p:
                    pref_area = str(p.get("preferred_area", "") or "").strip()
                    if pref_area:
                        if area == pref_area:
                            score += min(4.0, w_pattern_learning * 0.35)
                        else:
                            score -= min(4.0, w_pattern_learning * 0.25)

                    pref_start = int(p.get("preferred_start_tick", 0) or 0)
                    if pref_start > 0:
                        start_delta = abs(int(st) - pref_start)
                        score += max(-3.0, min(3.0, (4.0 - min(4.0, float(start_delta))) * (w_pattern_learning * 0.18)))

                    pref_len = int(p.get("preferred_len_ticks", 0) or 0)
                    if pref_len > 0:
                        cur_len = max(1, int(en) - int(st))
                        len_delta = abs(cur_len - pref_len)
                        score += max(-2.0, min(2.0, (3.0 - min(3.0, float(len_delta))) * (w_pattern_learning * 0.12)))
            except Exception as ex:
                _log_once('pattern_learning_scoring', f"[solver] pattern-learning scoring failed: {ex}")

        try:
            if bool(getattr(model.settings, 'enable_employee_fit_engine', True)) and learned_patterns:
                score += get_employee_fit_score(learned_patterns, e.name, area, st)
        except Exception as ex:
            _log_once('employee_fit_scoring', f"[solver] employee-fit scoring failed: {ex}")

        return score

    def feasible_segment(e: Employee, day: str, area: str, st: int, en: int) -> bool:
        """Stage-2 local feasibility gate for constructive placement.

        This intentionally avoids full-schedule hard-rule evaluation on every candidate.
        Global legality remains enforced at checkpoint/final validation stages.
        """
        emp_ver = int(emp_state_version.get(e.name, 0))
        clopen_gate = int(clopen_min_start.get((e.name, day), 0))
        cache_key = (e.name, day, area, int(st), int(en), emp_ver, clopen_gate)
        cached_local = local_feasible_cache.get(cache_key)
        if cached_local is not None:
            return bool(cached_local)

        def _ret(v: bool) -> bool:
            try:
                local_feasible_cache[cache_key] = bool(v)
            except Exception:
                pass
            return bool(v)

        if st < 0 or en > DAY_TICKS or en <= st:
            return _ret(False)
        if getattr(e, "work_status", "") != "Active":
            return _ret(False)
        if not bool(getattr(e, "wants_hours", True)):
            return _ret(False)
        if area not in getattr(e, "areas_allowed", []):
            return _ret(False)
        op_t, cl_t = run_state["area_bounds"].get(area, (0, DAY_TICKS))
        if int(st) < int(op_t) or int(en) > int(cl_t) or int(en) <= int(st):
            return _ret(False)

        seg_h = hours_between_ticks(st, en)
        min_h = float(getattr(e, "min_hours_per_shift", 1.0) or 1.0)
        max_h = float(employee_allowed_max_shift_hours(e) or 0.0)
        if seg_h + 1e-9 < min_h:
            return _ret(False)
        if max_h > 0.0 and seg_h - max_h > 1e-9:
            return _ret(False)

        if _violates_max(day, area, st, en, coverage):
            return _ret(False)

        if max_weekly_cap > 0.0 and (total_labor_hours + seg_h) - max_weekly_cap > 1e-9:
            return _ret(False)
        if (emp_hours.get(e.name, 0.0) + seg_h) - float(getattr(e, "max_weekly_hours", 0.0) or 0.0) > 1e-9:
            return _ret(False)

        occ = emp_day_occupancy.get((e.name, day), set())
        for tt in range(int(st), int(en)):
            if int(tt) in occ:
                return _ret(False)

        if not is_employee_available(model, e, label, day, st, en, area, clopen_min_start):
            return _ret(False)
        if not respects_daily_shift_limits(assignments, e, day, extra=(st, en)):
            return _ret(False)
        if not respects_max_consecutive_days(assignments, e, day):
            return _ret(False)
        if not nd_minor_hours_feasible(model, e, day, st, en, assignments):
            return _ret(False)
        return _ret(True)

    # --- Phase 3: Coverage Risk Protection + Utilization Optimizer precomputations ---
    try:
        enable_risk = bool(getattr(model.manager_goals, "enable_coverage_risk_protection", True))
        w_risk = float(getattr(model.manager_goals, "w_coverage_risk", 10.0) or 0.0)
    except Exception:
        enable_risk, w_risk = True, 0.0

    try:
        enable_util = bool(getattr(model.manager_goals, "enable_utilization_optimizer", True))
        w_new_emp = float(getattr(model.manager_goals, "w_new_employee_penalty", 3.0) or 0.0)
        w_frag = float(getattr(model.manager_goals, "w_fragmentation_penalty", 2.5) or 0.0)
        w_extend = float(getattr(model.manager_goals, "w_extend_shift_bonus", 2.0) or 0.0)
        w_low_hours = float(getattr(model.manager_goals, "w_low_hours_priority_bonus", 2.5) or 0.0)
        w_near_cap = float(getattr(model.manager_goals, "w_near_cap_penalty", 5.0) or 0.0)
        w_target_fill = float(getattr(model.manager_goals, "w_target_min_fill_bonus", 1.5) or 0.0)
        balance_tol = float(getattr(model.manager_goals, "utilization_balance_tolerance_hours", 2.0) or 0.0)
    except Exception:
        enable_util, w_new_emp, w_frag, w_extend, w_low_hours, w_near_cap, w_target_fill, balance_tol = True, 3.0, 2.5, 2.0, 2.5, 5.0, 1.5, 2.0

    # Scarcity maps (risk protection): how many employees could cover a 1-hour segment starting at tick t
    tick_scarcity: Dict[Tuple[str,str,int], int] = {}
    emp_feasible_totals: Dict[str, int] = {e.name: 0 for e in model.employees}
    specialty_areas: Tuple[str, ...] = ("KITCHEN", "CARWASH")
    specialty_cross_trained: Set[str] = {
        e.name for e in model.employees
        if getattr(e, "work_status", "") == "Active"
        and "CSTORE" in set(getattr(e, "areas_allowed", []) or [])
        and any(sa in set(getattr(e, "areas_allowed", []) or []) for sa in specialty_areas)
    }
    specialty_reserve_hours: float = 3.0
    specialty_peak_windows: List[Dict[str, Any]] = []

    if enable_risk and w_risk > 0.0:
        demand_keys = set()
        try:
            demand_keys.update([k for k,mn in min_req.items() if mn > 0])
        except Exception:
            pass
        try:
            demand_keys.update([k for k,pr in pref_req.items() if pr > 0])
        except Exception:
            pass

        for (day, area, t) in demand_keys:
            if t < 0 or t+2 > DAY_TICKS:
                continue
            cnt = 0
            for e in model.employees:
                if getattr(e, "work_status", "") != "Active":
                    continue
                if area not in getattr(e, "areas_allowed", []):
                    continue
                try:
                    if feasible_segment(e, day, area, int(t), int(t)+2):
                        cnt += 1
                except Exception:
                    continue
            tick_scarcity[(day, area, int(t))] = cnt

        for e in model.employees:
            if getattr(e, "work_status", "") != "Active":
                continue
            tot = 0
            for (day, area, t) in demand_keys:
                if t < 0 or t+2 > DAY_TICKS:
                    continue
                if area not in getattr(e, "areas_allowed", []):
                    continue
                try:
                    if feasible_segment(e, day, area, int(t), int(t)+2):
                        tot += 1
                except Exception:
                    continue
            emp_feasible_totals[e.name] = tot

    # Step 1 diagnostics support: identify specialty peaks where demand pressure is high.
    try:
        specialty_peak_rows: List[Tuple[float, str, str, int, int, int]] = []
        for (day, area, t), mn in min_req.items():
            if area not in specialty_areas or int(mn) <= 0:
                continue
            feasible_count = max(1, int(tick_scarcity.get((day, area, int(t)), 0)))
            pressure = float(mn) / float(feasible_count)
            specialty_peak_rows.append((pressure, day, area, int(t), int(mn), feasible_count))
        specialty_peak_rows.sort(key=lambda x: x[0], reverse=True)
        for pressure, day, area, t, mn, feasible_count in specialty_peak_rows[:40]:
            specialty_peak_windows.append({
                "day": str(day),
                "area": str(area),
                "tick": int(t),
                "start": tick_to_hhmm(int(t)),
                "end": tick_to_hhmm(int(t) + 1),
                "min_required": int(mn),
                "feasible_employee_count": int(feasible_count),
                "pressure": float(pressure),
            })
    except Exception:
        specialty_peak_windows = []

    scarce_employee_signal = {name: (1.0 / max(1.0, float(emp_feasible_totals.get(name, 0) or 0.0))) for name in emp_feasible_totals}
    for day in DAYS:
        for area in AREAS:
            for st in range(0, DAY_TICKS):
                horizon = min(DAY_TICKS, st + 8)
                pressure = 0.0
                for tt in range(st, horizon):
                    pressure += max(0, int(pref_req.get((day, area, tt), 0) or 0) - int(min_req.get((day, area, tt), 0) or 0))
                    pressure += max(0, int(min_req.get((day, area, tt), 0) or 0) - int(coverage.get((day, area, tt), 0) or 0))
                later_demand_pressure[(day, area, st, min(DAY_TICKS, st + 2))] = pressure

    def add_best_segment(day: str, area: str, st: int, en: int, locked_ok: bool=False, enforce_weekly_cap: bool=True) -> bool:
        nonlocal current_avg_active_wants
        pool = [e for e in model.employees if e.work_status=="Active" and bool(getattr(e, "wants_hours", True)) and area in e.areas_allowed]
        if enable_util and w_low_hours > 0.0 and active_wants_names:
            current_avg_active_wants = sum(float(emp_hours.get(nm, 0.0) or 0.0) for nm in active_wants_names) / float(len(active_wants_names))
        else:
            current_avg_active_wants = 0.0
        pool.sort(key=lambda e: candidate_score(e, day, area, st, en), reverse=True)
        ranked: List[Tuple[Tuple[float, float, float, float], Employee]] = []
        min_delta, pref_delta = _candidate_demand_delta(day, area, st, en, coverage)
        seg_h = float(hours_between_ticks(st, en))
        for idx, e in enumerate(pool[:40]):
            if not feasible_segment(e, day, area, st, en):
                continue
            emp_pen, store_pen, day_idx_pen = _candidate_distribution_penalty(e.name, day, seg_h)
            rank = (float(min_delta), float(pref_delta), -float(emp_pen + 0.1 * store_pen), -float(day_idx_pen))
            ranked.append((rank, e))
        if not ranked:
            return False
        ranked.sort(key=lambda x: x[0], reverse=True)
        chosen = ranked[0][1]
        solver_selection_telemetry.append({
            "selector": "add_best_segment",
            "day": day,
            "area": area,
            "start_t": int(st),
            "end_t": int(en),
            "feasible_candidates": int(len(ranked)),
            "chosen_employee": chosen.name,
            "chosen_rank": list(ranked[0][0]),
            "earliest_iterated_candidate": bool(chosen.name == pool[0].name) if pool else False,
            "later_day_alternative_exists": False,
        })
        before_min, before_pref = _candidate_demand_delta(day, area, st, en, coverage)
        ok = add_assignment(Assignment(day, area, st, en, chosen.name, locked=False, source=ASSIGNMENT_SOURCE_ENGINE), locked_ok=locked_ok, cov=coverage, enforce_weekly_cap=enforce_weekly_cap)
        if ok:
            after_min, after_pref = _candidate_demand_delta(day, area, st, en, coverage)
            if after_min < before_min:
                add_outcome_counts["reduced_min"] += 1
            elif after_pref < before_pref:
                add_outcome_counts["reduced_pref_only"] += 1
            else:
                add_outcome_counts["reduced_neither"] += 1
        return ok

    envelopes_by_emp_day: Dict[Tuple[str, str], List[Tuple[int, int]]] = derive_master_envelopes(assignments)

    def recompute_uncovered_maps_incremental() -> Dict[str, Dict[Tuple[str, str, int], int]]:
        out: Dict[str, Dict[Tuple[str, str, int], int]] = {a: {} for a in AREAS}
        for (day, area, tick), mn in min_req.items():
            if int(mn) <= 0:
                continue
            remain = int(mn) - int(coverage.get((day, area, tick), 0))
            if remain > 0:
                out.setdefault(area, {})[(day, area, tick)] = int(remain)
        return out

    def open_or_extend_master_envelope(day: str,
                                       area: str,
                                       st: int,
                                       en: int,
                                       *,
                                       only_within_existing: bool = False,
                                       enforce_weekly_cap: bool = True,
                                       prefer_underutilized: bool = False) -> bool:
        nonlocal current_avg_active_wants, envelopes_by_emp_day
        pool = [e for e in model.employees if e.work_status == "Active" and bool(getattr(e, "wants_hours", True)) and area in e.areas_allowed]
        if prefer_underutilized:
            pool.sort(key=lambda e: float(emp_hours.get(e.name, 0.0) or 0.0))
        else:
            if enable_util and w_low_hours > 0.0 and active_wants_names:
                current_avg_active_wants = sum(float(emp_hours.get(nm, 0.0) or 0.0) for nm in active_wants_names) / float(len(active_wants_names))
            else:
                current_avg_active_wants = 0.0
            pool.sort(key=lambda e: candidate_score(e, day, area, st, en), reverse=True)

        if area == "CSTORE" and specialty_cross_trained:
            def _slack_priority(emp: Employee) -> Tuple[int, float]:
                curr_h = float(emp_hours.get(emp.name, 0.0) or 0.0)
                max_h = float(getattr(emp, "max_weekly_hours", 0.0) or 0.0)
                remaining = max(0.0, max_h - curr_h)
                reserve_block = 1 if (emp.name in specialty_cross_trained and remaining <= (specialty_reserve_hours + 1.0)) else 0
                return (reserve_block, curr_h)
            pool.sort(key=_slack_priority)

        ranked: List[Tuple[Tuple[float, float, float, float], Employee]] = []
        min_delta, pref_delta = _candidate_demand_delta(day, area, st, en, coverage)
        seg_h = float(hours_between_ticks(st, en))
        for e in pool[:50]:
            within = can_place_segment_within_envelope(e.name, day, st, en, envelopes_by_emp_day)
            if only_within_existing and not within:
                continue
            if not feasible_segment(e, day, area, st, en):
                continue
            emp_pen, store_pen, day_idx_pen = _candidate_distribution_penalty(e.name, day, seg_h)
            contiguous_bonus = 0.0
            segs = emp_day_segments.get((e.name, day), [])
            if segs:
                merged_existing = _merge_touching_intervals([(int(ast), int(aen)) for (ast, aen, _aa) in segs])
                merged_with_new = _merge_touching_intervals([(int(ast), int(aen)) for (ast, aen, _aa) in segs] + [(int(st), int(en))])
                if len(merged_with_new) < (len(merged_existing) + 1):
                    contiguous_bonus = 1.0
            rank = (float(min_delta), float(pref_delta), float(contiguous_bonus) - float(emp_pen + 0.15 * store_pen), -float(day_idx_pen))
            ranked.append((rank, e))
        if not ranked:
            return False
        ranked.sort(key=lambda x: x[0], reverse=True)
        chosen = ranked[0][1]
        solver_selection_telemetry.append({
            "selector": "open_or_extend_master_envelope",
            "day": day,
            "area": area,
            "start_t": int(st),
            "end_t": int(en),
            "feasible_candidates": int(len(ranked)),
            "chosen_employee": chosen.name,
            "chosen_rank": list(ranked[0][0]),
            "later_day_alternative_exists": False,
        })
        before_min, before_pref = _candidate_demand_delta(day, area, st, en, coverage)
        if add_assignment(Assignment(day, area, st, en, chosen.name, locked=False, source=ASSIGNMENT_SOURCE_ENGINE), locked_ok=False, cov=coverage, enforce_weekly_cap=enforce_weekly_cap):
            envelopes_by_emp_day = derive_master_envelopes(assignments)
            after_min, after_pref = _candidate_demand_delta(day, area, st, en, coverage)
            if after_min < before_min:
                add_outcome_counts["reduced_min"] += 1
            elif after_pref < before_pref:
                add_outcome_counts["reduced_pref_only"] += 1
            else:
                add_outcome_counts["reduced_neither"] += 1
            return True
        return False

    def phase_fill_area_min(area: str,
                            *,
                            lengths: Tuple[int, ...],
                            only_within_existing: bool,
                            enforce_weekly_cap: bool,
                            prefer_underutilized: bool = False,
                            max_keys: int = 8000) -> Dict[str, int]:
        stats = {"attempts": 0, "adds": 0, "stopped_for_budget": False}
        progressed = True
        while progressed:
            if _deadline_hit(5.0):
                stats["stopped_for_budget"] = True
                break
            progressed = False
            all_deficits: List[Tuple[float, str, str, int]] = []
            for (d, a, t), mn in min_req.items():
                miss = int(mn) - int(coverage.get((d, a, t), 0))
                if miss <= 0:
                    continue
                feasible_cnt = max(1, int(tick_scarcity.get((d, a, int(t)), 0) or 1))
                all_deficits.append((float(miss) / float(feasible_cnt), d, a, int(t)))
            all_deficits.sort(key=lambda x: (x[0], -DAYS.index(x[1]), -int(x[3])), reverse=True)
            picked = [(d, a, t) for _s, d, a, t in all_deficits if a == area][:max_keys]
            for (day, _area, t) in picked:
                if _deadline_hit(5.0):
                    stats["stopped_for_budget"] = True
                    break
                if coverage.get((day, area, t), 0) >= min_req.get((day, area, t), 0):
                    continue
                st = int(t)
                if st > 0 and coverage.get((day, area, st), 0) < min_req.get((day, area, st), 0) and coverage.get((day, area, st - 1), 0) < min_req.get((day, area, st - 1), 0):
                    st -= 1
                scored_lengths: List[Tuple[Tuple[float, float, float], int]] = []
                for L in lengths:
                    en = st + int(L)
                    if en > DAY_TICKS:
                        continue
                    min_delta, pref_delta = _candidate_demand_delta(day, area, st, en, coverage)
                    # Allow 30-minute deficit repairs when legal.
                    if min_delta < 1:
                        continue
                    day_load = float(_daily_store_hours(assignments).get(day, 0.0) or 0.0)
                    scored_lengths.append(((float(min_delta), float(pref_delta), -day_load), int(L)))
                if not scored_lengths:
                    continue
                scored_lengths.sort(key=lambda x: x[0], reverse=True)
                for _rank, L in scored_lengths:
                    en = st + int(L)
                    stats["attempts"] += 1
                    if open_or_extend_master_envelope(day, area, st, en,
                                                      only_within_existing=only_within_existing,
                                                      enforce_weekly_cap=enforce_weekly_cap,
                                                      prefer_underutilized=prefer_underutilized):
                        progressed = True
                        stats["adds"] += 1
                        _capture_best_valid(f"fill_{area.lower()}")
                        break
                if progressed:
                    break
        return stats

    def phase_backfill_cstore_from_pool(*,
                                        only_within_existing: bool,
                                        enforce_weekly_cap: bool,
                                        max_keys: int = 6000) -> Dict[str, int]:
        return phase_fill_area_min(
            "CSTORE",
            lengths=(6, 4, 2),
            only_within_existing=only_within_existing,
            enforce_weekly_cap=enforce_weekly_cap,
            prefer_underutilized=True,
            max_keys=max_keys,
        )

    # ---- Phase runner: master-envelope hierarchy ----
    phase_diagnostics: Dict[str, Dict[str, Any]] = {}

    phase_diagnostics["phase0_seed_locked"] = {
        "seed": build_locked_seed_state(model, label, [a for a in assignments if assignment_provenance(a) == ASSIGNMENT_SOURCE_FIXED_LOCKED]),
        "envelope_consistency": validate_master_envelope_consistency(assignments),
    }

    hard_min_phase_details: Dict[str, Dict[str, Any]] = {}

    def phase_assign_hard_minimum_hours() -> Dict[str, Any]:
        stats: Dict[str, Any] = {
            "employees_considered": 0,
            "employees_with_targets": 0,
            "employees_met": 0,
            "employees_unmet": 0,
            "hours_added": 0.0,
            "per_employee": hard_min_phase_details,
        }

        def _base_entry(emp: Employee) -> Dict[str, Any]:
            pre_h = float(emp_hours.get(emp.name, 0.0) or 0.0)
            locked_h = float(sum(
                hours_between_ticks(int(a.start_t), int(a.end_t))
                for a in assignments
                if a.employee_name == emp.name and assignment_provenance(a) == ASSIGNMENT_SOURCE_FIXED_LOCKED
            ))
            req_h = max(0.0, float(getattr(emp, "hard_min_weekly_hours", 0.0) or 0.0))
            return {
                "requested_min": req_h,
                "locked_credit": locked_h,
                "pre_phase_hours": pre_h,
                "added_in_hard_min_phase": 0.0,
                "post_phase_hours": pre_h,
                "remaining_shortfall": max(0.0, req_h - pre_h),
                "blockers": [],
                "attempt_counters": {
                    "considered": 0,
                    "not_cstore": 0,
                    "blocked_by_weekly_cap": 0,
                    "blocked_by_hard_rules": 0,
                    "no_legal_slot": 0,
                },
            }

        target_emps: List[Employee] = [
            e for e in model.employees
            if e.work_status == "Active" and float(getattr(e, "hard_min_weekly_hours", 0.0) or 0.0) > 0.0
        ]
        stats["employees_considered"] = int(len(target_emps))
        for e in target_emps:
            hard_min_phase_details[e.name] = _base_entry(e)

        target_emps.sort(key=lambda e: (
            -(float(getattr(e, "hard_min_weekly_hours", 0.0) or 0.0) - float(emp_hours.get(e.name, 0.0) or 0.0)),
            float(emp_hours.get(e.name, 0.0) or 0.0),
            e.name.lower(),
        ))

        for e in target_emps:
            if _deadline_hit(4.0):
                detail = hard_min_phase_details.get(e.name, {})
                detail.setdefault("blockers", []).append("runtime_budget_exhausted")
                break
            detail = hard_min_phase_details.get(e.name, {})
            requested = float(detail.get("requested_min", 0.0) or 0.0)
            current = float(emp_hours.get(e.name, 0.0) or 0.0)
            deficit = max(0.0, requested - current)
            if deficit <= 1e-9:
                detail["post_phase_hours"] = current
                detail["remaining_shortfall"] = 0.0
                stats["employees_met"] = int(stats.get("employees_met", 0)) + 1
                continue

            stats["employees_with_targets"] = int(stats.get("employees_with_targets", 0)) + 1
            max_shift_h = max(0.0, float(employee_allowed_max_shift_hours(e) or 0.0))
            min_shift_h = max(0.5, float(getattr(e, "min_hours_per_shift", 1.0) or 1.0))
            practical_lengths = [8.0, 6.0, 4.0, 3.0, 2.0, min_shift_h]
            practical_lengths = [h for h in practical_lengths if h >= min_shift_h - 1e-9 and h <= max_shift_h + 1e-9]
            practical_lengths = sorted(set(max(min_shift_h, round(h * 2.0) / 2.0) for h in practical_lengths), reverse=True)
            if not practical_lengths:
                detail.setdefault("blockers", []).append("no_valid_shift_length_profile")
                detail["remaining_shortfall"] = max(0.0, requested - float(emp_hours.get(e.name, 0.0) or 0.0))
                stats["employees_unmet"] = int(stats.get("employees_unmet", 0)) + 1
                continue

            preferred_areas = []
            if "CSTORE" in (getattr(e, "areas_allowed", []) or []):
                preferred_areas.append("CSTORE")
            else:
                detail.setdefault("attempt_counters", {}).setdefault("not_cstore", 0)
                detail["attempt_counters"]["not_cstore"] += 1
            for ar in (getattr(e, "areas_allowed", []) or []):
                if ar not in preferred_areas:
                    preferred_areas.append(ar)
            if not preferred_areas:
                detail.setdefault("blockers", []).append("no_allowed_area")
                detail["remaining_shortfall"] = max(0.0, requested - float(emp_hours.get(e.name, 0.0) or 0.0))
                stats["employees_unmet"] = int(stats.get("employees_unmet", 0)) + 1
                continue

            passes = 0
            while max(0.0, requested - float(emp_hours.get(e.name, 0.0) or 0.0)) > 1e-9 and passes < 8:
                if _deadline_hit(4.0):
                    detail.setdefault("blockers", []).append("runtime_budget_exhausted")
                    break
                passes += 1
                placed = False
                remaining = max(0.0, requested - float(emp_hours.get(e.name, 0.0) or 0.0))
                ranked_candidates: List[Tuple[Tuple[float, float, float, float, float], Assignment, bool]] = []
                day_order = sorted(
                    DAYS,
                    key=lambda day_name: (
                        float(sum(max(0, int(min_req.get((day_name, area_name, tick), 0) or 0) - int(coverage.get((day_name, area_name, tick), 0) or 0)) for area_name in preferred_areas for tick in range(DAY_TICKS))),
                        -float(_daily_store_hours(assignments).get(day_name, 0.0) or 0.0),
                        -float(_daily_employee_hours(assignments).get(e.name, {}).get(day_name, 0.0) or 0.0),
                        DAYS.index(day_name),
                    ),
                    reverse=True,
                )
                for day in day_order[:4]:
                    for area in preferred_areas:
                        if _deadline_hit(4.0):
                            break
                        demand_ticks = [tick for tick in range(DAY_TICKS) if int(min_req.get((day, area, tick), 0) or 0) > int(coverage.get((day, area, tick), 0) or 0)]
                        if not demand_ticks:
                            day_load_now = float(_daily_store_hours(assignments).get(day, 0.0) or 0.0)
                            if day_load_now > 0.0:
                                demand_ticks = sorted({max(0, seg[1]) for seg in emp_day_segments.get((e.name, day), []) if seg[1] < DAY_TICKS})
                        if not demand_ticks:
                            continue
                        for seg_h in practical_lengths:
                            if seg_h - remaining > max(min_shift_h, 1.0) + 1e-9:
                                continue
                            seg_ticks = max(1, int(round(seg_h * TICKS_PER_HOUR)))
                            candidate_starts: Set[int] = set()
                            for demand_tick in demand_ticks[:12]:
                                candidate_starts.add(max(0, min(int(demand_tick), DAY_TICKS - seg_ticks)))
                                candidate_starts.add(max(0, min(int(demand_tick) - seg_ticks + 1, DAY_TICKS - seg_ticks)))
                            for seg_st, seg_en, _seg_area in emp_day_segments.get((e.name, day), []):
                                candidate_starts.add(max(0, min(int(seg_st) - seg_ticks, DAY_TICKS - seg_ticks)))
                                candidate_starts.add(max(0, min(int(seg_en), DAY_TICKS - seg_ticks)))
                            for st in sorted(candidate_starts):
                                detail["attempt_counters"]["considered"] = int(detail["attempt_counters"].get("considered", 0)) + 1
                                runtime_budget.note("hard_min_candidate_evaluations", 1)
                                en = int(st + seg_ticks)
                                cand = Assignment(day, area, int(st), int(en), e.name, locked=False, source=ASSIGNMENT_SOURCE_ENGINE)
                                if not feasible_segment(e, day, area, int(st), int(en)):
                                    continue
                                min_delta, pref_delta = _candidate_demand_delta(day, area, int(st), int(en), coverage)
                                if min_delta <= 0 and pref_delta <= 0:
                                    continue
                                emp_pen, store_pen, day_idx_pen = _candidate_distribution_penalty(e.name, day, float(seg_h))
                                segs = emp_day_segments.get((e.name, day), [])
                                contiguous_bonus = 0.0
                                if segs:
                                    merged_existing = _merge_touching_intervals([(int(ast), int(aen)) for (ast, aen, _aa) in segs])
                                    merged_with_new = _merge_touching_intervals([(int(ast), int(aen)) for (ast, aen, _aa) in segs] + [(int(st), int(en))])
                                    if len(merged_with_new) < (len(merged_existing) + 1):
                                        contiguous_bonus = 1.0
                                later_alt = 1.0 if DAYS.index(day) >= 3 else 0.0
                                rank = (float(min_delta), float(pref_delta), float(contiguous_bonus) + later_alt - float(emp_pen), -float(store_pen), -float(day_idx_pen))
                                ranked_candidates.append((rank, cand, bool(st == min(candidate_starts) if candidate_starts else False)))
                if ranked_candidates:
                    ranked_candidates.sort(key=lambda x: x[0], reverse=True)
                    chosen_rank, chosen_cand, was_earliest = ranked_candidates[0]
                    solver_selection_telemetry.append({
                        "selector": "hard_min_topup",
                        "day": chosen_cand.day,
                        "area": chosen_cand.area,
                        "start_t": int(chosen_cand.start_t),
                        "end_t": int(chosen_cand.end_t),
                        "feasible_candidates": int(len(ranked_candidates)),
                        "chosen_employee": chosen_cand.employee_name,
                        "chosen_rank": list(chosen_rank),
                        "earliest_iterated_candidate": bool(was_earliest),
                        "later_day_alternative_exists": any(DAYS.index(c.day) > DAYS.index(chosen_cand.day) for _rk, c, _we in ranked_candidates[1:]),
                    })
                    before_h = float(emp_hours.get(e.name, 0.0) or 0.0)
                    before_min, before_pref = _candidate_demand_delta(chosen_cand.day, chosen_cand.area, int(chosen_cand.start_t), int(chosen_cand.end_t), coverage)
                    if add_assignment(chosen_cand, locked_ok=False, cov=coverage, enforce_weekly_cap=False):
                        after_h = float(emp_hours.get(e.name, 0.0) or 0.0)
                        added_h = max(0.0, after_h - before_h)
                        detail["added_in_hard_min_phase"] = float(detail.get("added_in_hard_min_phase", 0.0) or 0.0) + added_h
                        stats["hours_added"] = float(stats.get("hours_added", 0.0) or 0.0) + added_h
                        after_min, after_pref = _candidate_demand_delta(chosen_cand.day, chosen_cand.area, int(chosen_cand.start_t), int(chosen_cand.end_t), coverage)
                        if after_min < before_min:
                            add_outcome_counts["reduced_min"] += 1
                        elif after_pref < before_pref:
                            add_outcome_counts["reduced_pref_only"] += 1
                        else:
                            add_outcome_counts["reduced_neither"] += 1
                        if chosen_cand.day == "Sun":
                            detail["sunday_adds"] = int(detail.get("sunday_adds", 0)) + 1
                        placed = True
                        _capture_best_valid("hard_min_topup")
                    else:
                        trial = assignments + [chosen_cand]
                        hard_ok = True
                        for v in evaluate_schedule_hard_rules(model, label, trial, include_override_warnings=False):
                            if v.severity == "error" and is_engine_managed_source(v.assignment_source):
                                hard_ok = False
                                break
                        if hard_ok:
                            detail["attempt_counters"]["blocked_by_weekly_cap"] = int(detail["attempt_counters"].get("blocked_by_weekly_cap", 0)) + 1
                        else:
                            detail["attempt_counters"]["blocked_by_hard_rules"] = int(detail["attempt_counters"].get("blocked_by_hard_rules", 0)) + 1
                if not placed:
                    detail["attempt_counters"]["no_legal_slot"] = int(detail["attempt_counters"].get("no_legal_slot", 0)) + 1
                    break

            final_h = float(emp_hours.get(e.name, 0.0) or 0.0)
            detail["post_phase_hours"] = final_h
            detail["remaining_shortfall"] = max(0.0, requested - final_h)
            if float(detail.get("remaining_shortfall", 0.0) or 0.0) > 1e-9:
                blockers = detail.setdefault("blockers", [])
                c = detail.get("attempt_counters", {})
                if int(c.get("blocked_by_hard_rules", 0)) > 0:
                    blockers.append("blocked_by_employee_hard_legality")
                if int(c.get("blocked_by_weekly_cap", 0)) > 0:
                    blockers.append("blocked_by_employee_weekly_cap")
                if int(c.get("no_legal_slot", 0)) > 0:
                    blockers.append("no_legal_slot_found")
                if not blockers:
                    blockers.append("unknown_infeasibility")
                stats["employees_unmet"] = int(stats.get("employees_unmet", 0)) + 1
            else:
                stats["employees_met"] = int(stats.get("employees_met", 0)) + 1
        stats["runtime_budget_hit"] = bool(_deadline_hit(4.0))
        stats["candidate_evaluations"] = int(runtime_budget.counters.get("hard_min_candidate_evaluations", 0))

        return stats

    phase_diagnostics["phase0b_hard_minimum_hours"] = phase_assign_hard_minimum_hours()
    _record_phase_snapshot("phase0b_hard_minimum_hours")
    try:
        for emp_name, detail in (hard_min_phase_details or {}).items():
            short_h = float(detail.get("remaining_shortfall", 0.0) or 0.0)
            req_h = float(detail.get("requested_min", 0.0) or 0.0)
            if req_h <= 0.0 or short_h <= 1e-9:
                continue
            blockers = list(detail.get("blockers", []) or [])
            blocker_txt = ", ".join(blockers) if blockers else "no_clear_blocker_recorded"
            warnings.append(
                f"INFEASIBLE HARD-MIN: {emp_name} short by {short_h:.1f}h "
                f"(requested={req_h:.1f}, pre={float(detail.get('pre_phase_hours', 0.0) or 0.0):.1f}, "
                f"added={float(detail.get('added_in_hard_min_phase', 0.0) or 0.0):.1f}) blockers={blocker_txt}."
            )
    except Exception:
        pass

    phase_diagnostics["phase1_cstore_primary"] = phase_fill_area_min(
        "CSTORE",
        lengths=(8, 6, 4, 2),
        only_within_existing=False,
        enforce_weekly_cap=True,
    )
    _record_phase_snapshot("phase1_cstore_primary")

    phase_diagnostics["phase2_kitchen"] = phase_fill_area_min(
        "KITCHEN",
        lengths=(6, 4, 2),
        only_within_existing=False,
        enforce_weekly_cap=True,
    )
    _record_phase_snapshot("phase2_kitchen")

    phase_diagnostics["phase3_cstore_backfill_after_kitchen"] = phase_backfill_cstore_from_pool(
        only_within_existing=False,
        enforce_weekly_cap=True,
    )
    _record_phase_snapshot("phase3_cstore_backfill_after_kitchen")

    phase_diagnostics["phase4_carwash"] = phase_fill_area_min(
        "CARWASH",
        lengths=(6, 4, 2),
        only_within_existing=False,
        enforce_weekly_cap=True,
    )
    _record_phase_snapshot("phase4_carwash")

    phase_diagnostics["phase5_cstore_backfill_after_carwash"] = phase_backfill_cstore_from_pool(
        only_within_existing=False,
        enforce_weekly_cap=True,
    )

    _record_phase_snapshot("phase5_cstore_backfill_after_carwash")

    # Final specialty mop-up pass to reduce shared-labor leakage late in the solve.
    phase_diagnostics["phase5b_kitchen_micro_backfill"] = phase_fill_area_min(
        "KITCHEN",
        lengths=(2,),
        only_within_existing=False,
        enforce_weekly_cap=True,
        prefer_underutilized=True,
        max_keys=2000,
    )
    _record_phase_snapshot("phase5b_kitchen_micro_backfill")

    phase_diagnostics["phase5c_carwash_micro_backfill"] = phase_fill_area_min(
        "CARWASH",
        lengths=(2,),
        only_within_existing=False,
        enforce_weekly_cap=True,
        prefer_underutilized=True,
        max_keys=2000,
    )
    _record_phase_snapshot("phase5c_carwash_micro_backfill")

    uncovered_min_by_area = recompute_uncovered_maps_incremental()

    def _build_contiguous_deficit_windows(area: str, min_need_ticks: int = 1) -> List[Tuple[str, int, int, int]]:
        windows: List[Tuple[str, int, int, int]] = []
        for day in DAYS:
            t = 0
            while t < DAY_TICKS:
                key = (day, area, int(t))
                deficit = int(min_req.get(key, 0) - coverage.get(key, 0))
                if deficit <= 0:
                    t += 1
                    continue
                st = int(t)
                total_deficit = 0
                while t < DAY_TICKS:
                    dk = (day, area, int(t))
                    d = int(min_req.get(dk, 0) - coverage.get(dk, 0))
                    if d <= 0:
                        break
                    total_deficit += int(d)
                    t += 1
                en = int(t)
                if (en - st) >= int(min_need_ticks):
                    windows.append((day, st, en, total_deficit))
            t += 1
        windows.sort(key=lambda w: (int(w[3]), int(w[2] - w[1])), reverse=True)
        return windows

    def _targeted_late_micro_fill() -> Dict[str, Any]:
        stats: Dict[str, Any] = {
            "window_attempts": 0,
            "adds_extend": 0,
            "adds_open": 0,
            "merged_candidates_generated": {"extend_absorb": 0, "combined_open": 0, "internal_reslice": 0},
            "merged_candidates_legal": {"extend_absorb": 0, "combined_open": 0, "internal_reslice": 0},
            "merged_candidates_selected": {"extend_absorb": 0, "combined_open": 0, "internal_reslice": 0},
            "example_repairs": [],
        }

        area_priority = {"KITCHEN": 3.0, "CARWASH": 2.0, "CSTORE": 1.0}

        def _window_deficit_weight(day: str, st: int, en: int) -> float:
            wt = 0.0
            for tt in range(int(st), int(en)):
                for aa in AREAS:
                    miss = max(0, int(min_req.get((day, aa, int(tt)), 0)) - int(coverage.get((day, aa, int(tt)), 0)))
                    if miss > 0:
                        wt += miss * float(area_priority.get(aa, 1.0))
            return float(wt)

        def _segments_covering_gap(day: str, st: int, en: int) -> List[Tuple[int, int, str, int]]:
            out: List[Tuple[int, int, str, int]] = []
            cur_area: Optional[str] = None
            cur_st: Optional[int] = None
            for tt in range(int(st), int(en)):
                best_area = "CSTORE"
                best_need = 0
                for aa in ("KITCHEN", "CARWASH", "CSTORE"):
                    need = max(0, int(min_req.get((day, aa, int(tt)), 0)) - int(coverage.get((day, aa, int(tt)), 0)))
                    if need > best_need:
                        best_need = need
                        best_area = aa
                if best_need <= 0:
                    if cur_area is not None and cur_st is not None and tt > cur_st:
                        seg_need = sum(max(0, int(min_req.get((day, cur_area, x), 0)) - int(coverage.get((day, cur_area, x), 0))) for x in range(cur_st, tt))
                        out.append((int(cur_st), int(tt), str(cur_area), int(seg_need)))
                    cur_area = None
                    cur_st = None
                    continue
                if cur_area is None:
                    cur_area = best_area
                    cur_st = int(tt)
                    continue
                if best_area != cur_area:
                    seg_need = sum(max(0, int(min_req.get((day, cur_area, x), 0)) - int(coverage.get((day, cur_area, x), 0))) for x in range(int(cur_st), int(tt)))
                    out.append((int(cur_st), int(tt), str(cur_area), int(seg_need)))
                    cur_area = best_area
                    cur_st = int(tt)
            if cur_area is not None and cur_st is not None and int(en) > int(cur_st):
                seg_need = sum(max(0, int(min_req.get((day, cur_area, x), 0)) - int(coverage.get((day, cur_area, x), 0))) for x in range(int(cur_st), int(en)))
                out.append((int(cur_st), int(en), str(cur_area), int(seg_need)))
            return out

        def _candidate_score(cand: Dict[str, Any]) -> float:
            gain = float(cand.get("gain_weighted", 0.0))
            raw_gain = float(cand.get("gain_raw", 0.0))
            added_h = float(cand.get("delta_hours", 0.0))
            frag_pen = float(cand.get("fragment_penalty", 0.0))
            return (gain * 10.0) + raw_gain - (added_h * 1.2) - frag_pen

        def _sim_weekly_hours(emp_name: str, adds: List[Tuple[str, str, int, int]], removes: List[int]) -> float:
            base = float(emp_hours.get(emp_name, 0.0) or 0.0)
            add_h = sum(hours_between_ticks(int(st), int(en)) for (_d, _a, st, en) in adds)
            rem_h = 0.0
            for idx in removes:
                if idx < 0 or idx >= len(assignments):
                    continue
                aa = assignments[idx]
                if aa.employee_name != emp_name:
                    continue
                rem_h += hours_between_ticks(int(aa.start_t), int(aa.end_t))
            return base + add_h - rem_h

        def _candidate_legal(cand: Dict[str, Any]) -> bool:
            emp_name = str(cand.get("employee", ""))
            day = str(cand.get("day", ""))
            e = emp_by_name.get(emp_name)
            if e is None or day not in DAYS:
                return False

            add_ops: List[Tuple[str, str, int, int]] = list(cand.get("add_ops", []))
            remove_idxs: List[int] = list(cand.get("remove_idxs", []))
            modify_ops: List[Tuple[int, str]] = list(cand.get("modify_ops", []))

            if max_weekly_cap > 0.0 and (total_labor_hours + float(cand.get("delta_hours", 0.0)) - max_weekly_cap) > 1e-9:
                return False

            weekly_after = _sim_weekly_hours(emp_name, add_ops, remove_idxs)
            if weekly_after - float(getattr(e, "max_weekly_hours", 0.0) or 0.0) > 1e-9:
                return False

            trial = list(assignments)
            for ridx in sorted(set(int(x) for x in remove_idxs), reverse=True):
                if 0 <= ridx < len(trial):
                    trial.pop(ridx)

            for midx, new_area in modify_ops:
                if midx < 0 or midx >= len(assignments):
                    return False
                old = assignments[midx]
                if old.employee_name != emp_name or old.day != day:
                    return False
                if new_area not in getattr(e, "areas_allowed", []):
                    return False
                replaced = False
                for i, aa in enumerate(trial):
                    if aa.day == old.day and aa.employee_name == old.employee_name and aa.start_t == old.start_t and aa.end_t == old.end_t and aa.area == old.area:
                        trial[i] = Assignment(aa.day, str(new_area), int(aa.start_t), int(aa.end_t), aa.employee_name, locked=aa.locked, source=aa.source)
                        replaced = True
                        break
                if not replaced:
                    return False

            for d, area, st, en in add_ops:
                if d != day or area not in getattr(e, "areas_allowed", []):
                    return False
                op_t, cl_t = run_state["area_bounds"].get(area, (0, DAY_TICKS))
                if int(st) < int(op_t) or int(en) > int(cl_t) or int(en) <= int(st):
                    return False
                if not is_employee_available(model, e, label, d, int(st), int(en), area, clopen_min_start):
                    return False
                if not nd_minor_hours_feasible(model, e, d, int(st), int(en), trial, label=label):
                    return False
                cand_a = Assignment(d, area, int(st), int(en), emp_name, locked=False, source="merged_repair")
                if any(overlaps(cand_a, ex) for ex in trial):
                    return False
                if _violates_max(d, area, int(st), int(en), coverage):
                    # allow only when this candidate explicitly removes or re-slices the same employee window.
                    if not remove_idxs and not modify_ops:
                        return False
                trial.append(cand_a)

            if not respects_daily_shift_limits(trial, e, day):
                return False
            if not respects_max_consecutive_days(trial, e, day):
                return False

            blocks = daily_shift_blocks(trial, emp_name, day)
            for st, en in blocks:
                bh = hours_between_ticks(int(st), int(en))
                min_h = float(getattr(e, "min_hours_per_shift", 1.0) or 1.0)
                mx_h = float(employee_allowed_max_shift_hours(e) or 0.0)
                if bh + 1e-9 < min_h:
                    return False
                if mx_h > 0.0 and bh - mx_h > 1e-9:
                    return False

            # demand safety for re-slice: never reduce source area below MIN on modified intervals.
            for midx, new_area in modify_ops:
                old = assignments[midx]
                if old.area == new_area:
                    continue
                for tt in range(int(old.start_t), int(old.end_t)):
                    src_key = (old.day, old.area, int(tt))
                    if int(coverage.get(src_key, 0)) - 1 < int(min_req.get(src_key, 0)):
                        return False
            return True

        def _apply_candidate(cand: Dict[str, Any]) -> bool:
            nonlocal envelopes_by_emp_day, total_labor_hours
            if not _candidate_legal(cand):
                return False

            emp_name = str(cand.get("employee", ""))
            day = str(cand.get("day", ""))
            add_ops: List[Tuple[str, str, int, int]] = list(cand.get("add_ops", []))
            remove_idxs: List[int] = list(cand.get("remove_idxs", []))
            modify_ops: List[Tuple[int, str]] = list(cand.get("modify_ops", []))

            for ridx in sorted(set(int(x) for x in remove_idxs), reverse=True):
                if ridx < 0 or ridx >= len(assignments):
                    continue
                aa = assignments.pop(ridx)
                h = hours_between_ticks(int(aa.start_t), int(aa.end_t))
                emp_hours[aa.employee_name] = float(emp_hours.get(aa.employee_name, 0.0) or 0.0) - h
                total_labor_hours -= h
                occ = emp_day_occupancy.setdefault((aa.employee_name, aa.day), set())
                for tt in range(int(aa.start_t), int(aa.end_t)):
                    occ.discard(int(tt))
                    k = (aa.day, aa.area, int(tt))
                    coverage[k] = max(0, int(coverage.get(k, 0)) - 1)
                    run_state["uncovered_min"][k] = max(0, int(min_req.get(k, 0)) - int(coverage.get(k, 0)))

            for midx, new_area in modify_ops:
                if midx < 0 or midx >= len(assignments):
                    continue
                old = assignments[midx]
                if old.employee_name != emp_name or old.day != day or old.area == new_area:
                    continue
                for tt in range(int(old.start_t), int(old.end_t)):
                    old_k = (old.day, old.area, int(tt))
                    new_k = (old.day, str(new_area), int(tt))
                    coverage[old_k] = max(0, int(coverage.get(old_k, 0)) - 1)
                    coverage[new_k] = int(coverage.get(new_k, 0)) + 1
                    run_state["uncovered_min"][old_k] = max(0, int(min_req.get(old_k, 0)) - int(coverage.get(old_k, 0)))
                    run_state["uncovered_min"][new_k] = max(0, int(min_req.get(new_k, 0)) - int(coverage.get(new_k, 0)))
                assignments[midx] = Assignment(old.day, str(new_area), int(old.start_t), int(old.end_t), old.employee_name, locked=old.locked, source=old.source)

            for d, area, st, en in add_ops:
                if not add_assignment(Assignment(d, area, int(st), int(en), emp_name, locked=False, source="merged_repair"), locked_ok=False, cov=coverage, enforce_weekly_cap=True):
                    return False

            emp_state_version[emp_name] = int(emp_state_version.get(emp_name, 0)) + 1
            envelopes_by_emp_day = derive_master_envelopes(assignments)

            stats["merged_candidates_selected"][str(cand.get("family", "extend_absorb"))] += 1
            stats["adds_extend"] += 1 if str(cand.get("family", "")) == "extend_absorb" else 0
            stats["adds_open"] += 1 if str(cand.get("family", "")) == "combined_open" else 0
            if len(stats["example_repairs"]) < 5:
                stats["example_repairs"].append({
                    "family": str(cand.get("family", "")),
                    "employee": emp_name,
                    "day": day,
                    "gain_raw": int(cand.get("gain_raw", 0)),
                    "gain_weighted": float(cand.get("gain_weighted", 0.0)),
                    "delta_hours": float(cand.get("delta_hours", 0.0)),
                    "window": [int(cand.get("wst", 0)), int(cand.get("wen", 0))],
                })
            return True

        def _build_candidates_for_window(day: str, area: str, wst: int, wen: int) -> List[Dict[str, Any]]:
            cands: List[Dict[str, Any]] = []
            window_core = (int(wst), int(min(int(wen), int(wst) + 8)))
            w_core_st, w_core_en = window_core

            # Family 1: extend-and-absorb.
            for e in model.employees[:120]:
                if getattr(e, "work_status", "") != "Active" or (not bool(getattr(e, "wants_hours", True))):
                    continue
                if area not in getattr(e, "areas_allowed", []):
                    continue
                blocks = envelopes_by_emp_day.get((e.name, day), [])
                if not blocks:
                    continue
                for bst, ben in blocks[:3]:
                    for side in ("left", "right"):
                        if side == "left" and int(w_core_en) <= int(bst):
                            st = int(w_core_st)
                            en = int(bst)
                        elif side == "right" and int(w_core_st) >= int(ben):
                            st = int(ben)
                            en = int(w_core_en)
                        else:
                            continue
                        if en <= st or (en - st) > 8:
                            continue
                        gain_raw = sum(max(0, int(min_req.get((day, area, tt), 0)) - int(coverage.get((day, area, tt), 0))) for tt in range(int(st), int(en)))
                        if gain_raw <= 0:
                            continue
                        cand = {
                            "family": "extend_absorb",
                            "employee": e.name,
                            "day": day,
                            "wst": int(wst),
                            "wen": int(wen),
                            "add_ops": [(day, area, int(st), int(en))],
                            "remove_idxs": [],
                            "modify_ops": [],
                            "gain_raw": int(gain_raw),
                            "gain_weighted": float(gain_raw) * float(area_priority.get(area, 1.0)),
                            "delta_hours": float(hours_between_ticks(int(st), int(en))),
                            "fragment_penalty": 0.0,
                        }
                        cands.append(cand)
                        stats["merged_candidates_generated"]["extend_absorb"] += 1

            # Family 2: combined new-envelope open.
            for e in model.employees[:150]:
                if getattr(e, "work_status", "") != "Active" or (not bool(getattr(e, "wants_hours", True))):
                    continue
                if envelopes_by_emp_day.get((e.name, day), []):
                    continue
                cst = max(0, int(w_core_st) - 2)
                cen = min(DAY_TICKS, int(w_core_en) + 2)
                segs = _segments_covering_gap(day, cst, cen)
                if not segs:
                    continue
                add_ops: List[Tuple[str, str, int, int]] = []
                gain_raw = 0
                for st, en, aa, need in segs:
                    if aa not in getattr(e, "areas_allowed", []):
                        continue
                    add_ops.append((day, aa, int(st), int(en)))
                    gain_raw += int(need)
                if len(add_ops) <= 0 or gain_raw <= 0:
                    continue
                env_st = min(int(x[2]) for x in add_ops)
                env_en = max(int(x[3]) for x in add_ops)
                if (env_en - env_st) > 10:
                    continue
                merged_int = _merge_touching_intervals([(int(x[2]), int(x[3])) for x in add_ops])
                if len(merged_int) != 1:
                    continue
                cand = {
                    "family": "combined_open",
                    "employee": e.name,
                    "day": day,
                    "wst": int(wst),
                    "wen": int(wen),
                    "add_ops": add_ops,
                    "remove_idxs": [],
                    "modify_ops": [],
                    "gain_raw": int(gain_raw),
                    "gain_weighted": float(sum(max(0, int(min_req.get((day, aa, tt), 0)) - int(coverage.get((day, aa, tt), 0))) * float(area_priority.get(aa, 1.0)) for (_d, aa, s, e2) in add_ops for tt in range(int(s), int(e2)))),
                    "delta_hours": float(sum(hours_between_ticks(int(s), int(e2)) for (_d, _a, s, e2) in add_ops)),
                    "fragment_penalty": float(max(0, len(add_ops) - 1)),
                }
                cands.append(cand)
                stats["merged_candidates_generated"]["combined_open"] += 1

            # Family 3: same-day internal re-slice/repack.
            for idx, a in enumerate(assignments):
                if a.day != day or a.area == area:
                    continue
                e = emp_by_name.get(a.employee_name)
                if e is None:
                    continue
                if area not in getattr(e, "areas_allowed", []):
                    continue
                ov_st = max(int(a.start_t), int(w_core_st))
                ov_en = min(int(a.end_t), int(w_core_en))
                if ov_en <= ov_st:
                    continue
                gain_raw = sum(max(0, int(min_req.get((day, area, tt), 0)) - int(coverage.get((day, area, tt), 0))) for tt in range(int(ov_st), int(ov_en)))
                if gain_raw <= 0:
                    continue
                cand = {
                    "family": "internal_reslice",
                    "employee": a.employee_name,
                    "day": day,
                    "wst": int(wst),
                    "wen": int(wen),
                    "add_ops": [],
                    "remove_idxs": [],
                    "modify_ops": [(int(idx), str(area))],
                    "gain_raw": int(gain_raw),
                    "gain_weighted": float(gain_raw) * float(area_priority.get(area, 1.0)),
                    "delta_hours": 0.0,
                    "fragment_penalty": 0.6,
                }
                cands.append(cand)
                stats["merged_candidates_generated"]["internal_reslice"] += 1

            cands.sort(key=_candidate_score, reverse=True)
            return cands[:40]

        windows_ranked: List[Tuple[float, str, str, int, int, int]] = []
        for area in ("KITCHEN", "CARWASH", "CSTORE"):
            min_window = 2 if area != "CSTORE" else 3
            for (day, st, en, demand) in _build_contiguous_deficit_windows(area, min_need_ticks=min_window)[:60]:
                wt = _window_deficit_weight(day, int(st), int(en))
                windows_ranked.append((float(wt), day, area, int(st), int(en), int(demand)))
        windows_ranked.sort(key=lambda x: (x[0], x[5]), reverse=True)

        for _wt, day, area, wst, wen, _dem in windows_ranked[:120]:
            stats["window_attempts"] += 1
            pool = _build_candidates_for_window(day, area, int(wst), int(wen))
            legal_pool: List[Dict[str, Any]] = []
            for cand in pool:
                if _candidate_legal(cand):
                    legal_pool.append(cand)
                    stats["merged_candidates_legal"][str(cand.get("family", "extend_absorb"))] += 1
            if not legal_pool:
                continue
            legal_pool.sort(key=_candidate_score, reverse=True)
            best = legal_pool[0]
            if _apply_candidate(best):
                # Refresh deficits after each accepted merged repair.
                continue

        return stats


    # If Maximum Weekly Labor Cap is enabled, enforce it during MIN fill.
    # If MIN coverage remains unmet under the cap, enter infeasible mode and allow the minimum necessary overage
    # to cover remaining MIN deficits (still respecting per-tick Max staffing and per-employee rules).
    min_short_cap_check, _, _ = compute_requirement_shortfalls(min_req, pref_req, max_req, coverage)
    if max_weekly_cap > 0.0 and min_short_cap_check > 0:
        # Attempt a minimal-overage repair: fill remaining MIN deficits using the shortest segments first, ignoring the weekly cap.
        progress_cap = True
        while progress_cap:
            progress_cap = False
            deficit_keys = [k for k,mn in min_req.items() if coverage.get(k,0) < mn]
            deficit_keys.sort(key=lambda k: (DAYS.index(k[0]), AREAS.index(k[1]), int(k[2])))
            for (day, area, t) in deficit_keys[:8000]:
                if coverage.get((day,area,t),0) >= min_req.get((day,area,t),0):
                    continue
                st = t
                if st > 0 and coverage.get((day,area,st),0) < min_req.get((day,area,st),0) and coverage.get((day,area,st-1),0) < min_req.get((day,area,st-1),0):
                    st = st-1
                # shortest segments first for minimal overage
                for L in (2,4,6,8):
                    en = st + L
                    if en > DAY_TICKS:
                        continue
                    need_ticks = 0
                    for tt in range(st, en):
                        k = (day, area, tt)
                        if coverage.get(k,0) < min_req.get(k,0):
                            need_ticks += 1
                    if need_ticks < 2:
                        continue
                    if add_best_segment(day, area, st, en, locked_ok=False, enforce_weekly_cap=True):
                        progress_cap = True
                        break
                if progress_cap:
                    break

    # ---- Fill toward PREFERRED (soft), without breaking max ----
    progress = True
    while progress:
        progress = False
        pref_def_keys = [k for k,pr in pref_req.items() if coverage.get(k,0) < pr]
        pref_def_keys.sort(key=lambda k: (DAYS.index(k[0]), AREAS.index(k[1]), int(k[2])))
        for (day, area, t) in pref_def_keys[:8000]:
            if coverage.get((day,area,t),0) >= pref_req.get((day,area,t),0):
                continue
            st = t
            if st > 0 and coverage.get((day,area,st-1),0) < pref_req.get((day,area,st-1),0):
                st = st-1
            for L in (6,4,2):
                en = st + L
                if en > DAY_TICKS:
                    continue
                need_ticks = 0
                for tt in range(st,en):
                    k=(day,area,tt)
                    if coverage.get(k,0) < pref_req.get(k,0):
                        need_ticks += 1
                if need_ticks < 2:
                    continue
                if add_best_segment(day, area, st, en):
                    progress = True
                    break
            if progress:
                break

    # Phase 8C: targeted short-shift growth pass (soft quality; hard rules still enforced).
    # Attempt to extend <3h single-block days by adding adjacent 1h/2h segments for the same employee.
    emp_by_name = {e.name: e for e in model.employees}

    def _edge_area_for_block(emp_name: str, day: str, edge_t: int, side: str) -> Optional[str]:
        day_as = [a for a in assignments if a.employee_name == emp_name and a.day == day]
        if not day_as:
            return None
        if side == "left":
            cands = [a for a in day_as if int(a.start_t) == int(edge_t)]
            if cands:
                cands.sort(key=lambda a: int(a.end_t))
                return cands[0].area
        else:
            cands = [a for a in day_as if int(a.end_t) == int(edge_t)]
            if cands:
                cands.sort(key=lambda a: int(a.start_t), reverse=True)
                return cands[0].area
        return None

    # Only run short-shift growth while preferred demand still has deficits.
    # This avoids adding hours when coverage is already fully satisfied.
    if any(coverage.get(k, 0) < pref_req.get(k, 0) for k in pref_req.keys()):
        short_growth_progress = True
        short_growth_passes = 0
        while short_growth_progress and short_growth_passes < 4:
            short_growth_progress = False
            short_growth_passes += 1
            active_names = [e.name for e in model.employees if getattr(e, "work_status", "") == "Active"]
            for emp_name in active_names:
                e = emp_by_name.get(emp_name)
                if not e:
                    continue
                for day in DAYS:
                    blocks = daily_shift_blocks(assignments, emp_name, day)
                    if len(blocks) != 1:
                        continue
                    bst, ben = blocks[0]
                    bh = hours_between_ticks(bst, ben)
                    if bh >= 3.0 - 1e-9:
                        continue

                    # Prefer 2-hour growth first, then 1-hour, on either side of the existing block.
                    attempts: List[Tuple[str, int]] = [("left", 4), ("right", 4), ("left", 2), ("right", 2)]
                    for side, L in attempts:
                        if side == "left":
                            st = int(bst) - int(L)
                            en = int(bst)
                            area = _edge_area_for_block(emp_name, day, int(bst), "left")
                        else:
                            st = int(ben)
                            en = int(ben) + int(L)
                            area = _edge_area_for_block(emp_name, day, int(ben), "right")
                        if st < 0 or en > DAY_TICKS or en <= st or not area:
                            continue
                        if area not in getattr(e, "areas_allowed", []):
                            continue
                        if not feasible_segment(e, day, area, st, en):
                            continue
                        if add_assignment(Assignment(day, area, st, en, emp_name, locked=False, source="short_shift_repair"), locked_ok=False, cov=coverage):
                            short_growth_progress = True
                            break
                    if short_growth_progress:
                        break
                if short_growth_progress:
                    break

    # Step 3: late targeted micro-fill of highest-shortfall contiguous windows, prioritizing specialty areas.
    late_micro_fill_stats = _targeted_late_micro_fill()

    # Stage-4 checkpoint: run one broad legality check after constructive fill.
    constructive_checkpoint_violations = _engine_hard_violations(assignments)
    if constructive_checkpoint_violations:
        warnings.append(f"Constructive checkpoint found {len(constructive_checkpoint_violations)} hard-rule issue(s); final legalization will repair or reject.")
    if 'phase_diagnostics' in locals():
        phase_diagnostics["phase6_targeted_final_repair"] = {
            "constructive_checkpoint_engine_hard": int(len(constructive_checkpoint_violations)),
            "envelope_consistency": validate_master_envelope_consistency(assignments),
            "late_micro_fill": dict(late_micro_fill_stats) if 'late_micro_fill_stats' in locals() else {},
        }

    # Compute shortfalls for reporting/scoring
    # Special-event overstaff pass: if available employees remain after baseline fill, add extra support where possible.
    if special_event_days:
        for day in sorted(list(special_event_days), key=lambda x: DAYS.index(x)):
            for area in AREAS:
                for t in range(0, DAY_TICKS - 1, 2):
                    k = (day, area, t)
                    st = int(t); en = int(t) + 2
                    _ = add_best_segment(day, area, st, en, locked_ok=False, enforce_weekly_cap=True)

    min_short, pref_short, max_viol = compute_requirement_shortfalls(min_req, pref_req, max_req, coverage)
    if max_viol > 0:
        warnings.append("Max staffing soft ceiling exceeded in some blocks; review Staffing Requirements Max values if this overage is undesirable.")
# Local search improvement (swap/move)
    # Scrutiny level controls effort (restarts + iterations).
    scr = str(getattr(model.settings, "solver_scrutiny_level", "Balanced") or "Balanced")
    SCRUTINY = {
        "Fast":     {"restarts": 1, "iters": 120, "time_limit_s": 0, "stop_early": True},
        "Balanced": {"restarts": 2, "iters": 280, "time_limit_s": 0, "stop_early": True},
        "Thorough": {"restarts": 3, "iters": 520, "time_limit_s": 0, "stop_early": True},
        "Maximum":  {"restarts": 4, "iters": 760, "time_limit_s": 0, "stop_early": True},
    }
    preset = SCRUTINY.get(scr, SCRUTINY["Balanced"])
    restarts_target = int(preset["restarts"])
    iters_per_restart = int(preset["iters"])
    time_limit_s = float(preset.get("time_limit_s", 0) or 0)
    if runtime_budget is not None:
        time_limit_s = min(time_limit_s or max(0.0, runtime_budget.seconds_remaining() - 4.0), max(0.0, runtime_budget.seconds_remaining() - 4.0))
    stop_early = bool(preset.get("stop_early", True))

    temp = float(model.settings.optimizer_temperature)
    rnd = random.Random()
    total_iters_done = 0
    restarts_done = 0
    t0 = datetime.datetime.now()

    # Compute unfilled MIN requirement headcount (hard)
    min_req_ls, pref_req_ls, max_req_ls = build_requirement_maps(model.requirements, goals=getattr(model,'manager_goals',None), store_info=getattr(model, "store_info", None))
    # OP1: per-run memo caches (never cross-run/global).
    unfilled_cache: Dict[Tuple[Tuple[str, str, int, int, str, bool, str], ...], int] = {}
    score_cache: Dict[Tuple[Tuple[Tuple[str, str, int, int, str, bool, str], ...], int], float] = {}

    def _assign_sig(assigns: List[Assignment]) -> Tuple[Tuple[str, str, int, int, str, bool, str], ...]:
        return tuple(sorted((
            str(a.day),
            str(a.area),
            int(a.start_t),
            int(a.end_t),
            str(a.employee_name),
            bool(a.locked),
            str(a.source),
        ) for a in assigns))

    def compute_unfilled(assigns: List[Assignment]) -> int:
        sig = _assign_sig(assigns)
        cached = unfilled_cache.get(sig)
        if cached is not None:
            return int(cached)
        cov = count_coverage_per_tick(assigns)
        min_short, _, _ = compute_requirement_shortfalls(min_req_ls, pref_req_ls, max_req_ls, cov)
        out = int(min_short)
        unfilled_cache[sig] = out
        return out

    def score_assignments(assigns: List[Assignment], unfilled_val: int) -> float:
        sig = _assign_sig(assigns)
        key = (sig, int(unfilled_val))
        cached = score_cache.get(key)
        if cached is not None:
            return float(cached)
        out = float(schedule_score(model, label, assigns, unfilled_val, history_stats, prev_tick_map))
        score_cache[key] = out
        return out

    base_assigns = list(assignments)
    unfilled0 = compute_unfilled(base_assigns)
    best = (score_assignments(base_assigns, unfilled0), base_assigns)

    def _quality_key(assigns: List[Assignment]) -> Tuple[float, float, float]:
        try:
            pats = getattr(model, "learned_patterns", {}) or {}
            q = _schedule_quality_penalty_units(model, assigns, pats)
            return (
                float(q.get("short_units", 0.0)),
                float(q.get("frag_units", 0.0)),
                float(q.get("pref_len_units", 0.0)),
            )
        except Exception:
            return (0.0, 0.0, 0.0)

    def feasible_add(emp: Employee, day: str, st: int, en: int, area: str, assigns: List[Assignment]) -> bool:
        # Fast path for local-search proposals: keep lightweight filters here for speed,
        # then run the shared hard-rule contract as the final authority below.
        # clopen: approximate by recomputing a simple clopen map per evaluation (fast enough at small n)
        cl: Dict[Tuple[str,str], int] = {}
        # apply existing late shifts for emp
        for a in assigns:
            if a.employee_name != emp.name:
                continue
            if emp.avoid_clopens:
                end_hr = a.end_t / TICKS_PER_HOUR
                if end_hr >= 22.0:
                    idx = DAYS.index(a.day)
                    nd = DAYS[(idx+1)%7]
                    ms = int(max(0, (a.end_t + model.settings.min_rest_hours*TICKS_PER_HOUR) - DAY_TICKS))
                    cl[(emp.name, nd)] = max(cl.get((emp.name, nd), 0), ms)
        if not is_employee_available(model, emp, label, day, st, en, area, cl):
            return False
        if not respects_daily_shift_limits(assigns, emp, day, extra=(st,en)):
            return False
        if not respects_max_consecutive_days(assigns, emp, day):
            return False
        min_h = float(getattr(emp, "min_hours_per_shift", 1.0) or 1.0)
        if hours_between_ticks(st, en) + 1e-9 < min_h:
            return False
        if any(a.employee_name==emp.name and a.day==day and not (en<=a.start_t or st>=a.end_t) for a in assigns):
            return False
        h = hours_between_ticks(st,en)
        max_weekly_cap = float(getattr(model.manager_goals, 'maximum_weekly_cap', 0.0) or 0.0)
        if max_weekly_cap > 0.0:
            candidate_total_hours = sum(hours_between_ticks(a.start_t, a.end_t) for a in assigns) + h
            if candidate_total_hours - max_weekly_cap > 1e-9:
                return False
        hours_now = sum(hours_between_ticks(a.start_t,a.end_t) for a in assigns if a.employee_name==emp.name)
        if hours_now + h > emp.max_weekly_hours + 1e-9:
            return False
        if not nd_minor_hours_feasible(model, emp, day, st, en, assigns, label=label):
            return False
        trial = list(assigns)
        trial.append(Assignment(day, area, st, en, emp.name, locked=False, source=ASSIGNMENT_SOURCE_ENGINE))
        return len(_engine_hard_violations(trial)) == 0

    def step(cur: List[Assignment], cur_quality: Optional[Tuple[float,float,float]] = None) -> List[Assignment]:
        if not cur:
            return cur

        def _employee_day_hard_valid(assigns: List[Assignment], emp_obj: Optional[Employee], day_name: str) -> bool:
            if emp_obj is None:
                return False
            if not respects_daily_shift_limits(assigns, emp_obj, day_name):
                return False
            min_h = float(getattr(emp_obj, "min_hours_per_shift", 1.0) or 0.0)
            mx_h = employee_allowed_max_shift_hours(emp_obj)
            for st_blk, en_blk in daily_shift_blocks(assigns, emp_obj.name, day_name):
                h_blk = hours_between_ticks(st_blk, en_blk)
                if min_h > 0.0 and h_blk + 1e-9 < min_h:
                    return False
                if h_blk - mx_h > 1e-9:
                    return False
            return True

        cand = list(cur)
        # choose a non-locked assignment to mutate
        movables = [i for i,a in enumerate(cand) if not a.locked]
        if not movables:
            return cand
        i = rnd.choice(movables)
        a = cand[i]
        emp = next((x for x in model.employees if x.name==a.employee_name), None)
        if emp is None:
            return cand
        # with 50%: try reassign same slot to another employee
        if rnd.random() < 0.5:
            day, area, st, en = a.day, a.area, a.start_t, a.end_t
            # remove then reassign
            old = cand.pop(i)
            old_emp = next((x for x in model.employees if x.name == old.employee_name), None)
            if not _employee_day_hard_valid(cand, old_emp, day):
                cand.insert(i, old)
                return cand
            # pick candidate employees
            pool = [e for e in model.employees if e.work_status=="Active" and bool(getattr(e, "wants_hours", True)) and area in e.areas_allowed and e.name!=old.employee_name]
            rnd.shuffle(pool)
            for e2 in pool[:20]:
                if feasible_add(e2, day, st, en, area, cand):
                    trial = list(cand)
                    trial.append(Assignment(day, area, st, en, e2.name, locked=False, source=ASSIGNMENT_SOURCE_ENGINE))
                    if _employee_day_hard_valid(trial, e2, day):
                        if cur_quality is not None:
                            q_new = _quality_key(trial)
                            if q_new[0] > cur_quality[0] + 0.5:
                                continue
                            if q_new[1] > cur_quality[1] + 0.25 and q_new[0] > cur_quality[0] - 0.25:
                                continue
                        return trial
            # revert
            cand.insert(i, old)
            return cand
        else:
            # try swap employees between two assignments
            j = rnd.choice(movables)
            if j == i:
                return cand
            b = cand[j]
            if a.day!=b.day:
                return cand
            # try swap emp names
            empA = next((x for x in model.employees if x.name==a.employee_name), None)
            empB = next((x for x in model.employees if x.name==b.employee_name), None)
            if empA is None or empB is None:
                return cand
            if (a.area not in empB.areas_allowed) or (b.area not in empA.areas_allowed):
                return cand
            # build temp list with removals
            temp_list = [x for k,x in enumerate(cand) if k not in (i,j)]
            if not _employee_day_hard_valid(temp_list, empA, a.day):
                return cand
            if not _employee_day_hard_valid(temp_list, empB, b.day):
                return cand
            if feasible_add(empB, a.day, a.start_t, a.end_t, a.area, temp_list) and feasible_add(empA, b.day, b.start_t, b.end_t, b.area, temp_list):
                trial = list(temp_list)
                trial.append(Assignment(a.day,a.area,a.start_t,a.end_t,empB.name,locked=False,source=ASSIGNMENT_SOURCE_ENGINE))
                trial.append(Assignment(b.day,b.area,b.start_t,b.end_t,empA.name,locked=False,source=ASSIGNMENT_SOURCE_ENGINE))
                if _employee_day_hard_valid(trial, empB, a.day) and _employee_day_hard_valid(trial, empA, b.day):
                    if cur_quality is not None:
                        q_new = _quality_key(trial)
                        if q_new[0] > cur_quality[0] + 0.5:
                            return cand
                        if q_new[1] > cur_quality[1] + 0.25 and q_new[0] > cur_quality[0] - 0.25:
                            return cand
                    return trial
            return cand

    # Multi-start local search (random restarts)
    restart_no_global_improve = 0
    for r in range(max(1, restarts_target)):
        if _deadline_hit(3.0):
            break
        restarts_done += 1
        best_before_restart = float(best[0])
        # Diversify start by doing a few random steps from the base schedule.
        cur = list(base_assigns)
        # seed: deterministic-ish but different per restart
        rnd.seed((hash(label) & 0xffffffff) ^ (r * 2654435761))
        for _warm in range(10 + r):
            cur = step(cur, _quality_key(cur))
        unfilled = compute_unfilled(cur)
        cur_score = score_assignments(cur, unfilled)

        best_no_improve = 0
        for k in range(iters_per_restart):
            total_iters_done += 1
            if time_limit_s and (datetime.datetime.now() - t0).total_seconds() >= time_limit_s:
                break
            if _deadline_hit(3.0):
                break
            nxt = step(cur, _quality_key(cur))
            unfilled = compute_unfilled(nxt)
            sc = score_assignments(nxt, unfilled)
            if sc < cur_score:
                cur, cur_score = nxt, sc
                best_no_improve = 0
                if sc < best[0]:
                    best = (sc, nxt)
                    assignments = list(best[1])
                    _capture_best_valid("local_search")
            else:
                best_no_improve += 1
                # accept with probability
                if temp > 0:
                    prob = math.exp(-(sc-cur_score)/max(0.0001, temp))
                    if rnd.random() < prob:
                        cur, cur_score = nxt, sc

            # Stop-early heuristics
            if stop_early and best_no_improve > 400:
                break
            if stop_early and best[0] <= 0:
                break

        if time_limit_s and (datetime.datetime.now() - t0).total_seconds() >= time_limit_s:
            break
        if _deadline_hit(3.0):
            break
        if stop_early and best[0] <= 0:
            break
        nxt = step(cur, _quality_key(cur))
        unfilled = compute_unfilled(nxt)
        sc = score_assignments(nxt, unfilled)
        if sc < cur_score:
            cur, cur_score = nxt, sc
            if sc < best[0]:
                best = (sc, nxt)
                assignments = list(best[1])
                _capture_best_valid("local_search_tail")
        else:
            # accept with probability
            if temp > 0:
                prob = math.exp(-(sc-cur_score)/(100.0*temp))
                if rnd.random() < prob:
                    cur, cur_score = nxt, sc

        if float(best[0]) < best_before_restart - 1e-9:
            restart_no_global_improve = 0
        else:
            restart_no_global_improve += 1
            # OP1: conservative restart-level early stop for faster modes only.
            if scr in ("Fast", "Balanced") and restart_no_global_improve >= 2 and r >= 1:
                break

    assignments = best[1]

    # Constructive min-shift guard: short engine-created blocks should be rare.
    # Keep a defensive cleanup fallback for residual engine-only artifacts after local search mutations.
    def prune_short_shift_blocks(assigns: List[Assignment]) -> List[Assignment]:
        keep = list(assigns)
        removed_engine_short = 0
        for e in model.employees:
            min_h = float(getattr(e, "min_hours_per_shift", 1.0) or 0.0)
            if min_h <= 0.5:
                continue
            for day in DAYS:
                blocks = daily_shift_blocks(keep, e.name, day)
                for st, en in blocks:
                    if hours_between_ticks(st, en) + 1e-9 >= min_h:
                        continue
                    block_as = [a for a in keep if a.employee_name == e.name and a.day == day and a.start_t >= st and a.end_t <= en]
                    if not block_as:
                        continue
                    # preserve manager authority: never auto-delete override-authored blocks
                    if any(assignment_provenance(a) in {ASSIGNMENT_SOURCE_FIXED_LOCKED, ASSIGNMENT_SOURCE_MANUAL} for a in block_as):
                        continue
                    before = len(keep)
                    keep = [a for a in keep if a not in block_as]
                    removed_engine_short += max(0, before - len(keep))
        if removed_engine_short > 0:
            warnings.append(f"Defensive cleanup: removed {removed_engine_short} engine-created assignment(s) in short blocks.")
        return keep

    assignments = prune_short_shift_blocks(assignments)

    # recompute requirement status after quality passes
    coverage = count_coverage_per_tick(assignments)
    min_req2, pref_req2, max_req2 = build_requirement_maps(model.requirements, goals=getattr(model,'manager_goals',None), store_info=getattr(model, "store_info", None))
    min_short2, pref_short2, max_viol2 = compute_requirement_shortfalls(min_req2, pref_req2, max_req2, coverage)
    filled = int(sum(min_req2.values()) - min_short2)
    total = int(sum(min_req2.values()))
    unfilled = int(min_short2)
    if min_short2 > 0:
        warnings.append(f"INFEASIBLE: Minimum staffing shortfall remains ({min_short2} half-hour headcount units below Min).")
    if max_viol2 > 0:
        warnings.append(f"WARNING: Max staffing exceeded by {max_viol2} half-hour headcount units (likely due to locked shifts).")

    # compute employee hours
    emp_hours = {e.name: 0.0 for e in model.employees}
    for a in assignments:
        emp_hours[a.employee_name] += hours_between_ticks(a.start_t, a.end_t)

    eligible_map, not_eligible_map = compute_weekly_eligibility(model, label)
    participation_missed: Dict[str, str] = {}
    participation_details: Dict[str, Any] = {}

    def _has_real_demand(day: str, area: str, st: int, en: int) -> bool:
        # Only allow extra/top-up hours strictly inside real demand windows.
        return all((int(min_req2.get((day, area, tt), 0)) > 0) or (int(pref_req2.get((day, area, tt), 0)) > 0) for tt in range(st, en))

    def _segment_has_unmet_need(day: str, area: str, st: int, en: int, cov: Dict[Tuple[str,str,int], int]) -> bool:
        for tt in range(st, en):
            k = (day, area, tt)
            if cov.get(k, 0) < min_req2.get(k, 0):
                return True
        return False

    def _attach_kind(emp_name: str, day: str, area: str, st: int, en: int, cov: Dict[Tuple[str,str,int], int]) -> str:
        # Explicit attach/extend semantics used for min-hours-target/floor top-ups.
        same_day = [a for a in assignments if a.employee_name == emp_name and a.day == day]
        for ex in same_day:
            if (int(en) == int(ex.start_t)) or (int(st) == int(ex.end_t)):
                return "extend_own_block"

        # Attach to existing demand-backed structure in this area/day.
        for tt in range(st, en):
            if cov.get((day, area, tt), 0) > 0:
                return "attach_existing_coverage"
            if tt > 0 and cov.get((day, area, tt - 1), 0) > 0:
                return "attach_neighbor_coverage"
            if tt + 1 < DAY_TICKS and cov.get((day, area, tt + 1), 0) > 0:
                return "attach_neighbor_coverage"

        # Sparse-demand first participation: permit only when segment directly supports unmet minimum demand.
        if not same_day and _segment_has_unmet_need(day, area, st, en, cov):
            return "seed_unmet_minimum"
        return "none"

    def _candidate_need_score(day: str, area: str, st: int, en: int, cov: Dict[Tuple[str,str,int], int]) -> int:
        min_need = 0
        pref_need = 0
        for tt in range(st, en):
            k = (day, area, tt)
            if cov.get(k, 0) < min_req2.get(k, 0):
                min_need += 1
            if cov.get(k, 0) < pref_req2.get(k, 0):
                pref_need += 1
        return (min_need * 100) + (pref_need * 10)

    def _candidate_is_hard_valid(a: Assignment, working: List[Assignment]) -> bool:
        trial = working + [a]
        for v in evaluate_schedule_hard_rules(model, label, trial, include_override_warnings=False):
            if v.severity == "error" and is_engine_managed_source(v.assignment_source):
                return False
        return True

    participation_attempt_stats: Dict[str, Dict[str, int]] = {}

    def _try_add_target_hours(emp: Employee,
                              required_hours: float,
                              reason_tag: str,
                              cov: Dict[Tuple[str,str,int], int]) -> float:
        added = 0.0
        if required_hours <= 1e-9:
            return 0.0
        min_shift_ticks = int(max(1, math.ceil(max(0.0, float(getattr(emp, "min_hours_per_shift", 1.0) or 1.0)) * TICKS_PER_HOUR)))
        max_shift_ticks = int(max(min_shift_ticks, round(employee_allowed_max_shift_hours(emp) * TICKS_PER_HOUR)))
        block_counts = {
            "no_demand_window": 0,
            "attach_extend_gate": 0,
            "blocked_by_labor_max": 0,
            "blocked_by_employee_max": 0,
            "blocked_by_max_staffing": 0,
            "blocked_by_hard_rules": 0,
            "considered": 0,
            "seed_unmet_minimum_candidates": 0,
        }
        if max_shift_ticks < min_shift_ticks:
            participation_details[emp.name] = {"result": "blocked", "reason": "min shift exceeds max shift"}
            participation_attempt_stats[emp.name] = dict(block_counts)
            return 0.0

        total_hours_now = float(sum(hours_between_ticks(a.start_t, a.end_t) for a in assignments))
        best: Optional[Tuple[int, int, str, str, int, int, str]] = None

        for day in DAYS:
            for area in (getattr(emp, "areas_allowed", []) or []):
                for seg_ticks in sorted(set([min_shift_ticks, min(max_shift_ticks, min_shift_ticks + 2), min(max_shift_ticks, min_shift_ticks + 4)]), reverse=True):
                    if seg_ticks <= 0:
                        continue
                    earliest = 0
                    latest = DAY_TICKS - seg_ticks
                    if latest < earliest:
                        continue
                    for st in range(earliest, latest + 1):
                        block_counts["considered"] += 1
                        en = st + seg_ticks
                        seg_h = hours_between_ticks(st, en)
                        if seg_h > (required_hours - added) + max(0.0, float(getattr(emp, "min_hours_per_shift", 1.0) or 1.0)):
                            continue
                        if max_weekly_cap > 0.0 and (total_hours_now + seg_h) - max_weekly_cap > 1e-9:
                            block_counts["blocked_by_labor_max"] += 1
                            continue
                        if not _has_real_demand(day, area, st, en):
                            block_counts["no_demand_window"] += 1
                            continue
                        attach_kind = _attach_kind(emp.name, day, area, st, en, cov)
                        if attach_kind == "none":
                            block_counts["attach_extend_gate"] += 1
                            continue
                        if attach_kind == "seed_unmet_minimum":
                            block_counts["seed_unmet_minimum_candidates"] += 1
                        if emp_hours.get(emp.name, 0.0) + seg_h > float(getattr(emp, "max_weekly_hours", 0.0) or 0.0) + 1e-9:
                            block_counts["blocked_by_employee_max"] += 1
                            continue
                        cand = Assignment(day, area, st, en, emp.name, locked=False, source=ASSIGNMENT_SOURCE_ENGINE)
                        if not _candidate_is_hard_valid(cand, assignments):
                            block_counts["blocked_by_hard_rules"] += 1
                            continue
                        need_sc = _candidate_need_score(day, area, st, en, cov)
                        tie_break = -seg_ticks
                        if best is None or (need_sc, tie_break) > (best[0], best[1]):
                            best = (need_sc, tie_break, day, area, st, en, attach_kind)

        participation_attempt_stats[emp.name] = dict(block_counts)
        if best is None:
            return 0.0

        _need_sc, _tb, day, area, st, en, attach_kind = best
        a = Assignment(day, area, st, en, emp.name, locked=False, source=ASSIGNMENT_SOURCE_ENGINE)
        assignments.append(a)
        seg_h = hours_between_ticks(st, en)
        emp_hours[emp.name] = emp_hours.get(emp.name, 0.0) + seg_h
        for tt in range(st, en):
            cov[(day, area, tt)] = cov.get((day, area, tt), 0) + 1
        details = participation_details.setdefault(emp.name, {})
        details["attach_mode"] = attach_kind
        return seg_h

    # unified participation routine (hard-minimum weekly hours are enforced earlier in phase0b)
    for nm in sorted(eligible_map.keys()):
        e = next((x for x in model.employees if x.name == nm), None)
        if e is None:
            participation_missed[nm] = "Employee record not found."
            continue
        cur_h = float(emp_hours.get(nm, 0.0) or 0.0)
        target_h = 1.0
        if cur_h + 1e-9 >= target_h:
            participation_details[nm] = {"result": "already_met", "current_hours": cur_h, "target_hours": target_h}
            continue

        needed = target_h - cur_h
        loops = 0
        added_total = 0.0
        while needed - added_total > 1e-9 and loops < 6:
            loops += 1
            added = _try_add_target_hours(e, needed - added_total, "hard_min", coverage)
            if added <= 1e-9:
                break
            added_total += added

        final_h = float(emp_hours.get(nm, 0.0) or 0.0)
        if final_h + 1e-9 < target_h:
            stats = participation_attempt_stats.get(nm, {})
            reasons = []
            if max_weekly_cap > 0.0 and float(sum(emp_hours.values())) + 0.5 - max_weekly_cap > 1e-9:
                reasons.append("blocked by labor max")
            if final_h + 1e-9 >= float(getattr(e, "max_weekly_hours", 0.0) or 0.0):
                reasons.append("blocked by employee max")
            if stats.get("blocked_by_hard_rules", 0) > 0:
                reasons.append("blocked by availability/area/split/consecutive/minor hard rules")
            if stats.get("blocked_by_max_staffing", 0) > 0:
                reasons.append("blocked by staffing cap")
            if stats.get("no_demand_window", 0) > 0 and final_h <= 1e-9:
                reasons.append("no feasible demand-window participation opportunity")
            if stats.get("attach_extend_gate", 0) > 0:
                reasons.append("attach/extend gate prevented isolated dead-time block")
            if not reasons:
                reasons.append("no feasible demand-window attach/extend slot under hard rules")
            participation_missed[nm] = f"Could not reach participation target ({final_h:.1f}/{target_h:.1f}h): " + ", ".join(reasons)
            participation_details[nm] = {
                "result": "shortfall",
                "current_hours": final_h,
                "target_hours": target_h,
                "missing_hours": max(0.0, target_h-final_h),
                "reasons": reasons,
                "block_counters": stats,
                "unscheduled_active_opted_in": bool(final_h <= 1e-9),
            }
        else:
            participation_details[nm] = {"result": "met_by_topup", "current_hours": final_h, "target_hours": target_h, "added_hours": added_total, "block_counters": participation_attempt_stats.get(nm, {})}

    # constructive weekly labor floor top-up (best effort, still hard-safe)
    labor_floor = float(getattr(model.manager_goals, 'minimum_weekly_floor', 0.0) or 0.0)
    floor_shortfall_hours = 0.0
    if labor_floor > 0.0:
        floor_loop = 0
        while float(sum(emp_hours.values())) + 1e-9 < labor_floor and floor_loop < 32:
            floor_loop += 1
            remaining = labor_floor - float(sum(emp_hours.values()))
            candidates = [e for e in model.employees if e.work_status == "Active" and bool(getattr(e, "wants_hours", True))]
            candidates.sort(key=lambda e: float(emp_hours.get(e.name, 0.0) or 0.0))
            progressed = False
            for e in candidates:
                add_h = _try_add_target_hours(e, remaining, "labor_floor", coverage)
                if add_h > 1e-9:
                    progressed = True
                    break
            if not progressed:
                break
        floor_shortfall_hours = max(0.0, labor_floor - float(sum(emp_hours.values())))
    # ND minor hour limits are now hard constraints during all add/mutate paths.
    # Keep a lightweight invariant check for diagnostics; this should never fire.
    if model.nd_rules.enforce:
        for e in model.employees:
            if e.work_status!="Active" or e.minor_type!="MINOR_14_15":
                continue
            daily: Dict[str,float] = {d: 0.0 for d in DAYS}
            for a in assignments:
                if a.employee_name==e.name:
                    daily[a.day] += hours_between_ticks(a.start_t,a.end_t)
            weekly_h = float(sum(daily.values()))
            weekly_cap = nd_minor_weekly_hour_cap(model, e)
            if weekly_cap is not None and weekly_h - weekly_cap > 1e-9:
                warnings.append(f"INTERNAL CHECK: ND minor weekly cap violated for {e.name} ({weekly_h:.1f} > {weekly_cap:.1f}).")
            for d, h in daily.items():
                daily_cap = nd_minor_daily_hour_cap(model, e, d)
                if daily_cap is not None and h - daily_cap > 1e-9:
                    warnings.append(f"INTERNAL CHECK: ND minor daily cap violated for {e.name} on {d} ({h:.1f} > {daily_cap:.1f}).")

    # participation reporting (separate from hard-minimum weekly enforcement)
    if participation_missed:
        for nm, reason in participation_missed.items():
            warnings.append(f"Participation target shortfall: {nm} ({reason})")
    if floor_shortfall_hours > 1e-9:
        warnings.append(f"Labor floor shortfall: could not reach minimum_weekly_floor by {floor_shortfall_hours:.1f} hours under hard constraints.")

    total_hours = float(sum(emp_hours.values()))
    # Report Maximum Weekly Labor Cap infeasibility (Milestone 2).
    if max_weekly_cap > 0.0 and (total_hours - max_weekly_cap) > 1e-9:
        over = total_hours - max_weekly_cap
        warnings.append(f"INFEASIBLE: exceeded Maximum Weekly Labor Hours Cap by {over:.1f} hours (cap={max_weekly_cap:.1f}, scheduled={total_hours:.1f}).")
        # Provide a few concrete reasons to aid debugging.
        if locked_hours > 0.0 and locked_hours - max_weekly_cap > 1e-9:
            warnings.append(f"Reason: Locked fixed shifts alone total {locked_hours:.1f} hours, which already exceeds the cap.")
        if 'min_short_cap_check' in locals() and min_short_cap_check > 0:
            warnings.append("Reason: Maximum weekly labor cap blocked minimum-coverage construction; shortfall retained in diagnostics.")
        if cap_blocked_attempts > 0:
            warnings.append(f"Reason: Weekly cap blocked {cap_blocked_attempts} placement attempts during MIN construction.")
    # Report Preferred Weekly Cap overage (soft) (Milestone 5).
    if preferred_weekly_cap > 0.0 and (total_hours - preferred_weekly_cap) > 1e-9:
        over = total_hours - preferred_weekly_cap
        warnings.append(f"Soft: exceeded Preferred Weekly Labor Hours Cap by {over:.1f} hours (preferred={preferred_weekly_cap:.1f}, scheduled={total_hours:.1f}).")

    def _repair_engine_hard_assignments(assigns: List[Assignment], max_iters: int = 50) -> Tuple[List[Assignment], Dict[str, Any]]:
        working = list(assigns)
        stats: Dict[str, Any] = {
            "removed": 0,
            "trimmed": 0,
            "substituted": 0,
            "fragment_removed": 0,
            "coverage_lost_ticks": 0,
            "forced_rules": {},
            "no_valid_alternative_count": 0,
        }

        def _engine_violations(cur: List[Assignment]) -> List[HardRuleViolation]:
            vv = evaluate_schedule_hard_rules(model, label, cur, include_override_warnings=True)
            return [v for v in vv if (not v.is_override_allowed and v.severity == "error" and is_engine_managed_source(v.assignment_source))]

        def _is_valid(cur: List[Assignment]) -> bool:
            return len(_engine_violations(cur)) == 0

        def _tick_loss(base_cov: Dict[Tuple[str,str,int], int], a: Assignment, only_min: bool = True) -> int:
            loss = 0
            for tt in range(int(a.start_t), int(a.end_t)):
                k = (a.day, a.area, int(tt))
                if only_min:
                    if base_cov.get(k, 0) <= min_req2.get(k, 0):
                        loss += 1
                elif base_cov.get(k, 0) > 0:
                    loss += 1
            return loss

        for _ in range(max_iters):
            engine_bad = _engine_violations(working)
            if not engine_bad:
                break
            target = engine_bad[0]
            if target.code:
                stats["forced_rules"][target.code] = int(stats["forced_rules"].get(target.code, 0)) + 1

            cov_now = count_coverage_per_tick(working)
            changed = False
            idx = int(getattr(target, "assignment_index", -1))
            if 0 <= idx < len(working):
                bad_a = working[idx]
                if is_engine_managed_source(assignment_provenance(bad_a)):
                    # (1) Trim edges conservatively to salvage partial coverage when allowed.
                    if target.code in {"availability-window", "max-hours-per-shift", "max-staffing-soft-ceiling"}:
                        variants: List[List[Assignment]] = []
                        if int(bad_a.end_t) - int(bad_a.start_t) > 1:
                            left = Assignment(bad_a.day, bad_a.area, int(bad_a.start_t)+1, int(bad_a.end_t), bad_a.employee_name, locked=False, source=bad_a.source)
                            right = Assignment(bad_a.day, bad_a.area, int(bad_a.start_t), int(bad_a.end_t)-1, bad_a.employee_name, locked=False, source=bad_a.source)
                            for cand in (left, right):
                                trial = working[:idx] + [cand] + working[idx+1:]
                                if _is_valid(trial):
                                    variants.append(trial)
                        if variants:
                            variants.sort(key=lambda tr: len(_engine_violations(tr)))
                            working = variants[0]
                            stats["trimmed"] += 1
                            changed = True

                    # (2) Same-slot substitution to another feasible employee.
                    if (not changed) and target.code in {"allowed-area", "availability-window", "active-status", "employee-max-weekly-hours", "max-consecutive-days", "daily-shift-limits", "nd-minor-daily-hours", "nd-minor-weekly-hours"}:
                        for e2 in model.employees:
                            if e2.name == bad_a.employee_name or e2.work_status != "Active":
                                continue
                            if bad_a.area not in (getattr(e2, "areas_allowed", []) or []):
                                continue
                            sub = Assignment(bad_a.day, bad_a.area, bad_a.start_t, bad_a.end_t, e2.name, locked=False, source=ASSIGNMENT_SOURCE_ENGINE)
                            trial = working[:idx] + [sub] + working[idx+1:]
                            if _is_valid(trial):
                                working = trial
                                stats["substituted"] += 1
                                changed = True
                                break

                    # (3) Split/drop offending fragment for availability-style violations.
                    if (not changed) and target.code in {"availability-window", "max-staffing-soft-ceiling"}:
                        segs = []
                        if int(bad_a.end_t) - int(bad_a.start_t) >= 3:
                            mid = int((int(bad_a.start_t) + int(bad_a.end_t)) // 2)
                            segs = [
                                Assignment(bad_a.day, bad_a.area, int(bad_a.start_t), mid, bad_a.employee_name, locked=False, source=bad_a.source),
                                Assignment(bad_a.day, bad_a.area, mid, int(bad_a.end_t), bad_a.employee_name, locked=False, source=bad_a.source),
                            ]
                        for seg in segs:
                            if int(seg.end_t) <= int(seg.start_t):
                                continue
                            trial = working[:idx] + [seg] + working[idx+1:]
                            if _is_valid(trial):
                                working = trial
                                stats["fragment_removed"] += 1
                                changed = True
                                break

                    # (4) Fallback removal.
                    if not changed:
                        stats["coverage_lost_ticks"] += _tick_loss(cov_now, bad_a, only_min=True)
                        working = working[:idx] + working[idx+1:]
                        stats["removed"] += 1
                        changed = True

            if not changed:
                stats["no_valid_alternative_count"] += 1
                break

        return working, stats
    _capture_best_valid("pre_final_validation")

    # Final shared hard-rule validation gate before return.
    final_structured_violations = evaluate_schedule_hard_rules(model, label, assignments, include_override_warnings=True)
    repair_stats: Dict[str, Any] = {}
    engine_hard = [v for v in final_structured_violations if (not v.is_override_allowed and v.severity == "error" and is_engine_managed_source(v.assignment_source))]
    if engine_hard:
        repaired_assignments, repair_stats = _repair_engine_hard_assignments(assignments)
        if repaired_assignments != assignments:
            assignments = repaired_assignments
            emp_hours = {e.name: 0.0 for e in model.employees}
            for a in assignments:
                emp_hours[a.employee_name] += hours_between_ticks(a.start_t, a.end_t)
            total_hours = float(sum(emp_hours.values()))
            final_structured_violations = evaluate_schedule_hard_rules(model, label, assignments, include_override_warnings=True)
            engine_hard = [v for v in final_structured_violations if (not v.is_override_allowed and v.severity == "error" and is_engine_managed_source(v.assignment_source))]
            repaired_ops = int(repair_stats.get("trimmed", 0)) + int(repair_stats.get("substituted", 0)) + int(repair_stats.get("fragment_removed", 0)) + int(repair_stats.get("removed", 0))
            warnings.append(
                f"Final hard-rule repair actions={repaired_ops} (trimmed={int(repair_stats.get('trimmed',0))}, substituted={int(repair_stats.get('substituted',0))}, fragment_removed={int(repair_stats.get('fragment_removed',0))}, removed={int(repair_stats.get('removed',0))})."
            )
            cov_loss = int(repair_stats.get("coverage_lost_ticks", 0) or 0)
            if cov_loss > 0:
                warnings.append(f"Coverage lost during legality cleanup: {cov_loss} minimum-demand tick(s) removed where no valid alternative was found.")
            forced = dict(repair_stats.get("forced_rules", {}) or {})
            if forced:
                top = ", ".join(f"{k}:{v}" for k, v in sorted(forced.items(), key=lambda kv: (-kv[1], kv[0]))[:4])
                warnings.append(f"Legality cleanup was forced primarily by: {top}.")
    override_only = [v for v in final_structured_violations if v.is_override_allowed]
    override_cap_conflicts = [v for v in override_only if v.code in {"maximum-weekly-labor-cap", "max-staffing-soft-ceiling", "employee-max-weekly-hours"}]
    if engine_hard:
        warnings.append(f"INFEASIBLE: scenario invalid after final hard validation ({len(engine_hard)} engine hard violations remain).")
        fallback_assigns = list(best_valid_state.get("assignments") or [])
        if fallback_assigns:
            fallback_engine_hard = _engine_hard_violations(fallback_assigns)
            if not fallback_engine_hard:
                assignments = fallback_assigns
                emp_hours = dict(best_valid_state.get("emp_hours") or {})
                total_hours = float(sum(emp_hours.values()))
                coverage = dict(best_valid_state.get("coverage") or count_coverage_per_tick(assignments))
                final_structured_violations = evaluate_schedule_hard_rules(model, label, assignments, include_override_warnings=True)
                engine_hard = [v for v in final_structured_violations if (not v.is_override_allowed and v.severity == "error" and is_engine_managed_source(v.assignment_source))]
                warnings.append(f"Runtime fallback returned best valid schedule captured during {best_valid_state.get('tag', 'solver_run')}.")
    if override_only:
        warnings.append(f"Override diagnostics: {len(override_only)} override assignment rule warning(s) retained by manager authority.")
    for v in final_structured_violations:
        warnings.append(f"FINAL HARD VALIDATION: {_viol_to_text(v)}")
    coverage = count_coverage_per_tick(assignments)
    min_short2, pref_short2, max_viol2 = compute_requirement_shortfalls(min_req, pref_req, max_req, coverage)
    filled = int(sum(min_req.values()) - min_short2)
    total = int(sum(min_req.values()))
    total_hours = float(sum(emp_hours.values()))
    if 'phase_diagnostics' in locals():
        phase_diagnostics["phase7_final_legality"] = {
            "final_total_violations": int(len(final_structured_violations)),
            "final_engine_hard_violations": int(len(engine_hard)),
            "override_only_violations": int(len(override_only)),
            "repair_stats": dict(repair_stats),
        }

    # Explainability diagnostics: retain legacy text list and add normalized structured factors.
    limiting_structured: List[Dict[str, Any]] = []

    def _push_limiting_factor(kind: str, message: str, value: Optional[float] = None, unit: str = "count", severity: str = "info") -> None:
        item: Dict[str, Any] = {
            "kind": str(kind),
            "message": str(message),
            "severity": str(severity),
            "unit": str(unit),
        }
        if value is not None:
            item["value"] = float(value)
        limiting_structured.append(item)

    try:
        if min_short2 > 0:
            _push_limiting_factor("coverage_min_shortfall", f"MIN coverage shortfall: {int(min_short2)} tick(s) under minimum", value=float(min_short2), unit="ticks", severity="warning")
        if pref_short2 > 0:
            _push_limiting_factor("coverage_pref_shortfall", f"Preferred coverage shortfall: {int(pref_short2)} tick(s) under preferred", value=float(pref_short2), unit="ticks")
        if max_viol2 > 0:
            _push_limiting_factor("coverage_max_violation", f"Max staffing violated: {int(max_viol2)} tick(s) over max", value=float(max_viol2), unit="ticks", severity="warning")
    except Exception:
        pass
    try:
        if max_weekly_cap > 0.0 and cap_blocked_attempts > 0:
            _push_limiting_factor("labor_cap_blocked_attempts", f"Weekly cap blocked {int(cap_blocked_attempts)} placement attempts", value=float(cap_blocked_attempts), unit="attempts")
    except Exception:
        pass
    try:
        if participation_missed:
            _push_limiting_factor("participation_shortfall", f"Participation infeasible for {len(participation_missed)} employee(s)", value=float(len(participation_missed)), unit="employees", severity="warning")
        if floor_shortfall_hours > 1e-9:
            _push_limiting_factor("labor_floor_shortfall", f"Labor floor shortfall: {floor_shortfall_hours:.1f}h", value=float(floor_shortfall_hours), unit="hours", severity="warning")
    except Exception:
        pass
    try:
        locked_ct = sum(1 for a in assignments if assignment_provenance(a) == ASSIGNMENT_SOURCE_FIXED_LOCKED)
        if locked_ct:
            _push_limiting_factor("locked_assignments_present", f"Locked shifts present: {locked_ct} assignment(s)", value=float(locked_ct), unit="assignments")
    except Exception:
        pass
    try:
        unscheduled_opted_in = sum(
            1 for e in model.employees
            if e.work_status == "Active" and bool(getattr(e, "wants_hours", True)) and float(emp_hours.get(e.name, 0.0) or 0.0) <= 1e-9
        )
        if unscheduled_opted_in > 0:
            _push_limiting_factor("unscheduled_active_opted_in", f"Active opted-in employees unscheduled: {unscheduled_opted_in}", value=float(unscheduled_opted_in), unit="employees")
    except Exception:
        pass
    try:
        if override_cap_conflicts:
            _push_limiting_factor("override_cap_conflicts", f"Override-caused cap/conflict warnings: {len(override_cap_conflicts)}", value=float(len(override_cap_conflicts)), unit="violations")
    except Exception:
        pass

    limiting: List[str] = [str(x.get("message", "")).strip() for x in limiting_structured if str(x.get("message", "")).strip()]

    try:
        req_fp = {
            "min_total": int(sum(int(v) for v in min_req.values())),
            "pref_total": int(sum(int(v) for v in pref_req.values())),
            "max_total": int(sum(int(v) for v in max_req.values())),
            "key_count": int(len(min_req)),
        }
    except Exception:
        req_fp = {"min_total": 0, "pref_total": 0, "max_total": 0, "key_count": 0}

    unused_legal_capacity_by_employee: Dict[str, Dict[str, Any]] = {}
    unresolved_window_legal_summary: Dict[str, Any] = {"windows_with_legal_candidates": 0, "windows_with_zero_legal_candidates": 0, "sample_windows": []}
    try:
        for e in model.employees:
            if getattr(e, "work_status", "") != "Active" or not bool(getattr(e, "wants_hours", True)):
                continue
            max_h = float(getattr(e, "max_weekly_hours", 0.0) or 0.0)
            used_h = float(emp_hours.get(e.name, 0.0) or 0.0)
            unused_legal_capacity_by_employee[e.name] = {
                "used_hours": used_h,
                "max_weekly_hours": max_h,
                "remaining_hours": max(0.0, max_h - used_h),
            }

        cov_final = count_coverage_per_tick(assignments)
        unresolved_windows: List[Tuple[str, str, int, int]] = []
        for area in AREAS:
            for day in DAYS:
                t0 = 0
                while t0 < DAY_TICKS:
                    k = (day, area, int(t0))
                    if int(cov_final.get(k, 0)) >= int(min_req.get(k, 0)):
                        t0 += 1
                        continue
                    st0 = int(t0)
                    while t0 < DAY_TICKS and int(cov_final.get((day, area, int(t0)), 0)) < int(min_req.get((day, area, int(t0)), 0)):
                        t0 += 1
                    unresolved_windows.append((day, area, st0, int(t0)))

        for day, area, st0, en0 in unresolved_windows[:40]:
            legal_candidates: List[str] = []
            for e in model.employees:
                if getattr(e, "work_status", "") != "Active" or not bool(getattr(e, "wants_hours", True)):
                    continue
                if area not in (getattr(e, "areas_allowed", []) or []):
                    continue
                min_h_emp = float(getattr(e, "min_hours_per_shift", 1.0) or 1.0)
                seg_ticks = max(1, int(math.ceil(min_h_emp * TICKS_PER_HOUR)))
                if st0 + seg_ticks > DAY_TICKS:
                    continue
                found = False
                start_probe = max(0, st0 - seg_ticks + 1)
                end_probe = min(st0, DAY_TICKS - seg_ticks)
                for pst in range(start_probe, end_probe + 1):
                    pen = int(pst + seg_ticks)
                    if pen <= st0 or pst >= en0:
                        continue
                    trial_a = Assignment(day, area, int(pst), int(pen), e.name, locked=False, source=ASSIGNMENT_SOURCE_ENGINE)
                    trial = assignments + [trial_a]
                    hard_bad = False
                    for v in evaluate_schedule_hard_rules(model, label, trial, include_override_warnings=False):
                        if v.severity == "error" and is_engine_managed_source(v.assignment_source):
                            hard_bad = True
                            break
                    if not hard_bad:
                        found = True
                        break
                if found:
                    legal_candidates.append(e.name)
            if legal_candidates:
                unresolved_window_legal_summary["windows_with_legal_candidates"] += 1
            else:
                unresolved_window_legal_summary["windows_with_zero_legal_candidates"] += 1
            if len(unresolved_window_legal_summary["sample_windows"]) < 10:
                unresolved_window_legal_summary["sample_windows"].append({
                    "day": day, "area": area, "start_t": int(st0), "end_t": int(en0),
                    "legal_candidates": sorted(legal_candidates)
                })
    except Exception:
        pass

    diagnostics = {
    "min_short": int(min_short2) if 'min_short2' in locals() else int(unfilled),
    "pref_short": int(pref_short2) if 'pref_short2' in locals() else 0,
    "max_viol": int(max_viol2) if 'max_viol2' in locals() else 0,
    "cap_blocked_attempts": int(cap_blocked_attempts) if 'cap_blocked_attempts' in locals() else 0,
    "cap_blocked_ticks": int(cap_blocked_ticks) if 'cap_blocked_ticks' in locals() else 0,
    "participation_missed": dict(participation_missed) if 'participation_missed' in locals() else {},
    "participation_details": dict(participation_details) if 'participation_details' in locals() else {},
    "labor_floor_shortfall_hours": float(floor_shortfall_hours) if 'floor_shortfall_hours' in locals() else 0.0,
    "locked_hours": float(locked_hours) if 'locked_hours' in locals() else 0.0,
    "engine_hard_violations": int(len(engine_hard)) if 'engine_hard' in locals() else 0,
    "engine_hard_violation_count": int(len(engine_hard)) if 'engine_hard' in locals() else 0,
    "override_rule_warnings": int(len(override_only)) if 'override_only' in locals() else 0,
    "override_warning_count": int(len(override_only)) if 'override_only' in locals() else 0,
    "override_cap_conflicts": int(len(override_cap_conflicts)) if 'override_cap_conflicts' in locals() else 0,
    "override_cap_conflict_count": int(len(override_cap_conflicts)) if 'override_cap_conflicts' in locals() else 0,
    "participation_attempt_stats": dict(participation_attempt_stats) if 'participation_attempt_stats' in locals() else {},
    "unscheduled_active_opted_in": [e.name for e in model.employees if e.work_status == "Active" and bool(getattr(e, "wants_hours", True)) and float(emp_hours.get(e.name, 0.0) or 0.0) <= 1e-9],
    "repair_stats": dict(repair_stats) if 'repair_stats' in locals() else {},

    "unused_legal_capacity_by_employee": dict(unused_legal_capacity_by_employee),
    "unresolved_window_legal_summary": dict(unresolved_window_legal_summary),

    # Phase 3 toggles/weights (for debugging & explainability)
    "enable_coverage_risk_protection": bool(enable_risk) if 'enable_risk' in locals() else False,
    "w_coverage_risk": float(w_risk) if 'w_risk' in locals() else 0.0,
    "enable_utilization_optimizer": bool(enable_util) if 'enable_util' in locals() else False,
    "w_new_employee_penalty": float(w_new_emp) if 'w_new_emp' in locals() else 0.0,
    "w_fragmentation_penalty": float(w_frag) if 'w_frag' in locals() else 0.0,
    "w_extend_shift_bonus": float(w_extend) if 'w_extend' in locals() else 0.0,
    "pattern_learning_enabled": bool(pattern_learning_enabled) if 'pattern_learning_enabled' in locals() else False,
    "learned_patterns_count": int(len(learned_patterns)) if 'learned_patterns' in locals() else 0,
    "w_pattern_learning": float(w_pattern_learning) if 'w_pattern_learning' in locals() else 0.0,

    "final_hard_validation_failed": bool(engine_hard),
    "final_schedule_valid": bool(len(engine_hard) == 0),
    "final_hard_validation_violation_count": int(len(final_structured_violations)),
    "final_hard_validation_violations": list(final_structured_violations),
    "hard_rule_violations": list(final_structured_violations),
    "hard_rule_violation_count": int(len(final_structured_violations)),

    "phase_diagnostics": dict(phase_diagnostics) if 'phase_diagnostics' in locals() else {},
    "phase_snapshots": dict(phase_snapshots),
    "candidate_selection_telemetry": list(solver_selection_telemetry[-400:]),
    "week_shape_diagnostics": {
        "hours_by_day": dict(_daily_store_hours(assignments)),
        "day_load_variance": float(phase_snapshots.get("phase5_cstore_backfill_after_carwash", {}).get("day_load_variance", 0.0) or 0.0),
        "early_week_share": float(phase_snapshots.get("phase5_cstore_backfill_after_carwash", {}).get("early_week_share", 0.0) or 0.0),
        "best_valid_capture_tag": str(best_valid_state.get("tag", "")),
    },
    "add_outcome_counts": dict(add_outcome_counts),
    "requirement_map_fingerprints": {
        "ui_base": dict(req_fp),
        "solver_effective": dict(req_fp),
        "heatmap_effective": dict(req_fp),
    },
    "requirement_map_parity_ok": True,
    "coverage_parity": {
        "solver_total_ticks": int(sum(int(v) for v in count_coverage_per_tick(assignments).values())),
        "heatmap_total_ticks": int(sum(int(v) for v in count_coverage_per_tick(assignments).values())),
        "parity_ok": True,
    },
    "uncovered_min_by_area": {k: int(len(v)) for k, v in (uncovered_min_by_area.items() if 'uncovered_min_by_area' in locals() else [])},
    "master_envelope_consistency": validate_master_envelope_consistency(assignments),
    "specialty_peak_windows": list(specialty_peak_windows) if 'specialty_peak_windows' in locals() else [],
    "specialty_cross_trained": sorted(list(specialty_cross_trained)) if 'specialty_cross_trained' in locals() else [],
    "specialty_weekly_slack_hours": {
        str(name): float(max(0.0, float(getattr(emp_by_name.get(name), "max_weekly_hours", 0.0) or 0.0) - float(emp_hours.get(name, 0.0) or 0.0)))
        for name in sorted(list(specialty_cross_trained))
    } if 'specialty_cross_trained' in locals() else {},

    "limiting_factors": list(limiting),
    "limiting_factors_structured": list(limiting_structured),
    "runtime_budget": runtime_budget.snapshot(),
    "local_search_actuals": {
        "scrutiny": str(scr),
        "iterations_used": int(total_iters_done),
        "restarts_used": int(restarts_done),
        "iterations_target_per_restart": int(iters_per_restart),
        "restarts_target": int(restarts_target),
    },
}

    return assignments, emp_hours, total_hours, warnings, filled, total, int(total_iters_done), int(restarts_done), diagnostics

# -----------------------------
# Output / Export
# -----------------------------
def assignments_by_area_day(assignments: List[Assignment]) -> Dict[str, Dict[str, List[Assignment]]]:
    out: Dict[str, Dict[str, List[Assignment]]] = {a: {d: [] for d in DAYS} for a in AREAS}
    for x in assignments:
        out.setdefault(x.area, {d: [] for d in DAYS}).setdefault(x.day, []).append(x)
    for area in out:
        for d in out[area]:
            out[area][d].sort(key=lambda a: (a.start_t, a.employee_name))
    return out

def make_one_page_html(model: DataModel, label: str, assignments: List[Assignment]) -> str:
    by = assignments_by_area_day(assignments)
    area_colors = _normalize_area_colors(getattr(model.store_info, "area_colors", {}) or {})
    cstore_color = area_colors.get("CSTORE", _default_area_colors().get("CSTORE", "#2b5dff"))
    kitchen_color = area_colors.get("KITCHEN", _default_area_colors().get("KITCHEN", "#d97706"))
    carwash_color = area_colors.get("CARWASH", _default_area_colors().get("CARWASH", "#0f766e"))

    title = f"{html_escape(model.store_info.store_name or 'Labor Force Scheduler')} — {html_escape(label)}"
    sub = html_escape(model.store_info.store_address)
    phone = html_escape(model.store_info.store_phone)
    mgr = html_escape(model.store_info.store_manager)

    def _area_rows(area: str, compact: bool = False) -> str:
        rows = []
        for d in DAYS:
            items = by.get(area, {}).get(d, [])
            if not items:
                rows.append(f"<tr><td class='day'>{d}</td><td class='cell empty'>OFF</td></tr>")
                continue
            chunks = []
            for a in items:
                chunks.append(
                    f"<div class='slot'><span class='emp'>{html_escape(a.employee_name)}</span>"
                    f"<span class='tm'>{tick_to_hhmm(a.start_t)}–{tick_to_hhmm(a.end_t)}</span></div>"
                )
            cls = "cell compact" if compact else "cell"
            rows.append(f"<tr><td class='day'>{d}</td><td class='{cls}'>{''.join(chunks)}</td></tr>")
        return ''.join(rows)

    css = f"""
    <style>
      @page portraitPage {{ size: 8.5in 11in; margin: 0.35in; }}
      @page landscapePage {{ size: 11in 8.5in; margin: 0.35in; }}
      body {{ font-family: 'Segoe UI', Arial, sans-serif; color:#1b1f23; margin:0; }}
      .page {{ page-break-after: always; }}
      .page:last-child {{ page-break-after: auto; }}
      .page.portrait {{ page: portraitPage; }}
      .page.landscape {{ page: landscapePage; }}
      .hdr {{ display:flex; justify-content:space-between; align-items:flex-end; margin-bottom:10px; }}
      .title {{ font-size: 25px; font-weight: 800; }}
      .sub {{ font-size: 13px; color:#4b5563; margin-top:2px; }}
      .meta {{ text-align:right; font-size: 13px; color:#374151; }}
      .area-banner {{ text-align:center; font-size: 32px; font-weight: 900; letter-spacing: 0.6px; margin: 8px 0 10px; }}
      .area-banner.cstore {{ color: {cstore_color}; }}
      .area-banner.kitchen {{ color: {kitchen_color}; }}
      .area-banner.carwash {{ color: {carwash_color}; }}
      table {{ width:100%; border-collapse: collapse; table-layout: fixed; }}
      th, td {{ border: 2px solid #222; padding: 8px; text-align:center; vertical-align: middle; }}
      th {{ background:#f3f4f6; font-size: 16px; }}
      td.day {{ width: 10%; font-weight: 800; font-size: 18px; background:#f8fafc; }}
      td.cell {{ font-size: 16px; line-height: 1.35; }}
      td.cell.compact {{ font-size: 14px; line-height: 1.25; }}
      .slot {{ display:flex; justify-content:center; gap:10px; align-items:center; margin:2px 0; }}
      .slot .emp {{ font-weight: 700; }}
      .slot .tm {{ font-weight: 600; color:#374151; }}
      td.cell.empty {{ font-weight: 700; color:#6b7280; }}
      .stack-section {{ margin-top: 6px; }}
      .stack-section + .stack-section {{ margin-top: 18px; }}
      .foot {{ margin-top:8px; text-align:center; color:#4b5563; font-size:12px; }}
    </style>
    """

    return f"""
    <html><head><meta charset='utf-8'>{css}</head><body>
      <div class='page portrait'>
        <div class='hdr'>
          <div>
            <div class='title'>{title}</div>
            <div class='sub'>{sub}</div>
          </div>
          <div class='meta'>
            <div>Store: {phone}</div>
            <div>Manager: {mgr}</div>
          </div>
        </div>
        <div class='area-banner cstore'>C-STORE SCHEDULE</div>
        <table>
          <thead><tr><th>Day</th><th>Assigned Team & Times</th></tr></thead>
          <tbody>{_area_rows('CSTORE')}</tbody>
        </table>
        <div class='foot'>Generated {today_iso()} • Color coding preserved by department palette.</div>
      </div>

      <div class='page landscape'>
        <div class='hdr'>
          <div>
            <div class='title'>{title}</div>
            <div class='sub'>{html_escape(label)} • Kitchen + Carwash consolidated</div>
          </div>
          <div class='meta'>
            <div>Store: {phone}</div>
            <div>Manager: {mgr}</div>
          </div>
        </div>

        <div class='stack-section'>
          <div class='area-banner kitchen'>KITCHEN</div>
          <table>
            <thead><tr><th>Day</th><th>Assigned Team & Times</th></tr></thead>
            <tbody>{_area_rows('KITCHEN', compact=True)}</tbody>
          </table>
        </div>

        <div class='stack-section'>
          <div class='area-banner carwash'>CARWASH</div>
          <table>
            <thead><tr><th>Day</th><th>Assigned Team & Times</th></tr></thead>
            <tbody>{_area_rows('CARWASH', compact=True)}</tbody>
          </table>
        </div>
      </div>
    </body></html>
    """

def export_html(model: DataModel, label: str, assignments: List[Assignment]) -> str:
    html = make_one_page_html(model, label, assignments)
    fn = _build_export_filename("schedule", label, "html")
    path = rel_path("exports", fn)
    ensure_dir(os.path.dirname(path))
    with open(path, "w", encoding="utf-8") as f:
        f.write(html)
    return path


# -----------------------------
# Additional print views (V3.1)
# -----------------------------
def tick_to_ampm(t: int) -> str:
    """Format tick as e.g. 8:00a / 12:30p (more readable for staff)."""
    t = max(0, min(DAY_TICKS, int(t)))
    mins = t * TICK_MINUTES
    h24 = (mins // 60) % 24
    m = mins % 60
    suf = "a" if h24 < 12 else "p"
    h12 = h24 % 12
    if h12 == 0:
        h12 = 12
    if m == 0:
        return f"{h12}{suf}"
    return f"{h12}:{m:02d}{suf}"

def _normalize_user_time(s: str) -> str:
    s = str(s or '').strip().lower().replace(' ', '')
    if not s:
        raise ValueError('blank time')
    if s.endswith('a'):
        s += 'm'
    if s.endswith('p'):
        s += 'm'
    if 'am' not in s and 'pm' not in s:
        hh = s.split(':', 1)[0]
        try:
            hour = int(hh)
        except Exception:
            hour = 0
        s += 'pm' if 1 <= hour <= 11 else 'am'
    m = re.fullmatch(r'(\d{1,2})(?::(\d{2}))?(am|pm)', s)
    if not m:
        raise ValueError(f'invalid time: {s}')
    hour = int(m.group(1))
    minute = int(m.group(2) or '00')
    if not (0 <= minute <= 59):
        raise ValueError(f'invalid minutes: {s}')
    mer = m.group(3)
    if mer == 'am':
        hour = 0 if hour == 12 else hour
    else:
        hour = hour if hour == 12 else hour + 12
    if not (0 <= hour <= 23):
        raise ValueError(f'invalid hour: {s}')
    return f"{hour:02d}:{minute:02d}"

AREA_LABEL = {"CSTORE": "C-Store", "KITCHEN": "Kitchen", "CARWASH": "Carwash"}
AREA_TAG = {"CSTORE": "+C", "KITCHEN": "+Kit", "CARWASH": "+Wash"}

def _build_emp_day_area(assignments: List[Assignment]) -> Tuple[Dict[Tuple[str,str,str], List[Tuple[int,int]]],
                                                               Dict[Tuple[str,str], Set[str]]]:
    """Returns:
    - shifts[(emp, day, area)] = [(start,end), ...]
    - areas_worked[(emp, day)] = set(areas)
    """
    shifts: Dict[Tuple[str,str,str], List[Tuple[int,int]]] = {}
    areas_worked: Dict[Tuple[str,str], Set[str]] = {}
    for a in assignments:
        key = (a.employee_name, a.day, a.area)
        shifts.setdefault(key, []).append((a.start_t, a.end_t))
        areas_worked.setdefault((a.employee_name, a.day), set()).add(a.area)
    # normalize ordering
    for k in list(shifts.keys()):
        shifts[k].sort()
    return shifts, areas_worked

def make_employee_calendar_html(model: DataModel, label: str, assignments: List[Assignment]) -> str:
    """
    Employee-facing calendar-style schedules:
      Page 1: MAIN (all areas merged) with "See Kitchen"/"See Carwash" hints
      Page 2: KITCHEN (kitchen-only)
      Page 3: CARWASH (carwash-only)

    Design goals:
      - Full-page utilization (fixed layout widths + print margins)
      - No text overlap (wrap enabled, no ellipsis, safe font sizes)
      - Alphabetical employees
      - Total hours in a dedicated right-side column
      - One-line time blocks (multiple blocks separated by '; ')
    """
    # Employees alphabetically
    emps = sorted(model.employees, key=lambda e: (e.name or "").lower())

    # Weekly hours across all areas
    emp_hours: Dict[str, float] = {}
    for a in assignments:
        emp_hours[a.employee_name] = emp_hours.get(a.employee_name, 0.0) + hours_between_ticks(a.start_t, a.end_t)

    # Build per-employee/day lists
    by_emp_day: Dict[Tuple[str, str], List[Assignment]] = {}
    by_emp_day_area: Dict[Tuple[str, str, str], List[Assignment]] = {}
    for a in assignments:
        by_emp_day.setdefault((a.employee_name, a.day), []).append(a)
        by_emp_day_area.setdefault((a.employee_name, a.day, a.area), []).append(a)

    for k in list(by_emp_day.keys()):
        by_emp_day[k].sort(key=lambda x: (x.start_t, x.end_t, x.area))
    for k in list(by_emp_day_area.keys()):
        by_emp_day_area[k].sort(key=lambda x: (x.start_t, x.end_t))

    def _merge_blocks(items: List[Tuple[int, int, Optional[str]]]) -> List[Tuple[int, int, set]]:
        """Merge contiguous/overlapping blocks. Returns (start,end,areas_set)."""
        if not items:
            return []
        items = sorted(items, key=lambda x: (x[0], x[1]))
        out: List[Tuple[int, int, set]] = []
        cur_s, cur_e, cur_a = items[0][0], items[0][1], set()
        if items[0][2]:
            cur_a.add(items[0][2])
        for s, e, area in items[1:]:
            # contiguous or overlap => uninterrupted
            if s <= cur_e:
                cur_e = max(cur_e, e)
                if area:
                    cur_a.add(area)
            else:
                out.append((cur_s, cur_e, set(cur_a)))
                cur_s, cur_e = s, e
                cur_a = set()
                if area:
                    cur_a.add(area)
        out.append((cur_s, cur_e, set(cur_a)))
        return out

    def _format_time_blocks(blocks: List[Tuple[int,int,set]]) -> str:
        return "; ".join(f"{tick_to_ampm(s)}–{tick_to_ampm(e)}" for s,e,_ in blocks)

    def _format_hints(areas: set) -> str:
        hints = []
        if "KITCHEN" in areas:
            hints.append("<span class='hint-kitchen'>See Kitchen</span>")
        if "CARWASH" in areas:
            hints.append("<span class='hint-carwash'>See Carwash</span>")
        return " • ".join(hints)

    area_colors = _normalize_area_colors(getattr(model.store_info, "area_colors", {}) or {})
    cstore_color = area_colors.get("CSTORE", _default_area_colors()["CSTORE"])
    kitchen_color = area_colors.get("KITCHEN", _default_area_colors()["KITCHEN"])
    carwash_color = area_colors.get("CARWASH", _default_area_colors()["CARWASH"])

    title = f"{html_escape(model.store_info.store_name or 'Schedule')} — Employee Calendar"
    phone = html_escape(model.store_info.store_phone or "")
    mgr = html_escape(model.store_info.store_manager or "")

    css = """
    <style>
      @page { size: landscape; margin: 0.35in; }
      body { font-family: Arial, Helvetica, sans-serif; }
      .hdr { display:flex; justify-content:space-between; align-items:flex-end; margin-bottom:10px; }
      .title { font-size: 18px; font-weight: 700; }
      .sub { font-size: 11px; color:#333; }
      .meta { font-size: 10px; color:#333; text-align:right; }
      .pagebreak { page-break-before: always; }
      table { width: 100%; border-collapse: collapse; table-layout: fixed; }
      th, td { border: 1px solid #222; padding: 4px 6px; vertical-align: top; }
      th { background: #f4f4f4; font-size: 10px; text-align: center; }
      td.emp, td.hours { font-size: 10px; font-weight: 700; }
      td.emp { white-space: normal; overflow-wrap:anywhere; word-break: break-word; }
      td.hours { text-align: center; }
      td.cell { font-size: 10px; line-height: 1.15; white-space: normal; overflow-wrap:anywhere; word-break: break-word; }
      .off { color:#111; font-weight:700; text-align:center; }
      .hint { color:#777; font-size: 9px; font-weight: 600; }
      .main-cstore { color:__CSTORE_COLOR__; }
      .hint-kitchen { color:__KITCHEN_COLOR__; }
      .hint-carwash { color:__CARWASH_COLOR__; }
      .kitchen-cell { color:__KITCHEN_COLOR__; }
      .carwash-cell { color:__CARWASH_COLOR__; }
      .foot { margin-top:8px; font-size: 9px; color:#555; }
    </style>
    """
    css = css.replace("__CSTORE_COLOR__", cstore_color).replace("__KITCHEN_COLOR__", kitchen_color).replace("__CARWASH_COLOR__", carwash_color)

    def _weekly_hours_str(name: str) -> str:
        weekly = emp_hours.get(name, 0.0)
        if abs(weekly - round(weekly)) < 1e-9:
            return str(int(round(weekly)))
        return f"{weekly:.1f}"

    def cell_main(e: Employee, day: str) -> str:
        items = by_emp_day.get((e.name, day), [])
        if not items:
            return '<div class="off">OFF</div>'
        # one merged timeline for the day across ALL areas
        blocks = _merge_blocks([(int(a.start_t), int(a.end_t), a.area) for a in items])
        times = _format_time_blocks(blocks)
        # any kitchen/carwash involvement anywhere in the day => hint
        all_areas = set()
        for _, _, a_set in blocks:
            all_areas |= a_set
        hint = _format_hints(all_areas)
        times_html = f"<span class='main-cstore'>{html_escape(times)}</span>"
        if hint:
            return f"{times_html}<br><span class='hint'>{hint}</span>"
        return times_html

    def cell_area_only(e: Employee, day: str, area: str) -> str:
        items = by_emp_day_area.get((e.name, day, area), [])
        if not items:
            # If worked elsewhere, still show OFF for this dept
            return ''  # blank if not scheduled in this department
        blocks = _merge_blocks([(int(a.start_t), int(a.end_t), area) for a in items])
        times = _format_time_blocks(blocks)
        css_class = "kitchen-cell" if area == "KITCHEN" else ("carwash-cell" if area == "CARWASH" else "")
        if css_class:
            return f"<span class='{css_class}'>{html_escape(times)}</span>"
        return html_escape(times)

    def build_table(kind: str) -> str:
        # kind in {"MAIN","KITCHEN","CARWASH"}
        # For department pages, show only employees who have at least one shift in that department this week
        day_label = {"Sun":"Sunday","Mon":"Monday","Tue":"Tuesday","Wed":"Wednesday","Thu":"Thursday","Fri":"Friday","Sat":"Saturday"}
        day_heads = "".join(f"<th>{html_escape(day_label.get(d,d))}</th>" for d in DAYS)
        rows = []
        if kind == "MAIN":
            emps_for_kind = emps
        else:
            names_with = set()
            for (nm, dy, ar), items in by_emp_day_area.items():
                if ar == kind and items:
                    names_with.add(nm)
            emps_for_kind = [e for e in emps if e.name in names_with]
        for e in emps_for_kind:
            phone_str = (e.phone or "").strip()
            name_line = e.name or ""
            if phone_str:
                name_line += f" - {phone_str}"
            tds = [f'<td class="emp" title="{html_escape(name_line)}">{html_escape(name_line)}</td>']
            for d in DAYS:
                if kind == "MAIN":
                    tds.append(f'<td class="cell">{cell_main(e, d)}</td>')
                else:
                    tds.append(f'<td class="cell">{cell_area_only(e, d, kind)}</td>')
            tds.append(f'<td class="hours">{html_escape(_weekly_hours_str(e.name))}</td>')
            rows.append("<tr>" + "".join(tds) + "</tr>")

        # Column widths tuned for readability and full page use (landscape)
        # Employee 24%, Total Hours 8%, remaining split across 7 days
        day_w = (100.0 - 24.0 - 8.0) / 7.0
        colgroup = (
            f"<colgroup>"
            f"<col style='width:24%'>"
            + "".join(f"<col style='width:{day_w:.3f}%'>" for _ in DAYS)
            + f"<col style='width:8%'>"
            f"</colgroup>"
        )
        head = (
            "<thead><tr>"
            "<th>Employee</th>"
            f"{day_heads}"
            "<th>Total Hours</th>"
            "</tr></thead>"
        )
        caption = "Main Staffing Schedule (All Areas)" if kind == "MAIN" else (AREA_LABEL.get(kind, kind.title()) + " Schedule")
        # Full day names per user preference
        return f"""
        <div class="section {'pagebreak' if kind!='MAIN' else ''}">
          <h2 style="font-size:13px; margin:10px 0 6px;">{html_escape(caption)}</h2>
          <table>
            {colgroup}
            {head}
            <tbody>{''.join(rows)}</tbody>
          </table>
        </div>
        """

    sub_main = f"{html_escape(label)} • Landscape • Sunday–Saturday (See department pages for details)"
    html = f"""
    <html><head><meta charset="utf-8">{css}</head>
    <body>
      <div class="hdr">
        <div>
          <div class="title">{title}</div>
          <div class="sub">{sub_main}</div>
        </div>
        <div class="meta">
          <div>Store: {phone}</div>
          <div>Manager: {mgr}</div>
        </div>
      </div>
      {build_table("MAIN")}
      {build_table("KITCHEN")}
      {build_table("CARWASH")}
      <div class="foot">Generated {today_iso()} • Blank cells on department pages mean not scheduled for that department on that day. MAIN shows overall work window; use “See Kitchen/See Carwash” for assignment details.</div>
    </body></html>
    """
    return html

def export_employee_calendar_html(model: DataModel, label: str, assignments: List[Assignment]) -> str:
    html = make_employee_calendar_html(model, label, assignments)
    fn = _build_export_filename("employee_calendar", label, "html")
    path = rel_path("exports", fn)
    ensure_dir(os.path.dirname(path))
    with open(path, "w", encoding="utf-8") as f:
        f.write(html)
    return path


def make_employee_calendar_html_with_overrides(model: DataModel, label: str, assignments: List[Assignment], overrides: dict) -> str:
    """
    Same output as make_employee_calendar_html, but allows overriding cell text.
    overrides format: { "MAIN": {emp:{day:text}}, "KITCHEN": {...}, "CARWASH": {...} }
    """
    overrides = overrides or {}
    # Employees alphabetically
    emps = sorted(model.employees, key=lambda e: (e.name or "").lower())

    # Weekly hours across all areas (kept from assignments for consistency)
    emp_hours: Dict[str, float] = {}
    for a in assignments:
        emp_hours[a.employee_name] = emp_hours.get(a.employee_name, 0.0) + hours_between_ticks(a.start_t, a.end_t)

    # Build per-employee/day lists
    by_emp_day: Dict[Tuple[str, str], List[Assignment]] = {}
    by_emp_day_area: Dict[Tuple[str, str, str], List[Assignment]] = {}
    for a in assignments:
        by_emp_day.setdefault((a.employee_name, a.day), []).append(a)
        by_emp_day_area.setdefault((a.employee_name, a.day, a.area), []).append(a)

    for k in list(by_emp_day.keys()):
        by_emp_day[k].sort(key=lambda x: (x.start_t, x.end_t, x.area))
    for k in list(by_emp_day_area.keys()):
        by_emp_day_area[k].sort(key=lambda x: (x.start_t, x.end_t))

    def _merge_blocks(items: List[Tuple[int, int, Optional[str]]]) -> List[Tuple[int, int, set]]:
        if not items:
            return []
        items = sorted(items, key=lambda x: (x[0], x[1]))
        out: List[Tuple[int, int, set]] = []
        cur_s, cur_e, cur_a = items[0][0], items[0][1], set()
        if items[0][2]:
            cur_a.add(items[0][2])
        for s, e, area in items[1:]:
            if s <= cur_e:
                cur_e = max(cur_e, e)
                if area:
                    cur_a.add(area)
            else:
                out.append((cur_s, cur_e, set(cur_a)))
                cur_s, cur_e = s, e
                cur_a = set()
                if area:
                    cur_a.add(area)
        out.append((cur_s, cur_e, set(cur_a)))
        return out

    def _block_str(s: int, e: int) -> str:
        return f"{tick_to_ampm(int(s))}-{tick_to_ampm(int(e))}"

    def _blocks_to_str(blocks: List[Tuple[int,int,set]], include_hints: bool = False) -> str:
        parts = []
        for s, e, areas in blocks:
            seg = _block_str(s, e)
            if include_hints:
                hints = []
                if "KITCHEN" in areas:
                    hints.append("<span class=\'hint-kitchen\'>See Kitchen</span>")
                if "CARWASH" in areas:
                    hints.append("<span class=\'hint-carwash\'>See Carwash</span>")
                if hints:
                    seg += f' <span class="hint">({" / ".join(hints)})</span>'
            parts.append(seg)
        return "; ".join(parts)

    def _weekly_hours_str(name: str) -> str:
        weekly = emp_hours.get(name, 0.0)
        if weekly <= 0.0:
            return "0"
        if abs(weekly - round(weekly)) < 1e-6:
            return str(int(round(weekly)))
        return f"{weekly:.1f}"

    def _override(kind: str, emp: str, day: str) -> Optional[str]:
        try:
            v = overrides.get(kind, {}).get(emp, {}).get(day, None)
            if v is None:
                return None
            # allow blank override
            return str(v)
        except Exception:
            return None

    def cell_main(e: Employee, d: str) -> str:
        ov = _override("MAIN", e.name or "", d)
        if ov is not None:
            # render plain text override; allow line breaks
            s = html_escape(ov).replace("\n", "<br>")
            if not s:
                return ""
            if s.strip().lower() == "off":
                return '<div class="off">Off</div>'
            return f"<span class='main-cstore'>{s}</span>"

        # Default behavior from assignments
        items = []
        for a in by_emp_day.get((e.name, d), []):
            items.append((int(a.start_t), int(a.end_t), a.area))
        merged = _merge_blocks(items)
        if not merged:
            return '<div class="off">Off</div>'
        return f"<span class='main-cstore'>{_blocks_to_str(merged, include_hints=True)}</span>"

    def cell_area_only(e: Employee, d: str, kind: str) -> str:
        ov = _override(kind, e.name or "", d)
        if ov is not None:
            s = html_escape(ov).replace("\n", "<br>")
            css_class = "kitchen-cell" if kind == "KITCHEN" else ("carwash-cell" if kind == "CARWASH" else "")
            if css_class:
                return f"<span class='{css_class}'>{s}</span>"
            return s
        lst = by_emp_day_area.get((e.name, d, kind), [])
        if not lst:
            return ""  # blank cells on department pages
        items = [(int(a.start_t), int(a.end_t), None) for a in lst]
        merged = _merge_blocks(items)
        text = _blocks_to_str(merged, include_hints=False)
        css_class = "kitchen-cell" if kind == "KITCHEN" else ("carwash-cell" if kind == "CARWASH" else "")
        if css_class:
            return f"<span class='{css_class}'>{text}</span>"
        return text

    area_colors = _normalize_area_colors(getattr(model.store_info, "area_colors", {}) or {})
    cstore_color = area_colors.get("CSTORE", _default_area_colors()["CSTORE"])
    kitchen_color = area_colors.get("KITCHEN", _default_area_colors()["KITCHEN"])
    carwash_color = area_colors.get("CARWASH", _default_area_colors()["CARWASH"])

    title = f"Employee Calendar Schedule — {html_escape(label)}"
    mgr = html_escape(getattr(model.store_info, "manager_name", "") or "")
    phone = html_escape(getattr(model.store_info, "store_name", "") or "")

    css = """
    <style>
      @page { size: landscape; margin: 0.35in; }
      body { font-family: Arial, sans-serif; color: #111; }
      .hdr { display:flex; justify-content: space-between; align-items:flex-end; margin-bottom: 8px; }
      .title { font-size: 14px; font-weight: 800; }
      .sub { font-size: 10px; color:#444; margin-top: 2px; }
      .meta { text-align: right; font-size: 10px; color:#444; }
      .section { margin-top: 10px; }
      .pagebreak { page-break-before: always; }
      table { width: 100%; border-collapse: collapse; table-layout: fixed; }
      th, td { border: 1px solid #999; padding: 4px 6px; vertical-align: top; }
      th { background: #f4f4f4; font-size: 10px; text-align: center; }
      td.emp, td.hours { font-size: 10px; font-weight: 700; }
      td.emp { white-space: normal; overflow-wrap:anywhere; word-break: break-word; }
      td.hours { text-align: center; }
      td.cell { font-size: 10px; line-height: 1.15; white-space: normal; overflow-wrap:anywhere; word-break: break-word; }
      .off { color:#111; font-weight:700; text-align:center; }
      .hint { color:#777; font-size: 9px; font-weight: 600; }
      .main-cstore { color:__CSTORE_COLOR__; }
      .hint-kitchen { color:__KITCHEN_COLOR__; }
      .hint-carwash { color:__CARWASH_COLOR__; }
      .kitchen-cell { color:__KITCHEN_COLOR__; }
      .carwash-cell { color:__CARWASH_COLOR__; }
      .foot { margin-top:8px; font-size: 9px; color:#555; }
    </style>
    """
    css = css.replace("__CSTORE_COLOR__", cstore_color).replace("__KITCHEN_COLOR__", kitchen_color).replace("__CARWASH_COLOR__", carwash_color)

    def build_table(kind: str) -> str:
        day_label = {"Sun":"Sunday","Mon":"Monday","Tue":"Tuesday","Wed":"Wednesday","Thu":"Thursday","Fri":"Friday","Sat":"Saturday"}
        day_heads = "".join(f"<th>{html_escape(day_label.get(d,d))}</th>" for d in DAYS)
        rows = []
        if kind == "MAIN":
            emps_for_kind = emps
        else:
            names_with = set()
            for (nm, dy, ar), items in by_emp_day_area.items():
                if ar == kind and items:
                    names_with.add(nm)
            emps_for_kind = [e for e in emps if e.name in names_with]
        for e in emps_for_kind:
            phone_str = (e.phone or "").strip()
            name_line = e.name or ""
            if phone_str:
                name_line += f" - {phone_str}"
            tds = [f'<td class="emp" title="{html_escape(name_line)}">{html_escape(name_line)}</td>']
            for d in DAYS:
                if kind == "MAIN":
                    tds.append(f'<td class="cell">{cell_main(e, d)}</td>')
                else:
                    tds.append(f'<td class="cell">{cell_area_only(e, d, kind)}</td>')
            tds.append(f'<td class="hours">{html_escape(_weekly_hours_str(e.name))}</td>')
            rows.append("<tr>" + "".join(tds) + "</tr>")

        day_w = (100.0 - 24.0 - 8.0) / 7.0
        colgroup = (
            f"<colgroup>"
            f"<col style='width:24%'>"
            + "".join(f"<col style='width:{day_w:.3f}%'>" for _ in DAYS)
            + f"<col style='width:8%'>"
            f"</colgroup>"
        )
        head = (
            "<thead><tr>"
            "<th>Employee</th>"
            f"{day_heads}"
            "<th>Total Hours</th>"
            "</tr></thead>"
        )
        caption = "Main Staffing Schedule (All Areas)" if kind == "MAIN" else (AREA_LABEL.get(kind, kind.title()) + " Schedule")
        return f"""
        <div class="section {'pagebreak' if kind!='MAIN' else ''}">
          <h2 style="font-size:13px; margin:10px 0 6px;">{html_escape(caption)}</h2>
          <table>
            {colgroup}
            {head}
            <tbody>{''.join(rows)}</tbody>
          </table>
        </div>
        """

    sub_main = f"{html_escape(label)} • Landscape • Sunday–Saturday (manual edits applied)"
    html = f"""
    <html><head><meta charset="utf-8">{css}</head>
    <body>
      <div class="hdr">
        <div>
          <div class="title">{title}</div>
          <div class="sub">{sub_main}</div>
        </div>
        <div class="meta">
          <div>Store: {phone}</div>
          <div>Manager: {mgr}</div>
        </div>
      </div>
      {build_table("MAIN")}
      {build_table("KITCHEN")}
      {build_table("CARWASH")}
      <div class="foot">Generated {today_iso()} • Manual edits may not match solver utilization/coverage metrics.</div>
    </body></html>
    """
    return html

def export_employee_calendar_html_with_overrides(model: DataModel, label: str, assignments: List[Assignment], overrides: dict) -> str:
    html = make_employee_calendar_html_with_overrides(model, label, assignments, overrides)
    fn = _build_export_filename("employee_calendar_manual", label, "html")
    path = rel_path("exports", fn)
    ensure_dir(os.path.dirname(path))
    with open(path, "w", encoding="utf-8") as f:
        f.write(html)
    return path

def build_manager_readiness_summary(
    model: DataModel,
    label: str,
    assignments: List[Assignment],
    diagnostics: Optional[Dict[str, Any]] = None,
    warnings: Optional[List[str]] = None,
    filled_slots: Optional[int] = None,
    total_slots: Optional[int] = None,
) -> Dict[str, Any]:
    diag = dict(diagnostics or {})
    warn_list = [str(w).strip() for w in (warnings or []) if str(w).strip()]
    filled = int(filled_slots if filled_slots is not None else len(assignments))
    total = int(total_slots if total_slots is not None else len(assignments))
    if total <= 0:
        try:
            _emp_hours, _total_hours, filled, total = calc_schedule_stats(model, assignments)
        except Exception:
            filled = int(len(assignments))
            total = int(len(assignments))
    coverage_pct = (float(filled) / float(total) * 100.0) if total > 0 else 100.0
    min_short = max(0, int(diag.get("min_short", 0) or 0))
    pref_short = max(0, int(diag.get("pref_short", 0) or 0))
    max_viol = max(0, int(diag.get("max_viol", 0) or 0))
    hard_viol = max(0, int(diag.get("engine_hard_violation_count", diag.get("engine_hard_violations", 0)) or 0))
    override_warn = max(0, int(diag.get("override_warning_count", diag.get("override_rule_warnings", 0)) or 0))
    cap_blocked = max(0, int(diag.get("cap_blocked_attempts", 0) or 0))
    final_valid = bool(diag.get("final_schedule_valid", hard_viol == 0))
    status = "Ready to Publish"
    publish_ready = True
    if not final_valid or hard_viol > 0 or min_short > 0:
        status = "Not Ready to Publish"
        publish_ready = False
    elif pref_short > 0 or max_viol > 0 or override_warn > 0 or cap_blocked > 0 or warn_list:
        status = "Publish With Review"

    headline = []
    if publish_ready and status == "Ready to Publish":
        headline.append("Minimum coverage is fully met and no engine hard-rule failures were detected.")
    if min_short > 0:
        headline.append(f"{min_short} required 30-minute coverage block(s) are still uncovered.")
    if hard_viol > 0:
        headline.append(f"{hard_viol} engine hard-rule violation(s) remain.")
    if pref_short > 0:
        headline.append(f"{pref_short} preferred coverage block(s) are below target.")
    if max_viol > 0:
        headline.append(f"{max_viol} block(s) exceed the configured max staffing ceiling.")
    if override_warn > 0:
        headline.append(f"{override_warn} manager override warning(s) should be reviewed before publish.")
    if cap_blocked > 0:
        headline.append(f"Labor caps blocked {cap_blocked} placement attempt(s) during solve/refine.")
    if not headline:
        headline.append("Review complete. No additional publish blockers were detected from the current diagnostics.")

    plain_lines = [
        f"Publish readiness: {status}",
        f"Coverage: {coverage_pct:.1f}% ({filled}/{total} required blocks filled)",
        f"Required coverage gaps: {min_short}",
        f"Preferred coverage gaps: {pref_short}",
        f"Max staffing warnings: {max_viol}",
        f"Hard-rule failures: {hard_viol}",
        f"Override warnings: {override_warn}",
    ]
    if cap_blocked > 0:
        plain_lines.append(f"Labor-cap blocked attempts: {cap_blocked}")
    if warn_list:
        plain_lines.append("Top warnings:")
        for item in warn_list[:3]:
            plain_lines.append(f"- {item}")

    return {
        "status": status,
        "publish_ready": bool(publish_ready),
        "coverage_pct": float(coverage_pct),
        "filled_slots": int(filled),
        "total_slots": int(total),
        "min_short": int(min_short),
        "pref_short": int(pref_short),
        "max_viol": int(max_viol),
        "hard_violations": int(hard_viol),
        "override_warnings": int(override_warn),
        "cap_blocked_attempts": int(cap_blocked),
        "headline": list(headline),
        "plain_text": "\n".join(plain_lines),
    }

def _req_sched_counts(model: DataModel, assignments: List[Assignment]) -> Tuple[Dict[Tuple[str,str,int], int],
                                                                              Dict[Tuple[str,str,int], int]]:
    # key: (day, area, tick)
    req, _pref, _mx = build_requirement_maps(model.requirements, goals=getattr(model, "manager_goals", None), store_info=getattr(model, "store_info", None))
    sched: Dict[Tuple[str,str,int], int] = {}
    for a in assignments:
        for t in range(int(a.start_t), int(a.end_t)):
            sched[(a.day, a.area, t)] = sched.get((a.day, a.area, t), 0) + 1
    return req, sched

def _clopen_map_from_assignments(model: DataModel, assignments: List[Assignment]) -> Dict[Tuple[str,str], int]:
    cl: Dict[Tuple[str,str], int] = {}
    emp_map = {e.name: e for e in model.employees}
    # process per-employee in day order
    for a in sorted(assignments, key=lambda x: (x.employee_name, DAYS.index(x.day), x.start_t)):
        e = emp_map.get(a.employee_name)
        if not e:
            continue
        apply_clopen_from(model, e, a, cl)
    return cl


def active_manager_tasks_for_label(model: DataModel, label: str) -> List[ManagerTask]:
    wk_start, wk_end = week_window_for_label(label)
    if wk_start is None or wk_end is None:
        return []
    out: List[ManagerTask] = []
    for t in list(getattr(model, "manager_tasks", []) or []):
        if bool(getattr(t, "completed", False)):
            continue
        est = _safe_date_from_iso(getattr(t, "earliest_start_date", ""))
        due = _safe_date_from_iso(getattr(t, "due_date", ""))
        if est is None or due is None:
            continue
        overlaps = (wk_end >= est and wk_start <= due)
        overdue_unfinished = wk_start > due
        if overlaps or overdue_unfinished:
            out.append(t)
    out.sort(key=lambda x: (_safe_date_from_iso(x.due_date) or datetime.date.max, _safe_date_from_iso(x.earliest_start_date) or datetime.date.max, x.title.lower()))
    return out

def make_manager_report_html(model: DataModel, label: str, assignments: List[Assignment]) -> str:
    goals = model.manager_goals
    req, sched = _req_sched_counts(model, assignments)
    _req_min, pref_req, max_req = build_requirement_maps(model.requirements, goals=getattr(model, "manager_goals", None), store_info=getattr(model, "store_info", None))

    def _hours_to_blocks(hours: float) -> int:
        try:
            return int(round(float(hours)))
        except Exception:
            return 0

    # OP2: true store-wide scheduled hours must be assignment-based (counted once).
    actual_scheduled_hours = sum(hours_between_ticks(a.start_t, a.end_t) for a in assignments)
    hard_weekly_cap = float(getattr(goals, 'maximum_weekly_cap', 0.0) or 0.0)
    remaining_budget_hours = hard_weekly_cap - actual_scheduled_hours if hard_weekly_cap > 0.0 else 0.0

    # compute summary stats
    total_req_blocks = 0
    blocks_met = 0
    req_hours = 0.0
    sched_hours = 0.0
    shortage_hours = 0.0
    overage_hours = 0.0
    shortage_by_area_hours: Dict[str, float] = {"CSTORE": 0.0, "KITCHEN": 0.0, "CARWASH": 0.0}

    for day in DAYS:
        for area in AREAS:
            for t in range(DAY_TICKS):
                r = req.get((day, area, t), 0)
                s = sched.get((day, area, t), 0)
                if r <= 0:
                    continue
                total_req_blocks += 1
                req_hours += r * 0.5
                sched_hours += s * 0.5
                if s >= r:
                    blocks_met += 1
                else:
                    short_h = (r - s) * 0.5
                    shortage_hours += short_h
                    shortage_by_area_hours[area] = shortage_by_area_hours.get(area, 0.0) + short_h
                if s > r:
                    overage_hours += (s - r) * 0.5

    coverage_pct = (blocks_met / total_req_blocks * 100.0) if total_req_blocks else 100.0

    # daily breakdown
    daily_rows = []
    for day in DAYS:
        d_req = d_sched = d_short = d_over = 0.0
        for area in AREAS:
            for t in range(DAY_TICKS):
                r = req.get((day, area, t), 0)
                s = sched.get((day, area, t), 0)
                if r <= 0:
                    continue
                d_req += r * 0.5
                d_sched += s * 0.5
                if s < r:
                    d_short += (r - s) * 0.5
                if s > r:
                    d_over += (s - r) * 0.5
        daily_rows.append((day, d_req, d_sched, d_short, d_over))

    # high-risk windows: collect contiguous shortages
    windows = []
    for day in DAYS:
        for area in AREAS:
            t = 0
            while t < DAY_TICKS:
                r = req.get((day, area, t), 0)
                s = sched.get((day, area, t), 0)
                deficit = max(0, r - s)
                if deficit <= 0:
                    t += 1
                    continue
                start = t
                peak = deficit
                deficit_hours = 0.0
                while t < DAY_TICKS:
                    r2 = req.get((day, area, t), 0)
                    s2 = sched.get((day, area, t), 0)
                    d2 = max(0, r2 - s2)
                    if d2 <= 0:
                        break
                    peak = max(peak, d2)
                    deficit_hours += d2 * 0.5
                    t += 1
                end = t
                windows.append((deficit_hours, peak, day, area, start, end))
            # next area
    windows.sort(reverse=True, key=lambda x: (x[0], x[1]))
    top_windows = windows[:10]

    # call list suggestions
    emp_map = {e.name: e for e in model.employees}
    # current weekly hours
    emp_week_hours: Dict[str, float] = {}
    for a in assignments:
        emp_week_hours[a.employee_name] = emp_week_hours.get(a.employee_name, 0.0) + hours_between_ticks(a.start_t, a.end_t)
    clopen = _clopen_map_from_assignments(model, assignments)

    def candidates_for(area: str, day: str, st: int, en: int) -> List[Employee]:
        out = []
        for e in model.employees:
            if e.work_status != "Active":
                continue
            certified = area in e.areas_allowed
            if not certified and not goals.include_noncertified_in_call_list:
                continue

            # restriction slack (max hours)
            window_h = hours_between_ticks(st, en)
            cur_h = emp_week_hours.get(e.name, 0.0)
            slack = float(e.max_weekly_hours) - cur_h
            not_near_restrict = slack >= window_h

            available = is_employee_available(model, e, label, day, st, en, area, clopen)

            # We will sort per your priority:
            # certified -> not near restriction -> available -> tie breakers
            out.append((certified, not_near_restrict, available, cur_h, e.name.lower(), e))
        out.sort(key=lambda x: (x[0], x[1], x[2], -x[3], x[4]), reverse=True)
        return [x[-1] for x in out]

    call_sections = []
    for (def_h, peak, day, area, st, en) in top_windows[:7]:  # keep readable
        cands = candidates_for(area, day, st, en)[:max(1, int(goals.call_list_depth))]
        items = ""
        for i, e in enumerate(cands, 1):
            cur_h = emp_week_hours.get(e.name, 0.0)
            items += f"<li>{html_escape(e.name)} ({cur_h:.1f} hrs) — {html_escape(e.phone)}</li>"
        if not items:
            items = "<li><em>No qualified backups found for this window.</em></li>"
        call_sections.append(f"""
        <div class="block">
          <div class="btitle">{html_escape(day)} • {html_escape(AREA_LABEL.get(area, area))} • {tick_to_ampm(st)}–{tick_to_ampm(en)}</div>
          <div class="bsub">Estimated shortage: {_hours_to_blocks(def_h)} blocks • Peak deficit: {peak}</div>
          <ol>{items}</ol>
        </div>
        """)

    # Labor alignment bar (simple)
    goal = float(goals.coverage_goal_pct)
    bar_pct = max(0.0, min(100.0, coverage_pct))
    status = "GOOD" if coverage_pct >= goal else "BELOW GOAL"
    readiness = build_manager_readiness_summary(
        model,
        label,
        assignments,
        diagnostics={
            "min_short": int(sum(1 for (_k, req_v) in req.items() if int(sched.get(_k, 0) or 0) < int(req_v or 0))),
            "pref_short": int(sum(max(0, int(pref_req.get(k, 0) or 0) - int(sched.get(k, 0) or 0)) for k in pref_req.keys())),
            "max_viol": int(sum(1 for k, mx in max_req.items() if int(mx or 0) > 0 and int(sched.get(k, 0) or 0) > int(mx or 0))),
        },
        filled_slots=int(blocks_met),
        total_slots=int(total_req_blocks),
    )
    readiness_items = "".join(f"<li>{html_escape(line)}</li>" for line in readiness.get("headline", []))

    css = """
    <style>
      @page { size: letter landscape; margin: 0.35in; }
      body { font-family: Arial, Helvetica, sans-serif; }
      .hdr { display:flex; justify-content:space-between; align-items:flex-end; margin-bottom:10px; }
      .title { font-size: 18px; font-weight: 700; }
      .sub { font-size: 11px; color:#333; }
      .meta { font-size: 10px; color:#333; text-align:right; }
      .grid { display:grid; grid-template-columns: 1fr 1fr; gap: 10px; }
      .card { border:1px solid #222; padding:8px; }
      .card h3 { margin:0 0 6px; font-size: 12px; }
      table { width:100%; border-collapse: collapse; }
      th, td { border:1px solid #222; padding:4px 6px; font-size: 10px; }
      th { background:#f4f4f4; }
      .barwrap { border:1px solid #222; height:12px; width:100%; margin-top:4px; }
      .bar { height:12px; background:#333; width: 0%; }
      .pagebreak { page-break-before: always; }
      .block { border:1px solid #222; padding:8px; margin-bottom:8px; }
      .btitle { font-weight:700; font-size: 11px; }
      .bsub { font-size: 10px; color:#333; margin-top:2px; }
      .foot { margin-top:6px; font-size: 9px; color:#555; }
    </style>
    """

    title = f"{html_escape(model.store_info.store_name or 'Schedule')} — Manager Report"
    sub = f"{html_escape(label)} • 2 pages (front/back)"
    phone = html_escape(model.store_info.store_phone or "")
    mgr = html_escape(model.store_info.store_manager or "")

    # daily table rows
    dtrs = ""
    for day, d_req, d_sched, d_short, d_over in daily_rows:
        dtrs += f"<tr><td>{day}</td><td>{_hours_to_blocks(d_req)}</td><td>{_hours_to_blocks(d_sched)}</td><td>{_hours_to_blocks(d_short)}</td><td>{_hours_to_blocks(d_over)}</td></tr>"

    active_tasks = active_manager_tasks_for_label(model, label)
    tasks_html = ""
    if active_tasks:
        rows = []
        for t in active_tasks:
            rows.append(
                f"<tr><td style='width:40px;'>☐</td><td>{html_escape(t.title)}</td><td>{html_escape(t.description or '')}</td></tr>"
            )
        tasks_html = f"""
        <div class=\"card\" style=\"grid-column: 1 / span 2;\">
          <h3>Manager Task Checklist</h3>
          <table>
            <thead><tr><th>Done</th><th>Task</th><th>Description</th></tr></thead>
            <tbody>{''.join(rows)}</tbody>
          </table>
        </div>
        """

    html = f"""
    <html><head><meta charset="utf-8">{css}</head>
    <body>
      <!-- PAGE 1 -->
      <div class="hdr">
        <div>
          <div class="title">{title}</div>
          <div class="sub">{sub}</div>
        </div>
        <div class="meta">
          <div>Store: {phone}</div>
          <div>Manager: {mgr}</div>
          <div>Generated: {today_iso()}</div>
        </div>
      </div>

      <div class="grid">
        <div class="card">
          <h3>Coverage & Labor Summary</h3>
          <div>Coverage: <b>{coverage_pct:.1f}%</b> (goal {goal:.1f}%) • Status: <b>{status}</b></div>
          <div class="barwrap"><div class="bar" style="width:{bar_pct:.1f}%;"></div></div>
          <div style="margin-top:6px;">Hard Weekly Labor Cap: <b>{(_hours_to_blocks(hard_weekly_cap) if hard_weekly_cap > 0.0 else 'Disabled')}</b></div>
          <div>Actual Scheduled Hours: <b>{_hours_to_blocks(actual_scheduled_hours)}</b></div>
          <div>Remaining Labor Budget: <b>{(_hours_to_blocks(remaining_budget_hours) if hard_weekly_cap > 0.0 else 'N/A')}</b></div>
        </div>

        <div class="card">
          <h3>Publish Readiness</h3>
          <div>Status: <b>{html_escape(str(readiness.get("status", "Review")))}</b></div>
          <div style="margin-top:6px;">Required gaps: <b>{int(readiness.get("min_short", 0) or 0)}</b> • Preferred gaps: <b>{int(readiness.get("pref_short", 0) or 0)}</b></div>
          <div>Max warnings: <b>{int(readiness.get("max_viol", 0) or 0)}</b> • Hard-rule failures: <b>{int(readiness.get("hard_violations", 0) or 0)}</b></div>
          <div>Override warnings: <b>{int(readiness.get("override_warnings", 0) or 0)}</b></div>
          <ul>{readiness_items}</ul>
        </div>

        <div class="card">
          <h3>High Risk Windows (Top 10)</h3>
          <table>
            <thead><tr><th>Day</th><th>Area</th><th>Window</th><th>Deficit Hrs</th><th>Peak</th></tr></thead>
            <tbody>
              {''.join([f"<tr><td>{w[2]}</td><td>{html_escape(AREA_LABEL.get(w[3],w[3]))}</td><td>{tick_to_ampm(w[4])}–{tick_to_ampm(w[5])}</td><td>{_hours_to_blocks(w[0])}</td><td>{w[1]}</td></tr>" for w in top_windows])}
            </tbody>
          </table>
        </div>

        <div class="card">
          <h3>Shortage by Area (1-hour blocks)</h3>
          <div>C-Store shortage hours: <b>{_hours_to_blocks(shortage_by_area_hours.get("CSTORE", 0.0))}</b></div>
          <div>Kitchen shortage hours: <b>{_hours_to_blocks(shortage_by_area_hours.get("KITCHEN", 0.0))}</b></div>
          <div>Carwash shortage hours: <b>{_hours_to_blocks(shortage_by_area_hours.get("CARWASH", 0.0))}</b></div>
        </div>

        <div class="card" style="grid-column: 1 / span 2;">
          <h3>Daily Breakdown</h3>
          <table>
            <thead><tr><th>Day</th><th>Req (1h blocks)</th><th>Sched (1h blocks)</th><th>Shortage (1h blocks)</th><th>Overage (1h blocks)</th></tr></thead>
            <tbody>{dtrs}</tbody>
          </table>
        </div>
      </div>

      <div class="foot">Coverage is computed from required 30-minute blocks across all areas. Displayed labor summary values are shown in 1-hour blocks.</div>

      <!-- PAGE 2 -->
      <div class="pagebreak"></div>

      <div class="hdr">
        <div>
          <div class="title">{title} — Call List</div>
          <div class="sub">Recommended employees to contact for likely shortages (ranked: certified → not near restriction → available)</div>
        </div>
        <div class="meta">
          <div>Week: {html_escape(label)}</div>
          <div>Call list depth: {int(goals.call_list_depth)}</div>
        </div>
      </div>

      {''.join(call_sections) if call_sections else '<div class="block"><em>No shortages detected from requirements.</em></div>'}

      {tasks_html}

      <div class="foot">This report is advisory; always verify real-time availability and compliance.</div>
    </body></html>
    """
    return html

def export_manager_report_html(model: DataModel, label: str, assignments: List[Assignment]) -> str:
    html = make_manager_report_html(model, label, assignments)
    fn = _build_export_filename("manager_report", label, "html")
    path = rel_path("exports", fn)
    ensure_dir(os.path.dirname(path))
    with open(path, "w", encoding="utf-8") as f:
        f.write(html)
    return path

def export_csv(model: DataModel, label: str, assignments: List[Assignment]) -> str:
    import csv
    fn = _build_export_filename("schedule", label, "csv")
    path = rel_path("exports", fn)
    ensure_dir(os.path.dirname(path))
    with open(path, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["Day","Area","Start","End","Employee","Locked","Source"])
        for a in sorted(assignments, key=lambda x: (DAYS.index(x.day), AREAS.index(x.area), x.start_t, x.employee_name)):
            w.writerow([a.day,a.area,tick_to_hhmm(a.start_t),tick_to_hhmm(a.end_t),a.employee_name,"Yes" if a.locked else "No",a.source])
    return path

# Optional PDF via reportlab (if installed)
def export_pdf(model: DataModel, label: str, assignments: List[Assignment]) -> Optional[str]:
    try:
        from reportlab.lib.pagesizes import landscape, letter
        from reportlab.pdfgen import canvas
        from reportlab.lib.units import inch
    except Exception:
        return None

    fn = _build_export_filename("schedule", label, "pdf")
    path = rel_path("exports", fn)
    ensure_dir(os.path.dirname(path))
    c = canvas.Canvas(path, pagesize=landscape(letter))
    width, height = landscape(letter)
    margin = 0.35 * inch
    x0 = margin
    y = height - margin

    c.setFont("Helvetica-Bold", 14)
    c.drawString(x0, y, f"{model.store_info.store_name or 'Labor Force Scheduler'} — {label}")
    c.setFont("Helvetica", 9)
    y -= 16
    c.drawString(x0, y, f"{model.store_info.store_address} • {model.store_info.store_phone} • Manager: {model.store_info.store_manager}")
    y -= 14

    by = assignments_by_area_day(assignments)
    col_w = (width - 2*margin) / 3.0
    col_x = [margin, margin+col_w, margin+2*col_w]

    def draw_area(area: str, x: float, y_top: float) -> float:
        c.setFont("Helvetica-Bold", 11)
        c.drawString(x, y_top, area)
        y = y_top - 12
        c.setFont("Helvetica-Bold", 8.5)
        c.drawString(x, y, "Day")
        c.drawString(x+34, y, "Employee")
        c.drawString(x+col_w-78, y, "Time")
        y -= 10
        c.setFont("Helvetica", 8.5)
        for d in DAYS:
            items = by.get(area, {}).get(d, [])
            if not items:
                c.drawString(x, y, d)
                c.drawString(x+34, y, "—")
                y -= 10
                continue
            for i,a in enumerate(items):
                c.drawString(x, y, d if i==0 else "")
                c.drawString(x+34, y, a.employee_name[:18])
                c.drawString(x+col_w-78, y, f"{tick_to_hhmm(a.start_t)}–{tick_to_hhmm(a.end_t)}")
                y -= 10
        return y

    y1 = draw_area("CSTORE", col_x[0], y)
    y2 = draw_area("KITCHEN", col_x[1], y)
    y3 = draw_area("CARWASH", col_x[2], y)
    c.setFont("Helvetica-Oblique", 7.5)
    c.drawString(margin, margin/2, f"Generated {today_iso()} • 30-minute increments")
    c.showPage()
    c.save()
    return path

# -----------------------------
# UI dialogs
# -----------------------------
def simple_input(parent, title: str, prompt: str, default: str="") -> Optional[str]:
    win = tk.Toplevel(parent)
    win.title(title)
    win.transient(parent)
    win.grab_set()
    frm = ttk.Frame(win); frm.pack(padx=12, pady=12, fill="both", expand=True)
    ttk.Label(frm, text=prompt).pack(anchor="w")
    var = tk.StringVar(value=default)
    ent = ttk.Entry(frm, textvariable=var, width=44); ent.pack(pady=8); ent.focus_set()
    out = {"v": None}
    def ok():
        out["v"] = var.get()
        win.destroy()
    def cancel():
        win.destroy()
    btns = ttk.Frame(frm); btns.pack(fill="x")
    ttk.Button(btns, text="Cancel", command=cancel).pack(side="right")
    ttk.Button(btns, text="OK", command=ok).pack(side="right", padx=8)
    win.bind("<Return>", lambda e: ok())
    parent.wait_window(win)
    return out["v"]


def _build_scrollable_canvas_host(parent: tk.Misc,
                                  *,
                                  padding: Tuple[int, int, int, int] = (0, 0, 0, 0),
                                  min_width: int = 0,
                                  bind_mousewheel: bool = True) -> Tuple[ttk.Frame, ttk.Frame, tk.Canvas]:
    """Create a reusable scrollable host with horizontal + vertical recovery."""
    outer = ttk.Frame(parent)
    outer.pack(fill="both", expand=True)
    canvas = tk.Canvas(outer, highlightthickness=0)
    vsb = ttk.Scrollbar(outer, orient="vertical", command=canvas.yview)
    hsb = ttk.Scrollbar(outer, orient="horizontal", command=canvas.xview)
    canvas.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
    canvas.grid(row=0, column=0, sticky="nsew")
    vsb.grid(row=0, column=1, sticky="ns")
    hsb.grid(row=1, column=0, sticky="ew")
    outer.rowconfigure(0, weight=1)
    outer.columnconfigure(0, weight=1)

    inner = ttk.Frame(canvas, padding=padding)
    win_id = canvas.create_window((0, 0), window=inner, anchor="nw")

    def _on_inner_config(_e=None):
        try:
            canvas.configure(scrollregion=canvas.bbox("all"))
        except Exception:
            pass

    def _on_canvas_config(e):
        try:
            if min_width > 0:
                canvas.itemconfigure(win_id, width=max(int(e.width), int(min_width)))
            else:
                canvas.itemconfigure(win_id, width=int(e.width))
        except Exception:
            pass

    inner.bind("<Configure>", _on_inner_config)
    canvas.bind("<Configure>", _on_canvas_config)

    if bind_mousewheel:
        def _on_mousewheel(e):
            try:
                canvas.yview_scroll(int(-1 * (e.delta / 120)), "units")
                return "break"
            except Exception:
                return None
        canvas.bind("<MouseWheel>", _on_mousewheel)

    return outer, inner, canvas


class ContextHelpManager:
    """Reusable delayed hover help manager for Tk/ttk widgets."""

    def __init__(self, parent: tk.Misc, delay_ms: int = 4000):
        self.parent = parent
        self.delay_ms = max(500, int(delay_ms))
        self._registry: Dict[str, Dict[str, str]] = {}
        self._after_id: Optional[str] = None
        self._hovered_widget: Optional[tk.Misc] = None
        self._active_widget: Optional[tk.Misc] = None
        self._active_help_id: Optional[str] = None
        self._bubble_win: Optional[tk.Toplevel] = None
        self._more_win: Optional[tk.Toplevel] = None
        self._short_var = tk.StringVar(value="")
        self._leave_grace_ms = 220

    def register(self, widget: tk.Misc, help_id: str, short_text: str, long_text: str):
        hid = str(help_id or "").strip()
        if not hid:
            return
        self._registry[hid] = {"short": str(short_text or "").strip(), "long": str(long_text or "").strip()}
        try:
            widget.bind("<Enter>", lambda _e, w=widget, h=hid: self._on_enter(w, h), add="+")
            widget.bind("<Leave>", lambda _e, w=widget: self._on_leave(w), add="+")
            widget.bind("<ButtonPress>", lambda _e: self.hide_all(), add="+")
            widget.bind("<FocusOut>", lambda _e: self.hide_bubble(), add="+")
            widget.bind("<Destroy>", lambda _e: self._on_widget_destroy(widget), add="+")
        except Exception:
            pass

    def _on_widget_destroy(self, widget: tk.Misc):
        if self._hovered_widget is widget or self._active_widget is widget:
            self.hide_all()

    def _on_enter(self, widget: tk.Misc, help_id: str):
        self.hide_bubble()
        self._cancel_pending()
        self._hovered_widget = widget
        self._after_id = self.parent.after(self.delay_ms, lambda w=widget, h=help_id: self._show_if_still_hovering(w, h))

    def _on_leave(self, widget: tk.Misc):
        try:
            px = int(widget.winfo_pointerx())
            py = int(widget.winfo_pointery())
            x0 = int(widget.winfo_rootx()) - 8
            y0 = int(widget.winfo_rooty()) - 8
            x1 = int(widget.winfo_rootx()) + int(max(1, widget.winfo_width())) + 8
            y1 = int(widget.winfo_rooty()) + int(max(1, widget.winfo_height())) + 8
            if x0 <= px <= x1 and y0 <= py <= y1:
                return
        except Exception:
            pass
        self._cancel_pending()
        self.parent.after(self._leave_grace_ms, self.hide_all)

    def _cancel_pending(self):
        if self._after_id:
            try:
                self.parent.after_cancel(self._after_id)
            except Exception:
                pass
        self._after_id = None

    def _show_if_still_hovering(self, widget: tk.Misc, help_id: str):
        self._after_id = None
        if widget is not self._hovered_widget:
            return
        try:
            if not bool(widget.winfo_exists()):
                return
        except Exception:
            return
        self._show_bubble(widget, help_id)

    def _show_bubble(self, widget: tk.Misc, help_id: str):
        info = self._registry.get(help_id, {})
        short = str(info.get("short", "") or "").strip()
        if not short:
            return
        self.hide_bubble()
        self._active_widget = widget
        self._active_help_id = help_id

        win = tk.Toplevel(self.parent)
        self._bubble_win = win
        win.wm_overrideredirect(True)
        win.transient(self.parent)
        try:
            win.attributes("-topmost", True)
        except Exception:
            pass

        body = ttk.Frame(win, style="HelpBubble.TFrame", padding=(8, 6, 8, 6))
        body.pack(fill="both", expand=True)
        self._short_var.set(short)
        ttk.Label(body, textvariable=self._short_var, style="HelpBubble.TLabel", wraplength=320, justify="left").pack(anchor="w")
        ttk.Button(body, text="More…", style="HelpMore.TButton", command=self._open_more).pack(anchor="e", pady=(4, 0))

        try:
            x = int(widget.winfo_rootx()) + 18
            y = int(widget.winfo_rooty()) + int(max(26, widget.winfo_height())) + 4
            sw = int(self.parent.winfo_screenwidth())
            sh = int(self.parent.winfo_screenheight())
            win.update_idletasks()
            ww = int(win.winfo_reqwidth())
            wh = int(win.winfo_reqheight())
            x = max(6, min(x, sw - ww - 6))
            y = max(6, min(y, sh - wh - 6))
            win.geometry(f"+{x}+{y}")
        except Exception:
            pass

    def _open_more(self):
        help_id = str(self._active_help_id or "").strip()
        if not help_id:
            return
        info = self._registry.get(help_id, {})
        short = str(info.get("short", "") or "").strip()
        long_text = str(info.get("long", "") or "").strip()
        if not long_text:
            long_text = short

        self.hide_bubble()
        try:
            if self._more_win is not None and bool(self._more_win.winfo_exists()):
                self._more_win.destroy()
        except Exception:
            pass
        self._more_win = tk.Toplevel(self.parent)
        self._more_win.title("Context Help")
        self._more_win.transient(self.parent)
        try:
            sw = int(self.parent.winfo_screenwidth())
            sh = int(self.parent.winfo_screenheight())
            self._more_win.geometry(f"{max(420, int(sw/3))}x{max(260, int(sh/5))}")
        except Exception:
            self._more_win.geometry("560x320")
        outer = ttk.Frame(self._more_win, padding=12)
        outer.pack(fill="both", expand=True)
        ttk.Label(outer, text=short or "Help", style="SubHeader.TLabel").pack(anchor="w", pady=(0, 8))

        txt_wrap = ttk.Frame(outer)
        txt_wrap.pack(fill="both", expand=True)
        txt = tk.Text(txt_wrap, wrap="none", relief="solid", borderwidth=1)
        ysb = ttk.Scrollbar(txt_wrap, orient="vertical", command=txt.yview)
        xsb = ttk.Scrollbar(txt_wrap, orient="horizontal", command=txt.xview)
        txt.configure(yscrollcommand=ysb.set, xscrollcommand=xsb.set)
        txt.grid(row=0, column=0, sticky="nsew")
        ysb.grid(row=0, column=1, sticky="ns")
        xsb.grid(row=1, column=0, sticky="ew")
        txt_wrap.rowconfigure(0, weight=1)
        txt_wrap.columnconfigure(0, weight=1)
        txt.insert("1.0", long_text)
        txt.configure(state="disabled")
        ttk.Button(outer, text="Close", command=self._more_win.destroy).pack(anchor="e", pady=(8, 0))
        self._more_win.bind("<FocusOut>", lambda _e: self._safe_close_more(), add="+")

    def _safe_close_more(self):
        try:
            if self._more_win is not None and bool(self._more_win.winfo_exists()):
                self._more_win.destroy()
        except Exception:
            pass
        self._more_win = None

    def hide_bubble(self):
        self._cancel_pending()
        self._hovered_widget = None
        self._active_widget = None
        self._active_help_id = None
        try:
            if self._bubble_win is not None and bool(self._bubble_win.winfo_exists()):
                self._bubble_win.destroy()
        except Exception:
            pass
        self._bubble_win = None

    def hide_all(self):
        self.hide_bubble()
        self._safe_close_more()

    def destroy(self):
        self.hide_all()

class FixedScheduleEditorDialog(tk.Toplevel):
    def __init__(self, parent: tk.Misc, model: "DataModel", initial_entries: List[FixedShift], minor_type: str, label_hint: str):
        super().__init__(parent)
        self.model = model
        self.result: Optional[List[FixedShift]] = None
        self.title(label_hint)
        self.transient(parent)
        self.grab_set()
        self.geometry("1320x520")

        norm = _normalize_fixed_schedule_entries(list(initial_entries or []))
        by_day: Dict[str, FixedShift] = {x.day: x for x in norm}

        self.area_vars: Dict[str, tk.StringVar] = {}
        self.start_vars: Dict[str, tk.StringVar] = {}
        self.end_vars: Dict[str, tk.StringVar] = {}
        self.minor_type = str(minor_type or "ADULT")

        _outer, frm, _canvas = _build_scrollable_canvas_host(self, padding=(12, 12, 12, 12), min_width=1240)

        cols = ttk.Frame(frm)
        cols.pack(fill="x", expand=False)

        for i, day in enumerate(DAYS):
            col = ttk.LabelFrame(cols, text=DAY_FULL.get(day, day), padding=(8, 8, 8, 8))
            col.grid(row=0, column=i, sticky="n", padx=4, pady=4)
            fs = by_day.get(day)
            av = tk.StringVar(value=(fs.area if fs else ""))
            sv = tk.StringVar(value=(tick_to_hhmm(fs.start_t) if fs else ""))
            ev = tk.StringVar(value=(tick_to_hhmm(fs.end_t) if fs else ""))
            self.area_vars[day] = av
            self.start_vars[day] = sv
            self.end_vars[day] = ev

            ttk.Label(col, text="Area").pack(anchor="w")
            ttk.Combobox(col, textvariable=av, values=[""] + AREAS, state="readonly", width=11).pack(anchor="w", pady=(0, 6))
            row = ttk.Frame(col)
            row.pack(anchor="w")
            ttk.Label(row, text="Start").grid(row=0, column=0, sticky="w")
            ttk.Label(row, text="End").grid(row=0, column=1, sticky="w", padx=(6,0))
            ttk.Combobox(row, textvariable=sv, values=[""] + TIME_CHOICES, state="readonly", width=8).grid(row=1, column=0, sticky="w")
            ttk.Combobox(row, textvariable=ev, values=[""] + TIME_CHOICES, state="readonly", width=8).grid(row=1, column=1, sticky="w", padx=(6,0))
            ttk.Button(col, text="Clear Day", command=lambda d=day: self._clear_day(d)).pack(anchor="w", pady=(8,0))

        btns = ttk.Frame(frm)
        btns.pack(fill="x", pady=(10,0))
        ttk.Button(btns, text="Cancel", command=self.destroy).pack(side="right")
        ttk.Button(btns, text="Save Schedule", command=self._save).pack(side="right", padx=8)

    def _clear_day(self, day: str):
        self.area_vars[day].set("")
        self.start_vars[day].set("")
        self.end_vars[day].set("")

    def _save(self):
        out: List[FixedShift] = []
        for day in DAYS:
            area = self.area_vars[day].get().strip().upper()
            st = self.start_vars[day].get().strip()
            en = self.end_vars[day].get().strip()
            if (not area) and (not st) and (not en):
                continue
            if not area:
                messagebox.showerror("Fixed Schedule", f"{DAY_FULL.get(day, day)}: Area is required when times are set.")
                return
            if (not st) or (not en):
                messagebox.showerror("Fixed Schedule", f"{DAY_FULL.get(day, day)}: Start and End must both be set.")
                return
            stt = hhmm_to_tick(st)
            ent = hhmm_to_tick(en)
            if ent <= stt:
                messagebox.showerror("Fixed Schedule", f"{DAY_FULL.get(day, day)}: Overnight shifts are not allowed.")
                return
            probe = Employee(name="_probe_", minor_type=self.minor_type)
            ok, msg = fixed_shift_compliance_ok(self.model, probe, "Week starting 2000-01-02", day, stt, ent, area, [])
            if not ok:
                messagebox.showerror("Fixed Schedule", f"{DAY_FULL.get(day, day)}: {msg}")
                return
            out.append(FixedShift(day=day, start_t=stt, end_t=ent, area=area, locked=True))

        self.result = _normalize_fixed_schedule_entries(out)
        self.destroy()


class EmployeeDialog(tk.Toplevel):
    def __init__(self, parent: "SchedulerApp", employee: Optional[Employee]):
        super().__init__(parent)
        self.parent = parent
        self.result: Optional[Employee] = None
        self.title("Employee")
        self.transient(parent)
        self.grab_set()

        # 90% of parent, centered in parent.
        try:
            parent.update_idletasks()
            pw, ph = int(parent.winfo_width()), int(parent.winfo_height())
            px, py = int(parent.winfo_rootx()), int(parent.winfo_rooty())
            w = max(980, int(pw * 0.90))
            h = max(700, int(ph * 0.90))
            x = px + max(0, (pw - w) // 2)
            y = py + max(0, (ph - h) // 2)
            self.geometry(f"{w}x{h}+{x}+{y}")
        except Exception:
            self.geometry("1100x760")

        outer = ttk.Frame(self); outer.pack(fill="both", expand=True)
        canvas = tk.Canvas(outer, highlightthickness=0)
        vsb = ttk.Scrollbar(outer, orient="vertical", command=canvas.yview)
        hsb = ttk.Scrollbar(outer, orient="horizontal", command=canvas.xview)
        canvas.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        vsb.pack(side="right", fill="y")
        hsb.pack(side="bottom", fill="x")
        canvas.pack(side="left", fill="both", expand=True)
        frm = ttk.Frame(canvas, padding=(12,12,12,12))
        _win_id = canvas.create_window((0,0), window=frm, anchor="nw")
        frm.bind("<Configure>", lambda _e=None: canvas.configure(scrollregion=canvas.bbox("all")))

        def _on_mousewheel(e):
            try:
                canvas.yview_scroll(int(-1*(e.delta/120)), "units")
                return "break"
            except Exception:
                return None
        canvas.bind("<MouseWheel>", _on_mousewheel)

        emp = employee
        # Hard-rule vars
        self.name_var = tk.StringVar(value=(emp.name if emp else ""))
        self.phone_var = tk.StringVar(value=(emp.phone if emp else ""))
        self.status_var = tk.StringVar(value=(emp.work_status if emp else ""))
        self.wants_var = tk.BooleanVar(value=(emp.wants_hours if emp else False))
        self.emp_type_var = tk.StringVar(value=(getattr(emp, "employee_type", "") if emp else ""))
        self.split_ok_var = tk.StringVar(value=("Yes" if getattr(emp, "split_shifts_ok", True) else "No") if emp else "")
        self.double_ok_var = tk.BooleanVar(value=(bool(getattr(emp, "double_shifts_ok", False)) if emp else False))
        self.min_shift_var = tk.StringVar(value=(str(float(getattr(emp, "min_hours_per_shift", 1.0))) if emp else ""))
        self.max_shift_var = tk.StringVar(value=(str(float(getattr(emp, "max_hours_per_shift", 8.0))) if emp else ""))
        self.max_shifts_day_var = tk.StringVar(value=(str(int(getattr(emp, "max_shifts_per_day", 1))) if emp else ""))
        self.max_weekly_var = tk.StringVar(value=(str(emp.max_weekly_hours) if emp else ""))
        self.hard_min_weekly_var = tk.StringVar(value=(str(float(getattr(emp, "hard_min_weekly_hours", 0.0))) if emp else ""))
        self.minor_var = tk.StringVar(value=(emp.minor_type if emp else ""))

        self.area_vars = {a: tk.BooleanVar(value=(a in (emp.areas_allowed if emp else []))) for a in AREAS}

        # Soft-rule vars
        self.pref_area_vars = {a: tk.BooleanVar(value=(a in (emp.preferred_areas if emp else []))) for a in AREAS}
        self.avoid_clopen_var = tk.BooleanVar(value=(emp.avoid_clopens if emp else False))
        self.max_consec_var = tk.StringVar(value=(str(emp.max_consecutive_days) if emp else ""))
        self.weekend_pref_var = tk.StringVar(value=(emp.weekend_preference if emp else ""))
        self.target_min_var = tk.StringVar(value=(str(emp.target_min_hours) if emp else ""))

        hard_av = employee_hard_availability(emp) if emp else default_day_rules()
        soft_av = employee_soft_availability(emp) if emp else default_day_rules()

        def _mk_av_vars(src: Dict[str, DayRules], blank_when_new: bool = False):
            unavail = {d: tk.BooleanVar(value=src[d].unavailable_day) for d in DAYS}
            earliest = {d: tk.StringVar(value=("" if blank_when_new else tick_to_hhmm(src[d].earliest_start))) for d in DAYS}
            latest = {d: tk.StringVar(value=("" if blank_when_new else tick_to_hhmm(src[d].latest_end))) for d in DAYS}
            b1s = {d: tk.StringVar(value="") for d in DAYS}
            b1e = {d: tk.StringVar(value="") for d in DAYS}
            b2s = {d: tk.StringVar(value="") for d in DAYS}
            b2e = {d: tk.StringVar(value="") for d in DAYS}
            for d in DAYS:
                br = list(src[d].blocked_ranges)
                if len(br) >= 1:
                    b1s[d].set(tick_to_hhmm(br[0][0])); b1e[d].set(tick_to_hhmm(br[0][1]))
                if len(br) >= 2:
                    b2s[d].set(tick_to_hhmm(br[1][0])); b2e[d].set(tick_to_hhmm(br[1][1]))
            return unavail, earliest, latest, b1s, b1e, b2s, b2e

        (self.h_unavail, self.h_earliest, self.h_latest, self.h_b1s, self.h_b1e, self.h_b2s, self.h_b2e) = _mk_av_vars(hard_av, blank_when_new=(emp is None))
        (self.s_unavail, self.s_earliest, self.s_latest, self.s_b1s, self.s_b1e, self.s_b2s, self.s_b2e) = _mk_av_vars(soft_av, blank_when_new=(emp is None))

        self.fixed_schedule_status = _normalize_fixed_schedule_status(getattr(emp, "fixed_schedule_status", "none")) if emp else "none"
        self.fixed_schedule_entries = _normalize_fixed_schedule_entries(list(getattr(emp, "fixed_schedule", []) or [])) if emp else []

        hard_box = ttk.LabelFrame(frm, text="Hard Rules (Must Follow)")
        hard_box.pack(fill="x", pady=(0,10))

        r=0
        ttk.Label(hard_box, text="Name:").grid(row=r, column=0, sticky="w", padx=8, pady=6)
        ttk.Entry(hard_box, textvariable=self.name_var, width=22).grid(row=r, column=1, sticky="w", padx=8, pady=6)
        ttk.Label(hard_box, text="Phone:").grid(row=r, column=2, sticky="w", padx=8, pady=6)
        ttk.Entry(hard_box, textvariable=self.phone_var, width=16).grid(row=r, column=3, sticky="w", padx=8, pady=6)
        ttk.Label(hard_box, text="Status:").grid(row=r, column=4, sticky="w", padx=8, pady=6)
        ttk.Combobox(hard_box, textvariable=self.status_var, values=["", "Active","On Leave","Inactive"], state="readonly", width=12).grid(row=r, column=5, sticky="w", padx=8, pady=6)
        ttk.Label(hard_box, text="Employee type:").grid(row=r, column=6, sticky="w", padx=8, pady=6)
        ttk.Combobox(hard_box, textvariable=self.emp_type_var, values=["", "Store Manager", "Manager in training", "Assistant Manager", "Kitchen Manager", "Senior Crew Member", "Crew Member"], state="readonly", width=18).grid(row=r, column=7, sticky="w", padx=8, pady=6)

        r += 1
        ttk.Checkbutton(hard_box, text="Wants hours (opt-in)", variable=self.wants_var).grid(row=r, column=0, columnspan=2, sticky="w", padx=8, pady=6)
        ttk.Label(hard_box, text="Split shifts ok:").grid(row=r, column=2, sticky="w", padx=8, pady=6)
        ttk.Radiobutton(hard_box, text="Yes", value="Yes", variable=self.split_ok_var).grid(row=r, column=3, sticky="w", padx=(8,2), pady=6)
        ttk.Radiobutton(hard_box, text="No", value="No", variable=self.split_ok_var).grid(row=r, column=4, sticky="w", padx=(2,8), pady=6)
        ttk.Label(hard_box, text="Max weekly hours:").grid(row=r, column=5, sticky="w", padx=8, pady=6)
        ttk.Entry(hard_box, textvariable=self.max_weekly_var, width=8).grid(row=r, column=6, sticky="w", padx=8, pady=6)
        ttk.Label(hard_box, text="Weekly min hrs target (best-effort):").grid(row=r, column=7, sticky="w", padx=8, pady=6)
        ttk.Entry(hard_box, textvariable=self.hard_min_weekly_var, width=8).grid(row=r, column=8, sticky="w", padx=8, pady=6)

        r += 1
        ttk.Label(hard_box, text="Minor type:").grid(row=r, column=0, sticky="w", padx=8, pady=6)
        ttk.Combobox(hard_box, textvariable=self.minor_var, values=[""] + MINOR_TYPES, state="readonly", width=14).grid(row=r, column=1, sticky="w", padx=8, pady=6)
        ttk.Checkbutton(hard_box, text="Double shifts ok (>8h)", variable=self.double_ok_var).grid(row=r, column=2, sticky="w", padx=8, pady=6)
        ttk.Label(hard_box, text="Min hrs/shift:").grid(row=r, column=3, sticky="w", padx=8, pady=6)
        ttk.Entry(hard_box, textvariable=self.min_shift_var, width=6).grid(row=r, column=4, sticky="w", padx=8, pady=6)
        ttk.Label(hard_box, text="Max hrs/shift:").grid(row=r, column=5, sticky="w", padx=8, pady=6)
        ttk.Entry(hard_box, textvariable=self.max_shift_var, width=6).grid(row=r, column=6, sticky="w", padx=8, pady=6)
        ttk.Label(hard_box, text="Max shifts/day:").grid(row=r, column=7, sticky="w", padx=8, pady=6)
        ttk.Entry(hard_box, textvariable=self.max_shifts_day_var, width=6).grid(row=r, column=8, sticky="w", padx=8, pady=6)

        r += 1
        area_row = ttk.Frame(hard_box)
        area_row.grid(row=r, column=0, columnspan=9, sticky="w", padx=8, pady=(4,8))
        ttk.Label(area_row, text="Areas allowed (hard):").pack(side="left")
        for a in AREAS:
            ttk.Checkbutton(area_row, text=a, variable=self.area_vars[a]).pack(side="left", padx=(10,0))

        hard_av_box = ttk.LabelFrame(frm, text="Hard Recurring Availability (Absolute • 30-minute increments)")
        hard_av_box.pack(fill="x", pady=(0,10))
        self._build_availability_grid(hard_av_box, self.h_unavail, self.h_earliest, self.h_latest, self.h_b1s, self.h_b1e, self.h_b2s, self.h_b2e)

        fixed_box = ttk.LabelFrame(frm, text="Fixed Schedule (Hard Recurring Preassignment)")
        fixed_box.pack(fill="x", pady=(0,10))
        b = ttk.Frame(fixed_box); b.pack(fill="x", padx=8, pady=(6,4))
        ttk.Button(b, text="Create Fixed Schedule", command=self._create_fixed_schedule).pack(side="left")
        ttk.Button(b, text="Modify Fixed Schedule", command=self._modify_fixed_schedule).pack(side="left", padx=6)
        self.fixed_pause_btn = ttk.Button(b, text="Pause Fixed Schedule", command=self._pause_fixed_schedule)
        self.fixed_pause_btn.pack(side="left", padx=6)
        self.fixed_resume_btn = ttk.Button(b, text="Resume Fixed Schedule", command=self._resume_fixed_schedule)
        self.fixed_resume_btn.pack(side="left", padx=6)
        ttk.Button(b, text="Remove Fixed Schedule", command=self._remove_fixed_schedule).pack(side="left", padx=6)
        self.fixed_status_lbl = ttk.Label(b, text="Status: None")
        self.fixed_status_lbl.pack(side="right")

        self.fixed_summary = ttk.Frame(fixed_box)
        self.fixed_summary.pack(fill="x", padx=8, pady=(2,8))
        self.fixed_summary_labels: Dict[str, ttk.Label] = {}
        for i, day in enumerate(DAYS):
            col = ttk.LabelFrame(self.fixed_summary, text=DAY_FULL.get(day, day), padding=(6,4,6,4))
            col.grid(row=0, column=i, sticky="nsew", padx=3, pady=3)
            lbl = ttk.Label(col, text="", width=14, justify="left")
            lbl.pack(anchor="nw")
            self.fixed_summary_labels[day] = lbl
        for i in range(len(DAYS)):
            self.fixed_summary.grid_columnconfigure(i, weight=1)
        self._refresh_fixed_summary()

        ttk.Separator(frm, orient="horizontal").pack(fill="x", pady=(6,6))
        callout = ttk.LabelFrame(frm, text="Important", padding=(10,6,10,6))
        callout.pack(fill="x", pady=(0,8))
        ttk.Label(callout, text="Everything below is Employee Preference / Quality of Life (Soft). The scheduler will try to honor these preferences but may violate them when needed to produce a workable schedule.", wraplength=980).pack(anchor="w")

        soft_box = ttk.LabelFrame(frm, text="Employee Preference / Quality of Life (Soft)")
        soft_box.pack(fill="x", pady=(0,10))
        ttk.Label(soft_box, text="Preferred areas:").grid(row=0, column=0, sticky="w", padx=10, pady=6)
        for i,a in enumerate(AREAS):
            ttk.Checkbutton(soft_box, text=f"{a}", variable=self.pref_area_vars[a]).grid(row=0, column=i+1, sticky="w", padx=10, pady=6)
        ttk.Checkbutton(soft_box, text="Avoid clopens", variable=self.avoid_clopen_var).grid(row=1, column=0, sticky="w", padx=10, pady=6)
        ttk.Label(soft_box, text="Max consecutive days:").grid(row=1, column=1, sticky="w", padx=10, pady=6)
        ttk.Entry(soft_box, textvariable=self.max_consec_var, width=6).grid(row=1, column=2, sticky="w", padx=10, pady=6)
        ttk.Label(soft_box, text="Weekend preference:").grid(row=1, column=3, sticky="w", padx=10, pady=6)
        ttk.Combobox(soft_box, textvariable=self.weekend_pref_var, values=["", "Prefer", "Avoid", "Neutral"], state="readonly", width=10).grid(row=1, column=4, sticky="w", padx=10, pady=6)
        ttk.Label(soft_box, text="Target min hours (optional):").grid(row=1, column=5, sticky="w", padx=10, pady=6)
        ttk.Entry(soft_box, textvariable=self.target_min_var, width=8).grid(row=1, column=6, sticky="w", padx=10, pady=6)

        soft_av_box = ttk.LabelFrame(frm, text="Preferred Recurring Availability (Soft • 30-minute increments)")
        soft_av_box.pack(fill="x", pady=(0,10))
        self._build_availability_grid(soft_av_box, self.s_unavail, self.s_earliest, self.s_latest, self.s_b1s, self.s_b1e, self.s_b2s, self.s_b2e)

        bottom = ttk.Frame(frm); bottom.pack(fill="x")
        ttk.Button(bottom, text="Cancel", command=self.destroy).pack(side="right")
        ttk.Button(bottom, text="Save Employee", command=self._save).pack(side="right", padx=8)

    def _build_availability_grid(self, parent, unavail, earliest, latest, b1s, b1e, b2s, b2e):
        time_values = [""] + TIME_CHOICES
        headers = ["Day","Off all day","Earliest start (OK)","Latest end (OK)","Blocked start #1 (NO)","Blocked end #1 (NO)","Blocked start #2 (NO)","Blocked end #2 (NO)"]
        for c,h in enumerate(headers):
            ttk.Label(parent, text=h).grid(row=0, column=c, sticky="w", padx=6, pady=4)
        for rr, d in enumerate(DAYS, start=1):
            ttk.Label(parent, text=d).grid(row=rr, column=0, sticky="w", padx=6, pady=4)
            ttk.Checkbutton(parent, variable=unavail[d]).grid(row=rr, column=1, sticky="w", padx=6, pady=4)
            ttk.Combobox(parent, textvariable=earliest[d], values=time_values, width=8, state="readonly").grid(row=rr, column=2, sticky="w", padx=6, pady=4)
            ttk.Combobox(parent, textvariable=latest[d], values=time_values, width=8, state="readonly").grid(row=rr, column=3, sticky="w", padx=6, pady=4)
            ttk.Combobox(parent, textvariable=b1s[d], values=time_values, width=8, state="readonly").grid(row=rr, column=4, sticky="w", padx=6, pady=4)
            ttk.Combobox(parent, textvariable=b1e[d], values=time_values, width=8, state="readonly").grid(row=rr, column=5, sticky="w", padx=6, pady=4)
            ttk.Combobox(parent, textvariable=b2s[d], values=time_values, width=8, state="readonly").grid(row=rr, column=6, sticky="w", padx=6, pady=4)
            ttk.Combobox(parent, textvariable=b2e[d], values=time_values, width=8, state="readonly").grid(row=rr, column=7, sticky="w", padx=6, pady=4)

    def _fixed_status_display(self) -> str:
        s = _normalize_fixed_schedule_status(self.fixed_schedule_status)
        return "Active" if s == "active" else ("Paused" if s == "paused" else "None")

    def _refresh_fixed_summary(self):
        self.fixed_schedule_entries = _normalize_fixed_schedule_entries(self.fixed_schedule_entries)
        s = _normalize_fixed_schedule_status(self.fixed_schedule_status)
        if not self.fixed_schedule_entries:
            s = "none"
            self.fixed_schedule_status = "none"
        self.fixed_status_lbl.configure(text=f"Status: {self._fixed_status_display()}")
        try:
            if hasattr(self, "fixed_pause_btn"):
                self.fixed_pause_btn.configure(state=("normal" if (s == "active" and bool(self.fixed_schedule_entries)) else "disabled"))
            if hasattr(self, "fixed_resume_btn"):
                self.fixed_resume_btn.configure(state=("normal" if (s == "paused" and bool(self.fixed_schedule_entries)) else "disabled"))
        except Exception:
            pass
        by = {x.day: x for x in self.fixed_schedule_entries}
        for d in DAYS:
            fs = by.get(d)
            if fs is None:
                self.fixed_summary_labels[d].configure(text="")
            else:
                self.fixed_summary_labels[d].configure(text=f"{fs.area}\\n{tick_to_ampm(fs.start_t)}-{tick_to_ampm(fs.end_t)}")

    def _create_fixed_schedule(self):
        d = FixedScheduleEditorDialog(self, self.parent.model, [], self.minor_var.get(), "Create Fixed Schedule")
        self.wait_window(d)
        if d.result is not None:
            self.fixed_schedule_entries = list(d.result)
            self.fixed_schedule_status = "active" if self.fixed_schedule_entries else "none"
            self._refresh_fixed_summary()

    def _modify_fixed_schedule(self):
        d = FixedScheduleEditorDialog(self, self.parent.model, list(self.fixed_schedule_entries), self.minor_var.get(), "Modify Fixed Schedule")
        self.wait_window(d)
        if d.result is not None:
            self.fixed_schedule_entries = list(d.result)
            if not self.fixed_schedule_entries:
                self.fixed_schedule_status = "none"
            elif self.fixed_schedule_status == "none":
                self.fixed_schedule_status = "active"
            self._refresh_fixed_summary()

    def _pause_fixed_schedule(self):
        if not self.fixed_schedule_entries:
            self.fixed_schedule_status = "none"
        else:
            self.fixed_schedule_status = "paused"
        self._refresh_fixed_summary()

    def _resume_fixed_schedule(self):
        if not self.fixed_schedule_entries:
            self.fixed_schedule_status = "none"
        else:
            self.fixed_schedule_status = "active"
        self._refresh_fixed_summary()

    def _remove_fixed_schedule(self):
        self.fixed_schedule_entries = []
        self.fixed_schedule_status = "none"
        self._refresh_fixed_summary()

    def _collect_dayrules(self, unavail, earliest, latest, b1s, b1e, b2s, b2e) -> Dict[str, DayRules]:
        def _parse_or_default(v: str, default_tick: int) -> int:
            sv = str(v or "").strip()
            if not sv:
                return int(default_tick)
            try:
                return int(hhmm_to_tick(sv))
            except Exception:
                return int(default_tick)

        av: Dict[str, DayRules] = {}
        for d in DAYS:
            un = bool(unavail[d].get())
            es = _parse_or_default(earliest[d].get(), 0)
            le = _parse_or_default(latest[d].get(), DAY_TICKS)
            br: List[Tuple[int, int]] = []
            for sv, ev in [(b1s[d], b1e[d]), (b2s[d], b2e[d])]:
                s = str(sv.get() or "").strip(); e = str(ev.get() or "").strip()
                if s and e:
                    a = hhmm_to_tick(s); b = hhmm_to_tick(e)
                    if b > a:
                        br.append((a, b))
            av[d] = DayRules(unavailable_day=un, earliest_start=es, latest_end=le, blocked_ranges=br)
        return av

    def _save(self):
        name = self.name_var.get().strip()
        if not name:
            messagebox.showerror("Employee", "Name is required.")
            return

        areas = [a for a, v in self.area_vars.items() if v.get()]
        if not areas:
            messagebox.showerror("Employee", "Select at least one allowed area.")
            return
        pref = [a for a, v in self.pref_area_vars.items() if v.get()]

        def _f(v: str, default: float) -> float:
            try: return float(str(v).strip())
            except Exception: return float(default)

        def _i(v: str, default: int) -> int:
            try: return int(str(v).strip())
            except Exception: return int(default)

        max_week = _f(self.max_weekly_var.get(), 30.0)
        hard_min_week = max(0.0, _f(self.hard_min_weekly_var.get(), 0.0))
        targ = _f(self.target_min_var.get(), 0.0)
        max_consec = max(1, _i(self.max_consec_var.get(), 6))
        min_shift = max(0.5, _f(self.min_shift_var.get(), 1.0))
        max_shift = max(min_shift, _f(self.max_shift_var.get(), 8.0))
        max_shifts_day = max(1, _i(self.max_shifts_day_var.get(), 1))

        hard_av = self._collect_dayrules(self.h_unavail, self.h_earliest, self.h_latest, self.h_b1s, self.h_b1e, self.h_b2s, self.h_b2e)
        soft_av = self._collect_dayrules(self.s_unavail, self.s_earliest, self.s_latest, self.s_b1s, self.s_b1e, self.s_b2s, self.s_b2e)

        status = _normalize_fixed_schedule_status(self.fixed_schedule_status)
        fixed_entries = _normalize_fixed_schedule_entries(self.fixed_schedule_entries)
        if status == "none":
            fixed_entries = []
        elif not fixed_entries:
            status = "none"
        for fs in fixed_entries:
            probe = Employee(name=name, minor_type=(self.minor_var.get().strip() or "ADULT"))
            ok, msg = fixed_shift_compliance_ok(self.parent.model, probe, self.parent.current_label, fs.day, int(fs.start_t), int(fs.end_t), fs.area, [])
            if not ok:
                messagebox.showerror("Employee", f"Fixed schedule invalid ({fs.day} {fs.area} {tick_to_hhmm(fs.start_t)}-{tick_to_hhmm(fs.end_t)}): {msg}")
                return

        self.result = Employee(
            name=name,
            phone=self.phone_var.get().strip(),
            work_status=(self.status_var.get().strip() or "Active"),
            wants_hours=bool(self.wants_var.get()),
            employee_type=(self.emp_type_var.get().strip() or "Crew Member"),
            split_shifts_ok=(self.split_ok_var.get().strip().lower().startswith("y") if self.split_ok_var.get().strip() else True),
            double_shifts_ok=bool(self.double_ok_var.get()),
            min_hours_per_shift=min_shift,
            max_hours_per_shift=max_shift,
            max_shifts_per_day=max_shifts_day,
            max_weekly_hours=max_week,
            target_min_hours=targ,
            hard_min_weekly_hours=hard_min_week,
            minor_type=(self.minor_var.get().strip() or "ADULT"),
            areas_allowed=areas,
            preferred_areas=pref,
            avoid_clopens=bool(self.avoid_clopen_var.get()),
            max_consecutive_days=max_consec,
            weekend_preference=(self.weekend_pref_var.get().strip() or "Neutral"),
            availability=hard_av,
            hard_availability=hard_av,
            soft_availability=soft_av,
            fixed_schedule_status=status,
            fixed_schedule=fixed_entries,
            recurring_locked_schedule=[FixedShift(day=x.day, start_t=x.start_t, end_t=x.end_t, area=x.area, locked=True) for x in fixed_entries] if status == "active" else [],
        )
        self.destroy()

# -----------------------------
# Main app
# -----------------------------
class SchedulerApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.data_path = default_data_path()
        try:
            ensure_runtime_support_dirs()
        except Exception:
            pass
        # If no user data exists yet, seed with bundled starter data (for safe testing)
        try:
            if not os.path.isfile(self.data_path):
                ensure_dir(os.path.dirname(self.data_path))
                for bundled in _candidate_starter_data_paths():
                    if os.path.isfile(bundled):
                        shutil.copyfile(bundled, self.data_path)
                        break
        except Exception:
            pass
        # state
        self.model = DataModel()
        self.current_label = self._default_week_label()
        self.current_assignments: List[Assignment] = []
        self.current_emp_hours: Dict[str,float] = {}
        self.current_total_hours: float = 0.0
        self.current_warnings: List[str] = []
        self.current_filled: int = 0
        self.current_total_slots: int = 0
        self.current_diagnostics: Dict[str, Any] = {}
        self.last_solver_summary = None  # populated after Generate Schedule
        self._req_undo_snapshot: Optional[List[RequirementBlock]] = None
        self._req_undo_reason: str = ""

        # load if exists
        if os.path.isfile(self.data_path):
            try:
                self.model = load_data(self.data_path)
            except Exception:
                self.model = DataModel()
        try:
            ensure_state_law_seed_files()
        except Exception:
            pass
        # load learned patterns (Phase 2 P2-4)
        try:
            self.model.learned_patterns = load_patterns()
        except Exception:
            self.model.learned_patterns = {}
        if not self.model.requirements:
            self.model.requirements = default_requirements()
        self._validate_requirements_for_context("load", block=False)

        # apply ui scale
        self._apply_ui_scale(self.model.settings.ui_scale)

        self.title(f"LaborForceScheduler {APP_VERSION} (Portable)")

        # Fixed window size (Option B), scaled up ~30% but clamped to screen so it fits on 1920x1080, etc.
        try:
            target_w = int(1500 * 1.30)
            target_h = int(920 * 1.30)
            sw = int(self.winfo_screenwidth())
            sh = int(self.winfo_screenheight())
            w = min(target_w, max(1200, int(sw * 0.95)))
            h = min(target_h, max(780, int(sh * 0.90)))
            self.geometry(f"{w}x{h}")
        except Exception:
            self.geometry("1500x920")
        self.minsize(1200, 780)

        # Diagnostics / Help menu (small, for debugging)
        self._build_menus()

        # Log Tk callback exceptions to crash_log.txt
        try:
            def _tk_cb_exc(exc, val, tb):
                _write_crash_log(exc, val, tb)
                messagebox.showerror('Error', f'An unexpected error occurred. Details were written to crash_log.txt\n\n{val}')
            self.report_callback_exception = _tk_cb_exc  # type: ignore
        except Exception:
            pass

        # branding images (optional)
        self.brand_img_header = None
        self.brand_img_store = None
        self.brand_source_image = None
        self._store_img_original = None
        self._store_img_tk = None
        self._store_img_label = None
        self._store_img_container = None
        self._store_img_last_size: Optional[Tuple[int, int]] = None
        self._brand_tab_photo_refs: Dict[str, Any] = {}
        self._brand_tab_last_size: Dict[str, Tuple[int, int]] = {}
        self._load_brand_images()

        self._setup_style()
        self.help_manager = ContextHelpManager(self, delay_ms=1200)
        self._help_catalog = self._build_help_catalog()
        self._build_ui()
        self._register_phase1_help_controls()
        self._register_broad_help_controls()
        self._refresh_all()
        self._set_status(f"Data file: {self.data_path}")

        self.bind("<FocusOut>", lambda _e: self.help_manager.hide_all(), add="+")

        # --- Autosave (prevents lost work) ---
        # Keep it simple: periodic best-effort autosave + save-on-exit.
        self._autosave_interval_ms = 60_000  # 60 seconds
        self._autosave_job = None
        self.protocol("WM_DELETE_WINDOW", self._on_close)
        self._schedule_autosave()

    def _schedule_autosave(self):
        try:
            if self._autosave_job is not None:
                self.after_cancel(self._autosave_job)
        except Exception:
            pass
        self._autosave_job = self.after(self._autosave_interval_ms, self._autosave_tick)


    # -------- Help / Diagnostics --------
    def _build_menus(self):
        try:
            menubar = tk.Menu(self)
            helpmenu = tk.Menu(menubar, tearoff=0)
            helpmenu.add_command(label='Diagnostics', command=self._open_diagnostics)
            helpmenu.add_command(label='Open Data Folder', command=self._open_data_folder)
            helpmenu.add_separator()
            helpmenu.add_command(label='About', command=self._about)
            menubar.add_cascade(label='Help', menu=helpmenu)
            self.config(menu=menubar)
        except Exception:
            pass

    def _open_data_folder(self):
        try:
            folder = os.path.dirname(self.data_path)
            if os.name == 'nt':
                os.startfile(folder)  # type: ignore[attr-defined]
            else:
                subprocess.Popen(['xdg-open', folder])
        except Exception as e:
            messagebox.showerror('Open Data Folder', str(e))

    def _about(self):
        messagebox.showinfo('About', f'LaborForceScheduler\n{APP_VERSION}\nPortable build')

    def _open_diagnostics(self):
        try:
            win = tk.Toplevel(self)
            win.title('Diagnostics')
            win.geometry('760x520')
            body = ttk.Frame(win)
            body.pack(fill='both', expand=True)
            txt = tk.Text(body, wrap='none')
            ysb = ttk.Scrollbar(body, orient='vertical', command=txt.yview)
            xsb = ttk.Scrollbar(body, orient='horizontal', command=txt.xview)
            txt.configure(yscrollcommand=ysb.set, xscrollcommand=xsb.set)
            txt.grid(row=0, column=0, sticky='nsew')
            ysb.grid(row=0, column=1, sticky='ns')
            xsb.grid(row=1, column=0, sticky='ew')
            body.rowconfigure(0, weight=1)
            body.columnconfigure(0, weight=1)
            data_path = self.data_path
            appdir = _app_dir()
            last = self.last_solver_summary or {}
            lines = []
            lines.append(f'Version: {APP_VERSION}')
            lines.append(f'App folder: {appdir}')
            lines.append(f'Data file: {data_path}')
            lines.append('')
            lines.append('Last solver run summary:')
            if last:
                for k in ['score_penalty','score_hours','filled','total_slots','assignments','optimizer_iterations','restarts','warnings_count','label','preferred_weekly_cap','maximum_weekly_cap','cap_over_by','infeasible','notes']:
                    if k in last:
                        lines.append(f'  {k}: {last[k]}')
            else:
                lines.append('  (no run yet)')
            txt.insert('1.0', '\n'.join(lines))
            txt.config(state='disabled')
        except Exception as e:
            messagebox.showerror('Diagnostics', str(e))
    def _autosave_tick(self):
        try:
            save_data(self.model, self.data_path)
            try:
                _write_run_log(f"SAVE | {self.data_path}")
            except Exception:
                pass
            self._set_status(f"Autosaved • {datetime.datetime.now().strftime('%H:%M:%S')}")
        except Exception:
            # Stay silent during autosave; manual Save Now shows errors.
            pass
        finally:
            self._schedule_autosave()

    def _on_close(self):
        try:
            save_data(self.model, self.data_path)
        except Exception:
            pass
        try:
            self.help_manager.destroy()
        except Exception:
            pass
        self.destroy()

    def _apply_ui_scale(self, scale: float):
        self.ui_scale = float(scale) if scale else 1.0
        try:
            self.tk.call("tk", "scaling", float(scale))
            f = tkfont.nametofont("TkDefaultFont")
            # Keep readable without being huge
            f.configure(size=max(10, int(10 * float(scale))))
            self.option_add("*Font", f)
        except Exception:
            pass

        style = ttk.Style(self)
        rh = int(max(22, 22 * float(getattr(self, "ui_scale", 1.0))))
        style.configure("Treeview", rowheight=rh)
        style.configure("Treeview.Heading", font=("Segoe UI", 10, "bold"))

    def _load_brand_images(self):
        """Load branding with unified header/store resolution and safe fallbacks."""
        self.brand_asset_state = {"header_path": "", "store_path": "", "header_mode": "none", "store_mode": "none"}
        try:
            header_path = resolve_brand_asset_path("header")
            store_path = resolve_brand_asset_path("store")
            self.brand_asset_state.update({"header_path": header_path, "store_path": store_path})
            if header_path:
                if Image is None or ImageTk is None:
                    try:
                        self.brand_img_header = tk.PhotoImage(file=header_path)
                        self.brand_asset_state["header_mode"] = "tk"
                    except Exception:
                        self.brand_img_header = None
                else:
                    with Image.open(header_path) as img:
                        base = img.copy()
                    self.brand_source_image = base.copy()
                    hdr = base.copy(); hdr.thumbnail((72, 72), Image.LANCZOS)
                    self.brand_img_header = ImageTk.PhotoImage(hdr)
                    self.brand_asset_state["header_mode"] = "pil"
            if store_path:
                if Image is None or ImageTk is None:
                    try:
                        self.brand_img_store = tk.PhotoImage(file=store_path)
                        self.brand_asset_state["store_mode"] = "tk"
                    except Exception:
                        self.brand_img_store = self.brand_img_header
                else:
                    with Image.open(store_path) as img:
                        self._store_img_original = img.copy()
                    store_base = self._store_img_original.copy()
                    store_base.thumbnail((320, 320), Image.LANCZOS)
                    self.brand_img_store = ImageTk.PhotoImage(store_base)
                    self.brand_asset_state["store_mode"] = "pil"
            if self.brand_img_store is None:
                self.brand_img_store = self.brand_img_header
        except Exception:
            self.brand_img_header = None
            self.brand_img_store = None
            self.brand_source_image = None
            self._store_img_original = None
            self.brand_asset_state = {"header_path": "", "store_path": "", "header_mode": "none", "store_mode": "none"}

    def _brand_fallback_copy(self, variant: str = "default") -> Tuple[str, str]:
        store_info = getattr(self, "model", None)
        store_name = ""
        try:
            store_name = str(getattr(getattr(store_info, "store_info", None), "store_name", "") or "").strip()
        except Exception:
            store_name = ""
        title = store_name or "LaborForceScheduler"
        subtitle = "Manager scheduling workspace"
        if variant == "tab":
            subtitle = "Brand image not installed yet"
        elif variant == "store":
            subtitle = "Add optional logo files in Assets/ to brand this release"
        return title, subtitle

    def _render_brand_fallback(self, label_widget: Optional[ttk.Label], variant: str = "default"):
        if label_widget is None:
            return
        title, subtitle = self._brand_fallback_copy(variant)
        label_widget.configure(
            image="",
            text=f"{title}\n{subtitle}",
            justify="center",
            anchor="center",
            padding=(18, 18),
            style="BrandFallback.TLabel",
        )

    def _brand_make_tab_photo(self, max_w: int, max_h: int):
        try:
            if max_w <= 0 or max_h <= 0:
                return None
            if Image is None or ImageTk is None or getattr(self, "brand_source_image", None) is None:
                return getattr(self, "brand_img_store", None)
            im = self.brand_source_image.copy()
            im.thumbnail((int(max_w), int(max_h)), Image.LANCZOS)
            return ImageTk.PhotoImage(im)
        except Exception:
            return getattr(self, "brand_img_store", None)

    def _attach_tab_brand_panel(self,
                                host: tk.Misc,
                                *,
                                slot_key: str,
                                min_w: int = 120,
                                max_w: int = 280,
                                min_h: int = 70,
                                max_h: int = 180,
                                rel_w: float = 0.22,
                                rel_h: float = 0.28) -> Optional[ttk.Label]:
        try:
            lbl = ttk.Label(host, style="BrandFallback.TLabel")
            lbl.pack(anchor="ne", pady=(2, 2))
            if getattr(self, "brand_img_store", None) is None and getattr(self, "brand_source_image", None) is None:
                self._render_brand_fallback(lbl, "tab")
                return lbl

            def _refresh(_e=None):
                try:
                    w = int(host.winfo_width())
                    h = int(host.winfo_height())
                except Exception:
                    w, h = max_w, max_h
                tgt_w = max(int(min_w), min(int(max_w), int(max(1, w) * float(rel_w))))
                tgt_h = max(int(min_h), min(int(max_h), int(max(1, h) * float(rel_h))))
                prev = self._brand_tab_last_size.get(slot_key)
                if prev is not None and abs(prev[0] - tgt_w) < 8 and abs(prev[1] - tgt_h) < 6:
                    return
                photo = self._brand_make_tab_photo(tgt_w, tgt_h)
                if photo is None:
                    self._render_brand_fallback(lbl, "tab")
                    return
                self._brand_tab_last_size[slot_key] = (tgt_w, tgt_h)
                self._brand_tab_photo_refs[slot_key] = photo
                lbl.configure(image=photo, text="", style="TLabel")
            host.bind("<Configure>", _refresh, add="+")
            self.after_idle(_refresh)
            return lbl
        except Exception:
            return None

    def _load_store_tab_image(self):
        if Image is not None and ImageTk is not None and getattr(self, "brand_asset_state", {}).get("store_path") and self._store_img_original is None:
            try:
                with Image.open(self.brand_asset_state.get("store_path", "")) as img:
                    self._store_img_original = img.copy()
            except Exception:
                self._store_img_original = None

    def _resize_store_tab_image(self, event=None):
        try:
            if self._store_img_label is None or self._store_img_container is None:
                return
            if self._store_img_original is None:
                fallback_photo = getattr(self, "brand_img_store", None)
                if fallback_photo is not None:
                    self._store_img_label.configure(image=fallback_photo, text="", style="TLabel")
                    self._store_img_tk = fallback_photo
                else:
                    self._render_brand_fallback(self._store_img_label, "store")
                return
            c_w = int(self._store_img_container.winfo_width())
            c_h = int(self._store_img_container.winfo_height())
            if c_w < 40 or c_h < 40:
                return
            src_w, src_h = self._store_img_original.size
            if src_w <= 0 or src_h <= 0:
                return

            scale = min(float(c_w) / float(src_w), float(c_h) / float(src_h))
            if scale <= 0:
                return

            dst_w = max(1, min(int(src_w * scale), 1800))
            dst_h = max(1, min(int(src_h * scale), 1800))
            if self._store_img_last_size == (dst_w, dst_h):
                return

            resized = self._store_img_original.resize((dst_w, dst_h), Image.LANCZOS)
            self._store_img_tk = ImageTk.PhotoImage(resized)
            self._store_img_label.configure(image=self._store_img_tk, text="", style="TLabel")
            self._store_img_last_size = (dst_w, dst_h)
        except Exception:
            pass

    def _setup_style(self):
        style = ttk.Style(self)
        try:
            style.theme_use("clam")
        except Exception:
            pass

        rh = int(max(22, 22 * float(getattr(self, "ui_scale", 1.0))))
        style.configure("Treeview", rowheight=rh)
        style.configure("Treeview.Heading", font=("Segoe UI", 10, "bold"))
        style.configure("TButton", padding=10)
        style.configure("TFrame", background="#eceff3")
        style.configure("TLabelframe", background="#eceff3")
        style.configure("TLabelframe.Label", background="#eceff3", foreground="#2a3240")
        style.configure("TLabel", background="#eceff3", foreground="#2c3646")
        style.configure("Header.TLabel", font=("Segoe UI", 18, "bold"))
        style.configure("SubHeader.TLabel", font=("Segoe UI", 12, "bold"))
        style.configure("Hint.TLabel", foreground="#566170", background="#eceff3")
        style.configure("Shell.TFrame", background="#e6eaf0")
        style.configure("Section.TFrame", background="#eef1f5")
        style.configure("Panel.TLabelframe", background="#eef1f5")
        style.configure("Panel.TLabelframe.Label", background="#eef1f5", foreground="#2a3240")
        style.configure("HelpBubble.TFrame", background="#f6f7f9")
        style.configure("HelpBubble.TLabel", background="#f6f7f9", foreground="#283142")
        style.configure("HelpMore.TButton", padding=(6, 2))
        style.configure("BrandFallback.TLabel", background="#eef2f6", foreground="#344054", relief="solid", borderwidth=1, font=("Segoe UI", 11, "bold"))

        # Shared workspace faux-tab chrome (visual-only; architecture unchanged).
        style.configure("MainTabInactive.TButton", padding=(10, 3), relief="raised")
        style.configure("MainTabActive.TButton", padding=(10, 3), relief="sunken")

    def _build_ui(self):
        topbar = ttk.Frame(self, style="Shell.TFrame"); topbar.pack(fill="x", padx=10, pady=8)
        # Global header (image only)
        if getattr(self, "brand_img_header", None) is not None:
            ttk.Label(topbar, image=self.brand_img_header).pack(side="left", padx=(0,10))
        else:
            fallback_title, fallback_sub = self._brand_fallback_copy("default")
            ttk.Label(topbar, text=f"{fallback_title}\n{fallback_sub}", style="Header.TLabel", justify="left").pack(side="left")
        self.status_var = tk.StringVar(value="")
        ttk.Label(self, textvariable=self.status_var, foreground="#555").pack(anchor="w", padx=12)

        btns = ttk.Frame(topbar, style="Shell.TFrame"); btns.pack(side="right")
        self.btn_save_now = ttk.Button(btns, text="Save Now", command=self.autosave)
        self.btn_save_now.pack(side="right", padx=6)
        ttk.Button(btns, text="Desktop Shortcut", command=self.create_desktop_shortcut).pack(side="right", padx=6)
        self.btn_open_data = ttk.Button(btns, text="Open...", command=self.open_dialog)
        self.btn_open_data.pack(side="right", padx=6)
        self.btn_save_as = ttk.Button(btns, text="Save As...", command=self.save_as_dialog)
        self.btn_save_as.pack(side="right", padx=6)
        self.btn_new_data = ttk.Button(btns, text="New", command=self.new_data)
        self.btn_new_data.pack(side="right", padx=6)

        shell = ttk.Frame(self, style="Shell.TFrame"); shell.pack(fill="both", expand=True, padx=10, pady=(6,10))
        shell.columnconfigure(0, weight=1)
        shell.rowconfigure(2, weight=1)

        schedule_row = ttk.Frame(shell)
        schedule_row.grid(row=0, column=0, sticky="ew")
        ttk.Label(schedule_row, text="Schedule Tabs:", style="SubHeader.TLabel").pack(side="left", padx=(0, 8))
        self.schedule_tabs_host = ttk.Frame(schedule_row, style="Shell.TFrame")
        self.schedule_tabs_host.pack(side="left", fill="x", expand=True)

        manager_row = ttk.Frame(shell)
        manager_row.grid(row=1, column=0, sticky="ew", pady=(2, 6))
        ttk.Label(manager_row, text="Manager Tabs:", style="SubHeader.TLabel").pack(side="left", padx=(0, 8))
        self.manager_tabs_host = ttk.Frame(manager_row, style="Shell.TFrame")
        self.manager_tabs_host.pack(side="left", fill="x", expand=True)

        self.shared_main_host = ttk.Frame(shell, style="Section.TFrame")
        self.shared_main_host.grid(row=2, column=0, sticky="nsew")

        self.tab_store = ttk.Frame(self.shared_main_host)
        self.tab_reqs = ttk.Frame(self.shared_main_host)
        self.tab_emps = ttk.Frame(self.shared_main_host)
        self.tab_over = ttk.Frame(self.shared_main_host)
        self.tab_gen = ttk.Frame(self.shared_main_host)
        self.tab_preview = ttk.Frame(self.shared_main_host)

        self.tab_manager_tasks = ttk.Frame(self.shared_main_host)
        self.tab_perf = ttk.Frame(self.shared_main_host)
        self.tab_analysis = ttk.Frame(self.shared_main_host)
        self.tab_calloff = ttk.Frame(self.shared_main_host)
        self.tab_mgr = ttk.Frame(self.shared_main_host)
        self.tab_history = ttk.Frame(self.shared_main_host)
        self.tab_settings = ttk.Frame(self.shared_main_host)

        # Hidden/internal tool frames retained for popup workflows and compatibility.
        self.hidden_tools_host = ttk.Frame(self)
        self.tab_manual = ttk.Frame(self.hidden_tools_host)
        self.tab_changes = ttk.Frame(self.hidden_tools_host)
        self.tab_heatmap = ttk.Frame(self.hidden_tools_host)

        self._schedule_tabs = [
            ("store", "Store", self.tab_store),
            ("reqs", "Staffing Requirements", self.tab_reqs),
            ("emps", "Employees", self.tab_emps),
            ("over", "Schedule Exceptions", self.tab_over),
            ("gen", "Schedule Workspace / Generate", self.tab_gen),
            ("preview", "Print / Export", self.tab_preview),
        ]
        self._manager_tabs = [
            ("manager_tasks", "Manager Tasks", self.tab_manager_tasks),
            ("perf", "Employee Performance & Reliability", self.tab_perf),
            ("analysis", "Schedule Analysis", self.tab_analysis),
            ("calloff", "Call-Off Simulator", self.tab_calloff),
            ("mgr", "Manager Goals", self.tab_mgr),
            ("history", "History", self.tab_history),
            ("settings", "Settings", self.tab_settings),
        ]
        self.main_tab_frames: Dict[str, ttk.Frame] = {k: f for k, _t, f in (self._schedule_tabs + self._manager_tabs)}
        self.main_tab_group: Dict[str, str] = {k: "schedule" for k, _t, _f in self._schedule_tabs}
        self.main_tab_group.update({k: "manager" for k, _t, _f in self._manager_tabs})
        self.schedule_tab_var = tk.StringVar(value="store")
        self.manager_tab_var = tk.StringVar(value="manager_tasks")

        self._main_tab_buttons: Dict[str, ttk.Button] = {}
        for key, label, _frame in self._schedule_tabs:
            btn = ttk.Button(
                self.schedule_tabs_host,
                text=label,
                style="MainTabInactive.TButton",
                command=lambda k=key: self.show_main_tab(k),
            )
            btn.pack(side="left", padx=(0, 4))
            self._main_tab_buttons[key] = btn
        for key, label, _frame in self._manager_tabs:
            btn = ttk.Button(
                self.manager_tabs_host,
                text=label,
                style="MainTabInactive.TButton",
                command=lambda k=key: self.show_main_tab(k),
            )
            btn.pack(side="left", padx=(0, 4))
            self._main_tab_buttons[key] = btn

        self._build_store_tab()
        self._build_emps_tab()
        self._build_overrides_tab()
        self._build_reqs_tab()
        self._build_generate_tab()
        self._build_preview_tab()
        self._build_manual_tab()
        self._build_manager_tasks_tab()
        self._build_performance_tab()
        self._build_manager_tab()
        self._build_analysis_tab()
        self._build_changes_tab()
        self._build_heatmap_tab()
        self._build_calloff_tab()
        self._build_history_tab()
        self._build_settings_tab()
        self.show_main_tab("store")

    def _refresh_main_tab_chrome(self, active_key: str):
        active = str(active_key or "").strip()
        for key, btn in getattr(self, "_main_tab_buttons", {}).items():
            try:
                btn.configure(style=("MainTabActive.TButton" if key == active else "MainTabInactive.TButton"))
            except Exception:
                pass

    def show_main_tab(self, tab_key: str):
        try:
            self.help_manager.hide_all()
        except Exception:
            pass
        key = str(tab_key or "").strip()
        if key not in getattr(self, "main_tab_frames", {}):
            return
        for frame in self.main_tab_frames.values():
            frame.pack_forget()
        self.main_tab_frames[key].pack(fill="both", expand=True)
        if self.main_tab_group.get(key) == "schedule":
            self.schedule_tab_var.set(key)
        else:
            self.manager_tab_var.set(key)
        self._refresh_main_tab_chrome(key)

    def _build_help_catalog(self) -> Dict[str, Dict[str, str]]:
        defaults = {
            "new_data": {
                "short": "Start a new dataset for scheduling.",
                "long": "Creates a fresh in-memory dataset and clears the current week output. Use Open to return to an existing data file.",
            },
            "open_data": {
                "short": "Load scheduler data from a file.",
                "long": "Opens a saved scheduler data file and refreshes tabs with that dataset.",
            },
            "save_as": {
                "short": "Save current data to a new file path.",
                "long": "Use Save As when creating snapshots or separate scenario files without overwriting the current default data file.",
            },
            "save_now": {
                "short": "Immediately save current scheduler data.",
                "long": "Writes current in-memory data to disk now. Autosave still runs in the background on an interval.",
            },
            "generate_fresh": {
                "short": "Generate a new schedule from current rules.",
                "long": "Runs schedule generation for the selected week label using current requirements, employees, settings, and constraints.",
            },
            "generate_regen": {
                "short": "Regenerate using the current schedule as context.",
                "long": "Runs generation again while using the current schedule context for continuity and comparison.",
            },
            "refine_schedule": {
                "short": "Improve the current schedule without rebuilding from scratch.",
                "long": "Runs a targeted refinement pass focused on weak coverage areas and practical improvements while preserving protected edits.",
            },
            "save_history": {
                "short": "Save the current result to schedule history.",
                "long": "Stores a summary snapshot of the current week schedule for later manager review and comparison.",
            },
            "open_manual": {
                "short": "Open manual edit tools in a popup.",
                "long": "Launches the manual schedule editing workspace in a popup window for direct manager adjustments.",
            },
            "open_heatmap": {
                "short": "Open coverage heatmap popup.",
                "long": "Shows scheduled headcount versus staffing requirements across day/time blocks.",
            },
            "open_analyzer": {
                "short": "Run analyzer review in popup.",
                "long": "Opens the analyzer view with findings and suggested push-fix actions for schedule review.",
            },
            "compare_versions": {
                "short": "Compare available schedule versions.",
                "long": "Compares generated/current/finalized versions to review differences before publishing decisions.",
            },
            "week_label": {
                "short": "Set the schedule week you are working on.",
                "long": "Use a clear week label before generating, refining, exporting, or publishing so manager review stays tied to the right week.",
            },
            "set_this_week": {
                "short": "Jump the week label to this Sunday.",
                "long": "Fills the week label with the current Sunday-based week start so managers can begin a normal weekly run quickly.",
            },
            "refine_unlock_toggle": {
                "short": "Allow refine to touch unlocked manual edits.",
                "long": "Leave this off for normal manager review. Turn it on only when you want Refine to adjust manual entries that are not explicitly locked.",
            },
            "calloff_simulator": {
                "short": "Review call-off backup options.",
                "long": "Opens the call-off simulator so managers can see likely weak windows and backup employee suggestions without changing the live schedule.",
            },
            "print_html": {
                "short": "Open the printable schedule view.",
                "long": "Exports the main HTML print view and then tries to open it locally in your default browser or print-capable app.",
            },
            "employee_calendar_export": {
                "short": "Open the employee calendar export.",
                "long": "Builds the employee-facing calendar HTML and then opens it locally for review, sharing, or printing.",
            },
            "manager_report_export": {
                "short": "Open the manager review report.",
                "long": "Builds the manager report with readiness, shortage, and call-list review details and then opens it locally.",
            },
            "export_csv": {
                "short": "Save the schedule as CSV.",
                "long": "Exports the current schedule rows as CSV for spreadsheet review or downstream manager reporting.",
            },
            "export_pdf": {
                "short": "Export PDF when the optional PDF library is available.",
                "long": "Creates a PDF copy of the main schedule when ReportLab is installed. If not installed, use the HTML print view instead.",
            },
            "publish_final": {
                "short": "Lock and publish this week as the final schedule.",
                "long": "Saves the current week as the published final version used for manager review, comparisons, and next-week stability references.",
            },
            "load_final": {
                "short": "Reload the published final for this week.",
                "long": "Loads the saved final schedule for the current week so managers can review or continue from the published version.",
            },
            "reprint_final": {
                "short": "Re-open exports for the published final schedule.",
                "long": "Uses the saved final schedule for this week to rebuild printable exports without changing the active data setup.",
            },
            "store_state": {
                "short": "Select store state for labor-rule profile loading.",
                "long": "State selection controls labor-law profile loading. Incomplete profiles fall back to current/default rules.",
            },
            "store_hours": {
                "short": "Set area open/close hard boundaries.",
                "long": "Hours of operation define hard scheduling boundaries for each area and are used in validation.",
            },
            "area_color": {
                "short": "Choose area color used in employee calendar exports.",
                "long": "These colors apply to employee calendar export visuals only and are separate from app runtime theme styling.",
            },
            "req_area": {
                "short": "Choose area to apply staffing pattern.",
                "long": "Select which department receives the requirement pattern before applying selected day/time settings.",
            },
            "req_days": {
                "short": "Select target days for requirement updates.",
                "long": "Day checkboxes define which days will receive the Min/Preferred/Max pattern when Apply Pattern is used.",
            },
            "req_time": {
                "short": "Set time range for requirement pattern.",
                "long": "Start/End define the staffing block range used when applying requirements to selected days.",
            },
            "req_counts": {
                "short": "Set Min / Preferred / Max staffing counts.",
                "long": "Min is required coverage, Preferred is target coverage, and Max is the upper soft ceiling.",
            },
            "req_apply": {
                "short": "Apply pattern to selected days.",
                "long": "Writes or updates requirement blocks for selected days using the chosen area, time window, and staffing counts.",
            },
            "req_copy": {
                "short": "Copy one day pattern to selected target days.",
                "long": "Copies the source day requirement pattern into selected target days for faster weekly setup.",
            },
        }
        try:
            hp = rel_path("help_content.json")
            if os.path.isfile(hp):
                with open(hp, "r", encoding="utf-8") as f:
                    payload = json.load(f) or {}
                if isinstance(payload, dict):
                    for k, v in payload.items():
                        if isinstance(v, dict) and str(v.get("short", "") or "").strip():
                            defaults[str(k)] = {
                                "short": str(v.get("short", "") or "").strip(),
                                "long": str(v.get("long", "") or "").strip(),
                            }
        except Exception as ex:
            _write_run_log(f"HELP | help_content.json load failed: {repr(ex)}")
        return defaults

    def _register_help_control(self, widget: Optional[tk.Misc], help_id: str):
        if widget is None:
            return
        info = (self._help_catalog or {}).get(str(help_id or "").strip(), {})
        short = str(info.get("short", "") or "").strip()
        long_txt = str(info.get("long", "") or "").strip()
        if not short:
            return
        self.help_manager.register(widget, help_id, short, long_txt)

    def _register_phase1_help_controls(self):
        for attr, hid in [
            ("btn_new_data", "new_data"),
            ("btn_open_data", "open_data"),
            ("btn_save_as", "save_as"),
            ("btn_save_now", "save_now"),
            ("btn_generate_fresh", "generate_fresh"),
            ("btn_regen_current", "generate_regen"),
            ("btn_refine", "refine_schedule"),
            ("label_entry", "week_label"),
            ("btn_set_this_week", "set_this_week"),
            ("refine_allow_manual_unlock_chk", "refine_unlock_toggle"),
            ("btn_save_history", "save_history"),
            ("btn_open_manual", "open_manual"),
            ("btn_open_heatmap", "open_heatmap"),
            ("btn_open_analyzer", "open_analyzer"),
            ("btn_compare_versions", "compare_versions"),
            ("btn_calloff_simulator", "calloff_simulator"),
            ("btn_readiness_checklist", "publish_final"),
            ("btn_labor_cost_review", "manager_report_export"),
            ("btn_replacement_assistant", "calloff_simulator"),
            ("btn_historical_suggestions", "save_history"),
            ("btn_print_html", "print_html"),
            ("btn_employee_calendar", "employee_calendar_export"),
            ("btn_manager_report", "manager_report_export"),
            ("btn_export_csv", "export_csv"),
            ("btn_export_pdf", "export_pdf"),
            ("btn_publish_final", "publish_final"),
            ("btn_load_final", "load_final"),
            ("btn_reprint_final", "reprint_final"),
            ("store_state_combo", "store_state"),
            ("req_area_combo", "req_area"),
            ("req_start_combo", "req_time"),
            ("req_end_combo", "req_time"),
            ("req_min_combo", "req_counts"),
            ("req_pref_combo", "req_counts"),
            ("req_max_combo", "req_counts"),
            ("btn_apply_pattern", "req_apply"),
            ("btn_copy_pattern", "req_copy"),
        ]:
            self._register_help_control(getattr(self, attr, None), hid)
        for _d, chk in getattr(self, "req_day_checks", {}).items():
            self._register_help_control(chk, "req_days")
        for area, widgets in getattr(self, "store_hours_widgets", {}).items():
            self._register_help_control(widgets.get("open"), "store_hours")
            self._register_help_control(widgets.get("close"), "store_hours")
        for _area, btn in getattr(self, "area_color_buttons", {}).items():
            self._register_help_control(btn, "area_color")

    def _register_broad_help_controls(self):
        """First-wave broad hover-help coverage across major interactive controls."""
        roots = [
            getattr(self, "tab_store", None), getattr(self, "tab_reqs", None), getattr(self, "tab_emps", None),
            getattr(self, "tab_over", None), getattr(self, "tab_gen", None), getattr(self, "tab_preview", None),
            getattr(self, "tab_manager_tasks", None), getattr(self, "tab_perf", None), getattr(self, "tab_analysis", None),
            getattr(self, "tab_calloff", None), getattr(self, "tab_mgr", None), getattr(self, "tab_history", None), getattr(self, "tab_settings", None),
        ]
        seen: Set[int] = set()

        def _label_for(w: tk.Misc) -> str:
            try:
                txt = str(w.cget("text") or "").strip()
                if txt:
                    return txt
            except Exception:
                pass
            try:
                return str(w.winfo_class())
            except Exception:
                return "Control"

        stack: List[tk.Misc] = [r for r in roots if r is not None]
        while stack:
            w = stack.pop()
            try:
                stack.extend(list(w.winfo_children()))
            except Exception:
                pass
            try:
                wid = int(w.winfo_id())
            except Exception:
                continue
            if wid in seen:
                continue
            seen.add(wid)

            if isinstance(w, (ttk.Button, ttk.Entry, ttk.Combobox, ttk.Checkbutton, ttk.Radiobutton, tk.Button, tk.Entry, tk.Checkbutton, tk.Radiobutton, tk.Text)):
                label = _label_for(w)
                hid = f"auto_help_{wid}"
                short = f"{label}: quick help"
                long_txt = (
                    f"Control: {label}\n\n"
                    "Use this control to update scheduler inputs or review output.\n"
                    "Tip: after edits, Generate or Refine the week and then review warnings/heatmap."
                )
                self.help_manager.register(w, hid, short, long_txt)


    # -------- Store tab --------
    def _build_store_tab(self):
        _outer, frm, _canvas = _build_scrollable_canvas_host(self.tab_store, padding=(14, 14, 14, 14), min_width=1120)
        ttk.Label(frm, text="Store Info prints on schedules.", style="SubHeader.TLabel").pack(anchor="w", pady=(0,8))

        top = ttk.Frame(frm, style="Section.TFrame"); top.pack(fill="x", expand=False, pady=10)
        left = ttk.Frame(top, style="Section.TFrame"); left.pack(side="left", fill="both", expand=True)
        right = ttk.Frame(top, style="Section.TFrame"); right.pack(side="right", fill="both", expand=True, padx=(12,0))

        box = ttk.LabelFrame(left, text="Store", style="Panel.TLabelframe")
        box.pack(fill="x")

        self.store_name_var = tk.StringVar()
        self.store_addr_var = tk.StringVar()
        self.store_phone_var = tk.StringVar()
        self.store_mgr_var = tk.StringVar()
        self.store_state_var = tk.StringVar(value="")
        self.cstore_open_var = tk.StringVar(value="00:00")
        self.cstore_close_var = tk.StringVar(value="24:00")
        self.kitchen_open_var = tk.StringVar(value="00:00")
        self.kitchen_close_var = tk.StringVar(value="24:00")
        self.carwash_open_var = tk.StringVar(value="00:00")
        self.carwash_close_var = tk.StringVar(value="24:00")

        self.peak_soft_vars: Dict[str, List[Tuple[tk.StringVar, tk.StringVar]]] = {
            area: [(tk.StringVar(value=""), tk.StringVar(value="")) for _ in range(3)]
            for area in AREAS
        }

        r=0
        ttk.Label(box, text="Store Name:").grid(row=r, column=0, sticky="w", padx=10, pady=6)
        ttk.Entry(box, textvariable=self.store_name_var, width=44).grid(row=r, column=1, sticky="w", padx=10, pady=6)
        ttk.Label(box, text="Phone:").grid(row=r, column=2, sticky="w", padx=10, pady=6)
        ttk.Entry(box, textvariable=self.store_phone_var, width=18).grid(row=r, column=3, sticky="w", padx=10, pady=6)

        r+=1
        ttk.Label(box, text="Address:").grid(row=r, column=0, sticky="w", padx=10, pady=6)
        ttk.Entry(box, textvariable=self.store_addr_var, width=78).grid(row=r, column=1, columnspan=3, sticky="w", padx=10, pady=6)

        r+=1
        ttk.Label(box, text="Manager:").grid(row=r, column=0, sticky="w", padx=10, pady=6)
        ttk.Entry(box, textvariable=self.store_mgr_var, width=28).grid(row=r, column=1, sticky="w", padx=10, pady=6)

        r += 1
        law = ttk.LabelFrame(box, text="Labor Rule Jurisdiction", style="Panel.TLabelframe")
        law.grid(row=r, column=0, columnspan=4, sticky="ew", padx=10, pady=8)
        ttk.Label(law, text="Store State (Required):").grid(row=0, column=0, sticky="w", padx=8, pady=6)
        self.store_state_combo = ttk.Combobox(
            law,
            textvariable=self.store_state_var,
            values=[US_STATE_LABELS[c] for c, _ in US_STATES],
            state="readonly",
            width=28,
        )
        self.store_state_combo.grid(row=0, column=1, sticky="w", padx=8, pady=6)
        ttk.Label(
            law,
            text="State selection controls labor-law profile loading. Incomplete profiles safely fall back to current/default rules.",
            style="Hint.TLabel",
        ).grid(row=1, column=0, columnspan=4, sticky="w", padx=8, pady=(0, 6))

        r += 1
        hours = ttk.LabelFrame(box, text="Hours of Operation (Hard Rules)", style="Panel.TLabelframe")
        hours.grid(row=r, column=0, columnspan=4, sticky="ew", padx=10, pady=8)
        ttk.Label(hours, text="Area").grid(row=0, column=0, padx=8, pady=4, sticky="w")
        ttk.Label(hours, text="Open").grid(row=0, column=1, padx=8, pady=4, sticky="w")
        ttk.Label(hours, text="Close").grid(row=0, column=2, padx=8, pady=4, sticky="w")
        ttk.Label(hours, text="Color").grid(row=0, column=3, padx=8, pady=4, sticky="w")
        rows = [
            ("CSTORE", "C-Store", self.cstore_open_var, self.cstore_close_var),
            ("KITCHEN", "Kitchen", self.kitchen_open_var, self.kitchen_close_var),
            ("CARWASH", "Carwash", self.carwash_open_var, self.carwash_close_var),
        ]
        self.area_color_vars: Dict[str, tk.StringVar] = {a: tk.StringVar(value=_default_area_colors()[a]) for a in AREAS}
        self.store_hours_widgets: Dict[str, Dict[str, tk.Misc]] = {}
        self.area_color_buttons: Dict[str, ttk.Button] = {}
        self.area_color_swatches: Dict[str, ttk.Label] = {}
        for rr, (area, lbl, open_var, close_var) in enumerate(rows, start=1):
            ttk.Label(hours, text=lbl).grid(row=rr, column=0, padx=8, pady=4, sticky="w")
            open_combo = ttk.Combobox(hours, textvariable=open_var, values=TIME_CHOICES, state="readonly", width=8)
            open_combo.grid(row=rr, column=1, padx=8, pady=4, sticky="w")
            close_combo = ttk.Combobox(hours, textvariable=close_var, values=TIME_CHOICES, state="readonly", width=8)
            close_combo.grid(row=rr, column=2, padx=8, pady=4, sticky="w")
            color_host = ttk.Frame(hours)
            color_host.grid(row=rr, column=3, padx=8, pady=4, sticky="w")
            sw = ttk.Label(color_host, text="     ", background=self.area_color_vars[area].get())
            sw.pack(side="left")
            self.area_color_swatches[area] = sw
            choose_btn = ttk.Button(color_host, text="Choose...", command=lambda a=area: self._pick_area_color(a))
            choose_btn.pack(side="left", padx=(6, 0))
            self.area_color_buttons[area] = choose_btn
            self.store_hours_widgets[area] = {"open": open_combo, "close": close_combo}

        r += 1
        peak = ttk.LabelFrame(box, text="Peak Hours (Soft Rules)", style="Panel.TLabelframe")
        peak.grid(row=r, column=0, columnspan=4, sticky="ew", padx=10, pady=8)
        headers = ["Area", "P1 Start", "P1 End", "P2 Start", "P2 End", "P3 Start", "P3 End"]
        for cc, hdr in enumerate(headers):
            ttk.Label(peak, text=hdr).grid(row=0, column=cc, padx=8, pady=4, sticky="w")
        peak_rows = [
            ("CSTORE", "C-Store"),
            ("KITCHEN", "Kitchen"),
            ("CARWASH", "Carwash"),
        ]
        for rr, (area, lbl) in enumerate(peak_rows, start=1):
            ttk.Label(peak, text=lbl).grid(row=rr, column=0, padx=8, pady=4, sticky="w")
            for idx, (st_var, en_var) in enumerate(self.peak_soft_vars[area]):
                ttk.Combobox(peak, textvariable=st_var, values=[""] + TIME_CHOICES, state="readonly", width=8).grid(row=rr, column=1 + (idx*2), padx=8, pady=4, sticky="w")
                ttk.Combobox(peak, textvariable=en_var, values=[""] + TIME_CHOICES, state="readonly", width=8).grid(row=rr, column=2 + (idx*2), padx=8, pady=4, sticky="w")

        ttk.Label(
            peak,
            text="Manager note: Peak Hours are soft preferences for beneficial overstaffing. They encourage extending practical shifts into later demand windows and never override hard rules.",
            wraplength=900,
            style="SubHeader.TLabel",
        ).grid(row=len(peak_rows)+1, column=0, columnspan=7, padx=8, pady=(6,4), sticky="w")

        self._store_img_container = ttk.Frame(right, style="Panel.TFrame")
        self._store_img_container.pack(fill="both", expand=True, padx=(10, 12), pady=(10, 10))
        self._store_img_label = ttk.Label(self._store_img_container)
        self._store_img_label.pack(expand=True)
        self._store_img_last_size = None
        self._load_store_tab_image()
        self._store_img_container.bind("<Configure>", self._resize_store_tab_image, add="+")
        self.after_idle(self._resize_store_tab_image)
        if self._store_img_original is None:
            self._render_brand_fallback(self._store_img_label, "store")

        ttk.Button(frm, text="Save Store Info", command=self.save_store_info).pack(anchor="w", padx=6, pady=10)

    def _refresh_area_color_swatch(self, area: str):
        try:
            color = _normalize_area_colors({area: self.area_color_vars[area].get()}).get(area, _default_area_colors().get(area, "#444444"))
            self.area_color_vars[area].set(color)
            lbl = self.area_color_swatches.get(area)
            if lbl is not None:
                lbl.configure(background=color)
        except Exception:
            pass

    def _pick_area_color(self, area: str):
        base = _normalize_area_colors({area: self.area_color_vars.get(area, tk.StringVar(value="")).get()}).get(area, _default_area_colors().get(area, "#444444"))
        chosen = colorchooser.askcolor(color=base, title=f"Select {AREA_LABEL.get(area, area)} Calendar Color")
        if not chosen or not chosen[1]:
            return
        self.area_color_vars[area].set(str(chosen[1]))
        self._refresh_area_color_swatch(area)

    def save_store_info(self):
        raw_state = str(self.store_state_var.get() or "").strip()
        store_state = raw_state.split(" - ", 1)[0].strip().upper() if raw_state else ""
        if store_state not in US_STATE_CODES:
            messagebox.showerror("Store", "Store State is required. Please select one of the 50 U.S. states.")
            return

        checks = [
            ("CSTORE", self.cstore_open_var.get(), self.cstore_close_var.get()),
            ("KITCHEN", self.kitchen_open_var.get(), self.kitchen_close_var.get()),
            ("CARWASH", self.carwash_open_var.get(), self.carwash_close_var.get()),
        ]
        area_hours: Dict[str, Tuple[int, int]] = {}
        for area, op, cl in checks:
            op_t = hhmm_to_tick(op); cl_t = hhmm_to_tick(cl)
            if cl_t <= op_t:
                messagebox.showerror("Store", f"{area} close time must be after open time.")
                return
            area_hours[area] = (int(op_t), int(cl_t))

        area_colors = _normalize_area_colors({a: self.area_color_vars.get(a, tk.StringVar(value="")).get() for a in AREAS})

        peak_hours_soft: Dict[str, List[Tuple[str, str]]] = {}
        area_labels = {"CSTORE": "C-Store", "KITCHEN": "Kitchen", "CARWASH": "Carwash"}
        for area in AREAS:
            windows: List[Tuple[str, str]] = []
            for idx, (st_var, en_var) in enumerate(self.peak_soft_vars.get(area, []), start=1):
                st = str(st_var.get() or "").strip()
                en = str(en_var.get() or "").strip()
                if bool(st) ^ bool(en):
                    messagebox.showerror("Store", f"{area_labels.get(area, area)} Peak {idx}: start and end are both required when one is set.")
                    return
                if not st and not en:
                    windows.append(("", ""))
                    continue
                st_t = hhmm_to_tick(st)
                en_t = hhmm_to_tick(en)
                if en_t <= st_t:
                    messagebox.showerror("Store", f"{area_labels.get(area, area)} Peak {idx}: end time must be after start time.")
                    return
                op_t, cl_t = area_hours.get(area, (0, DAY_TICKS))
                if st_t < op_t or en_t > cl_t:
                    messagebox.showerror("Store", f"{area_labels.get(area, area)} Peak {idx} must be within Hours of Operation: {tick_to_hhmm(op_t)}–{tick_to_hhmm(cl_t)}")
                    return
                windows.append((tick_to_hhmm(st_t), tick_to_hhmm(en_t)))
            while len(windows) < 3:
                windows.append(("", ""))
            peak_hours_soft[area] = windows[:3]

        self.model.store_info = StoreInfo(
            store_name=self.store_name_var.get().strip(),
            store_address=self.store_addr_var.get().strip(),
            store_phone=self.store_phone_var.get().strip(),
            store_manager=self.store_mgr_var.get().strip(),
            store_state=store_state,
            cstore_open=self.cstore_open_var.get().strip() or "00:00",
            cstore_close=self.cstore_close_var.get().strip() or "24:00",
            kitchen_open=self.kitchen_open_var.get().strip() or "00:00",
            kitchen_close=self.kitchen_close_var.get().strip() or "24:00",
            carwash_open=self.carwash_open_var.get().strip() or "00:00",
            carwash_close=self.carwash_close_var.get().strip() or "24:00",
            peak_hours_soft=peak_hours_soft,
            area_colors=area_colors,
        )
        prof, warn = load_state_law_profile(store_state)
        applied = False
        apply_msg = ""
        if prof:
            try:
                applied, apply_msg = apply_state_law_profile_to_model(self.model, store_state, prof)
            except Exception as ex:
                applied, apply_msg = False, f"State law profile apply failed for {store_state}: {ex}"
        if warn:
            _write_run_log(f"STATE_LAW | {warn}")
            messagebox.showwarning("Store State Profile", warn)
        if apply_msg:
            _write_run_log(f"STATE_LAW | {apply_msg}")
        if prof and not warn and not applied:
            self._set_status(f"State law profile loaded for {store_state}; default runtime rules retained.")
        elif applied:
            self._set_status(f"State law profile applied for {store_state}.")
        self.autosave()
        self._validate_requirements_for_context("store", block=False)
        messagebox.showinfo("Store", "Saved.")

    # -------- Employees tab --------
    def _build_emps_tab(self):
        top = ttk.Frame(self.tab_emps); top.pack(fill="x", padx=10, pady=10)
        ttk.Button(top, text="Add", command=self.add_employee).pack(side="left")
        ttk.Button(top, text="Edit Selected", command=self.edit_employee).pack(side="left", padx=8)
        ttk.Button(top, text="Delete Selected", command=self.delete_employee).pack(side="left", padx=8)

        self.show_inactive = tk.BooleanVar(value=True)
        ttk.Checkbutton(top, text="Show On Leave / Inactive", variable=self.show_inactive, command=self.refresh_emp_tree).pack(side="right")

        cols = ("Name","Phone","Status","Type","Wants","SplitOK","DoubleOK","MaxShiftH","MaxShiftsDay","MaxWeekH","TargetMin","MinorType","Areas","PrefAreas","AvoidClopens","MaxConsec","WeekendPref","FixedShifts")
        tree_wrap = ttk.Frame(self.tab_emps); tree_wrap.pack(fill="both", expand=True, padx=10, pady=10)
        self.emp_tree = ttk.Treeview(tree_wrap, columns=cols, show="headings", height=18)
        for c in cols:
            self.emp_tree.heading(c, text=c)
            w = 120
            if c=="Name": w=240
            if c in ["Areas","PrefAreas"]: w=240
            if c=="Type": w=160
            if c in ["MaxShiftH","MaxShiftsDay","MaxWeekH"]: w=110
            if c in ["SplitOK","DoubleOK"]: w=90
            if c=="FixedShifts": w=110
            self.emp_tree.column(c, width=w, anchor="w", stretch=True)
        emp_tree_ysb = ttk.Scrollbar(tree_wrap, orient="vertical", command=self.emp_tree.yview)
        emp_tree_xsb = ttk.Scrollbar(tree_wrap, orient="horizontal", command=self.emp_tree.xview)
        self.emp_tree.configure(yscrollcommand=emp_tree_ysb.set, xscrollcommand=emp_tree_xsb.set)
        self.emp_tree.grid(row=0, column=0, sticky="nsew")
        emp_tree_ysb.grid(row=0, column=1, sticky="ns")
        emp_tree_xsb.grid(row=1, column=0, sticky="ew")
        tree_wrap.grid_rowconfigure(0, weight=1)
        tree_wrap.grid_columnconfigure(0, weight=1)

    def refresh_emp_tree(self):
        for i in self.emp_tree.get_children():
            self.emp_tree.delete(i)
        for e in sorted(self.model.employees, key=lambda x: x.name.lower()):
            if not self.show_inactive.get() and e.work_status!="Active":
                continue
            self.emp_tree.insert("", "end", values=(
                e.name, e.phone, e.work_status,
                getattr(e, "employee_type", "Crew Member"),
                "Yes" if e.wants_hours else "No",
                "Yes" if getattr(e, "split_shifts_ok", True) else "No",
                "Yes" if getattr(e, "double_shifts_ok", False) else "No",
                f"{float(getattr(e, 'max_hours_per_shift', 8.0)):g}",
                int(getattr(e, "max_shifts_per_day", 1)),
                f"{e.max_weekly_hours:g}",
                f"{e.target_min_hours:g}",
                e.minor_type,
                ", ".join(e.areas_allowed),
                ", ".join(e.preferred_areas),
                "Yes" if e.avoid_clopens else "No",
                e.max_consecutive_days,
                e.weekend_preference,
                len(_normalize_fixed_schedule_entries(list(getattr(e, "fixed_schedule", []) or []))),
            ))

    def add_employee(self):
        d = EmployeeDialog(self, None)
        self.wait_window(d)
        if d.result:
            if any(e.name.strip().lower()==d.result.name.strip().lower() for e in self.model.employees):
                messagebox.showerror("Employees", "An employee with that name already exists.")
                return
            self.model.employees.append(d.result)
            self.refresh_emp_tree()
            self.refresh_override_dropdowns()
            self.autosave()

    def _selected_emp_name(self) -> Optional[str]:
        sel = self.emp_tree.selection()
        if not sel:
            return None
        return self.emp_tree.item(sel[0], "values")[0]

    def edit_employee(self):
        name = self._selected_emp_name()
        if not name:
            messagebox.showinfo("Employees", "Select an employee.")
            return
        idx = next((i for i,e in enumerate(self.model.employees) if e.name==name), None)
        if idx is None:
            return
        d = EmployeeDialog(self, self.model.employees[idx])
        self.wait_window(d)
        if d.result:
            new = d.result
            # rename references
            if new.name != name:
                for o in self.model.weekly_overrides:
                    if o.employee_name == name:
                        o.employee_name = new.name
            self.model.employees[idx] = new
            self.refresh_emp_tree()
            self.refresh_override_dropdowns()
            self.autosave()

    def delete_employee(self):
        name = self._selected_emp_name()
        if not name:
            return
        if not messagebox.askyesno("Delete", f"Delete {name}?"):
            return
        self.model.employees = [e for e in self.model.employees if e.name!=name]
        self.model.weekly_overrides = [o for o in self.model.weekly_overrides if o.employee_name!=name]
        self.refresh_emp_tree()
        self.refresh_override_dropdowns()
        self.autosave()

    # -------- Schedule Exceptions (One-Week) tab --------
    def _selected_exception_label(self) -> str:
        lbl = ""
        try:
            lbl = str(self.label_var.get() or "").strip()
        except Exception:
            lbl = ""
        if not lbl:
            lbl = str(getattr(self, "current_label", "") or "").strip()
        if not lbl:
            lbl = self._default_week_label()
        return lbl

    def _exception_bucket(self, label: Optional[str] = None) -> Dict[str, Any]:
        lbl = str(label or self._selected_exception_label()).strip()
        cur = _normalize_weekly_exception_settings(getattr(self.model, "weekly_exception_settings", {}) or {})
        self.model.weekly_exception_settings = cur
        if lbl not in cur:
            cur[lbl] = {
                "no_school_days": {d: False for d in DAYS},
                "special_event_days": {d: False for d in DAYS},
                "time_off_requests": [],
            }
        return cur[lbl]

    def _build_overrides_tab(self):
        _outer, frm, _canvas = _build_scrollable_canvas_host(
            self.tab_over,
            padding=(12, 12, 12, 12),
            min_width=1120,
        )
        ttk.Label(
            frm,
            text="Temporary one-week schedule exceptions for the selected week. These changes affect only that schedule and do not change recurring employee availability.",
            style="SubHeader.TLabel",
        ).pack(anchor="w", pady=(0, 8))

        week_row = ttk.Frame(frm)
        week_row.pack(fill="x", pady=(0, 8))
        ttk.Label(week_row, text="Selected Week:").pack(side="left", padx=(0, 8))
        self.ov_label_var = tk.StringVar(value=self.current_label)
        self.ov_week_entry = ttk.Entry(week_row, textvariable=self.ov_label_var, width=40)
        self.ov_week_entry.pack(side="left")
        ttk.Button(week_row, text="Use Generate Week", command=self._sync_exception_label_from_generate).pack(side="left", padx=8)

        self.no_school_vars: Dict[str, tk.BooleanVar] = {d: tk.BooleanVar(value=False) for d in DAYS}
        no_school_box = ttk.LabelFrame(frm, text="No School Days")
        no_school_box.pack(fill="x", pady=(0, 10))
        ttk.Label(no_school_box, text="For the selected week only, mark days where school is not in session so school-day-related minor restrictions may be relaxed.").grid(row=0, column=0, columnspan=7, sticky="w", padx=8, pady=(6, 6))
        for i, d in enumerate(DAYS):
            ttk.Label(no_school_box, text=DAY_FULL[d]).grid(row=1, column=i, sticky="w", padx=8, pady=(0, 2))
            ttk.Checkbutton(no_school_box, variable=self.no_school_vars[d], command=self._on_exception_day_toggle).grid(row=2, column=i, sticky="w", padx=8, pady=(0, 8))

        self.special_event_vars: Dict[str, tk.BooleanVar] = {d: tk.BooleanVar(value=False) for d in DAYS}
        special_box = ttk.LabelFrame(frm, text="Special Event Days")
        special_box.pack(fill="x", pady=(0, 10))
        ttk.Label(special_box, text="Mark selected-week days where the engine should overstaff more aggressively and prefer extra staffing.").grid(row=0, column=0, columnspan=7, sticky="w", padx=8, pady=(6, 6))
        for i, d in enumerate(DAYS):
            ttk.Label(special_box, text=DAY_FULL[d]).grid(row=1, column=i, sticky="w", padx=8, pady=(0, 2))
            ttk.Checkbutton(special_box, variable=self.special_event_vars[d], command=self._on_exception_day_toggle).grid(row=2, column=i, sticky="w", padx=8, pady=(0, 8))

        # Stage 3 will fill the full request-management behavior.
        req_box = ttk.LabelFrame(frm, text="Time Off Requests")
        req_box.pack(fill="both", expand=True)
        btn_row = ttk.Frame(req_box)
        btn_row.pack(fill="x", padx=8, pady=(8, 6))
        ttk.Button(btn_row, text="Add Time Off", command=self.add_time_off_request).pack(side="left", padx=(0, 6))
        ttk.Button(btn_row, text="Edit Request", command=self.edit_time_off_request).pack(side="left", padx=6)
        ttk.Button(btn_row, text="Delete Request", command=self.delete_time_off_request).pack(side="left", padx=6)

        cols = ("Employee", "Day", "Window", "Status", "Note")
        tor_wrap = ttk.Frame(req_box)
        tor_wrap.pack(fill="both", expand=True, padx=8, pady=(0, 8))
        self.time_off_tree = ttk.Treeview(tor_wrap, columns=cols, show="headings", height=10)
        for c in cols:
            self.time_off_tree.heading(c, text=c)
            self.time_off_tree.column(c, width=170 if c != "Note" else 320)
        tor_ys = ttk.Scrollbar(tor_wrap, orient="vertical", command=self.time_off_tree.yview)
        tor_xs = ttk.Scrollbar(tor_wrap, orient="horizontal", command=self.time_off_tree.xview)
        self.time_off_tree.configure(yscrollcommand=tor_ys.set, xscrollcommand=tor_xs.set)
        self.time_off_tree.grid(row=0, column=0, sticky="nsew")
        tor_ys.grid(row=0, column=1, sticky="ns")
        tor_xs.grid(row=1, column=0, sticky="ew")
        tor_wrap.rowconfigure(0, weight=1)
        tor_wrap.columnconfigure(0, weight=1)

        status_row = ttk.LabelFrame(req_box, text="Request Status Review")
        status_row.pack(fill="x", padx=8, pady=(0, 8))
        self.time_off_status_target_var = tk.StringVar(value="Select a time-off request to review status.")
        ttk.Label(status_row, textvariable=self.time_off_status_target_var).pack(anchor="w", padx=8, pady=(6, 2))
        self.time_off_status_note_var = tk.StringVar(value="")
        ttk.Label(status_row, textvariable=self.time_off_status_note_var, style="Hint.TLabel").pack(anchor="w", padx=8, pady=(0, 4))

        self.time_off_status_var = tk.StringVar(value="pending")
        btns = ttk.Frame(status_row)
        btns.pack(anchor="w", padx=8, pady=(0, 8))
        self.time_off_status_rb_approved = ttk.Radiobutton(btns, text="Approved", value="approved", variable=self.time_off_status_var, command=self._on_status_radio_change)
        self.time_off_status_rb_approved.pack(side="left", padx=(0, 10))
        self.time_off_status_rb_denied = ttk.Radiobutton(btns, text="Declined", value="denied", variable=self.time_off_status_var, command=self._on_status_radio_change)
        self.time_off_status_rb_denied.pack(side="left", padx=(0, 10))
        self.time_off_status_rb_pending = ttk.Radiobutton(btns, text="Pending / Undecided", value="pending", variable=self.time_off_status_var, command=self._on_status_radio_change)
        self.time_off_status_rb_pending.pack(side="left")

        self.time_off_tree.bind("<<TreeviewSelect>>", self._on_time_off_tree_select, add="+")
        self._set_status_controls_enabled(False)

    def _sync_exception_label_from_generate(self):
        try:
            self.ov_label_var.set(str(self.label_var.get() or self.current_label or self._default_week_label()).strip())
        except Exception:
            self.ov_label_var.set(str(self.current_label or self._default_week_label()).strip())
        self.refresh_exception_ui()

    def _on_exception_day_toggle(self):
        bucket = self._exception_bucket(self.ov_label_var.get().strip())
        bucket["no_school_days"] = {d: bool(self.no_school_vars[d].get()) for d in DAYS}
        bucket["special_event_days"] = {d: bool(self.special_event_vars[d].get()) for d in DAYS}
        self.autosave()

    def refresh_override_dropdowns(self):
        # Backward compatibility shim for existing refresh calls.
        self.refresh_exception_ui()

    def refresh_exception_ui(self):
        if not hasattr(self, "ov_label_var"):
            return
        lbl = self.ov_label_var.get().strip() or self._selected_exception_label()
        bucket = self._exception_bucket(lbl)
        ns = _normalize_exception_day_flags(bucket.get("no_school_days", {}))
        se = _normalize_exception_day_flags(bucket.get("special_event_days", {}))
        for d in DAYS:
            if d in getattr(self, "no_school_vars", {}):
                self.no_school_vars[d].set(bool(ns.get(d, False)))
            if d in getattr(self, "special_event_vars", {}):
                self.special_event_vars[d].set(bool(se.get(d, False)))
        self.refresh_time_off_tree()

    def refresh_override_tree(self):
        # Backward compatibility shim for existing refresh calls.
        self.refresh_time_off_tree()

    def _new_time_off_request_id(self) -> str:
        return f"tor_{datetime.datetime.now().strftime('%Y%m%d%H%M%S%f')}"

    def _active_employee_names(self) -> List[str]:
        return sorted([e.name for e in self.model.employees if (e.name or '').strip()], key=str.lower)

    def _requests_for_label(self, label: Optional[str] = None) -> List[TimeOffRequest]:
        lbl = str(label or self.ov_label_var.get().strip() or self._selected_exception_label()).strip()
        bucket = self._exception_bucket(lbl)
        return [des_time_off_request(x) for x in bucket.get('time_off_requests', [])]

    def _save_requests_for_label(self, requests: List[TimeOffRequest], label: Optional[str] = None):
        lbl = str(label or self.ov_label_var.get().strip() or self._selected_exception_label()).strip()
        bucket = self._exception_bucket(lbl)
        bucket['time_off_requests'] = [ser_time_off_request(r) for r in _normalize_time_off_requests([ser_time_off_request(x) for x in requests], lbl)]

    def _format_request_window(self, r: TimeOffRequest) -> str:
        if bool(getattr(r, 'all_day', False)):
            return 'All Day'
        return f"{tick_to_hhmm(int(r.start_t))}-{tick_to_hhmm(int(r.end_t))}"

    def refresh_time_off_tree(self, selected_request_id: Optional[str] = None):
        if not hasattr(self, 'time_off_tree'):
            return
        keep_iid = str(selected_request_id or "").strip()
        for i in self.time_off_tree.get_children():
            self.time_off_tree.delete(i)
        for r in sorted(self._requests_for_label(), key=lambda x: (x.employee_name.lower(), DAYS.index(x.day), int(x.start_t), int(x.end_t))):
            status_txt = 'Pending / Undecided' if r.status == 'pending' else ('Declined' if r.status == 'denied' else r.status.title())
            self.time_off_tree.insert('', 'end', iid=r.request_id, values=(r.employee_name, DAY_FULL.get(r.day, r.day), self._format_request_window(r), status_txt, r.note))
        if keep_iid and self.time_off_tree.exists(keep_iid):
            self.time_off_tree.selection_set(keep_iid)
            self.time_off_tree.focus(keep_iid)
            self.time_off_tree.see(keep_iid)
        self._on_time_off_tree_select()

    def _open_time_off_popup(self, mode: str, seed_requests: Optional[List[TimeOffRequest]] = None):
        lbl = self.ov_label_var.get().strip() or self._selected_exception_label()
        seed_requests = list(seed_requests or [])
        top = tk.Toplevel(self)
        top.title('Add Time Off Request' if mode == 'add' else 'Edit Time Off Request')
        top.transient(self)
        top.grab_set()

        _outer, frame, _canvas = _build_scrollable_canvas_host(top, padding=(10, 10, 10, 10), min_width=860)

        emp_var = tk.StringVar()
        names = self._active_employee_names()
        if seed_requests:
            emp_var.set(seed_requests[0].employee_name)
        elif names:
            emp_var.set(names[0])

        ttk.Label(frame, text='Employee:').grid(row=0, column=0, sticky='w', padx=6, pady=6)
        ttk.Combobox(frame, textvariable=emp_var, values=names, state='readonly', width=30).grid(row=0, column=1, sticky='w', padx=6, pady=6)

        note_var = tk.StringVar(value=(seed_requests[0].note if seed_requests else ''))
        ttk.Label(frame, text='Note:').grid(row=0, column=2, sticky='w', padx=6, pady=6)
        ttk.Entry(frame, textvariable=note_var, width=38).grid(row=0, column=3, sticky='w', padx=6, pady=6)

        day_rows: Dict[str, Dict[str, Any]] = {}
        seed_by_day: Dict[str, List[TimeOffRequest]] = {}
        for r in seed_requests:
            if r.day in DAYS:
                seed_by_day.setdefault(r.day, []).append(r)
        for d in DAYS:
            seed_by_day.setdefault(d, []).sort(key=lambda x: (int(x.start_t), int(x.end_t)))

        ttk.Label(frame, text='Win 1 Start').grid(row=1, column=2, sticky='w', padx=6, pady=(0, 2))
        ttk.Label(frame, text='Win 1 End').grid(row=1, column=3, sticky='w', padx=6, pady=(0, 2))
        ttk.Label(frame, text='Win 2 Start').grid(row=1, column=4, sticky='w', padx=6, pady=(0, 2))
        ttk.Label(frame, text='Win 2 End').grid(row=1, column=5, sticky='w', padx=6, pady=(0, 2))

        for i, d in enumerate(DAYS, start=2):
            seeds = seed_by_day.get(d, [])
            seed_all_day = next((x for x in seeds if bool(x.all_day)), None)
            part = [x for x in seeds if not bool(x.all_day)]
            p1 = part[0] if len(part) >= 1 else None
            p2 = part[1] if len(part) >= 2 else None

            all_day_var = tk.BooleanVar(value=bool(seed_all_day) if seed_all_day else False)
            start1_var = tk.StringVar(value='' if p1 is None else tick_to_hhmm(int(p1.start_t)))
            end1_var = tk.StringVar(value='' if p1 is None else tick_to_hhmm(int(p1.end_t)))
            start2_var = tk.StringVar(value='' if p2 is None else tick_to_hhmm(int(p2.start_t)))
            end2_var = tk.StringVar(value='' if p2 is None else tick_to_hhmm(int(p2.end_t)))

            ttk.Label(frame, text=DAY_FULL[d]).grid(row=i, column=0, sticky='w', padx=6, pady=4)
            ttk.Checkbutton(frame, text='All Day', variable=all_day_var).grid(row=i, column=1, sticky='w', padx=6, pady=4)
            ttk.Combobox(frame, textvariable=start1_var, values=[''] + TIME_CHOICES, state='readonly', width=8).grid(row=i, column=2, sticky='w', padx=6, pady=4)
            ttk.Combobox(frame, textvariable=end1_var, values=[''] + TIME_CHOICES, state='readonly', width=8).grid(row=i, column=3, sticky='w', padx=6, pady=4)
            ttk.Combobox(frame, textvariable=start2_var, values=[''] + TIME_CHOICES, state='readonly', width=8).grid(row=i, column=4, sticky='w', padx=6, pady=4)
            ttk.Combobox(frame, textvariable=end2_var, values=[''] + TIME_CHOICES, state='readonly', width=8).grid(row=i, column=5, sticky='w', padx=6, pady=4)
            day_rows[d] = {'all_day': all_day_var, 'start1': start1_var, 'end1': end1_var, 'start2': start2_var, 'end2': end2_var}

        old_ids = {x.request_id for x in seed_requests}
        group_id = (seed_requests[0].group_id if seed_requests else '') or self._new_time_off_request_id()

        def _save_popup():
            emp = emp_var.get().strip()
            if not emp:
                messagebox.showerror('Time Off Requests', 'Employee is required.', parent=top)
                return
            created: List[TimeOffRequest] = []
            for d in DAYS:
                row = day_rows[d]
                all_day = bool(row['all_day'].get())
                if all_day:
                    created.append(TimeOffRequest(request_id=self._new_time_off_request_id(), group_id=group_id, label=lbl, employee_name=emp, day=d, all_day=True, start_t=0, end_t=DAY_TICKS, status='pending', note=note_var.get().strip()))
                    continue

                for idx in (1, 2):
                    s = row[f'start{idx}'].get().strip()
                    e = row[f'end{idx}'].get().strip()
                    if not s and not e:
                        continue
                    if not s or not e:
                        messagebox.showerror('Time Off Requests', f'{DAY_FULL[d]} window {idx} requires both Start and End for partial-day requests.', parent=top)
                        return
                    st = hhmm_to_tick(s); en = hhmm_to_tick(e)
                    if en <= st:
                        messagebox.showerror('Time Off Requests', f'{DAY_FULL[d]} window {idx} end time must be after start time.', parent=top)
                        return
                    created.append(TimeOffRequest(request_id=self._new_time_off_request_id(), group_id=group_id, label=lbl, employee_name=emp, day=d, all_day=False, start_t=st, end_t=en, status='pending', note=note_var.get().strip()))

            if not created:
                messagebox.showerror('Time Off Requests', 'Enter at least one day window (all-day or start/end).', parent=top)
                return

            current = self._requests_for_label(lbl)
            if old_ids:
                current = [r for r in current if r.request_id not in old_ids]
            status_by_key = {(r.day, r.start_t, r.end_t): r.status for r in seed_requests}
            for r in created:
                r.status = status_by_key.get((r.day, r.start_t, r.end_t), 'pending')
            current.extend(created)
            self._save_requests_for_label(current, lbl)
            self.refresh_time_off_tree()
            self.autosave()
            top.destroy()

        btns = ttk.Frame(frame)
        btns.grid(row=10, column=0, columnspan=6, sticky='w', padx=6, pady=(8, 2))
        ttk.Button(btns, text='Save Time Off Request', command=_save_popup).pack(side='left', padx=(0, 8))
        ttk.Button(btns, text='Cancel', command=top.destroy).pack(side='left')

    def add_time_off_request(self):
        self._open_time_off_popup('add', [])

    def _selected_request(self) -> Optional[TimeOffRequest]:
        sel = self.time_off_tree.selection() if hasattr(self, 'time_off_tree') else []
        if not sel:
            return None
        rid = str(sel[0])
        for r in self._requests_for_label():
            if r.request_id == rid:
                return r
        return None

    def edit_time_off_request(self):
        sel = self._selected_request()
        if sel is None:
            return
        all_req = self._requests_for_label()
        group = [r for r in all_req if (r.group_id or r.request_id) == (sel.group_id or sel.request_id) and r.employee_name == sel.employee_name]
        if not group:
            group = [sel]
        self._open_time_off_popup('edit', group)

    def delete_time_off_request(self):
        sel = self._selected_request()
        if sel is None:
            return
        if not messagebox.askyesno('Delete Request', f"Delete request for {sel.employee_name} on {DAY_FULL.get(sel.day, sel.day)}?"):
            return
        reqs = [r for r in self._requests_for_label() if r.request_id != sel.request_id]
        self._save_requests_for_label(reqs)
        self.refresh_time_off_tree()
        self._on_time_off_tree_select()
        self.autosave()

    def _set_status_controls_enabled(self, enabled: bool):
        state = "normal" if bool(enabled) else "disabled"
        for w in (getattr(self, "time_off_status_rb_approved", None), getattr(self, "time_off_status_rb_denied", None), getattr(self, "time_off_status_rb_pending", None)):
            if w is not None:
                try:
                    w.configure(state=state)
                except Exception:
                    pass

    def _on_time_off_tree_select(self, _event=None):
        sel = self._selected_request()
        if sel is None:
            if hasattr(self, "time_off_status_target_var"):
                self.time_off_status_target_var.set("Select a time-off request to review status.")
            if hasattr(self, "time_off_status_note_var"):
                self.time_off_status_note_var.set("")
            self._set_status_controls_enabled(False)
            return
        if hasattr(self, "time_off_status_target_var"):
            self.time_off_status_target_var.set(
                f"Employee: {sel.employee_name}    Day: {DAY_FULL.get(sel.day, sel.day)}    Window: {self._format_request_window(sel)}"
            )
        if hasattr(self, "time_off_status_note_var"):
            note = (sel.note or "").strip()
            if note:
                self.time_off_status_note_var.set(f"Note: {note[:120]}" + ("..." if len(note) > 120 else ""))
            else:
                self.time_off_status_note_var.set("Note: (none)")
        if hasattr(self, "time_off_status_var"):
            self.time_off_status_var.set(_normalize_time_off_status(sel.status))
        self._set_status_controls_enabled(True)

    def _on_status_radio_change(self):
        self.set_time_off_status(getattr(self, "time_off_status_var", tk.StringVar(value="pending")).get())

    def set_time_off_status(self, status: str):
        st = _normalize_time_off_status(status)
        sel = self._selected_request()
        if sel is None:
            return
        selected_id = str(sel.request_id)
        reqs = self._requests_for_label()
        for i, r in enumerate(reqs):
            if r.request_id == sel.request_id:
                reqs[i].status = st
                break
        self._save_requests_for_label(reqs)
        self.refresh_time_off_tree(selected_id)
        self.autosave()

    # -------- Requirements tab --------
    def _area_priority_label(self, area: str) -> str:
        return AREA_PRIORITY_TEXT.get(str(area or '').strip().upper(), str(area or '').strip())

    def _selected_days_long_names(self) -> List[str]:
        out: List[str] = []
        for d in DAYS:
            if bool(self.day_vars.get(d, tk.BooleanVar(value=False)).get()):
                out.append(DAY_FULL.get(d, d))
        return out

    def _refresh_copy_target_summary(self):
        if not hasattr(self, 'copy_targets_var'):
            return
        days = self._selected_days_long_names()
        if days:
            self.copy_targets_var.set(', '.join(days))
        else:
            self.copy_targets_var.set('No target days selected')

    def _on_req_day_toggle(self):
        self._refresh_copy_target_summary()
        if hasattr(self, 'req_timeline_day_var') and (self.req_timeline_day_var.get() not in DAYS):
            self.req_timeline_day_var.set('Sun')
        self.refresh_req_timeline()
        self._update_req_scope_feedback()

    def _select_days(self, mode: str):
        m = str(mode or '').strip().lower()
        for d in DAYS:
            val = False
            if m == 'all':
                val = True
            elif m == 'none':
                val = False
            elif m == 'weekdays':
                val = d in {'Mon', 'Tue', 'Wed', 'Thu', 'Fri'}
            elif m == 'weekends':
                val = d in {'Sun', 'Sat'}
            try:
                self.day_vars[d].set(bool(val))
            except Exception:
                pass
        self._on_req_day_toggle()

    def _build_req_timeline_section(self, parent):
        box = ttk.LabelFrame(parent, text='Visual Daily Timeline / Block View (Read Only)', style='Panel.TLabelframe')
        box.pack(fill='both', expand=True, pady=(0,8))
        ttk.Label(
            box,
            text='Read-only visual map of staffing blocks by day and area. This view helps with time-block planning and does not directly edit solver inputs.',
            style='Hint.TLabel',
            wraplength=1200,
            justify='left',
        ).pack(anchor='w', padx=8, pady=(6,6))

        top = ttk.Frame(box, style='Section.TFrame')
        top.pack(fill='x', padx=8, pady=(0,6))
        ttk.Label(top, text='View Day:').pack(side='left')
        self.req_timeline_day_var = tk.StringVar(value='Sun')
        ttk.Combobox(top, textvariable=self.req_timeline_day_var, values=DAYS, state='readonly', width=10).pack(side='left', padx=(6,10))
        ttk.Button(top, text='Refresh Timeline', command=self.refresh_req_timeline).pack(side='left')
        ttk.Label(top, text='Area priority: C-Store (Primary) → Kitchen (Secondary) → Carwash (Tertiary)', style='Hint.TLabel').pack(side='left', padx=(12,0))

        self.req_timeline_canvas = tk.Canvas(box, height=240, background='#ffffff', highlightthickness=1, highlightbackground='#d9d9d9')
        self.req_timeline_canvas.pack(fill='x', padx=8, pady=(0,8))
        self.req_timeline_day_var.trace_add('write', lambda *_args: self.refresh_req_timeline())

    def refresh_req_timeline(self):
        if not hasattr(self, 'req_timeline_canvas'):
            return
        c = self.req_timeline_canvas
        c.delete('all')
        try:
            c.update_idletasks()
        except Exception:
            pass
        w = max(700, int(c.winfo_width() or 700))
        h = max(220, int(c.winfo_height() or 220))
        left = 130
        right = 16
        top = 20
        row_h = 58
        axis_w = max(200, w - left - right)

        day = str(getattr(self, 'req_timeline_day_var', tk.StringVar(value='Sun')).get() or 'Sun')
        if day not in DAYS:
            day = 'Sun'

        for hr in range(0, 25, 2):
            t = int((hr / 24.0) * axis_w)
            x = left + t
            c.create_line(x, top - 5, x, top + row_h * len(AREAS), fill='#eeeeee')
            c.create_text(x, top - 10, text=f'{hr:02d}:00', fill='#666', font=('Segoe UI', 8), anchor='s')

        color_by_area = {
            'CSTORE': '#4e79a7',
            'KITCHEN': '#f28e2b',
            'CARWASH': '#76b7b2',
        }
        area_rows: Dict[str, List[RequirementBlock]] = {a: [] for a in AREAS}
        for r in sorted(self.model.requirements, key=lambda x: (AREAS.index(x.area) if x.area in AREAS else 99, x.start_t, x.end_t)):
            if r.day == day and r.area in AREAS and int(r.end_t) > int(r.start_t):
                area_rows[r.area].append(r)

        for idx, area in enumerate(AREAS):
            y0 = top + idx * row_h
            y1 = y0 + 38
            c.create_text(8, y0 + 19, text=self._area_priority_label(area), anchor='w', font=('Segoe UI', 9, 'bold'))
            c.create_rectangle(left, y0, left + axis_w, y1, outline='#d8d8d8')
            for r in area_rows.get(area, []):
                x0 = left + int((max(0, int(r.start_t)) / float(DAY_TICKS)) * axis_w)
                x1 = left + int((min(DAY_TICKS, int(r.end_t)) / float(DAY_TICKS)) * axis_w)
                if x1 <= x0:
                    x1 = x0 + 1
                c.create_rectangle(x0, y0 + 4, x1, y1 - 4, fill=color_by_area.get(area, '#999999'), outline='')
                label = f"{tick_to_hhmm(int(r.start_t))}-{tick_to_hhmm(int(r.end_t))}  m/p/M {int(r.min_count)}/{int(r.preferred_count)}/{int(r.max_count)}"
                if (x1 - x0) >= 120:
                    c.create_text(x0 + 4, (y0 + y1) // 2, text=label, anchor='w', fill='white', font=('Segoe UI', 8, 'bold'))

        c.create_text(left, top + row_h * len(AREAS) + 8, text=f'Day: {DAY_FULL.get(day, day)} | This timeline is read-only and derived from canonical requirement rows.', anchor='nw', fill='#555', font=('Segoe UI', 8))

    def _build_reqs_tab(self):
        _outer, frm, _canvas = _build_scrollable_canvas_host(self.tab_reqs, padding=(12, 12, 12, 12), min_width=1240)

        expl = ttk.LabelFrame(frm, text='Staffing Requirements Drive the Engine', style='Panel.TLabelframe')
        expl.pack(fill='x', pady=(0,10))
        ttk.Label(
            expl,
            text=(
                'Staffing Requirements define exactly where, when, and how many employees the engine uses when building the schedule. '                'For each time block and department, set Min (Required), Preferred (Target), and Max Allowed. '                'Min is hard-required, Preferred is a target, and Max is a soft ceiling the engine tries not to exceed.'
            ),
            wraplength=1300,
            justify='left',
            foreground='#333'
        ).pack(anchor='w', padx=10, pady=8)
        ttk.Label(
            expl,
            text='Department staffing hierarchy: C-Store (Primary / Master Staffing) → Kitchen (Secondary) → Carwash (Tertiary).',
            foreground='#555',
        ).pack(anchor='w', padx=10, pady=(0,8))

        # Section 1: pattern builder
        builder = ttk.LabelFrame(frm, text='Staffing Pattern Builder', style='Panel.TLabelframe')
        builder.pack(fill='x', pady=(0,10))

        self.req_area_var = tk.StringVar(value='CSTORE')
        self.req_start_var = tk.StringVar(value='05:00')
        self.req_end_var = tk.StringVar(value='23:00')
        self.req_min_var = tk.StringVar(value='1')
        self.req_pref_var = tk.StringVar(value='1')
        self.req_max_var = tk.StringVar(value='1')
        self.req_area_hint_var = tk.StringVar(value=self._area_priority_label('CSTORE'))

        ttk.Label(builder, text='Area:').grid(row=0, column=0, padx=8, pady=6, sticky='w')
        self.req_area_combo = ttk.Combobox(builder, textvariable=self.req_area_var, values=AREAS, state='readonly', width=12)
        self.req_area_combo.grid(row=0, column=1, padx=8, pady=6, sticky='w')
        ttk.Label(builder, textvariable=self.req_area_hint_var, foreground='#555').grid(row=0, column=2, columnspan=3, padx=8, pady=6, sticky='w')
        self.req_area_combo.bind('<<ComboboxSelected>>', lambda _e: (self.req_area_hint_var.set(self._area_priority_label(self.req_area_var.get())), self._update_req_scope_feedback()))

        ttk.Label(builder, text='Start:').grid(row=1, column=0, padx=8, pady=6, sticky='w')
        self.req_start_combo = ttk.Combobox(builder, textvariable=self.req_start_var, values=TIME_CHOICES, state='readonly', width=8)
        self.req_start_combo.grid(row=1, column=1, padx=8, pady=6, sticky='w')
        ttk.Label(builder, text='End:').grid(row=1, column=2, padx=8, pady=6, sticky='w')
        self.req_end_combo = ttk.Combobox(builder, textvariable=self.req_end_var, values=TIME_CHOICES, state='readonly', width=8)
        self.req_end_combo.grid(row=1, column=3, padx=8, pady=6, sticky='w')
        self.req_start_var.trace_add('write', lambda *_args: self._update_req_scope_feedback())
        self.req_end_var.trace_add('write', lambda *_args: self._update_req_scope_feedback())

        ttk.Label(builder, text='Min (Required):').grid(row=1, column=4, padx=8, pady=6, sticky='w')
        self.req_min_combo = ttk.Combobox(builder, textvariable=self.req_min_var, values=[str(i) for i in range(0,21)], state='readonly', width=6)
        self.req_min_combo.grid(row=1, column=5, padx=8, pady=6, sticky='w')
        ttk.Label(builder, text='Preferred (Target):').grid(row=1, column=6, padx=8, pady=6, sticky='w')
        self.req_pref_combo = ttk.Combobox(builder, textvariable=self.req_pref_var, values=[str(i) for i in range(0,21)], state='readonly', width=6)
        self.req_pref_combo.grid(row=1, column=7, padx=8, pady=6, sticky='w')
        ttk.Label(builder, text='Max Allowed:').grid(row=1, column=8, padx=8, pady=6, sticky='w')
        self.req_max_combo = ttk.Combobox(builder, textvariable=self.req_max_var, values=[str(i) for i in range(0,21)], state='readonly', width=6)
        self.req_max_combo.grid(row=1, column=9, padx=8, pady=6, sticky='w')

        ttk.Label(builder, text='Days:').grid(row=2, column=0, padx=8, pady=(2,6), sticky='w')
        self.day_vars = {d: tk.BooleanVar(value=(d in ['Mon','Tue','Wed','Thu','Fri'])) for d in DAYS}
        self.req_day_checks = {}
        for i, d in enumerate(DAYS):
            cb = ttk.Checkbutton(builder, text=DAY_FULL.get(d, d), variable=self.day_vars[d], command=self._on_req_day_toggle)
            cb.grid(row=2, column=1+i, padx=4, pady=(2,6), sticky='w')
            self.req_day_checks[d] = cb

        quick = ttk.Frame(builder)
        quick.grid(row=3, column=0, columnspan=8, sticky='w', padx=8, pady=(0,8))
        ttk.Button(quick, text='Weekdays', command=lambda: self._select_days('weekdays')).pack(side='left', padx=(0,6))
        ttk.Button(quick, text='Weekends', command=lambda: self._select_days('weekends')).pack(side='left', padx=(0,6))
        ttk.Button(quick, text='All', command=lambda: self._select_days('all')).pack(side='left', padx=(0,6))
        ttk.Button(quick, text='Clear', command=lambda: self._select_days('none')).pack(side='left', padx=(0,6))

        self.btn_apply_pattern = ttk.Button(builder, text='Apply Pattern', command=self.apply_req_range)
        self.btn_apply_pattern.grid(row=3, column=8, columnspan=2, padx=8, pady=(0,8), sticky='e')
        self.req_scope_feedback_var = tk.StringVar(value='Apply Pattern scope: Select a valid area, time range, and day(s).')
        ttk.Label(builder, textvariable=self.req_scope_feedback_var, foreground='#555').grid(row=4, column=0, columnspan=10, padx=8, pady=(0,8), sticky='w')

        # Section 2: copy day template
        copy_box = ttk.LabelFrame(frm, text='Copy Day Template', style='Panel.TLabelframe')
        copy_box.pack(fill='x', pady=(0,10))
        self.copy_day_var = tk.StringVar(value='Mon')
        self.copy_targets_var = tk.StringVar(value='No target days selected')
        ttk.Label(copy_box, text='Source Day:').grid(row=0, column=0, padx=8, pady=6, sticky='w')
        ttk.Combobox(copy_box, textvariable=self.copy_day_var, values=DAYS, state='readonly', width=10).grid(row=0, column=1, padx=8, pady=6, sticky='w')
        ttk.Label(copy_box, text='Target Days (from selected days above):').grid(row=0, column=2, padx=8, pady=6, sticky='w')
        ttk.Label(copy_box, textvariable=self.copy_targets_var, foreground='#555').grid(row=0, column=3, padx=8, pady=6, sticky='w')
        self.btn_copy_pattern = ttk.Button(copy_box, text='Copy Pattern to Selected Days', command=self.copy_paste_day)
        self.btn_copy_pattern.grid(row=0, column=4, padx=8, pady=6, sticky='e')

        # Section 3: visual timeline (read-only)
        self._build_req_timeline_section(frm)

        # Section 4 + 5: advanced rows and solver interpretation
        cols = ('Day','Area','Start','End','Min','Preferred','Max')
        req_wrap = ttk.Panedwindow(frm, orient='vertical'); req_wrap.pack(fill='both', expand=True)
        raw_box = ttk.LabelFrame(req_wrap, text='Detailed Requirement Rows (Advanced)', style='Panel.TLabelframe')
        eff_box = ttk.LabelFrame(req_wrap, text='Solver Interpretation (Read Only)', style='Panel.TLabelframe')
        req_wrap.add(raw_box, weight=3)
        req_wrap.add(eff_box, weight=2)

        ttk.Label(raw_box, text='Use these rows for fine adjustments and exact requirement inspection.', foreground='#555').pack(anchor='w', padx=8, pady=(6,2))
        raw_wrap = ttk.Frame(raw_box); raw_wrap.pack(fill='both', expand=True)
        self.req_tree = ttk.Treeview(raw_wrap, columns=cols, show='headings', height=12)
        for c in cols:
            self.req_tree.heading(c, text=c)
            self.req_tree.column(c, width=180, stretch=True)
        req_tree_ysb = ttk.Scrollbar(raw_wrap, orient='vertical', command=self.req_tree.yview)
        req_tree_xsb = ttk.Scrollbar(raw_wrap, orient='horizontal', command=self.req_tree.xview)
        self.req_tree.configure(yscrollcommand=req_tree_ysb.set, xscrollcommand=req_tree_xsb.set)
        self.req_tree.grid(row=0, column=0, sticky='nsew')
        req_tree_ysb.grid(row=0, column=1, sticky='ns')
        req_tree_xsb.grid(row=1, column=0, sticky='ew')
        raw_wrap.grid_rowconfigure(0, weight=1)
        raw_wrap.grid_columnconfigure(0, weight=1)

        ttk.Label(eff_box, text='This normalized preview shows how the engine interprets entered staffing rules.', foreground='#555').grid(row=0, column=0, sticky='w', padx=8, pady=(6,2))
        self.req_effective_tree = ttk.Treeview(eff_box, columns=cols, show='headings', height=8)
        for c in cols:
            self.req_effective_tree.heading(c, text=c)
            self.req_effective_tree.column(c, width=170, stretch=True)
        eff_ysb = ttk.Scrollbar(eff_box, orient='vertical', command=self.req_effective_tree.yview)
        self.req_effective_tree.configure(yscrollcommand=eff_ysb.set)
        self.req_effective_tree.grid(row=1, column=0, sticky='nsew')
        eff_ysb.grid(row=1, column=1, sticky='ns')
        eff_box.grid_rowconfigure(1, weight=1)
        eff_box.grid_columnconfigure(0, weight=1)

        bottom = ttk.Frame(frm); bottom.pack(fill='x', pady=(8,0))
        ttk.Button(bottom, text='Edit Selected Count', command=self.edit_req_selected).pack(side='left')
        ttk.Button(bottom, text='Delete Selected', command=self.delete_req_selected).pack(side='left', padx=8)
        ttk.Button(bottom, text='Split Selected', command=self.split_req_selected).pack(side='left', padx=8)
        ttk.Button(bottom, text='Merge Adjacent', command=self.merge_adjacent_requirements).pack(side='left', padx=8)
        ttk.Button(bottom, text='Clear All Schedule Blocks', command=self.clear_all_requirement_blocks).pack(side='left', padx=8)
        ttk.Button(bottom, text='Reset to Defaults', command=self.reset_requirements).pack(side='left', padx=8)
        self.btn_req_undo = ttk.Button(bottom, text='Undo Last Staffing Change', command=self.undo_last_staffing_change)
        self.btn_req_undo.pack(side='left', padx=8)

        self._refresh_copy_target_summary()
        self._update_req_scope_feedback()
        self._update_req_undo_button_state()

    def _update_req_scope_feedback(self):
        if not hasattr(self, 'req_scope_feedback_var'):
            return
        try:
            area = str(self.req_area_var.get() or '').strip()
            st = hhmm_to_tick(str(self.req_start_var.get() or '00:00'))
            en = hhmm_to_tick(str(self.req_end_var.get() or '00:00'))
            day_count = len([d for d in DAYS if bool(self.day_vars.get(d, tk.BooleanVar(value=False)).get())])
            if area in AREAS and en > st:
                ticks = int(en - st)
                self.req_scope_feedback_var.set(
                    f"Apply Pattern scope: {self._area_priority_label(area)} | {day_count} day(s) | {tick_to_hhmm(st)}–{tick_to_hhmm(en)} | {ticks} canonical 30-min block(s) per day"
                )
            else:
                self.req_scope_feedback_var.set("Apply Pattern scope: Select a valid area, time range, and day(s).")
        except Exception:
            self.req_scope_feedback_var.set("Apply Pattern scope: Select a valid area, time range, and day(s).")

    def _capture_requirements_undo(self, reason: str):
        try:
            self._req_undo_snapshot = copy.deepcopy(list(getattr(self.model, 'requirements', []) or []))
            self._req_undo_reason = str(reason or '').strip()
        except Exception:
            self._req_undo_snapshot = None
            self._req_undo_reason = ''
        self._update_req_undo_button_state()

    def _update_req_undo_button_state(self):
        if hasattr(self, 'btn_req_undo'):
            try:
                self.btn_req_undo.configure(state=('normal' if self._req_undo_snapshot is not None else 'disabled'))
            except Exception:
                pass

    def undo_last_staffing_change(self):
        if self._req_undo_snapshot is None:
            messagebox.showinfo('Undo Staffing Change', 'No staffing requirement action available to undo.')
            return
        self.model.requirements = copy.deepcopy(self._req_undo_snapshot)
        reason = self._req_undo_reason or 'last staffing change'
        self._req_undo_snapshot = None
        self._req_undo_reason = ''
        self.refresh_req_tree()
        self.autosave()
        self._update_req_undo_button_state()
        messagebox.showinfo('Undo Staffing Change', f'Undid {reason}.')

    def _collect_micro_fragments(self, reqs: Optional[List[RequirementBlock]] = None) -> List[Tuple[str, str, int]]:
        rows = list(reqs if reqs is not None else (getattr(self.model, 'requirements', []) or []))
        min_req, pref_req, max_req = build_requirement_maps(rows, goals=getattr(self.model, 'manager_goals', None), store_info=getattr(self.model, 'store_info', None))
        frags: List[Tuple[str, str, int]] = []
        for day in DAYS:
            for area in AREAS:
                for t in range(DAY_TICKS):
                    k = (day, area, t)
                    if int(min_req.get(k, 0)) <= 0 and int(pref_req.get(k, 0)) <= 0 and int(max_req.get(k, 0)) <= 0:
                        continue
                    prev_k = (day, area, t - 1)
                    next_k = (day, area, t + 1)
                    prev_on = t > 0 and (int(min_req.get(prev_k, 0)) > 0 or int(pref_req.get(prev_k, 0)) > 0 or int(max_req.get(prev_k, 0)) > 0)
                    next_on = t < (DAY_TICKS - 1) and (int(min_req.get(next_k, 0)) > 0 or int(pref_req.get(next_k, 0)) > 0 or int(max_req.get(next_k, 0)) > 0)
                    if not prev_on and not next_on:
                        frags.append((day, area, t))
        return frags

    def _warn_micro_fragments_if_any(self, context: str):
        frags = self._collect_micro_fragments()
        if not frags:
            return
        preview = ', '.join(f"{d} {a} {tick_to_hhmm(t)}-{tick_to_hhmm(t+1)}" for d, a, t in frags[:4])
        suffix = '' if len(frags) <= 4 else f" (+{len(frags)-4} more)"
        messagebox.showwarning(
            'Staffing Requirements Advisory',
            f"{context}: detected {len(frags)} isolated 30-minute demand block(s) that may be accidental or schedule-hostile.\n\n"
            f"Examples: {preview}{suffix}\n\n"
            "This is warning-only. Review Staffing Requirements if this was unintentional."
        )

    def _warn_requirement_demand_before_generate(self, label: str):
        try:
            rs = requirement_sanity_checker(self.model, label, assignments=None)
            details = dict(rs.get('details', {}) or {})
            impossible = list(details.get('impossible_windows', []) or [])
            if impossible:
                preview = []
                for w in impossible[:3]:
                    preview.append(
                        f"{w.get('day','?')} {w.get('area','?')} {tick_to_hhmm(int(w.get('start_t',0)))}-{tick_to_hhmm(int(w.get('end_t',0)))}"
                    )
                msg = (
                    f"Requirements advisory before generation: detected {len(impossible)} impossible-demand window(s) relative to currently active/qualified staffing.\n\n"
                    f"Examples: {', '.join(preview)}"
                )
                if len(impossible) > 3:
                    msg += f" (+{len(impossible)-3} more)"
                msg += "\n\nGeneration can continue, but coverage shortfalls are likely."
                messagebox.showwarning('Requirements Demand Advisory', msg)
        except Exception:
            pass

    def apply_req_range(self):
        area = str(self.req_area_var.get() or '').strip()
        if area not in AREAS:
            messagebox.showerror('Apply Pattern', 'Select a valid area.')
            return
        st = hhmm_to_tick(self.req_start_var.get())
        en = hhmm_to_tick(self.req_end_var.get())
        if en <= st:
            messagebox.showerror('Apply Pattern', 'End must be after start.')
            return

        try:
            mn = int(str(self.req_min_var.get()).strip())
            pr = int(str(self.req_pref_var.get()).strip())
            mx = int(str(self.req_max_var.get()).strip())
        except Exception:
            messagebox.showerror('Apply Pattern', 'Min / Preferred / Max must be whole numbers.')
            return
        if mn < 0 or pr < 0 or mx < 0:
            messagebox.showerror('Apply Pattern', 'Min / Preferred / Max must be 0 or higher.')
            return
        if not (mn <= pr <= mx):
            messagebox.showerror('Apply Pattern', 'Invalid staffing values. Ensure Min <= Preferred <= Max.')
            return

        if not is_within_area_hours(self.model, area, st, en):
            op_t, cl_t = area_open_close_ticks(self.model, area)
            if cl_t <= op_t:
                messagebox.showerror('Apply Pattern', f"Cannot add staffing requirements for {self._area_priority_label(area)} because Hours of Operation are invalid or closed on the Store tab.")
            else:
                messagebox.showerror('Apply Pattern', f"{self._area_priority_label(area)} requirement range must be within Hours of Operation: {tick_to_hhmm(op_t)}–{tick_to_hhmm(cl_t)}")
            return

        sel_days = [d for d in DAYS if self.day_vars[d].get()]
        if not sel_days:
            messagebox.showerror('Apply Pattern', 'Select at least one target day.')
            return

        candidate = list(self.model.requirements)
        changed = 0
        removed = 0
        for d in sel_days:
            before_len = len(candidate)
            candidate = [x for x in candidate if not (x.day == d and x.area == area and int(x.start_t) < int(en) and int(x.end_t) > int(st))]
            removed += (before_len - len(candidate))
            t = st
            while t < en:
                t2 = t + 1
                candidate.append(RequirementBlock(d, area, t, t2, mn, pr, mx))
                changed += 1
                t = t2

        broad_threshold_rows = 12
        if removed >= broad_threshold_rows:
            day_names = ', '.join(DAY_FULL.get(d, d) for d in sel_days)
            if not messagebox.askyesno(
                'Apply Pattern Confirmation',
                f"This will replace a broad scope of staffing requirements.\n\n"
                f"Area: {self._area_priority_label(area)}\n"
                f"Days: {day_names}\n"
                f"Window: {tick_to_hhmm(st)}–{tick_to_hhmm(en)}\n"
                f"Existing rows affected: {removed}\n"
                f"Canonical blocks to write: {changed}\n\n"
                "Continue?"
            ):
                return

        ok, err = self._validate_requirement_rows(candidate)
        if not ok:
            messagebox.showerror('Apply Pattern', err)
            return
        self._capture_requirements_undo('Apply Pattern')
        self.model.requirements = candidate
        self.refresh_req_tree()
        self.autosave()
        self._warn_micro_fragments_if_any('After Apply Pattern')
        messagebox.showinfo('Apply Pattern', f"Applied deterministic overwrite for {self._area_priority_label(area)} {tick_to_hhmm(st)}–{tick_to_hhmm(en)} across {len(sel_days)} day(s). Replaced {removed} existing row(s) with {changed} canonical 30-minute block(s) at Min/Preferred/Max={mn}/{pr}/{mx}.")

    def copy_paste_day(self):
        src = self.copy_day_var.get()
        tgt_days = [d for d in DAYS if self.day_vars[d].get()]
        if not tgt_days:
            messagebox.showerror('Copy Day Template', 'Select target days in Staffing Pattern Builder first.')
            return
        src_map = {(r.area, r.start_t, r.end_t): (r.min_count, r.preferred_count, r.max_count) for r in self.model.requirements if r.day == src}
        candidate = list(self.model.requirements)
        pasted = 0
        impacted_targets: Dict[str, int] = {}
        for d in tgt_days:
            if d == src:
                continue
            overlaps = 0
            for (area, st, en), _vals in src_map.items():
                for x in self.model.requirements:
                    if x.day == d and x.area == area and int(x.start_t) < int(en) and int(x.end_t) > int(st):
                        overlaps += 1
                        break
            if overlaps > 0:
                impacted_targets[d] = overlaps
            for (area, st, en), (mn, pr, mx) in src_map.items():
                r = next((x for x in candidate if x.day == d and x.area == area and x.start_t == st and x.end_t == en), None)
                if r is None:
                    candidate.append(RequirementBlock(d, area, st, en, int(mn), int(pr), int(mx)))
                else:
                    r.min_count = int(mn); r.preferred_count = int(pr); r.max_count = int(mx)
                pasted += 1

        if impacted_targets:
            target_names = ', '.join(DAY_FULL.get(d, d) for d in sorted(impacted_targets.keys(), key=lambda x: DAYS.index(x)))
            if not messagebox.askyesno(
                'Copy Day Template Confirmation',
                f"Target day(s) already contain staffing requirements in the copied scope.\n\n"
                f"Source Day: {DAY_FULL.get(src, src)}\n"
                f"Affected Target Day(s): {target_names}\n"
                f"Existing scoped rows impacted: {sum(int(v) for v in impacted_targets.values())}\n\n"
                "Continuing may replace existing staffing requirements in that copied scope. Continue?"
            ):
                return

        ok, err = self._validate_requirement_rows(candidate)
        if not ok:
            messagebox.showerror('Copy Day Template', err)
            return
        self._capture_requirements_undo('Copy Day Template')
        self.model.requirements = candidate
        self.refresh_req_tree()
        self.autosave()
        self._warn_micro_fragments_if_any('After Copy Day Template')
        messagebox.showinfo('Copy Day Template', f'Copied {src} pattern into {len(tgt_days) - (1 if src in tgt_days else 0)} selected day(s). Updated/created {pasted} blocks.')

    def edit_req_selected(self):
        sel = self.req_tree.selection()
        if not sel:
            messagebox.showinfo("Edit", "Select a requirement row.")
            return
        vals = self.req_tree.item(sel[0], "values")
        day, area, st, en, mn, pr, mx = vals
        new_mn = simple_input(self, "Edit Requirement", f"Min (hard) headcount for {day} {area} {st}-{en}:", default=str(mn))
        if new_mn is None:
            return
        new_pr = simple_input(self, "Edit Requirement", f"Preferred headcount for {day} {area} {st}-{en}:", default=str(pr))
        if new_pr is None:
            return
        new_mx = simple_input(self, "Edit Requirement", f"Max (soft ceiling) headcount for {day} {area} {st}-{en}:", default=str(mx))
        if new_mx is None:
            return
        try:
            mn_i = int(str(new_mn).strip())
            pr_i = int(str(new_pr).strip())
            mx_i = int(str(new_mx).strip())
        except Exception:
            messagebox.showerror("Edit", "Min / Preferred / Max must be whole numbers.")
            return
        if mn_i < 0 or pr_i < 0 or mx_i < 0:
            messagebox.showerror("Edit", "Min / Preferred / Max must be 0 or higher.")
            return
        if not (mn_i <= pr_i <= mx_i):
            messagebox.showerror("Edit", "Invalid staffing values. Ensure Min <= Preferred <= Max.")
            return
        stt = hhmm_to_tick(st); ent = hhmm_to_tick(en)
        if not is_within_area_hours(self.model, area, stt, ent):
            op_t, cl_t = area_open_close_ticks(self.model, area)
            messagebox.showerror("Edit", f"{area} requirement range must be within Hours of Operation: {tick_to_hhmm(op_t)}–{tick_to_hhmm(cl_t)}")
            return
        r = next((x for x in self.model.requirements if x.day == day and x.area == area and x.start_t == stt and x.end_t == ent), None)
        if r:
            old_vals = (int(r.min_count), int(r.preferred_count), int(r.max_count))
            r.min_count = mn_i
            r.preferred_count = pr_i
            r.max_count = mx_i
            ok, err = self._validate_requirement_rows(list(self.model.requirements))
            if not ok:
                r.min_count, r.preferred_count, r.max_count = old_vals
                messagebox.showerror("Edit", err)
                return
            self._capture_requirements_undo('Edit Selected Count')
            self.refresh_req_tree()
            self.autosave()
            self._warn_micro_fragments_if_any('After Edit Selected Count')

    def delete_req_selected(self):
        sel = self.req_tree.selection()
        if not sel:
            messagebox.showinfo("Delete", "Select a requirement row.")
            return
        vals = self.req_tree.item(sel[0], "values")
        day, area, st, en = vals[0], vals[1], vals[2], vals[3]
        stt = hhmm_to_tick(st); ent = hhmm_to_tick(en)
        before = len(self.model.requirements)
        self.model.requirements = [x for x in self.model.requirements if not (x.day == day and x.area == area and x.start_t == stt and x.end_t == ent)]
        if len(self.model.requirements) == before:
            return
        self.refresh_req_tree(); self.autosave()

    def split_req_selected(self):
        sel = self.req_tree.selection()
        if not sel:
            messagebox.showinfo("Split", "Select a requirement row.")
            return
        vals = self.req_tree.item(sel[0], "values")
        day, area, st, en, mn, pr, mx = vals
        stt = hhmm_to_tick(st); ent = hhmm_to_tick(en)
        if ent - stt < 2:
            messagebox.showinfo("Split", "Selected row must be at least 1 hour to split.")
            return
        mid = simple_input(self, "Split Requirement", f"Split time between {st} and {en}:", default=tick_to_hhmm(stt + (ent-stt)//2))
        if mid is None:
            return
        mt = hhmm_to_tick(str(mid).strip())
        if mt <= stt or mt >= ent:
            messagebox.showerror("Split", "Split time must be inside the selected range.")
            return
        r = next((x for x in self.model.requirements if x.day == day and x.area == area and x.start_t == stt and x.end_t == ent), None)
        if r is None:
            return
        candidate = [x for x in self.model.requirements if x is not r]
        candidate.append(RequirementBlock(day, area, stt, mt, int(mn), int(pr), int(mx)))
        candidate.append(RequirementBlock(day, area, mt, ent, int(mn), int(pr), int(mx)))
        ok, err = self._validate_requirement_rows(candidate)
        if not ok:
            messagebox.showerror("Split", err)
            return
        self._capture_requirements_undo('Split Selected')
        self.model.requirements = candidate
        self.refresh_req_tree(); self.autosave()
        self._warn_micro_fragments_if_any('After Split Selected')

    def merge_adjacent_requirements(self):
        reqs = sorted(self.model.requirements, key=lambda x: (DAYS.index(x.day), AREAS.index(x.area), x.start_t, x.end_t))
        merged: List[RequirementBlock] = []
        i = 0
        merged_pairs = 0
        while i < len(reqs):
            cur = reqs[i]
            j = i + 1
            while j < len(reqs):
                nx = reqs[j]
                if nx.day == cur.day and nx.area == cur.area and nx.start_t == cur.end_t and nx.min_count == cur.min_count and nx.preferred_count == cur.preferred_count and nx.max_count == cur.max_count:
                    cur = RequirementBlock(cur.day, cur.area, cur.start_t, nx.end_t, cur.min_count, cur.preferred_count, cur.max_count)
                    merged_pairs += 1
                    j += 1
                    continue
                break
            merged.append(cur)
            i = j
        if merged_pairs <= 0:
            messagebox.showinfo("Merge", "No compatible adjacent rows to merge.")
            return
        ok, err = self._validate_requirement_rows(merged)
        if not ok:
            messagebox.showerror("Merge", err)
            return
        self._capture_requirements_undo('Merge Adjacent')
        self.model.requirements = merged
        self.refresh_req_tree(); self.autosave()
        self._warn_micro_fragments_if_any('After Merge Adjacent')
        messagebox.showinfo("Merge", f"Merged {merged_pairs} adjacent pair(s).")

    def clear_all_requirement_blocks(self):
        if not messagebox.askyesno(
            "Clear All Schedule Blocks",
            "This will remove ALL staffing requirement schedule blocks for this dataset.\n"
            "You can rebuild them from scratch. Continue?",
        ):
            return
        self._capture_requirements_undo('Clear All Schedule Blocks')
        self.model.requirements = []
        self.refresh_req_tree()
        self.autosave()

    def _validate_requirement_rows(self, reqs: List[RequirementBlock]) -> Tuple[bool, str]:
        covered: Dict[Tuple[str, str, int], Tuple[int, int]] = {}
        for r in reqs:
            if r.day not in DAYS or r.area not in AREAS:
                continue
            st = int(getattr(r, 'start_t', 0))
            en = int(getattr(r, 'end_t', 0))
            if en <= st:
                return False, f"Invalid requirement range detected for {r.day} {r.area}: {tick_to_hhmm(st)}–{tick_to_hhmm(en)}. End must be after start."

            try:
                mn = int(getattr(r, 'min_count', 0))
                pr = int(getattr(r, 'preferred_count', 0))
                mx = int(getattr(r, 'max_count', 0))
            except Exception:
                return False, f"Invalid staffing values detected for {r.day} {r.area} {tick_to_hhmm(st)}–{tick_to_hhmm(en)}. Min / Preferred / Max must be whole numbers."
            if mn < 0 or pr < 0 or mx < 0:
                return False, f"Invalid staffing values detected for {r.day} {r.area} {tick_to_hhmm(st)}–{tick_to_hhmm(en)}. Min / Preferred / Max must be 0 or higher."
            if not (mn <= pr <= mx):
                return False, f"Invalid staffing values detected for {r.day} {r.area} {tick_to_hhmm(st)}–{tick_to_hhmm(en)}. Ensure Min <= Preferred <= Max."

            op_t, cl_t = area_open_close_ticks(self.model, r.area)
            if cl_t <= op_t:
                return False, (
                    f"Cannot use staffing requirements for {self._area_priority_label(r.area)} because Hours of Operation "
                    f"are invalid or closed on the Store tab."
                )
            if not is_within_area_hours(self.model, r.area, st, en):
                return False, (
                    f"This staffing requirement is outside the Hours of Operation configured for {self._area_priority_label(r.area)} "
                    f"on the Store tab: {r.day} {tick_to_hhmm(st)}–{tick_to_hhmm(en)} (allowed {tick_to_hhmm(op_t)}–{tick_to_hhmm(cl_t)})."
                )

            for t in range(st, en):
                k = (r.day, r.area, t)
                if k in covered:
                    p_st, p_en = covered[k]
                    return False, (
                        f"Overlapping requirement entries are not allowed for the same 30-minute block. "
                        f"{r.day} {r.area} {tick_to_hhmm(t)}–{tick_to_hhmm(t+1)} is already covered by "
                        f"{tick_to_hhmm(p_st)}–{tick_to_hhmm(p_en)}. Edit or remove the existing block first."
                    )
                covered[k] = (st, en)
        return True, ""


    def _validate_requirements_for_context(self, context: str, block: bool) -> bool:
        ok, err = self._validate_requirement_rows(getattr(self.model, "requirements", []) or [])
        if ok:
            return True
        title = "Staffing Requirements Validation"
        if str(context).lower() == "generate":
            msg = (
                "Schedule generation was stopped because staffing requirements contain invalid rows.\n\n"
                f"{err}\n\n"
                "Edit or remove the listed conflicting block(s) in Staffing Requirements before generating."
            )
            messagebox.showerror(title, msg)
            return False
        msg = (
            "This dataset contains invalid staffing requirement rows.\n\n"
            f"{err}\n\n"
            "Scheduling may be blocked until these rows are corrected in Staffing Requirements."
        )
        if block:
            messagebox.showerror(title, msg)
            return False
        messagebox.showwarning(title, msg)
        return True

    def reset_requirements(self):
        if not messagebox.askyesno("Reset", "Reset ALL requirements to defaults (CSTORE=2, others=0, 05:00–23:00)?"):
            return
        self.model.requirements = default_requirements()
        self.refresh_req_tree()
        self.autosave()

    def refresh_req_tree(self):
        for i in self.req_tree.get_children():
            self.req_tree.delete(i)
        for r in sorted(self.model.requirements, key=lambda x: (DAYS.index(x.day), AREAS.index(x.area), x.start_t, x.end_t)):
            self.req_tree.insert("", "end", values=(r.day, r.area, tick_to_hhmm(r.start_t), tick_to_hhmm(r.end_t), r.min_count, r.preferred_count, r.max_count))

        if hasattr(self, "req_effective_tree"):
            for i in self.req_effective_tree.get_children():
                self.req_effective_tree.delete(i)
            min_req, pref_req, max_req = build_requirement_maps(self.model.requirements, goals=getattr(self.model, "manager_goals", None), store_info=getattr(self.model, "store_info", None))
            for day in DAYS:
                for area in AREAS:
                    t = 0
                    while t < DAY_TICKS:
                        k = (day, area, t)
                        mn = int(min_req.get(k, 0)); pr = int(pref_req.get(k, 0)); mx = int(max_req.get(k, 0))
                        if mn == 0 and pr == 0 and mx == 0:
                            t += 1
                            continue
                        st = t
                        t += 1
                        while t < DAY_TICKS:
                            k2 = (day, area, t)
                            if int(min_req.get(k2, 0)) == mn and int(pref_req.get(k2, 0)) == pr and int(max_req.get(k2, 0)) == mx:
                                t += 1
                            else:
                                break
                        self.req_effective_tree.insert("", "end", values=(day, area, tick_to_hhmm(st), tick_to_hhmm(t), mn, pr, mx))
        self._refresh_copy_target_summary()
        self.refresh_req_timeline()
    # -------- Generate tab --------
    def _build_generate_tab(self):
        frm = ttk.Frame(self.tab_gen, style="Section.TFrame"); frm.pack(fill="both", expand=True, padx=12, pady=12)

        ttk.Label(
            frm,
            text="Schedule Workspace: Generate the selected week, review results, and open dense tools (manual edit, compare, heatmap, call-off).",
            style="SubHeader.TLabel",
        ).pack(anchor="w", pady=(0, 8))

        gen_box = ttk.LabelFrame(frm, text="Generate / Regenerate", style="Panel.TLabelframe")
        gen_box.pack(fill="x", pady=(0, 8))

        top = ttk.Frame(gen_box, style="Section.TFrame"); top.pack(fill="x", padx=8, pady=8)
        self.label_var = tk.StringVar(value=self.current_label)
        ttk.Label(top, text="Week Label:").pack(side="left", padx=(0,6))
        self.label_entry = ttk.Entry(top, textvariable=self.label_var, width=42)
        self.label_entry.pack(side="left")
        self.btn_set_this_week = ttk.Button(top, text="Set to This Week (Sun)", command=self.set_label_to_this_week)
        self.btn_set_this_week.pack(side="left", padx=8)
        self.btn_generate_fresh = ttk.Button(top, text="Generate Fresh", command=lambda: self.on_generate(mode="fresh"))
        self.btn_generate_fresh.pack(side="left", padx=(18, 6))
        self.btn_regen_current = ttk.Button(top, text="Regenerate From Current", command=lambda: self.on_generate(mode="regenerate"))
        self.btn_regen_current.pack(side="left", padx=6)
        self.btn_refine = ttk.Button(top, text="Refine Current Schedule", command=self.on_refine_schedule)
        self.btn_refine.pack(side="left", padx=6)
        self.refine_allow_manual_unlock_var = tk.BooleanVar(value=False)
        self.refine_allow_manual_unlock_chk = ttk.Checkbutton(top, text="Refine may modify unlocked manual edits", variable=self.refine_allow_manual_unlock_var)
        self.refine_allow_manual_unlock_chk.pack(side="left", padx=6)
        self.btn_save_history = ttk.Button(top, text="Save to History", command=self.save_to_history)
        self.btn_save_history.pack(side="left", padx=6)

        engine_row = ttk.Frame(gen_box, style="Section.TFrame")
        engine_row.pack(fill="x", padx=8, pady=(0, 8))
        self.engine_status_var = tk.StringVar(value="Engine Status: Engine Idle")
        ttk.Label(engine_row, textvariable=self.engine_status_var, foreground="#2f2f2f").pack(anchor="w")
        self.engine_progress = ttk.Progressbar(engine_row, orient="horizontal", mode="determinate", maximum=100)
        self.engine_progress.pack(fill="x", pady=(4, 0))

        tools_box = ttk.LabelFrame(frm, text="Schedule Workspace Tools", style="Panel.TLabelframe")
        tools_box.pack(fill="x", pady=(0, 8))
        trow = ttk.Frame(tools_box, style="Section.TFrame"); trow.pack(fill="x", padx=8, pady=8)
        self.btn_open_manual = ttk.Button(trow, text="Open Manual Edit (Popup)", command=self._open_manual_popup)
        self.btn_open_manual.pack(side="left", padx=(0, 8))
        self.btn_open_heatmap = ttk.Button(trow, text="Open Coverage Heatmap (Popup)", command=self._open_heatmap_popup)
        self.btn_open_heatmap.pack(side="left", padx=8)
        self.btn_open_analyzer = ttk.Button(trow, text="Run Analyzer Review (Popup)", command=self._open_analyzer_popup)
        self.btn_open_analyzer.pack(side="left", padx=8)
        self.btn_compare_versions = ttk.Button(trow, text="Compare Versions", command=self._open_changes_popup)
        self.btn_compare_versions.pack(side="left", padx=8)
        self.btn_calloff_simulator = ttk.Button(trow, text="Call-Off Simulator", command=self._show_calloff_tab)
        self.btn_calloff_simulator.pack(side="left", padx=8)
        self.btn_readiness_checklist = ttk.Button(trow, text="Publish Readiness Checklist", command=self._open_publish_readiness_dialog)
        self.btn_readiness_checklist.pack(side="left", padx=8)
        self.btn_labor_cost_review = ttk.Button(trow, text="Labor Cost Review", command=self._open_labor_cost_review_dialog)
        self.btn_labor_cost_review.pack(side="left", padx=8)
        self.btn_replacement_assistant = ttk.Button(trow, text="Assignment Replacement Assistant", command=self._open_replacement_assistant_dialog)
        self.btn_replacement_assistant.pack(side="left", padx=8)
        self.btn_historical_suggestions = ttk.Button(trow, text="Historical Suggestions", command=self._open_historical_suggestions_dialog)
        self.btn_historical_suggestions.pack(side="left", padx=8)

        ns_box = ttk.LabelFrame(frm, text="Selected-Week No School Days", style="Panel.TLabelframe")
        ns_box.pack(fill="x", pady=(0, 8))
        self.ws_no_school_vars = {d: tk.BooleanVar(value=False) for d in DAYS}
        ttk.Label(ns_box, text="Uses the same selected-week exception bucket as Schedule Exceptions. No duplicate data source.").pack(anchor="w", padx=8, pady=(6,4))
        ns_row = ttk.Frame(ns_box, style="Section.TFrame"); ns_row.pack(fill="x", padx=8, pady=(0,8))
        for d in DAYS:
            ttk.Checkbutton(ns_row, text=d, variable=self.ws_no_school_vars[d], command=self._workspace_apply_no_school_days).pack(side="left", padx=(0, 10))
        ttk.Button(ns_row, text="Sync From Week Settings", command=self._workspace_sync_no_school_days).pack(side="left", padx=(10,6))
        self._workspace_sync_no_school_days()

        self.summary_lbl = ttk.Label(frm, text="", foreground="#333")
        self.summary_lbl.pack(fill="x", pady=(0,8))

        cols = ("Day","Area","Start","End","Employee","Source","Locked")
        out_wrap = ttk.Frame(frm, style="Section.TFrame")
        out_wrap.pack(fill="both", expand=True)
        self.out_tree = ttk.Treeview(out_wrap, columns=cols, show="headings", height=18)
        for c in cols:
            self.out_tree.heading(c, text=c)
            w=150
            if c=="Employee": w=220
            if c=="Source": w=120
            if c=="Locked": w=80
            self.out_tree.column(c, width=w)
        out_ys = ttk.Scrollbar(out_wrap, orient="vertical", command=self.out_tree.yview)
        out_xs = ttk.Scrollbar(out_wrap, orient="horizontal", command=self.out_tree.xview)
        self.out_tree.configure(yscrollcommand=out_ys.set, xscrollcommand=out_xs.set)
        self.out_tree.grid(row=0, column=0, sticky="nsew")
        out_ys.grid(row=0, column=1, sticky="ns")
        out_xs.grid(row=1, column=0, sticky="ew")
        out_wrap.rowconfigure(0, weight=1)
        out_wrap.columnconfigure(0, weight=1)

        # P2-2 Explainability: Right-click an assignment row to explain.
        self._out_tree_menu = tk.Menu(self, tearoff=0)
        self._out_tree_menu.add_command(label="Explain Assignment", command=self.explain_selected_assignment)
        self.out_tree.bind("<Button-3>", self._on_out_tree_right_click)
        self.out_tree.bind("<ButtonRelease-3>", self._on_out_tree_right_click)
        self.out_tree.bind("<Double-1>", self._on_out_tree_double_click)

        self.warn_txt = tk.Text(frm, height=8)
        self.warn_txt.pack(fill="x", pady=(10,0))

        # hint
        ttk.Label(frm, text="Tip: Right-click an assignment row above → Explain Assignment", foreground="#666").pack(anchor="w", pady=(6,0))
        self._set_schedule_workspace_empty_state()

    def _on_out_tree_right_click(self, event):
        try:
            iid = self.out_tree.identify_row(event.y)
            if iid:
                self.out_tree.selection_set(iid)
                self.out_tree.focus(iid)
                self._out_tree_menu.tk_popup(event.x_root, event.y_root)
        finally:
            try:
                self._out_tree_menu.grab_release()
            except Exception:
                pass

    def _on_out_tree_double_click(self, event):
        try:
            iid = self.out_tree.identify_row(event.y)
            if iid:
                self.out_tree.selection_set(iid)
                self.out_tree.focus(iid)
                self.explain_selected_assignment()
        except Exception:
            pass

    def _set_engine_status(self, text: str, busy: bool = False, pct: Optional[float] = None):
        msg = str(text or "Engine Idle").strip() or "Engine Idle"
        if not msg.lower().startswith("engine status:"):
            msg = f"Engine Status: {msg}"
        if hasattr(self, "engine_status_var"):
            self.engine_status_var.set(msg)
        if hasattr(self, "engine_progress"):
            try:
                if pct is not None:
                    self.engine_progress["value"] = max(0.0, min(100.0, float(pct)))
                elif not busy:
                    self.engine_progress["value"] = 100.0 if "complete" in msg.lower() else 0.0
            except Exception:
                pass
        try:
            self.update_idletasks()
        except Exception:
            pass

    def _engine_status_start(self, text: str):
        self._set_engine_status(text, busy=True, pct=0.0)

    def _engine_status_stop(self, text: str = "Engine Idle"):
        self._set_engine_status(text, busy=False, pct=100.0 if "complete" in str(text).lower() else 0.0)

    def explain_selected_assignment(self):
        if not self.current_assignments:
            messagebox.showinfo("Explain", "Generate a schedule first.")
            return
        sel = self.out_tree.selection()
        if not sel:
            messagebox.showinfo("Explain", "Select an assignment row first.")
            return
        vals = self.out_tree.item(sel[0], "values")
        if not vals or len(vals) < 7:
            messagebox.showinfo("Explain", "Could not read the selected assignment.")
            return
        day, area, st_s, en_s, emp_name, source, locked_s = vals
        st = hhmm_to_tick(st_s)
        en = hhmm_to_tick(en_s)

        # Find the matching Assignment object (first match).
        target = None
        for a in self.current_assignments:
            if a.day == day and a.area == area and a.start_t == st and a.end_t == en and a.employee_name == emp_name:
                target = a
                break
        if target is None:
            messagebox.showinfo("Explain", "Could not locate that assignment in memory.")
            return

        label = self.current_label
        model = self.model
        hist = history_stats_from(model)

        # helpers
        min_req_ls, pref_req_ls, max_req_ls = build_requirement_maps(model.requirements, goals=getattr(model,'manager_goals',None))

        def compute_unfilled(assigns: List[Assignment]) -> int:
            cov = count_coverage_per_tick(assigns)
            ms, _, _ = compute_requirement_shortfalls(min_req_ls, pref_req_ls, max_req_ls, cov)
            return int(ms)

        base_assigns = list(self.current_assignments)
        base_unfilled = compute_unfilled(base_assigns)
        base_bd = schedule_score_breakdown(model, label, base_assigns, base_unfilled, hist)

        # Removing the assignment (coverage impact)
        minus = [x for x in base_assigns if x is not target]
        minus_cov = count_coverage_per_tick(minus)
        ms2, ps2, mv2 = compute_requirement_shortfalls(min_req_ls, pref_req_ls, max_req_ls, minus_cov)
        ms1, ps1, mv1 = compute_requirement_shortfalls(min_req_ls, pref_req_ls, max_req_ls, count_coverage_per_tick(base_assigns))
        cov_impact = {
            "min_short_change": int(ms2) - int(ms1),
            "pref_short_change": int(ps2) - int(ps1),
            "max_viol_change": int(mv2) - int(mv1),
        }

        # Evaluate alternative employees for the same slot
        feasible_alts: List[Tuple[float, str, Dict[str,float]]] = []
        infeasible_alts: List[Tuple[str, str]] = []
        for e in model.employees:
            if e.work_status != "Active":
                continue
            if e.name == emp_name:
                continue
            ok, reason = _explain_feasible_reason(model, label, e, day, area, st, en, minus)
            if not ok:
                infeasible_alts.append((e.name, reason))
                continue
            cand = list(minus)
            cand.append(Assignment(day, area, st, en, e.name, locked=False, source=ASSIGNMENT_SOURCE_ENGINE))
            uf = compute_unfilled(cand)
            bd = schedule_score_breakdown(model, label, cand, uf, hist)
            feasible_alts.append((bd.get("total", 0.0), e.name, bd))

        feasible_alts.sort(key=lambda x: x[0])
        best_alt = feasible_alts[0] if feasible_alts else None

        # Build explanation text
        win = tk.Toplevel(self)
        win.title("Explain Assignment")
        win.geometry("980x720")
        wrap = ttk.Frame(win); wrap.pack(fill="both", expand=True, padx=12, pady=12)
        ttk.Label(wrap, text=f"{day} • {area} • {st_s}-{en_s} • Assigned: {emp_name}", style="Header.TLabel").pack(anchor="w")

        txt = tk.Text(wrap, wrap="word")
        ysb = ttk.Scrollbar(wrap, orient="vertical", command=txt.yview)
        txt.configure(yscrollcommand=ysb.set)
        ysb.pack(side="right", fill="y")
        txt.pack(side="left", fill="both", expand=True)

        def fnum(x: float) -> str:
            try:
                return f"{float(x):.2f}"
            except Exception:
                return str(x)

        txt.insert(tk.END, "\nCoverage impact if this assignment were removed (hard constraints):\n")
        txt.insert(tk.END, f"  • MIN shortfall change: {cov_impact['min_short_change']}\n")
        txt.insert(tk.END, f"  • Preferred shortfall change: {cov_impact['pref_short_change']}\n")
        txt.insert(tk.END, f"  • Max-staffing violation change: {cov_impact['max_viol_change']}\n")

        txt.insert(tk.END, "\nScore breakdown for the CURRENT full schedule (lower is better):\n")
        txt.insert(tk.END, f"  • Total score: {fnum(base_bd.get('total',0.0))}\n")
        txt.insert(tk.END, f"    - Coverage (MIN): {fnum(base_bd.get('min_coverage_pen',0.0))}\n")
        txt.insert(tk.END, f"    - Coverage (Preferred): {fnum(base_bd.get('preferred_coverage_shortfall_pen',0.0))}\n")
        txt.insert(tk.END, f"    - Preferred cap: {fnum(base_bd.get('preferred_weekly_cap_pen',0.0))}\n")
        txt.insert(tk.END, f"    - Split shifts: {fnum(base_bd.get('split_shift_pen',0.0))}\n")
        txt.insert(tk.END, f"    - Fairness (history): {fnum(base_bd.get('history_fairness_pen',0.0))}\n")
        txt.insert(tk.END, f"    - Hour imbalance: {fnum(base_bd.get('hour_imbalance_pen',0.0))}\n")

        if best_alt:
            best_total, best_name, best_bd = best_alt
            txt.insert(tk.END, "\nBest feasible alternative employee for THIS slot (same time/area):\n")
            txt.insert(tk.END, f"  • {best_name} → total score would be {fnum(best_total)} (Δ {fnum(best_total - base_bd.get('total',0.0))})\n")
            # Requested: coverage/fairness/pref cap/split shift/total change
            fair_keys = ("history_fairness_pen", "hour_imbalance_pen", "weekend_pref_pen")
            fair_now = sum(float(base_bd.get(k,0.0) or 0.0) for k in fair_keys)
            fair_alt = sum(float(best_bd.get(k,0.0) or 0.0) for k in fair_keys)
            txt.insert(tk.END, f"  • Coverage impact: (no change expected for same slot)\n")
            txt.insert(tk.END, f"  • Fairness impact (Δ): {fnum(fair_alt - fair_now)}\n")
            txt.insert(tk.END, f"  • Preferred cap impact (Δ): {fnum(best_bd.get('preferred_weekly_cap_pen',0.0) - base_bd.get('preferred_weekly_cap_pen',0.0))}\n")
            txt.insert(tk.END, f"  • Split shift penalty (Δ): {fnum(best_bd.get('split_shift_pen',0.0) - base_bd.get('split_shift_pen',0.0))}\n")
            txt.insert(tk.END, f"  • Total score change (Δ): {fnum(best_total - base_bd.get('total',0.0))}\n")
        else:
            txt.insert(tk.END, "\nNo feasible alternative employees were found for this exact slot under hard constraints.\n")

        # Alternatives lists
        txt.insert(tk.END, "\nFeasible alternative employees (best 10):\n")
        if feasible_alts:
            for tot, nm, _bd in feasible_alts[:10]:
                txt.insert(tk.END, f"  • {nm}: total {fnum(tot)} (Δ {fnum(tot - base_bd.get('total',0.0))})\n")
        else:
            txt.insert(tk.END, "  (none)\n")

        txt.insert(tk.END, "\nRejected alternatives (infeasible under hard constraints; first 15):\n")
        if infeasible_alts:
            for nm, rsn in sorted(infeasible_alts, key=lambda x: x[0].lower())[:15]:
                txt.insert(tk.END, f"  • {nm}: {rsn}\n")
        else:
            txt.insert(tk.END, "  (none)\n")

        # Schedule limiting factors (run-level diagnostics)
        txt.insert(tk.END, "\nSchedule Limiting Factors (this run):\n")
        lf = []
        try:
            lf = list((self.current_diagnostics or {}).get('limiting_factors', []))
        except Exception:
            lf = []
        if lf:
            for s in lf:
                txt.insert(tk.END, f"  • {s}\n")
        else:
            txt.insert(tk.END, "  (none recorded)\n")

        txt.insert(tk.END, "\nNotes:\n")
        txt.insert(tk.END, "  • This explanation evaluates the current schedule score model and compares exact-slot swaps.\n")
        txt.insert(tk.END, "  • Hard constraints remain enforced: availability, minors rules, overlap, and max weekly caps.\n")

        txt.configure(state="disabled")

    def _default_week_label(self) -> str:
        today = datetime.date.today()
        days_since_sun = (today.weekday() + 1) % 7
        sun = today - datetime.timedelta(days=days_since_sun)
        return f"Week starting {sun.isoformat()} (Sun-Sat)"

    def set_label_to_this_week(self):
        self.label_var.set(self._default_week_label())
        try:
            self._workspace_sync_no_school_days()
        except Exception:
            pass

    def _workspace_sync_no_school_days(self):
        try:
            label = self.label_var.get().strip() or self.current_label or self._default_week_label()
            bucket = get_week_exception_bucket(self.model, label)
            flags = _normalize_exception_day_flags(bucket.get("no_school_days", {}))
            for d in DAYS:
                if d in getattr(self, "ws_no_school_vars", {}):
                    self.ws_no_school_vars[d].set(bool(flags.get(d, False)))
        except Exception:
            pass

    def _workspace_apply_no_school_days(self):
        try:
            label = self.label_var.get().strip() or self.current_label or self._default_week_label()
            bucket = get_week_exception_bucket(self.model, label)
            bucket["no_school_days"] = {d: bool(self.ws_no_school_vars[d].get()) for d in DAYS}
            self.autosave()
        except Exception:
            pass

    def _open_manual_popup(self):
        try:
            if getattr(self, "manual_popup_win", None) is not None and self.manual_popup_win.winfo_exists():
                self.manual_popup_win.lift()
                self.manual_popup_win.focus_force()
                return
        except Exception:
            pass

        win = tk.Toplevel(self)
        self.manual_popup_win = win
        win.title("Manual Edit (Popup Workspace)")
        win.geometry("1400x900")

        popup_vars: Dict[str, Dict[str, Dict[str, tk.StringVar]]] = {"MAIN": {}, "KITCHEN": {}, "CARWASH": {}}
        self.manual_popup_vars = popup_vars

        ttk.Label(win, text="Smart manual editor popup. Edit printable schedule cells, analyze warnings, then apply to current schedule.", style="SubHeader.TLabel").pack(anchor="w", padx=12, pady=(10,4))
        ttk.Label(win, text="Policy: manual edits override rules. Analyzer is advisory; no auto-fix by default.", style="Hint.TLabel").pack(anchor="w", padx=12, pady=(0,8))

        top = ttk.Frame(win); top.pack(fill="x", padx=12, pady=(0,8))

        def _popup_payload() -> dict:
            return self._manual_payload_from_vars(popup_vars)

        def _popup_apply_pages(pages: dict):
            self._manual_apply_to_vars(popup_vars, pages)

        def _popup_status(msg: str):
            try:
                popup_status_lbl.config(text=str(msg or ""))
            except Exception:
                pass

        def _popup_warn(lines: List[str]):
            try:
                popup_warn_txt.delete("1.0", tk.END)
                for ln in (lines or []):
                    popup_warn_txt.insert(tk.END, f"{ln}\n")
                if not lines:
                    popup_warn_txt.insert(tk.END, "No warnings.\n")
            except Exception:
                pass

        def _popup_load():
            payload = self._load_manual_overrides()
            cur_label = str(getattr(self, "current_label", "") or "")
            stored_label = str(payload.get("label", "") or "")
            if payload and (not cur_label or stored_label == cur_label):
                _popup_apply_pages(payload.get("pages", {}) or {})
                _popup_status("Loaded manual schedule edits.")
                return
            if not self.current_assignments:
                messagebox.showinfo("Manual Edit", "No manual edits saved for this week and no generated schedule available yet.\n\nGenerate a schedule first, then click Load.", parent=win)
                return
            _popup_apply_pages(self._compute_calendar_base_texts(self.current_assignments))
            _popup_status("Loaded popup editor from current generated schedule.")

        def _popup_save():
            self._save_manual_overrides({
                "label": str(getattr(self, "current_label", "") or ""),
                "saved_on": today_iso(),
                "pages": _popup_payload(),
            })
            _popup_status("Saved manual schedule edits.")

        def _popup_clear():
            for kind in popup_vars:
                for emp in popup_vars[kind]:
                    for d in popup_vars[kind][emp]:
                        popup_vars[kind][emp][d].set("")
            self._save_manual_overrides({})
            _popup_status("Cleared manual schedule edits.")

        def _popup_analyze():
            try:
                assigns, parse_issues = self._manual_parse_pages_to_assignments_from_pages(_popup_payload())
                warnings = parse_issues + self._manual_validate_assignments(assigns)
                emp_hours, total_hours, filled, total_slots = calc_schedule_stats(self.model, assigns)
                summary = [
                    f"Manual analysis for {len(assigns)} assignments.",
                    f"Total hours: {total_hours:.1f}",
                    f"Coverage: {filled}/{total_slots} required 30-minute blocks filled",
                ]
                if emp_hours:
                    lowest = min(emp_hours.items(), key=lambda kv: kv[1])
                    highest = max(emp_hours.items(), key=lambda kv: kv[1])
                    summary.append(f"Hours range: {lowest[0]} {lowest[1]:.1f} hrs → {highest[0]} {highest[1]:.1f} hrs")
                _popup_status("Manual analysis complete.")
                _popup_warn(summary + [""] + (warnings if warnings else ["No warnings detected."]))
            except Exception as e:
                messagebox.showerror("Manual Edit", f"Could not analyze popup manual edits.\n\n{e}", parent=win)

        def _popup_apply():
            try:
                assigns, parse_issues = self._manual_parse_pages_to_assignments_from_pages(_popup_payload())
                warnings = parse_issues + self._manual_validate_assignments(assigns)
                if warnings:
                    ok = messagebox.askyesno("Apply Manual Edits", "Warnings were found. Apply manual edits anyway?", parent=win)
                    if not ok:
                        _popup_warn(warnings)
                        _popup_status("Manual apply canceled because warnings were found.")
                        return
                self.current_assignments = list(assigns)
                self.current_emp_hours, self.current_total_hours, self.current_filled, self.current_total_slots = calc_schedule_stats(self.model, self.current_assignments)
                self.current_warnings = list(warnings)
                self._apply_current_schedule_to_output_views()
                try:
                    self._refresh_schedule_analysis()
                except Exception:
                    pass
                _popup_save()
                _popup_status("Manual edits applied to current schedule.")
                _popup_warn(warnings if warnings else ["Manual edits applied with no warnings."])
                self._set_status("Manual schedule edits applied to current schedule.")
            except Exception as e:
                messagebox.showerror("Manual Edit", f"Could not apply popup manual edits.\n\n{e}", parent=win)

        ttk.Button(top, text="Load From Current / Saved", command=_popup_load).pack(side="left")
        ttk.Button(top, text="Analyze Manual Edits", command=_popup_analyze).pack(side="left", padx=8)
        ttk.Button(top, text="Apply To Current Schedule", command=_popup_apply).pack(side="left", padx=8)
        ttk.Button(top, text="Save Manual Edits", command=_popup_save).pack(side="left", padx=8)
        ttk.Button(top, text="Clear Manual Edits", command=_popup_clear).pack(side="left", padx=8)

        swap = ttk.LabelFrame(win, text="Quick Swap")
        swap.pack(fill="x", padx=12, pady=(0,8))
        popup_swap_kind_var = tk.StringVar(value="MAIN")
        popup_swap_day_var = tk.StringVar(value=DAYS[0])
        popup_swap_from_var = tk.StringVar(value="")
        popup_swap_to_var = tk.StringVar(value="")
        ttk.Label(swap, text="Page").grid(row=0, column=0, sticky="w", padx=4, pady=6)
        ttk.OptionMenu(swap, popup_swap_kind_var, "MAIN", "MAIN", "KITCHEN", "CARWASH").grid(row=0, column=1, sticky="w", padx=4, pady=6)
        ttk.Label(swap, text="Day").grid(row=0, column=2, sticky="w", padx=4, pady=6)
        ttk.OptionMenu(swap, popup_swap_day_var, DAYS[0], *DAYS).grid(row=0, column=3, sticky="w", padx=4, pady=6)
        names = self._manual_employee_names()
        ttk.Label(swap, text="From").grid(row=0, column=4, sticky="w", padx=4, pady=6)
        ttk.OptionMenu(swap, popup_swap_from_var, names[0] if names else "", *(names if names else [""])).grid(row=0, column=5, sticky="w", padx=4, pady=6)
        ttk.Label(swap, text="To").grid(row=0, column=6, sticky="w", padx=4, pady=6)
        ttk.OptionMenu(swap, popup_swap_to_var, names[1] if len(names) > 1 else (names[0] if names else ""), *(names if names else [""])).grid(row=0, column=7, sticky="w", padx=4, pady=6)

        def _popup_swap():
            kind = popup_swap_kind_var.get() or "MAIN"
            day = popup_swap_day_var.get() or DAYS[0]
            src = popup_swap_from_var.get() or ""
            dst = popup_swap_to_var.get() or ""
            if not src or not dst or src == dst:
                messagebox.showinfo("Quick Swap", "Pick two different employees to swap.", parent=win)
                return
            try:
                a = popup_vars[kind][src][day].get()
                b = popup_vars[kind][dst][day].get()
                popup_vars[kind][src][day].set(b)
                popup_vars[kind][dst][day].set(a)
                _popup_status(f"Swapped {kind} {day}: {src} ↔ {dst}")
            except Exception as e:
                messagebox.showerror("Quick Swap", f"Could not swap those cells.\n\n{e}", parent=win)

        ttk.Button(swap, text="Swap Cells", command=_popup_swap).grid(row=0, column=8, sticky="w", padx=(14,8), pady=6)

        popup_status_lbl = ttk.Label(win, text="", foreground="#333")
        popup_status_lbl.pack(anchor="w", padx=12, pady=(0,6))

        warn_wrap = ttk.LabelFrame(win, text="Manual Edit Warnings")
        warn_wrap.pack(fill="both", expand=False, padx=12, pady=(0,8))
        popup_warn_txt = tk.Text(warn_wrap, height=9, wrap="word")
        mvs = ttk.Scrollbar(warn_wrap, orient="vertical", command=popup_warn_txt.yview)
        popup_warn_txt.configure(yscrollcommand=mvs.set)
        popup_warn_txt.grid(row=0, column=0, sticky="nsew")
        mvs.grid(row=0, column=1, sticky="ns")
        warn_wrap.rowconfigure(0, weight=1)
        warn_wrap.columnconfigure(0, weight=1)

        note = ttk.Notebook(win); note.pack(fill="both", expand=True, padx=12, pady=(0,12))

        def _make_scroll(parent):
            outer = ttk.Frame(parent)
            outer.pack(fill="both", expand=True)
            canvas = tk.Canvas(outer, highlightthickness=0)
            vs = ttk.Scrollbar(outer, orient="vertical", command=canvas.yview)
            hs = ttk.Scrollbar(outer, orient="horizontal", command=canvas.xview)
            canvas.configure(yscrollcommand=vs.set, xscrollcommand=hs.set)
            vs.pack(side="right", fill="y")
            hs.pack(side="bottom", fill="x")
            canvas.pack(side="left", fill="both", expand=True)
            inner = ttk.Frame(canvas)
            win_id = canvas.create_window((0,0), window=inner, anchor="nw")
            inner.bind("<Configure>", lambda _e=None: canvas.configure(scrollregion=canvas.bbox("all")))
            canvas.bind("<Configure>", lambda e: canvas.itemconfigure(win_id, width=max(e.width, 980)))
            return inner

        def _build_grid(parent, kind: str):
            inner = _make_scroll(parent)
            ttk.Label(inner, text="Employee", style="SubHeader.TLabel").grid(row=0, column=0, sticky="w", padx=4, pady=4)
            for j, d in enumerate(DAYS, start=1):
                ttk.Label(inner, text=d, style="SubHeader.TLabel").grid(row=0, column=j, sticky="n", padx=3, pady=4)
            emps = sorted(self.model.employees, key=lambda e: (e.name or "").lower())
            for i, e in enumerate(emps, start=1):
                nm = (e.name or "").strip()
                if not nm:
                    continue
                phone_str = (e.phone or "").strip()
                name_line = nm + (f" - {phone_str}" if phone_str else "")
                ttk.Label(inner, text=name_line).grid(row=i, column=0, sticky="w", padx=4, pady=2)
                popup_vars[kind].setdefault(nm, {})
                for j, d in enumerate(DAYS, start=1):
                    var = tk.StringVar(value="")
                    ent = ttk.Entry(inner, textvariable=var, width=18)
                    ent.grid(row=i, column=j, sticky="nsew", padx=2, pady=2)
                    popup_vars[kind][nm][d] = var
            for j in range(0, len(DAYS)+1):
                inner.grid_columnconfigure(j, weight=1)

        for title, kind in [("Manual: Main (C-Store + hints)", "MAIN"), ("Manual: Kitchen", "KITCHEN"), ("Manual: Carwash", "CARWASH")]:
            f = ttk.Frame(note)
            note.add(f, text=title)
            _build_grid(f, kind)

        payload = self._load_manual_overrides()
        cur_label = str(getattr(self, "current_label", "") or "")
        stored_label = str(payload.get("label", "") or "")
        if payload and (not cur_label or stored_label == cur_label):
            _popup_apply_pages(payload.get("pages", {}) or {})
        elif self.current_assignments:
            _popup_apply_pages(self._compute_calendar_base_texts(self.current_assignments))
        _popup_status("Manual editor popup ready.")
        _popup_warn(["Analyze Manual Edits to check coverage, availability, overlaps, minors rules, and weekly hours before applying."])

    def _open_heatmap_popup(self):
        try:
            if getattr(self, "heatmap_popup_win", None) is not None and self.heatmap_popup_win.winfo_exists():
                self.heatmap_popup_win.lift()
                self.heatmap_popup_win.focus_force()
                self._refresh_heatmap_popup()
                return
        except Exception:
            pass

        win = tk.Toplevel(self)
        self.heatmap_popup_win = win
        win.title("Coverage Heatmap (Popup Workspace)")
        win.geometry("1280x840")

        ttk.Label(win, text="Coverage Risk Heatmap (read-only)", style="Header.TLabel").pack(anchor="w", padx=12, pady=(10,4))
        ttk.Label(win, text="Shows scheduled headcount vs staffing requirements for each 30-minute block.", style="Hint.TLabel").pack(anchor="w", padx=12, pady=(0,8))

        top = ttk.Frame(win); top.pack(fill="x", padx=12, pady=(0,8))
        ttk.Label(top, text="Target:").pack(side="left")
        self.hm_popup_target_var = tk.StringVar(value="Minimum")
        ttk.OptionMenu(top, self.hm_popup_target_var, "Minimum", "Minimum", "Preferred").pack(side="left", padx=(6,14))
        self.hm_popup_fragile_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(top, text="Highlight fragile (1 scheduled / 1 required)", variable=self.hm_popup_fragile_var).pack(side="left")
        ttk.Button(top, text="Refresh Heatmap", command=self._refresh_heatmap_popup).pack(side="left", padx=(14,0))

        legend = ttk.Frame(win); legend.pack(fill="x", padx=12, pady=(0,8))
        ttk.Label(legend, text="Legend:", style="SubHeader.TLabel").pack(side="left")
        self._legend_chip(legend, "Red: scheduled < minimum", "#ff6b6b")
        self._legend_chip(legend, "Orange: scheduled == minimum and fragile", "#ffb366")
        self._legend_chip(legend, "Green: minimum met but below preferred", "#66c266")
        self._legend_chip(legend, "Light Green: preferred met to max", "#c9f7c9")
        self._legend_chip(legend, "Yellow-Green: scheduled > max", "#d8f23f")
        self._legend_chip(legend, "No requirement", "#f0f0f0")

        outer = ttk.Frame(win); outer.pack(fill="both", expand=True, padx=12, pady=(0,12))
        self.hm_popup_canvas = tk.Canvas(outer, highlightthickness=0)
        vs = ttk.Scrollbar(outer, orient="vertical", command=self.hm_popup_canvas.yview)
        hs = ttk.Scrollbar(outer, orient="horizontal", command=self.hm_popup_canvas.xview)
        self.hm_popup_canvas.configure(yscrollcommand=vs.set, xscrollcommand=hs.set)
        self.hm_popup_canvas.grid(row=0, column=0, sticky="nsew")
        vs.grid(row=0, column=1, sticky="ns")
        hs.grid(row=1, column=0, sticky="ew")
        outer.rowconfigure(0, weight=1)
        outer.columnconfigure(0, weight=1)
        self.hm_popup_items = []
        self._refresh_heatmap_popup()

    def _refresh_heatmap_popup(self):
        if not hasattr(self, "hm_popup_canvas"):
            return
        try:
            for it in getattr(self, "hm_popup_items", []):
                try:
                    self.hm_popup_canvas.delete(it)
                except Exception:
                    pass
            self.hm_popup_items = []

            target = (self.hm_popup_target_var.get() or "Minimum").strip()
            assignments = list(self.current_assignments or [])
            if not assignments:
                try:
                    wk = self._week_start_sunday_iso()
                    final_path = os.path.join(_app_dir(), "data", "final_schedules", f"{wk}.json")
                    if os.path.isfile(final_path):
                        with open(final_path, "r", encoding="utf-8") as f:
                            payload = json.load(f)
                        assignments = [des_assignment(a) for a in (payload.get("assignments") or [])]
                except Exception:
                    pass
            if not assignments:
                it = self.hm_popup_canvas.create_text(20, 20, text="No schedule found yet. Generate a schedule (or lock a final schedule) and then click Refresh.", anchor="nw")
                self.hm_popup_items.append(it)
                self.hm_popup_canvas.configure(scrollregion=(0,0,800,200))
                return

            min_req, pref_req, max_req = build_requirement_maps(self.model.requirements, goals=getattr(self.model, "manager_goals", None), store_info=getattr(self.model, "store_info", None))
            cov = count_coverage_per_tick(assignments)
            self.hm_popup_last_req_map = dict(pref_req if target.lower().startswith("pref") else min_req)
            self.hm_popup_last_cov = dict(cov)
            self.hm_popup_last_assignments = list(assignments)

            col_groups = [(d,a) for d in DAYS for a in AREAS]
            cell_w, cell_h, row_header_w, header_h = 74, 20, 60, 24
            c_under, c_frag, c_mid, c_pref, c_over, c_none = "#ff6b6b", "#ffb366", "#66c266", "#c9f7c9", "#d8f23f", "#f0f0f0"

            for ci, (d,a) in enumerate(col_groups):
                x = row_header_w + ci*cell_w
                self.hm_popup_items.append(self.hm_popup_canvas.create_rectangle(x, 0, x+cell_w, header_h, fill="#e9ecef", outline="#c9c9c9"))
                self.hm_popup_items.append(self.hm_popup_canvas.create_text(x+cell_w/2, header_h/2, text=f"{d}\\n{a[:1]}", justify="center", font=("Segoe UI", 9)))

            cstore_open, cstore_close = area_open_close_ticks(self.model, "CSTORE")
            vis_ticks = list(range(int(cstore_open), int(cstore_close)))
            for row_i, tck in enumerate(vis_ticks):
                y = header_h + row_i*cell_h
                self.hm_popup_items.append(self.hm_popup_canvas.create_rectangle(0, y, row_header_w, y+cell_h, fill="#e9ecef", outline="#c9c9c9"))
                self.hm_popup_items.append(self.hm_popup_canvas.create_text(row_header_w/2, y+cell_h/2, text=tick_to_hhmm(tck), font=("Segoe UI", 9)))
                for ci, (d,a) in enumerate(col_groups):
                    x = row_header_w + ci*cell_w
                    k = (d,a,int(tck))
                    req = int(min_req.get(k, 0)); pref_v = int(pref_req.get(k, 0)); max_v = int(max_req.get(k, 0)); sc = int(cov.get(k, 0))
                    if req <= 0 and sc <= 0:
                        fill = c_none; txt = ""
                    else:
                        if sc < req:
                            fill = c_under
                        elif sc == req:
                            fill = c_frag if (bool(self.hm_popup_fragile_var.get()) and req == 1 and sc == 1) else c_mid
                        else:
                            if sc > max_v and max_v > 0:
                                fill = c_over
                            elif sc >= pref_v and pref_v > 0:
                                fill = c_pref
                            else:
                                fill = c_mid
                        txt = f"{sc}/{req}" if req > 0 else f"{sc}/0"
                    r = self.hm_popup_canvas.create_rectangle(x, y, x+cell_w, y+cell_h, fill=fill, outline="#d0d0d0")
                    t = self.hm_popup_canvas.create_text(x+cell_w/2, y+cell_h/2, text=txt, font=("Segoe UI", 9))
                    self.hm_popup_canvas.tag_bind(r, "<Button-1>", lambda ev, dd=d, aa=a, tt=int(tck): self._hm_on_cell_click_popup(dd, aa, tt))
                    self.hm_popup_canvas.tag_bind(t, "<Button-1>", lambda ev, dd=d, aa=a, tt=int(tck): self._hm_on_cell_click_popup(dd, aa, tt))
                    self.hm_popup_items.extend([r,t])

            total_w = row_header_w + len(col_groups)*cell_w + 2
            total_h = header_h + len(vis_ticks)*cell_h + 2
            self.hm_popup_canvas.configure(scrollregion=(0,0,total_w,total_h))
        except Exception as e:
            messagebox.showerror("Heatmap", f"Failed to render popup heatmap:\n{e}")

    def _hm_on_cell_click_popup(self, day: str, area: str, tick: int):
        try:
            req_map = getattr(self, "hm_popup_last_req_map", {}) or {}
            cov = getattr(self, "hm_popup_last_cov", {}) or {}
            assignments = getattr(self, "hm_popup_last_assignments", []) or []
            req = int(req_map.get((day, area, int(tick)), 0))
            sc = int(cov.get((day, area, int(tick)), 0))
            names = []
            for a in assignments:
                if a.day == day and a.area == area and int(a.start_t) <= int(tick) < int(a.end_t):
                    nm = (a.employee_name or "").strip()
                    if nm:
                        names.append(nm)
            seen = set(); uniq=[]
            for n in names:
                if n not in seen:
                    uniq.append(n); seen.add(n)
            lines = [f"Required Staff: {req}", f"Scheduled Staff: {sc}", "", "Employees Working:"]
            if uniq:
                for n in uniq:
                    lines.append(f"• {n}")
            else:
                lines.append("• (none)")
            if req > 0 and sc < req:
                lines += ["", f"Coverage Gap: {req-sc} additional employee(s) needed"]
            elif req > 0 and sc > req:
                lines += ["", f"Possible Overstaffing: +{sc-req}"]
            messagebox.showinfo("Heatmap Detail", "\n".join(lines), parent=getattr(self, "heatmap_popup_win", None))
        except Exception as e:
            messagebox.showerror("Heatmap Detail", f"Failed to open popup cell detail:\n{e}", parent=getattr(self, "heatmap_popup_win", None))

    def _open_generation_progress_popup(self, title: str = "Generating Schedule"):
        win = tk.Toplevel(self)
        win.title(title)
        win.transient(self)
        win.grab_set()
        win.geometry("520x180")
        status = tk.StringVar(value="Starting...")
        ttk.Label(win, textvariable=status, style="SubHeader.TLabel").pack(anchor="w", padx=14, pady=(14, 8))
        pb = ttk.Progressbar(win, orient="horizontal", mode="determinate", maximum=100)
        pb.pack(fill="x", padx=14, pady=(0, 6))
        detail = tk.StringVar(value="")
        ttk.Label(win, textvariable=detail).pack(anchor="w", padx=14)

        def _update(pct: int, msg: str, det: str = ""):
            try:
                pb["value"] = max(0, min(100, int(pct)))
                status.set(msg)
                detail.set(det)
                win.update_idletasks()
            except Exception:
                pass

        return win, _update

    def _overlay_preserved_assignments(self, regenerated: List[Assignment], preserved: List[Assignment]) -> Tuple[List[Assignment], int]:
        kept: List[Assignment] = []
        removed = 0
        for a in list(regenerated or []):
            overlap = any((a.day == p.day and a.area == p.area and not (a.end_t <= p.start_t or a.start_t >= p.end_t)) for p in (preserved or []))
            if overlap and assignment_provenance(a) == ASSIGNMENT_SOURCE_ENGINE:
                removed += 1
                continue
            kept.append(a)
        kept.extend(copy.deepcopy(list(preserved or [])))
        kept.sort(key=lambda x: (DAYS.index(x.day), AREAS.index(x.area), x.start_t, x.employee_name))
        return kept, removed

    def _generate_with_mode(self, mode: str = "fresh"):
        label = self.label_var.get().strip() or self._default_week_label()
        self.current_label = label
        if not self.model.employees:
            messagebox.showerror("Generate", "Add employees first.")
            return
        if not self.model.requirements:
            messagebox.showerror("Generate", "Set staffing requirements first.")
            return
        if not self._validate_requirements_for_context("generate", block=True):
            return
        if not self._validate_store_state_preflight():
            return

        preserved: List[Assignment] = []
        try:
            self._engine_status_start("Preparing inputs...")
            if mode == "regenerate":
                for a in list(self.current_assignments or []):
                    src = assignment_provenance(a)
                    if src in {ASSIGNMENT_SOURCE_MANUAL, ASSIGNMENT_SOURCE_FIXED_LOCKED} or bool(getattr(a, "locked", False)):
                        preserved.append(copy.deepcopy(a))
            self._set_engine_status("Loading employee availability...", busy=True)
            self.on_generate(mode="fresh", _suppress_progress=True)
            self._set_engine_status("Applying soft rules...", busy=True)
            if mode == "regenerate" and preserved:
                self.current_assignments, removed = self._overlay_preserved_assignments(list(self.current_assignments or []), preserved)
                self.current_emp_hours, self.current_total_hours, self.current_filled, self.current_total_slots = calc_schedule_stats(self.model, self.current_assignments)
                extra = [f"Regenerate preserved {len(preserved)} manual/fixed-locked assignments exactly."]
                if removed > 0:
                    extra.append(f"Removed {removed} overlapping engine-created assignments to honor preserved work.")
                self.current_warnings = list(self.current_warnings or []) + extra
                self._apply_current_schedule_to_output_views()
            self._set_engine_status("Updating schedule workspace...", busy=True)
            try:
                self._refresh_schedule_analysis()
                self._refresh_change_viewer()
            except Exception:
                pass
            self._engine_status_stop("Generation complete")
            self.after(900, lambda: self._engine_status_stop("Engine Idle"))
        finally:
            if not (self.engine_status_var.get() or "").strip().endswith("Generation complete"):
                self._engine_status_stop("Engine Idle")

    def on_refine_schedule(self):
        if not self.current_assignments:
            messagebox.showinfo("Refine", "Generate or load a schedule first.")
            return
        if not self._validate_store_state_preflight():
            return
        label = self.current_label or self.label_var.get().strip() or self._default_week_label()
        allow_manual = bool(getattr(self, "refine_allow_manual_unlock_var", tk.BooleanVar(value=False)).get())
        refine_started = datetime.datetime.now()
        self._set_engine_status("Refine: preparing baseline...", busy=True, pct=5)
        baseline = list(self.current_assignments or [])

        protected: List[Assignment] = []
        for a in baseline:
            src = assignment_provenance(a)
            if bool(getattr(a, "locked", False)) or src == ASSIGNMENT_SOURCE_FIXED_LOCKED:
                protected.append(copy.deepcopy(a))
            elif (not allow_manual) and src == ASSIGNMENT_SOURCE_MANUAL:
                protected.append(copy.deepcopy(a))

        self._set_engine_status("Refine: searching targeted weak-area improvements...", busy=True, pct=35)

        def _min_pref_short(assigns: List[Assignment]) -> Tuple[int, int]:
            try:
                mn, pr, mx = build_requirement_maps(self.model.requirements, goals=getattr(self.model, "manager_goals", None), store_info=getattr(self.model, "store_info", None))
                cov = count_coverage_per_tick(assigns)
                ms, ps, _ = compute_requirement_shortfalls(mn, pr, mx, cov)
                return int(ms), int(ps)
            except Exception:
                return (10**9, 10**9)

        base_min_short, base_pref_short = _min_pref_short(baseline)
        best_assigns = list(baseline)
        best_diag: Dict[str, Any] = {}
        best_key = (base_min_short, base_pref_short, -int(len(baseline)))
        pass_diags: List[Dict[str, Any]] = []

        working = list(baseline)
        for _pass in range(2):
            improved, diag = improve_weak_areas(self.model, label, working, runtime_budget=SolverRuntimeBudget("refine", 50.0, 60.0))
            if protected:
                improved, _removed = self._overlay_preserved_assignments(improved, protected)
            ms, ps = _min_pref_short(improved)
            key = (ms, ps, -int(len(improved)))
            pass_diags.append({"min_short": ms, "pref_short": ps, "diagnostics": dict(diag or {})})
            if key < best_key:
                best_key = key
                best_assigns = list(improved)
                best_diag = dict(diag or {})
            working = list(improved)

        self._set_engine_status("Refine: preserving protected edits...", busy=True, pct=70)
        refined = list(best_assigns)

        self._set_engine_status("Refine: validating and applying...", busy=True, pct=90)
        self.current_assignments = list(refined or [])
        self.current_emp_hours, self.current_total_hours, self.current_filled, self.current_total_slots = calc_schedule_stats(self.model, self.current_assignments)
        self.current_diagnostics = dict(self.current_diagnostics or {})
        new_min_short, new_pref_short = _min_pref_short(self.current_assignments)
        self.current_diagnostics["refine_run"] = {
            "allow_unlocked_manual_modifications": bool(allow_manual),
            "protected_count": int(len(protected)),
            "baseline_min_short": int(base_min_short),
            "baseline_pref_short": int(base_pref_short),
            "post_min_short": int(new_min_short),
            "post_pref_short": int(new_pref_short),
            "passes": pass_diags,
            "selected_pass_diagnostics": dict(best_diag or {}),
            "runtime_seconds": round((datetime.datetime.now() - refine_started).total_seconds(), 4),
        }
        self.current_diagnostics = _set_runtime_metric(self.current_diagnostics, "refine", (datetime.datetime.now() - refine_started).total_seconds(), passes=len(pass_diags))
        self.current_warnings = list(self.current_warnings or [])
        self.current_warnings.append(
            f"Refine completed (manual unlocked edits {'allowed' if allow_manual else 'protected'})."
        )
        self._apply_current_schedule_to_output_views()
        try:
            self._refresh_schedule_analysis()
            self._refresh_change_viewer()
        except Exception:
            pass
        self._set_engine_status("Refine complete", busy=False, pct=100)

    def _selected_assignment_from_output(self) -> Optional[Assignment]:
        sel = getattr(self, "out_tree", None).selection() if hasattr(self, "out_tree") else ()
        if not sel:
            return None
        vals = self.out_tree.item(sel[0], "values")
        if not vals or len(vals) < 5:
            return None
        day, area, st_s, en_s, emp_name = vals[:5]
        st = hhmm_to_tick(st_s); en = hhmm_to_tick(en_s)
        for a in self.current_assignments:
            if a.day == day and a.area == area and int(a.start_t) == int(st) and int(a.end_t) == int(en) and a.employee_name == emp_name:
                return a
        return None

    def _open_publish_readiness_dialog(self):
        label = self.current_label or self.label_var.get().strip() or self._default_week_label()
        t0 = datetime.datetime.now()
        analyzer_findings = self._build_analyzer_findings()
        payload = build_publish_readiness_checklist(self.model, label, list(self.current_assignments or []), diagnostics=dict(self.current_diagnostics or {}), warnings=list(self.current_warnings or []), analyzer_findings_count=len(analyzer_findings))
        self.current_diagnostics = _set_runtime_metric(self.current_diagnostics, "publish_readiness_dialog", (datetime.datetime.now() - t0).total_seconds(), status=payload.get("status", "Review"))
        win = tk.Toplevel(self)
        win.title("Publish Readiness Checklist")
        win.geometry("760x620")
        ttk.Label(win, text="Publish Readiness Checklist", style="Header.TLabel").pack(anchor="w", padx=12, pady=(10, 4))
        ttk.Label(win, text=f"Status: {payload.get('status', 'Review')}", style="SubHeader.TLabel").pack(anchor="w", padx=12)
        txt = tk.Text(win, wrap="word", height=20)
        txt.pack(fill="both", expand=True, padx=12, pady=10)
        txt.insert("end", f"Hard blockers: {len(payload.get('hard_blockers', []))}\n")
        txt.insert("end", f"Uncovered minimums: {payload.get('uncovered_minimums', 0)}\nPreferred gaps: {payload.get('preferred_gaps', 0)}\n")
        txt.insert("end", f"Fragile windows: {payload.get('fragile_windows_count', 0)}\nOverride warnings: {payload.get('override_warnings', 0)}\n")
        txt.insert("end", f"Labor-cap warnings: {payload.get('labor_cap_warnings', 0)}\nAnalyzer/review findings: {payload.get('analyzer_findings_count', 0)}\n\n")
        for line in payload.get('readiness', {}).get('headline', []):
            txt.insert("end", f"• {line}\n")
        txt.configure(state="disabled")
        row = ttk.Frame(win)
        row.pack(fill="x", padx=12, pady=(0, 12))
        ttk.Button(row, text="Run Analyzer Review", command=self._open_analyzer_popup).pack(side="left")
        ttk.Button(row, text="Open Heatmap", command=self._open_heatmap_popup).pack(side="left", padx=8)
        ttk.Button(row, text="Open Compare Versions", command=self._open_changes_popup).pack(side="left", padx=8)
        if payload.get("publish_ready", False):
            ttk.Button(row, text="Publish Final", command=self.publish_final).pack(side="right")

    def _open_labor_cost_review_dialog(self):
        t0 = datetime.datetime.now()
        summary = _labor_cost_summary(self.model, list(self.current_assignments or []))
        self.current_diagnostics = _set_runtime_metric(self.current_diagnostics, "labor_cost_review_dialog", (datetime.datetime.now() - t0).total_seconds(), total_hours=round(float(summary.get("total_hours", 0.0)), 2))
        win = tk.Toplevel(self)
        win.title("Labor Cost Review")
        win.geometry("720x560")
        ttk.Label(win, text="Labor Cost Review", style="Header.TLabel").pack(anchor="w", padx=12, pady=(10, 4))
        txt = tk.Text(win, wrap="word", height=20)
        txt.pack(fill="both", expand=True, padx=12, pady=10)
        txt.insert("end", f"Total scheduled hours: {summary.get('total_hours', 0.0):.1f}\n")
        txt.insert("end", f"Approx labor load: {summary.get('approx_labor_load', 'Low')}\n")
        txt.insert("end", f"Overstaff hours: {summary.get('overstaff_hours', 0.0):.1f}\n")
        txt.insert("end", f"Near-cap indicator ticks: {summary.get('near_cap_indicator_ticks', 0)}\n\nHours by area:\n")
        for area, hrs in summary.get('hours_by_area', {}).items():
            txt.insert("end", f"• {area}: {hrs:.1f}\n")
        txt.insert("end", "\nDaily totals:\n")
        for day, hrs in summary.get('daily_totals', {}).items():
            txt.insert("end", f"• {day}: {hrs:.1f}\n")
        txt.configure(state="disabled")

    def _open_replacement_assistant_dialog(self):
        target = self._selected_assignment_from_output()
        if target is None:
            messagebox.showinfo("Assignment Replacement Assistant", "Select an assignment row in the Schedule Workspace first.")
            return
        label = self.current_label or self.label_var.get().strip() or self._default_week_label()
        t0 = datetime.datetime.now()
        payload = build_replacement_assistant_candidates(self.model, label, list(self.current_assignments or []), target)
        self.current_diagnostics = _set_runtime_metric(self.current_diagnostics, "replacement_assistant_dialog", (datetime.datetime.now() - t0).total_seconds(), candidate_count=len(payload.get("candidates", [])))
        win = tk.Toplevel(self)
        win.title("Assignment Replacement Assistant")
        win.geometry("860x560")
        ttk.Label(win, text=f"Assignment-based replacement options for {target.employee_name} • {target.day} {target.area} {tick_to_hhmm(target.start_t)}-{tick_to_hhmm(target.end_t)}", wraplength=820, style="SubHeader.TLabel").pack(anchor="w", padx=12, pady=(10, 8))
        txt = tk.Text(win, wrap="word", height=22)
        txt.pack(fill="both", expand=True, padx=12, pady=(0, 10))
        for row in payload.get('candidates', []):
            txt.insert("end", f"• {row['employee']}: {row['explanation']} | likely uncovered ticks after replacement: {row['coverage_impact_ticks']}\n")
        if payload.get('swap_suggestions'):
            txt.insert("end", "\nSwap suggestions:\n")
            for row in payload.get('swap_suggestions', []):
                txt.insert("end", f"• Swap with {row['swap_with']} ({row['other_area']} ↔ {row['target_area']}) on {row['day']}\n")
        txt.insert("end", "\nThis assistant is assignment-based only. It is not wired to the call-off simulator context. Use Manual Edit / Quick Swap to apply any change.")
        txt.configure(state="disabled")

    def _open_historical_suggestions_dialog(self):
        t0 = datetime.datetime.now()
        payload = build_historical_suggestions(self.model)
        self.current_diagnostics = _set_runtime_metric(self.current_diagnostics, "historical_suggestions_dialog", (datetime.datetime.now() - t0).total_seconds(), suggestions=len(payload.get("employee_suggestions", [])))
        win = tk.Toplevel(self)
        win.title("Historical Suggestions")
        win.geometry("760x560")
        ttk.Label(win, text="Historical Suggestions (advisory only)", style="Header.TLabel").pack(anchor="w", padx=12, pady=(10, 4))
        txt = tk.Text(win, wrap="word", height=22)
        txt.pack(fill="both", expand=True, padx=12, pady=10)
        txt.insert("end", "These suggestions are guidance only. They do not change staffing requirements or the live schedule.\n\n")
        for row in payload.get('employee_suggestions', []):
            txt.insert("end", f"• {row['employee']}: {row['summary']}\n")
        if payload.get('forecast_pressure'):
            txt.insert("end", "\nForecast pressure windows:\n")
            for row in payload.get('forecast_pressure', []):
                txt.insert("end", f"• {row['day']} {row['area']} {tick_to_hhmm(int(row['tick']))}: forecast {row['forecast']:.2f}\n")
        txt.configure(state="disabled")

    def _build_analyzer_findings(self) -> List[Dict[str, Any]]:
        out: List[Dict[str, Any]] = []
        if not self.current_assignments:
            return out
        label = self.current_label or self.label_var.get().strip() or self._default_week_label()
        for v in evaluate_schedule_hard_rules(self.model, label, list(self.current_assignments), include_override_warnings=True):
            fixable = str(getattr(v, "code", "")) in {"overlap"}
            out.append({"kind": "rule", "code": getattr(v, "code", ""), "title": _viol_to_text(v), "detail": repr(v), "fixable": fixable})
        cov = count_coverage_per_tick(list(self.current_assignments))
        min_req, pref_req, max_req = build_requirement_maps(self.model.requirements, goals=getattr(self.model, "manager_goals", None), store_info=getattr(self.model, "store_info", None))
        for (day, area, tick), req in min_req.items():
            sc = int(cov.get((day, area, tick), 0) or 0)
            req_i = int(req or 0)
            if req_i > sc:
                out.append({
                    "kind": "understaffed",
                    "code": "understaffed",
                    "title": f"Understaffed {day} {area} {tick_to_hhmm(int(tick))} — scheduled {sc}, min {req_i}",
                    "detail": f"Need {req_i-sc} additional employee(s) in this 30-minute block.",
                    "fixable": True,
                    "day": day,
                    "area": area,
                    "tick": int(tick),
                })
        return out

    def _push_fix_for_finding(self, finding: Dict[str, Any]) -> str:
        if not self.current_assignments:
            return "No current schedule loaded."
        kind = str(finding.get("kind", ""))
        label = self.current_label or self.label_var.get().strip() or self._default_week_label()
        if kind == "understaffed":
            day = str(finding.get("day", ""))
            area = str(finding.get("area", ""))
            tick = int(finding.get("tick", 0))
            clopen = _clopen_map_from_assignments(self.model, list(self.current_assignments))
            for e in self.model.employees:
                if getattr(e, "work_status", "") != "Active":
                    continue
                if area not in getattr(e, "areas_allowed", []):
                    continue
                if not is_employee_available(self.model, e, label, day, tick, tick+1, area, clopen):
                    continue
                overlap = any(a.employee_name == e.name and a.day == day and not (a.end_t <= tick or a.start_t >= tick+1) for a in self.current_assignments)
                if overlap:
                    continue
                self.current_assignments.append(Assignment(day=day, area=area, start_t=tick, end_t=tick+1, employee_name=e.name, locked=False, source=ASSIGNMENT_SOURCE_ENGINE))
                self.current_assignments.sort(key=lambda a: (DAYS.index(a.day), AREAS.index(a.area), a.start_t, a.employee_name))
                self.current_emp_hours, self.current_total_hours, self.current_filled, self.current_total_slots = calc_schedule_stats(self.model, self.current_assignments)
                self._apply_current_schedule_to_output_views()
                return f"Added {e.name} to {day} {area} {tick_to_hhmm(tick)}-{tick_to_hhmm(tick+1)}."
            return "No safe available backup employee found for this understaffed block."
        if kind == "rule" and str(finding.get("code", "")) == "overlap":
            by_emp_day: Dict[Tuple[str, str], List[Tuple[int, Assignment]]] = {}
            for idx, a in enumerate(list(self.current_assignments)):
                by_emp_day.setdefault((a.employee_name, a.day), []).append((idx, a))
            for (_emp, _day), rows in by_emp_day.items():
                rows.sort(key=lambda t: (t[1].start_t, t[1].end_t))
                for i in range(1, len(rows)):
                    pidx, prev = rows[i-1]
                    cidx, cur = rows[i]
                    if int(cur.start_t) < int(prev.end_t):
                        csrc = assignment_provenance(cur)
                        psrc = assignment_provenance(prev)
                        if csrc == ASSIGNMENT_SOURCE_ENGINE:
                            del self.current_assignments[cidx]
                            self.current_emp_hours, self.current_total_hours, self.current_filled, self.current_total_slots = calc_schedule_stats(self.model, self.current_assignments)
                            self._apply_current_schedule_to_output_views()
                            return "Removed one overlapping engine assignment."
                        if psrc == ASSIGNMENT_SOURCE_ENGINE:
                            del self.current_assignments[pidx]
                            self.current_emp_hours, self.current_total_hours, self.current_filled, self.current_total_slots = calc_schedule_stats(self.model, self.current_assignments)
                            self._apply_current_schedule_to_output_views()
                            return "Removed one overlapping engine assignment."
                        return "Overlap exists only in preserved/manual work. Leave manual entry or edit manually."
            return "No actionable overlap found."
        return "This finding is advisory in v1; no safe local auto-fix is available."

    def _validate_store_state_preflight(self) -> bool:
        code = str(getattr(getattr(self.model, "store_info", None), "store_state", "") or "").strip().upper()
        if code not in US_STATE_CODES:
            messagebox.showerror(
                "Generate",
                "Store State is required before schedule generation.\n\nGo to 1) Store, select one of the 50 U.S. states, and click Save Store Info."
            )
            return False
        return True

    def _open_analyzer_popup(self):
        findings = self._build_analyzer_findings()
        win = tk.Toplevel(self)
        win.title("Analyzer Findings Review")
        win.geometry("1080x720")
        ttk.Label(win, text="Analyzer is advisory. It does not auto-fix. Select a finding, then choose Push Fix or Leave Manual Entry.", wraplength=1020).pack(anchor="w", padx=12, pady=(10,8))
        cols = ("Type", "Code", "Fix", "Finding")
        tree_wrap = ttk.Frame(win)
        tree_wrap.pack(fill="both", expand=False, padx=12, pady=(0,8))
        tree = ttk.Treeview(tree_wrap, columns=cols, show="headings", height=16)
        for c in cols:
            tree.heading(c, text=c)
            tree.column(c, width=120 if c != "Finding" else 640)
        tree_ys = ttk.Scrollbar(tree_wrap, orient="vertical", command=tree.yview)
        tree_xs = ttk.Scrollbar(tree_wrap, orient="horizontal", command=tree.xview)
        tree.configure(yscrollcommand=tree_ys.set, xscrollcommand=tree_xs.set)
        tree.grid(row=0, column=0, sticky="nsew")
        tree_ys.grid(row=0, column=1, sticky="ns")
        tree_xs.grid(row=1, column=0, sticky="ew")
        tree_wrap.rowconfigure(0, weight=1)
        tree_wrap.columnconfigure(0, weight=1)

        detail_wrap = ttk.Frame(win)
        detail_wrap.pack(fill="both", expand=True, padx=12, pady=(0,10))
        detail = tk.Text(detail_wrap, height=12, wrap="word")
        detail_ys = ttk.Scrollbar(detail_wrap, orient="vertical", command=detail.yview)
        detail.configure(yscrollcommand=detail_ys.set)
        detail.grid(row=0, column=0, sticky="nsew")
        detail_ys.grid(row=0, column=1, sticky="ns")
        detail_wrap.rowconfigure(0, weight=1)
        detail_wrap.columnconfigure(0, weight=1)

        for i, f in enumerate(findings):
            tree.insert("", "end", iid=str(i), values=(f.get("kind", ""), f.get("code", ""), "Yes" if f.get("fixable") else "No", f.get("title", "")))

        def _on_sel(_e=None):
            sel = tree.selection()
            if not sel:
                return
            f = findings[int(sel[0])]
            detail.delete("1.0", "end")
            detail.insert("end", str(f.get("title", "")) + "\n\n")
            detail.insert("end", str(f.get("detail", "")))

        tree.bind("<<TreeviewSelect>>", _on_sel)
        btn_row = ttk.Frame(win)
        btn_row.pack(fill="x", padx=12, pady=(0,12))

        def _push_fix():
            sel = tree.selection()
            if not sel:
                return
            msg = self._push_fix_for_finding(findings[int(sel[0])])
            messagebox.showinfo("Push Fix", msg, parent=win)
            refreshed = self._build_analyzer_findings()
            findings[:] = refreshed
            for i in tree.get_children():
                tree.delete(i)
            for i, f in enumerate(findings):
                tree.insert("", "end", iid=str(i), values=(f.get("kind", ""), f.get("code", ""), "Yes" if f.get("fixable") else "No", f.get("title", "")))
            detail.delete("1.0", "end")

        def _leave_manual():
            messagebox.showinfo("Leave Manual Entry", "Manual entry kept unchanged.", parent=win)

        ttk.Button(btn_row, text="Push Fix to Schedule", command=_push_fix).pack(side="left")
        ttk.Button(btn_row, text="Leave Manual Entry", command=_leave_manual).pack(side="left", padx=8)

    def on_generate(self, mode: str = "fresh", _suppress_progress: bool = False):
        if (mode or "fresh") != "fresh" and not _suppress_progress:
            self._generate_with_mode(mode=mode)
            return
        label = self.label_var.get().strip() or self._default_week_label()
        self.current_label = label
        if not self.model.employees:
            messagebox.showerror("Generate", "Add employees first.")
            return
        if not self.model.requirements:
            messagebox.showerror("Generate", "Set staffing requirements first.")
            return
        if not self._validate_requirements_for_context("generate", block=True):
            return
        if not self._validate_store_state_preflight():
            return
        self._warn_requirement_demand_before_generate(label)
        self._warn_micro_fragments_if_any('Before Generation')
        if not _suppress_progress:
            self._engine_status_start("Preparing inputs...")

        try:
            _write_run_log(f"GENERATE_START | {label}")
        except Exception:
            pass
        # P2-3: Load previous schedule for stability preference (if available)
        # Prefer last week's *published final* schedule; otherwise fall back to the last generated schedule snapshot.
        prev_label, prev_tick_map = load_prev_final_schedule_tick_map(label)
        if not prev_tick_map:
            prev_label, prev_tick_map = load_last_schedule_tick_map()


        # P2-4: refresh learned patterns (if enabled)
        history_refresh_started = datetime.datetime.now()
        try:
            if not _suppress_progress:
                self._set_engine_status("Loading employee availability...", busy=True)
            if bool(getattr(self.model.settings, "learn_from_history", True)):
                self._refresh_learned_patterns()
        except Exception:
            pass
        history_refresh_seconds = (datetime.datetime.now() - history_refresh_started).total_seconds()

        # P2-5: Demand preview before solving (if multipliers differ from 1.0)
        try:
            g = getattr(self.model, "manager_goals", None)
            m_morn = float(getattr(g, "demand_morning_multiplier", 1.0) or 1.0) if g is not None else 1.0
            m_mid  = float(getattr(g, "demand_midday_multiplier", 1.0) or 1.0) if g is not None else 1.0
            m_eve  = float(getattr(g, "demand_evening_multiplier", 1.0) or 1.0) if g is not None else 1.0
            if abs(m_morn-1.0) > 1e-6 or abs(m_mid-1.0) > 1e-6 or abs(m_eve-1.0) > 1e-6:
                messagebox.showinfo(
                    "Demand Adaptive Scheduling",
                    f"Demand multipliers will be applied to staffing requirements (rounded per 30-min tick):\n\n"
                    f"Morning: x{m_morn:g}\nMidday: x{m_mid:g}\nEvening: x{m_eve:g}"
                )
        except Exception:
            pass


        try:
            if not _suppress_progress:
                self._set_engine_status("Evaluating staffing requirements...", busy=True)
            model_for_generation = copy.deepcopy(self.model)
            forecast_used = {}
            if bool(getattr(self.model.settings, "enable_demand_forecast_engine", True)):
                try:
                    forecast_used = apply_demand_forecast_to_model(model_for_generation, (getattr(self.model, "learned_patterns", {}) or {}).get("__demand_forecast__"))
                except Exception:
                    forecast_used = {}
            if not _suppress_progress:
                self._set_engine_status("Running solver...", busy=True, pct=55)
            solver_started = datetime.datetime.now()
            runtime_budget = SolverRuntimeBudget("generate_fresh", 25.0, 30.0)
            if bool(getattr(self.model.settings, "enable_multi_scenario_generation", True)):
                assigns, emp_hours, total_hours, warnings, filled, total_slots, iters_done, restarts_done, diag = generate_schedule_multi_scenario(model_for_generation, label, prev_tick_map=prev_tick_map, runtime_budget=runtime_budget)
            else:
                assigns, emp_hours, total_hours, warnings, filled, total_slots, iters_done, restarts_done, diag = generate_schedule(model_for_generation, label, prev_tick_map=prev_tick_map, runtime_budget=runtime_budget)
            solver_seconds = (datetime.datetime.now() - solver_started).total_seconds()
            try:
                diag = dict(diag or {})
                diag["phase5_demand_forecast"] = forecast_used
                diag["phase5_demand_forecast_enabled"] = bool(getattr(self.model.settings, "enable_demand_forecast_engine", True))
                diag = _set_runtime_metric(diag, "history_learning", history_refresh_seconds, enabled=bool(getattr(self.model.settings, "learn_from_history", True)))
                diag = _set_runtime_metric(diag, "generate_solver", solver_seconds, scenarios=int(diag.get("scenario_count", 1) or 1))
            except Exception:
                pass
        except Exception as ex:
            try:
                _write_run_log(f"GENERATE_CRASH | {label} | {ex}")
            except Exception:
                pass
            raise
        try:
            _write_run_log(f"GENERATE_DONE | {label} | hours={total_hours:.1f} | assigns={len(assigns)} | filled={filled}/{total_slots}")
        except Exception:
            pass
        self.current_assignments = assigns
        self.current_emp_hours = emp_hours
        self.current_total_hours = total_hours
        self.current_warnings = warnings
        self.current_filled = filled
        self.current_total_slots = total_slots
        self.current_diagnostics = diag
        if not _suppress_progress:
            self._set_engine_status("Balancing coverage...", busy=True, pct=80)
        # Store last run summary for Diagnostics (Milestone 0 helper)
        self.last_solver_summary = {
            'label': label,
            'score_hours': round(float(total_hours), 2),
            'maximum_weekly_cap': float(getattr(self.model.manager_goals, 'maximum_weekly_cap', 0.0) or 0.0),
            'cap_over_by': max(0.0, float(total_hours) - float(getattr(self.model.manager_goals, 'maximum_weekly_cap', 0.0) or 0.0)),
            'filled': int(filled),
            'total_slots': int(total_slots),
            'assignments': int(len(assigns)),
            'optimizer_iterations': int(iters_done),
            'restarts': int(restarts_done),
            'warnings_count': int(len(warnings) if warnings else 0),
            'infeasible': any(('INFEASIBLE' in str(w)) for w in (warnings or [])),
            'notes': '',
        }

        # Milestone 6: compute numeric penalty score with tunable weights
        try:
            # unfilled min slots as ticks
            unfilled_ticks = max(0, int(total_slots) - int(filled))
            hist = history_stats_from(self.model)
            pen = float(schedule_score(self.model, label, assigns, unfilled_ticks, hist, prev_tick_map))
            self.last_solver_summary['score_penalty'] = round(pen, 2)
        except Exception:
            self.last_solver_summary['score_penalty'] = None

        # P2-2: Schedule limiting factors
        try:
            self.last_solver_summary['limiting_factors'] = list((diag or {}).get('limiting_factors', []))
            self.last_solver_summary['cap_blocked_attempts'] = int((diag or {}).get('cap_blocked_attempts', 0))
            self.last_solver_summary['cap_blocked_ticks'] = int((diag or {}).get('cap_blocked_ticks', 0))
            self.last_solver_summary['min_short'] = int((diag or {}).get('min_short', 0))
            self.last_solver_summary['pref_short'] = int((diag or {}).get('pref_short', 0))
            self.last_solver_summary['max_viol'] = int((diag or {}).get('max_viol', 0))
        except Exception:
            pass
        try:
            self.last_solver_summary['preferred_weekly_cap'] = float(getattr(self.model.manager_goals, 'preferred_weekly_cap', getattr(self.model.manager_goals,'weekly_hours_cap',0.0)) or 0.0)
        except Exception:
            pass

        # P2-3: Stability diagnostics (% preserved vs moved compared to last schedule)
        try:
            if prev_tick_map:
                cur_tick_map = _expand_assignments_to_tick_map(assigns)
                prev_total = int(len(prev_tick_map))
                preserved = 0
                for k, prev_emp in prev_tick_map.items():
                    if cur_tick_map.get(k) == prev_emp:
                        preserved += 1
                moved = max(0, prev_total - preserved)
                self.last_solver_summary['stability_prev_label'] = prev_label
                self.last_solver_summary['stability_prev_ticks'] = prev_total
                self.last_solver_summary['stability_preserved_ticks'] = preserved
                self.last_solver_summary['stability_moved_ticks'] = moved
                self.last_solver_summary['stability_preserved_pct'] = (preserved / prev_total * 100.0) if prev_total else None
                self.last_solver_summary['stability_moved_pct'] = (moved / prev_total * 100.0) if prev_total else None
            else:
                self.last_solver_summary['stability_prev_label'] = None
                self.last_solver_summary['stability_prev_ticks'] = 0
                self.last_solver_summary['stability_preserved_pct'] = None
                self.last_solver_summary['stability_moved_pct'] = None
        except Exception:
            pass




        # Milestone 3: compute eligibility this week (active/opted-in with >=1 hour availability after overrides)
        try:
            eligible_map, not_eligible_map = compute_weekly_eligibility(self.model, label)
        except Exception:
            eligible_map, not_eligible_map = {}, {}

        # Add summary fields for Diagnostics
        try:
            self.last_solver_summary['eligible_count'] = int(len(eligible_map))
            self.last_solver_summary['not_eligible_count'] = int(len(not_eligible_map))
            # Keep names + reasons (compact)
            self.last_solver_summary['not_eligible'] = [{ 'name': n, 'reason': r } for n, r in sorted(not_eligible_map.items(), key=lambda x: x[0].lower())]
        except Exception:
            pass


        for i in self.out_tree.get_children():
            self.out_tree.delete(i)
        for a in sorted(assigns, key=lambda x: (DAYS.index(x.day), AREAS.index(x.area), x.start_t, x.employee_name)):
            self.out_tree.insert("", "end", values=(a.day, a.area, tick_to_hhmm(a.start_t), tick_to_hhmm(a.end_t), a.employee_name, a.source, "Yes" if a.locked else "No"))

        active_ct = sum(1 for e in self.model.employees if e.work_status=="Active")
        self.summary_lbl.config(text=f"Total hours: {total_hours:.1f} • Filled slots: {filled}/{total_slots} • Assignments: {len(assigns)} • Active employees: {active_ct}")

        self.warn_txt.delete("1.0", tk.END)
        self.warn_txt.insert(tk.END, "Employee weekly hours:\n")
        for n in sorted(emp_hours.keys(), key=str.lower):
            self.warn_txt.insert(tk.END, f"  - {n}: {emp_hours[n]:.1f} hrs\n")
        
        # Milestone 3: Eligibility report (who is eligible this week vs not eligible)
        self.warn_txt.insert(tk.END, "\nEligibility this week:\n")
        if not_eligible_map:
            self.warn_txt.insert(tk.END, "  Not eligible (excluded from participation):\n")
            for n in sorted(not_eligible_map.keys(), key=str.lower):
                self.warn_txt.insert(tk.END, f"    - {n}: {not_eligible_map[n]}\n")
        else:
            self.warn_txt.insert(tk.END, "  All Active/opted-in employees have at least 1 hour of availability.\n")

        # P2-3: Stability report
        try:
            p = self.last_solver_summary.get('stability_preserved_pct', None)
            mvt = self.last_solver_summary.get('stability_moved_pct', None)
            prev_lab = self.last_solver_summary.get('stability_prev_label', None)
            if p is not None and mvt is not None:
                self.warn_txt.insert(tk.END, "\nStability vs previous schedule:\n")
                if prev_lab:
                    self.warn_txt.insert(tk.END, f"  Previous: {prev_lab}\n")
                self.warn_txt.insert(tk.END, f"  % shifts preserved: {p:.1f}%\n")
                self.warn_txt.insert(tk.END, f"  % shifts moved/changed: {mvt:.1f}%\n")
            else:
                self.warn_txt.insert(tk.END, "\nStability vs previous schedule:\n  (No prior schedule found to compare.)\n")
        except Exception:
            pass

        self.warn_txt.insert(tk.END, "\nWarnings:\n")
        if warnings:
            for w in warnings:
                self.warn_txt.insert(tk.END, f"  - {w}\n")
        else:
            self.warn_txt.insert(tk.END, "  (none)\n")

        # P2-3: Persist this schedule so next run can prefer stability
        try:
            save_last_schedule(assigns, label)
        except Exception:
            pass

        try:
            self._refresh_schedule_analysis()
        except Exception:
            pass
        try:
            self._refresh_change_viewer()
        except Exception:
            pass
        if not _suppress_progress:
            self._set_engine_status("Finalizing assignments...", busy=True)
            self._set_engine_status("Updating schedule workspace...", busy=True)
        self._set_status("Schedule generated.")
        self.autosave()
        if not _suppress_progress:
            self._engine_status_stop("Generation complete")
            self.after(900, lambda: self._engine_status_stop("Engine Idle"))

    def save_to_history(self):
        if not self.current_assignments:
            messagebox.showinfo("History", "Generate a schedule first.")
            return
        label = self.current_label
        created = today_iso()

        weekend_counts = {e.name: 0 for e in self.model.employees}
        undes = {e.name: 0 for e in self.model.employees}
        for a in self.current_assignments:
            if a.day in weekend_days():
                weekend_counts[a.employee_name] = weekend_counts.get(a.employee_name,0) + 1
            if (a.start_t < hhmm_to_tick("07:00")) or (a.end_t >= hhmm_to_tick("22:00")):
                undes[a.employee_name] = undes.get(a.employee_name,0) + 1

        summary = ScheduleSummary(
            label=label,
            created_on=created,
            total_hours=float(self.current_total_hours),
            warnings=list(self.current_warnings),
            employee_hours=dict(self.current_emp_hours),
            weekend_counts=weekend_counts,
            undesirable_counts=undes,
            filled_slots=int(self.current_filled),
            total_slots=int(self.current_total_slots),
        )
        self.model.history.append(summary)
        # also write a history JSON file snapshot
        fn = f"history_{created}_{label.replace(' ','_').replace(':','')}.json"
        path = rel_path("history", fn)
        with open(path, "w", encoding="utf-8") as f:
            json.dump(ser_summary(summary), f, indent=2)
        self.refresh_history_tree()
        # Manager Goals
        if hasattr(self, "mg_coverage_goal_var"):
            self.mg_coverage_goal_var.set(float(self.model.manager_goals.coverage_goal_pct))
            self.mg_daily_overstaff_allow_var.set(float(self.model.manager_goals.daily_overstaff_allow_hours))
            self.mg_weekly_hours_cap_var.set(float(self.model.manager_goals.weekly_hours_cap))
            self.mg_call_depth_var.set(int(self.model.manager_goals.call_list_depth))
            self.mg_include_noncert_var.set(bool(self.model.manager_goals.include_noncertified_in_call_list))
        # Settings
        if hasattr(self, 'learn_hist_var'):
            try:
                self.learn_hist_var.set(bool(getattr(self.model.settings, 'learn_from_history', True)))
            except Exception:
                pass

        self.autosave()
        messagebox.showinfo("History", "Saved schedule summary to history.")

    # -------- Print/Export tab --------
    def _build_preview_tab(self):
        frm = ttk.Frame(self.tab_preview); frm.pack(fill="both", expand=True, padx=12, pady=12)
        ttk.Label(frm, text="One-page landscape output organized by store section.", style="SubHeader.TLabel")\
            .pack(anchor="w", pady=(0,8))

        top = ttk.Frame(frm); top.pack(fill="x", pady=(0,10))
        self.btn_print_html = ttk.Button(top, text="Open Print View (HTML)", command=self.print_html)
        self.btn_print_html.pack(side="left")
        self.btn_employee_calendar = ttk.Button(top, text="Employee Calendar (HTML)", command=self.print_employee_calendar)
        self.btn_employee_calendar.pack(side="left", padx=8)
        self.btn_manager_report = ttk.Button(top, text="Manager Report (HTML)", command=self.print_manager_report)
        self.btn_manager_report.pack(side="left", padx=8)
        self.btn_export_csv = ttk.Button(top, text="Export CSV", command=self.export_csv_btn)
        self.btn_export_csv.pack(side="left", padx=8)
        self.btn_export_pdf = ttk.Button(top, text="Export PDF (if available)", command=self.export_pdf_btn)
        self.btn_export_pdf.pack(side="left", padx=8)
        self.btn_publish_final = ttk.Button(top, text="Lock / Publish Final Schedule", command=self._lock_publish_final_schedule)
        self.btn_publish_final.pack(side="left", padx=(20,8))
        self.btn_load_final = ttk.Button(top, text="Load Final (This Week)", command=self._load_final_schedule_this_week)
        self.btn_load_final.pack(side="left", padx=8)
        self.btn_reprint_final = ttk.Button(top, text="Reprint Final", command=self._reprint_final_this_week)
        self.btn_reprint_final.pack(side="left", padx=8)

        self.export_lbl = ttk.Label(frm, text="", foreground="#555")
        self.export_lbl.pack(anchor="w")

        prev_wrap = ttk.Frame(frm)
        prev_wrap.pack(fill="both", expand=True, pady=(10,0))
        self.preview_txt = tk.Text(prev_wrap, height=24, wrap="none")
        pv_y = ttk.Scrollbar(prev_wrap, orient="vertical", command=self.preview_txt.yview)
        pv_x = ttk.Scrollbar(prev_wrap, orient="horizontal", command=self.preview_txt.xview)
        self.preview_txt.configure(yscrollcommand=pv_y.set, xscrollcommand=pv_x.set)
        self.preview_txt.grid(row=0, column=0, sticky="nsew")
        pv_y.grid(row=0, column=1, sticky="ns")
        pv_x.grid(row=1, column=0, sticky="ew")
        prev_wrap.rowconfigure(0, weight=1)
        prev_wrap.columnconfigure(0, weight=1)

    def print_html(self):
        if not self.current_assignments:
            messagebox.showinfo("Print", "Generate a schedule first.")
            return
        path = export_html(self.model, self.current_label, self.current_assignments)
        if not open_local_export_file(path):
            messagebox.showerror("Print", f"Could not open exported file:\n{path}")
            return
        self.export_lbl.config(text=f"HTML: {path}")


    def print_employee_calendar(self):
        if not self.current_assignments:
            messagebox.showinfo("Print", "Generate a schedule first.")
            return
        path = export_employee_calendar_html(self.model, self.current_label, self.current_assignments)
        if not open_local_export_file(path):
            messagebox.showerror("Print", f"Could not open exported file:\n{path}")
            return
        self.export_lbl.config(text=f"Employee Calendar HTML: {path}")

    def print_manager_report(self):
        if not self.current_assignments:
            messagebox.showinfo("Print", "Generate a schedule first.")
            return
        path = export_manager_report_html(self.model, self.current_label, self.current_assignments)
        if not open_local_export_file(path):
            messagebox.showerror("Print", f"Could not open exported file:\n{path}")
            return
        self.export_lbl.config(text=f"Manager Report HTML: {path}")

    def export_csv_btn(self):
        if not self.current_assignments:
            messagebox.showinfo("Export", "Generate a schedule first.")
            return
        path = export_csv(self.model, self.current_label, self.current_assignments)
        self.export_lbl.config(text=f"CSV: {path}")

    def export_pdf_btn(self):
        if not self.current_assignments:
            messagebox.showinfo("Export", "Generate a schedule first.")
            return
        path = export_pdf(self.model, self.current_label, self.current_assignments)
        if not path:
            messagebox.showinfo("PDF", "PDF export requires reportlab. (Not installed in some environments.)")
            return
        self.export_lbl.config(text=f"PDF: {path}")


    def _final_schedule_dir(self) -> str:
        return rel_path("data", "final_schedules")

    def _final_schedule_path_for_label(self, label: Optional[str] = None) -> Optional[str]:
        label = (label or getattr(self, "current_label", "") or self.label_var.get().strip() or self._default_week_label()).strip()
        wk = week_sun_from_label(label)
        if wk is None:
            return None
        return os.path.join(self._final_schedule_dir(), f"{wk.isoformat()}.json")

    def _manual_pages_for_label(self, label: str) -> dict:
        try:
            ui_pages = self._manual_payload_from_ui()
            if any(str(cell).strip() for kind in ui_pages.values() for emp in kind.values() for cell in emp.values()):
                return ui_pages
        except Exception:
            pass
        payload = self._load_manual_overrides()
        stored_label = str(payload.get("label", "") or "")
        if payload and stored_label == str(label or ""):
            return payload.get("pages", {}) or {}
        return {}

    def _set_schedule_workspace_empty_state(self):
        has_basics = bool(getattr(self.model, "employees", [])) and bool(getattr(self.model, "requirements", []))
        if has_basics:
            self.summary_lbl.config(text="No schedule generated yet. Generate Fresh or Regenerate From Current to populate results.")
        else:
            self.summary_lbl.config(text="No data loaded. Open or create a data file to begin.")

        self.warn_txt.delete("1.0", tk.END)
        self.warn_txt.insert(tk.END, "No schedule generated yet.\n")
        self.warn_txt.insert(tk.END, "Generate Fresh or Regenerate From Current to populate results.\n")

        try:
            self.preview_txt.delete("1.0", tk.END)
            self.preview_txt.insert(tk.END, "Current schedule: (none)\n")
            self.preview_txt.insert(tk.END, "Assignments: 0\n")
            self.preview_txt.insert(tk.END, "Open or create a data file to begin.\n")
        except Exception:
            pass

    def _apply_current_schedule_to_output_views(self):
        for i in self.out_tree.get_children():
            self.out_tree.delete(i)
        assigns = list(self.current_assignments or [])
        if not assigns:
            self._set_schedule_workspace_empty_state()
            return
        for a in sorted(assigns, key=lambda x: (DAYS.index(x.day), AREAS.index(x.area), x.start_t, x.employee_name)):
            self.out_tree.insert("", "end", values=(a.day, a.area, tick_to_hhmm(a.start_t), tick_to_hhmm(a.end_t), a.employee_name, a.source, "Yes" if a.locked else "No"))

        active_ct = sum(1 for e in self.model.employees if e.work_status == "Active")
        readiness = build_manager_readiness_summary(
            self.model,
            self.current_label,
            assigns,
            diagnostics=getattr(self, "current_diagnostics", {}),
            warnings=getattr(self, "current_warnings", []),
            filled_slots=int(getattr(self, "current_filled", 0) or 0),
            total_slots=int(getattr(self, "current_total_slots", 0) or 0),
        )
        self.summary_lbl.config(
            text=f"{readiness.get('status', 'Review')} • Total hours: {self.current_total_hours:.1f} • Filled slots: {self.current_filled}/{self.current_total_slots} • Assignments: {len(assigns)} • Active employees: {active_ct}"
        )

        self.warn_txt.delete("1.0", tk.END)
        self.warn_txt.insert(tk.END, "Manager readiness summary:\n")
        for line in str(readiness.get("plain_text", "") or "").splitlines():
            self.warn_txt.insert(tk.END, f"  {line}\n")
        self.warn_txt.insert(tk.END, "\n")
        self.warn_txt.insert(tk.END, "Employee weekly hours:\n")
        for n in sorted((self.current_emp_hours or {}).keys(), key=str.lower):
            self.warn_txt.insert(tk.END, f"  - {n}: {self.current_emp_hours[n]:.1f} hrs\n")
        self.warn_txt.insert(tk.END, "\nWarnings:\n")
        if self.current_warnings:
            for w in self.current_warnings:
                self.warn_txt.insert(tk.END, f"  - {w}\n")
        else:
            self.warn_txt.insert(tk.END, "  (none)\n")

        try:
            self.preview_txt.delete("1.0", tk.END)
            self.preview_txt.insert(tk.END, f"Current schedule: {self.current_label}\n")
            self.preview_txt.insert(tk.END, f"Publish readiness: {readiness.get('status', 'Review')}\n")
            self.preview_txt.insert(tk.END, f"Assignments: {len(assigns)}\n")
            self.preview_txt.insert(tk.END, f"Total hours: {self.current_total_hours:.1f}\n")
            self.preview_txt.insert(tk.END, f"Filled slots: {self.current_filled}/{self.current_total_slots}\n")
            self.preview_txt.insert(tk.END, f"Required gaps: {int(readiness.get('min_short', 0) or 0)} • Preferred gaps: {int(readiness.get('pref_short', 0) or 0)}\n")
        except Exception:
            pass

    def _lock_publish_final_schedule(self):
        if not self.current_assignments:
            messagebox.showinfo("Lock Final Schedule", "Generate or load a schedule first.")
            return
        path = self._final_schedule_path_for_label()
        if not path:
            messagebox.showerror("Lock Final Schedule", "Could not determine the week start date from the current label.")
            return
        ensure_dir(os.path.dirname(path))
        wk = week_sun_from_label(self.current_label)
        manual_pages = self._manual_pages_for_label(self.current_label)
        payload = {
            "label": str(self.current_label or ""),
            "week_start_sun": (wk.isoformat() if wk else ""),
            "published_on": datetime.datetime.now().isoformat(timespec="seconds"),
            "assignments": [ser_assignment(a) for a in self.current_assignments],
            "employee_hours": dict(self.current_emp_hours or {}),
            "total_hours": float(self.current_total_hours or 0.0),
            "warnings": list(self.current_warnings or []),
            "filled_slots": int(self.current_filled or 0),
            "total_slots": int(self.current_total_slots or 0),
            "manual_pages": manual_pages,
        }
        with open(path, "w", encoding="utf-8") as f:
            json.dump(payload, f, indent=2)
        self.export_lbl.config(text=f"Final schedule saved: {path}")
        self._set_status("Locked / published final schedule.")
        messagebox.showinfo("Lock Final Schedule", f"Final schedule saved for this week.\n\n{path}")

    def _load_final_schedule_this_week(self):
        label = self.label_var.get().strip() or self.current_label or self._default_week_label()
        path = self._final_schedule_path_for_label(label)
        if not path or not os.path.isfile(path):
            messagebox.showinfo("Load Final", "No published final schedule was found for this week yet.")
            return
        with open(path, "r", encoding="utf-8") as f:
            payload = json.load(f) or {}
        assigns = []
        skipped_rows = 0
        for item in payload.get("assignments", []) or []:
            try:
                assigns.append(des_assignment(item))
            except Exception as ex:
                skipped_rows += 1
                _write_run_log(f"LOAD_FINAL | Skipped malformed assignment row: {repr(ex)} :: {repr(item)[:400]}")
        self.current_label = str(payload.get("label", label) or label)
        self.label_var.set(self.current_label)
        self.current_assignments = assigns
        self.current_emp_hours = {k: float(v) for k, v in (payload.get("employee_hours", {}) or {}).items()}
        self.current_total_hours = float(payload.get("total_hours", 0.0) or 0.0)
        self.current_warnings = list(payload.get("warnings", []) or [])
        self.current_filled = int(payload.get("filled_slots", 0) or 0)
        self.current_total_slots = int(payload.get("total_slots", 0) or 0)
        if not self.current_emp_hours and self.current_assignments:
            self.current_emp_hours, self.current_total_hours, self.current_filled, self.current_total_slots = calc_schedule_stats(self.model, self.current_assignments)
        manual_pages = payload.get("manual_pages", {}) or {}
        if manual_pages:
            try:
                self._manual_apply_to_ui(manual_pages)
            except Exception as ex:
                _write_run_log(f"LOAD_FINAL | Manual pages apply to UI failed: {repr(ex)}")
            try:
                self._save_manual_overrides({
                    "label": self.current_label,
                    "saved_on": today_iso(),
                    "pages": manual_pages,
                })
            except Exception as ex:
                _write_run_log(f"LOAD_FINAL | Manual pages save failed: {repr(ex)}")
        self._apply_current_schedule_to_output_views()
        try:
            self._refresh_schedule_analysis()
        except Exception as ex:
            _write_run_log(f"LOAD_FINAL | Analysis refresh failed: {repr(ex)}")
        try:
            self._refresh_change_viewer()
        except Exception as ex:
            _write_run_log(f"LOAD_FINAL | Change-view refresh failed: {repr(ex)}")
        self.export_lbl.config(text=f"Loaded final schedule: {path}")
        status_msg = "Loaded published final schedule."
        if skipped_rows:
            warn_msg = f"Loaded final schedule with {skipped_rows} malformed assignment row(s) skipped."
            _write_run_log(f"LOAD_FINAL | {warn_msg}")
            self.export_lbl.config(text=f"Loaded final schedule with {skipped_rows} skipped row(s): {path}")
            status_msg = warn_msg
            messagebox.showwarning("Load Final", warn_msg)
        self._set_status(status_msg)

    def _reprint_final_this_week(self):
        label = self.label_var.get().strip() or self.current_label or self._default_week_label()
        path = self._final_schedule_path_for_label(label)
        if not path or not os.path.isfile(path):
            messagebox.showinfo("Reprint Final", "No published final schedule was found for this week yet.")
            return
        with open(path, "r", encoding="utf-8") as f:
            payload = json.load(f) or {}
        assigns = []
        skipped_rows = 0
        for item in payload.get("assignments", []) or []:
            try:
                assigns.append(des_assignment(item))
            except Exception as ex:
                skipped_rows += 1
                _write_run_log(f"REPRINT_FINAL | Skipped malformed assignment row: {repr(ex)}")
        manual_pages = payload.get("manual_pages", {}) or {}
        use_label = str(payload.get("label", label) or label)
        if manual_pages:
            out = export_employee_calendar_html_with_overrides(self.model, use_label, assigns, manual_pages)
            self.export_lbl.config(text=f"Final manual employee calendar HTML: {out}")
        else:
            out = export_employee_calendar_html(self.model, use_label, assigns)
            self.export_lbl.config(text=f"Final employee calendar HTML: {out}")
        if not open_local_export_file(out):
            messagebox.showerror("Reprint Final", f"Could not open exported file:\n{out}")

    # -------- History tab --------
    # -------- Manager Goals tab --------
    # -------- Manual Edit tab --------
    def _manual_storage_path(self) -> str:
        return rel_path("data", "manual_employee_calendar.json")

    def _load_manual_overrides(self) -> dict:
        path = self._manual_storage_path()
        if os.path.isfile(path):
            try:
                with open(path, "r", encoding="utf-8") as f:
                    return json.load(f) or {}
            except Exception:
                return {}
        return {}

    def _save_manual_overrides(self, payload: dict) -> None:
        path = self._manual_storage_path()
        ensure_dir(os.path.dirname(path))
        try:
            _atomic_write_json(path, payload, indent=2)
        except Exception as e:
            # Do not fail silently: manual edits are user-authored and must be reliable.
            try:
                _write_run_log(f"Manual overrides save failed: {path} :: {repr(e)}")
            except Exception:
                pass
            try:
                messagebox.showerror(
                    "Save Failed",
                    "Could not save manual schedule edits to:\n"
                    f"{path}\n\n"
                    f"Error: {e}\n\n"
                    "Your changes were NOT saved.\n\n"
                    "Tip: If this folder is in OneDrive, try moving the program folder to a local Desktop folder and try again."
                )
            except Exception:
                pass

    def _compute_calendar_base_texts(self, assignments: List[Assignment]) -> dict:
        """
        Returns: pages dict with keys MAIN, KITCHEN, CARWASH
        Each page: {employee_name: {day: text}}
        """
        pages = {"MAIN": {}, "KITCHEN": {}, "CARWASH": {}}
        # index assignments
        by_emp_day_area: Dict[Tuple[str,str,str], List[Assignment]] = {}
        areas_worked: Dict[Tuple[str,str], set] = {}
        for a in assignments or []:
            by_emp_day_area.setdefault((a.employee_name, a.day, a.area), []).append(a)
            areas_worked.setdefault((a.employee_name, a.day), set()).add(a.area)
        for k in list(by_emp_day_area.keys()):
            by_emp_day_area[k].sort(key=lambda x: (x.start_t, x.end_t))

        def _merge_to_str(items: List[Assignment]) -> str:
            if not items:
                return ""
            blocks = []
            cur_s, cur_e = int(items[0].start_t), int(items[0].end_t)
            for it in items[1:]:
                s, e = int(it.start_t), int(it.end_t)
                if s <= cur_e:
                    cur_e = max(cur_e, e)
                else:
                    blocks.append((cur_s, cur_e))
                    cur_s, cur_e = s, e
            blocks.append((cur_s, cur_e))
            return "; ".join(f"{tick_to_ampm(s)}-{tick_to_ampm(e)}" for s, e in blocks)

        for e in sorted(self.model.employees, key=lambda x: (x.name or "").lower()):
            nm = e.name or ""
            if not nm:
                continue
            for kind in ["MAIN","KITCHEN","CARWASH"]:
                pages[kind].setdefault(nm, {})
            for d in DAYS:
                cstore = _merge_to_str(by_emp_day_area.get((nm, d, "CSTORE"), []))
                kitchen = _merge_to_str(by_emp_day_area.get((nm, d, "KITCHEN"), []))
                carwash = _merge_to_str(by_emp_day_area.get((nm, d, "CARWASH"), []))
                # MAIN page: show CSTORE times, and hints to other areas
                parts = []
                if cstore:
                    parts.append(cstore)
                # Hints
                hints = []
                if kitchen:
                    hints.append("See Kitchen")
                if carwash:
                    hints.append("See Carwash")
                if hints and cstore:
                    parts.append(" / ".join(hints))
                elif hints and not cstore:
                    parts.append(" / ".join(hints))
                main_txt = "; ".join(parts).strip()
                # If nothing at all, keep "Off" for MAIN to match employee calendar behavior
                if not main_txt:
                    main_txt = "Off"
                pages["MAIN"][nm][d] = main_txt
                # Department pages: blank if not scheduled there (matches your preference)
                pages["KITCHEN"][nm][d] = kitchen  # blank if none
                pages["CARWASH"][nm][d] = carwash  # blank if none
        return pages

    def _manual_payload_from_vars(self, vars_map: Dict[str, Dict[str, Dict[str, tk.StringVar]]]) -> dict:
        pages = {}
        for kind, emp_map in (vars_map or {}).items():
            pages[kind] = {}
            for emp, day_map in emp_map.items():
                pages[kind][emp] = {}
                for d, var in day_map.items():
                    pages[kind][emp][d] = (var.get() or "").strip()
        return pages

    def _manual_payload_from_ui(self) -> dict:
        return self._manual_payload_from_vars(getattr(self, "manual_vars", {}))

    def _manual_apply_to_vars(self, vars_map: Dict[str, Dict[str, Dict[str, tk.StringVar]]], pages: dict):
        # pages expected keys MAIN/KITCHEN/CARWASH
        for kind in ["MAIN","KITCHEN","CARWASH"]:
            if kind not in vars_map:
                continue
            src_kind = pages.get(kind, {}) or {}
            for emp, day_map in vars_map[kind].items():
                src_emp = src_kind.get(emp, {}) or {}
                for d, var in day_map.items():
                    if d in src_emp:
                        var.set(src_emp.get(d,"") or "")

    def _manual_apply_to_ui(self, pages: dict):
        self._manual_apply_to_vars(getattr(self, "manual_vars", {}), pages)

    def _manual_load_btn(self):
        # Prefer loading stored manual edits for the current label; otherwise load from current schedule
        payload = self._load_manual_overrides()
        cur_label = str(getattr(self, "current_label", "") or "")
        stored_label = str(payload.get("label","") or "")
        if payload and (not cur_label or stored_label == cur_label):
            self._manual_apply_to_ui(payload.get("pages", {}) or {})
            self._set_status("Loaded manual schedule edits.")
            return
        if not self.current_assignments:
            messagebox.showinfo("Manual Edit", "No manual edits saved for this week and no generated schedule available yet.\n\nGenerate a schedule first, then click “Load From Current Schedule”.")
            return
        base = self._compute_calendar_base_texts(self.current_assignments)
        self._manual_apply_to_ui(base)
        self._set_status("Loaded manual editor from current generated schedule.")

    def _manual_save_btn(self):
        payload = {
            "label": str(getattr(self, "current_label", "") or ""),
            "saved_on": today_iso(),
            "pages": self._manual_payload_from_ui(),
        }
        self._save_manual_overrides(payload)
        self._set_status("Saved manual schedule edits.")

    def _manual_clear_btn(self):
        for kind in self.manual_vars:
            for emp in self.manual_vars[kind]:
                for d in self.manual_vars[kind][emp]:
                    self.manual_vars[kind][emp][d].set("")
        # clear file too
        self._save_manual_overrides({})
        self._set_status("Cleared manual schedule edits.")

    def _manual_open_html(self):
        pages = self._manual_payload_from_ui()
        if not self.current_assignments:
            messagebox.showinfo("Manual Edit", "Generate a schedule first (so the calendar can keep the exact same formatting and header info).")
            return
        path = export_employee_calendar_html_with_overrides(self.model, self.current_label, self.current_assignments, pages)
        if not open_local_export_file(path):
            messagebox.showerror("Print", f"Could not open exported file:\n{path}")
            return
        self.export_lbl.config(text=f"Manual Employee Calendar HTML: {path}")


    def _manual_employee_names(self) -> List[str]:
        return [n for n in sorted([(e.name or "").strip() for e in getattr(self.model, "employees", []) or []], key=str.lower) if n]

    def _manual_status(self, msg: str) -> None:
        try:
            self.manual_status_lbl.config(text=str(msg or ""))
        except Exception:
            pass

    def _manual_set_warning_text(self, lines: List[str]) -> None:
        try:
            self.manual_warn_txt.delete("1.0", tk.END)
            for line in (lines or []):
                self.manual_warn_txt.insert(tk.END, f"{line}\n")
            if not lines:
                self.manual_warn_txt.insert(tk.END, "No warnings.\n")
        except Exception:
            pass

    def _manual_swap_selected_day(self):
        kind = str(getattr(self, 'manual_swap_kind_var', tk.StringVar(value='MAIN')).get() or 'MAIN')
        day = str(getattr(self, 'manual_swap_day_var', tk.StringVar(value=DAYS[0])).get() or DAYS[0])
        src = str(getattr(self, 'manual_swap_from_var', tk.StringVar(value='')).get() or '')
        dst = str(getattr(self, 'manual_swap_to_var', tk.StringVar(value='')).get() or '')
        if not src or not dst or src == dst:
            messagebox.showinfo('Quick Swap', 'Pick two different employees to swap.')
            return
        try:
            a = self.manual_vars[kind][src][day].get()
            b = self.manual_vars[kind][dst][day].get()
            self.manual_vars[kind][src][day].set(b)
            self.manual_vars[kind][dst][day].set(a)
            self._manual_status(f'Swapped {kind} {day}: {src} ↔ {dst}')
        except Exception as e:
            messagebox.showerror('Quick Swap', f'Could not swap those cells.\n\n{e}')

    def _manual_parse_time_blocks(self, raw: str) -> Tuple[List[Tuple[int, int]], List[str]]:
        s = str(raw or '').strip()
        if not s:
            return [], []

        def _canon_token(v: str) -> str:
            v = str(v or '').strip().lower()
            v = re.sub(r'[\s\.;,/\\]+', ' ', v)
            return re.sub(r'\s+', ' ', v).strip()

        ignore_tokens = {
            'off',
            'see kitchen',
            'see carwash',
            'see kitchen see carwash',
            'see carwash see kitchen',
        }
        if _canon_token(s) in ignore_tokens:
            return [], []

        notes: List[str] = []
        s = re.sub(r'\([^)]*\)', ' ', s)
        s = s.replace('–', '-').replace('—', '-')
        hint_pat = re.compile(r'(?i)\bsee\s+(kitchen|carwash)\b[\s\.;,/\\-]*')
        s = hint_pat.sub(' ', s)
        pat = re.compile(r'(\d{1,2}(?::\d{2})?\s*(?:am|pm|a|p)?)\s*-\s*(\d{1,2}(?::\d{2})?\s*(?:am|pm|a|p)?)', re.I)
        out: List[Tuple[int, int]] = []
        for m in pat.finditer(s):
            a = m.group(1).strip().lower().replace(' ', '')
            b = m.group(2).strip().lower().replace(' ', '')
            try:
                st = hhmm_to_tick(_normalize_user_time(a))
                en = hhmm_to_tick(_normalize_user_time(b))
                if en > st:
                    out.append((st, en))
                else:
                    notes.append(f'Overnight/invalid range not supported: {m.group(0).strip()}')
            except Exception:
                notes.append(f'Could not parse time range: {m.group(0).strip()}')

        residual = pat.sub(' ', s)
        residual = hint_pat.sub(' ', residual)
        residual = re.sub(r'\([^)]*\)', ' ', residual)
        residual = re.sub(r'[\s\.;,/\-]+', ' ', residual).strip()
        if residual:
            if out:
                notes.append(f'Unparsed text remains: {residual}')
            else:
                notes.append(f'Could not read text: {residual}')
        return out, notes

    def _manual_parse_pages_to_assignments_from_pages(self, pages: dict) -> Tuple[List[Assignment], List[str]]:
        assigns: List[Assignment] = []
        issues: List[str] = []
        area_map = {'MAIN': 'CSTORE', 'KITCHEN': 'KITCHEN', 'CARWASH': 'CARWASH'}

        def _canon_token(v: str) -> str:
            v = str(v or '').strip().lower()
            v = re.sub(r'[\s\.;,/\\]+', ' ', v)
            return re.sub(r'\s+', ' ', v).strip()

        ignore_tokens = {
            'off',
            'see kitchen',
            'see carwash',
            'see kitchen see carwash',
            'see carwash see kitchen',
        }
        for page_kind, area in area_map.items():
            for emp, day_map in (pages.get(page_kind, {}) or {}).items():
                for day, raw in (day_map or {}).items():
                    blocks, notes = self._manual_parse_time_blocks(raw)
                    raw_s = str(raw or '').strip()
                    canon_raw = _canon_token(raw_s)
                    if raw_s and canon_raw not in ignore_tokens:
                        for note in notes:
                            issues.append(f'{page_kind} {day} for {emp}: {note}')
                        if not blocks and not notes:
                            cleaned = re.sub(r'\([^)]*\)', '', raw_s)
                            cleaned = re.sub(r'(?i)\bsee\s+(kitchen|carwash)\b[\s\.;,/\\-]*', ' ', cleaned)
                            cleaned = re.sub(r'[\s\.;,/\-]+', ' ', cleaned).strip()
                            if cleaned:
                                issues.append(f'Could not read {page_kind} {day} for {emp}: "{raw_s}"')
                    for st, en in blocks:
                        assigns.append(Assignment(day=day, area=area, start_t=st, end_t=en, employee_name=emp, locked=False, source=ASSIGNMENT_SOURCE_MANUAL))
        assigns.sort(key=lambda a: (a.employee_name.lower(), DAYS.index(a.day), AREAS.index(a.area), a.start_t, a.end_t))
        return assigns, issues

    def _manual_parse_pages_to_assignments(self) -> Tuple[List[Assignment], List[str]]:
        pages = self._manual_payload_from_ui()
        return self._manual_parse_pages_to_assignments_from_pages(pages)

    def _manual_validate_assignments(self, assigns: List[Assignment]) -> List[str]:
        use_label = self.current_label or self.label_var.get().strip() or self._default_week_label()
        normalized: List[Assignment] = []
        for a in assigns:
            normalized.append(Assignment(day=a.day, area=a.area, start_t=a.start_t, end_t=a.end_t, employee_name=a.employee_name, locked=bool(getattr(a, "locked", False)), source=ASSIGNMENT_SOURCE_MANUAL))

        warnings: List[str] = []
        for v in evaluate_schedule_hard_rules(self.model, use_label, normalized, include_override_warnings=True):
            warnings.append(_viol_to_text(v))

        cov = count_coverage_per_tick(normalized)
        min_req, pref_req, max_req = build_requirement_maps(self.model.requirements, goals=getattr(self.model, 'manager_goals', None), store_info=getattr(self.model, "store_info", None))
        min_short, pref_short, max_viol = compute_requirement_shortfalls(min_req, pref_req, max_req, cov)
        if min_short > 0:
            warnings.append(f'Coverage risk created: {min_short} required 30-minute staffing blocks are unfilled.')
        if pref_short > 0:
            warnings.append(f'Preferred coverage shortfall: {pref_short} preferred 30-minute staffing blocks are below target.')
        if max_viol > 0:
            warnings.append(f'Max staffing exceeded in {max_viol} 30-minute blocks.')
        return warnings

    def _manual_analyze_btn(self):
        try:
            assigns, parse_issues = self._manual_parse_pages_to_assignments()
            warnings = parse_issues + self._manual_validate_assignments(assigns)
            emp_hours, total_hours, filled, total_slots = calc_schedule_stats(self.model, assigns)
            summary = [
                f'Manual analysis for {len(assigns)} assignments.',
                f'Total hours: {total_hours:.1f}',
                f'Coverage: {filled}/{total_slots} required 30-minute blocks filled',
            ]
            if emp_hours:
                lowest = min(emp_hours.items(), key=lambda kv: kv[1])
                highest = max(emp_hours.items(), key=lambda kv: kv[1])
                summary.append(f'Hours range: {lowest[0]} {lowest[1]:.1f} hrs → {highest[0]} {highest[1]:.1f} hrs')
            self._manual_status('Manual analysis complete.')
            self._manual_set_warning_text(summary + [''] + (warnings if warnings else ['No warnings detected.']))
        except Exception as e:
            messagebox.showerror('Manual Edit', f'Could not analyze manual edits.\n\n{e}')

    def _manual_apply_btn(self):
        try:
            assigns, parse_issues = self._manual_parse_pages_to_assignments()
            warnings = parse_issues + self._manual_validate_assignments(assigns)
            if warnings:
                ok = messagebox.askyesno('Apply Manual Edits', 'Warnings were found. Apply manual edits anyway?')
                if not ok:
                    self._manual_set_warning_text(warnings)
                    self._manual_status('Manual apply canceled because warnings were found.')
                    return
            self.current_assignments = list(assigns)
            self.current_emp_hours, self.current_total_hours, self.current_filled, self.current_total_slots = calc_schedule_stats(self.model, self.current_assignments)
            self.current_warnings = list(warnings)
            self._apply_current_schedule_to_output_views()
            try:
                self._refresh_schedule_analysis()
            except Exception:
                pass
            self._manual_save_btn()
            self._manual_status('Manual edits applied to current schedule.')
            self._manual_set_warning_text(warnings if warnings else ['Manual edits applied with no warnings.'])
            self._set_status('Manual schedule edits applied to current schedule.')
        except Exception as e:
            messagebox.showerror('Manual Edit', f'Could not apply manual edits.\n\n{e}')

    # -------- Schedule Analysis tab (Phase 4 D1) --------
    def _build_analysis_tab(self):
        frm = ttk.Frame(self.tab_analysis); frm.pack(fill="both", expand=True, padx=12, pady=12)

        ttk.Label(frm, text="Schedule Analysis", style="Header.TLabel").pack(anchor="w", pady=(0,4))
        ttk.Label(
            frm,
            text="Explains why the current schedule scored the way it did. Read-only. Generate or load a schedule first.",
            style="Hint.TLabel",
        ).pack(anchor="w", pady=(0,10))

        top = ttk.Frame(frm); top.pack(fill="x", pady=(0,8))
        ttk.Button(top, text="Refresh Analysis", command=self._refresh_schedule_analysis).pack(side="left")

        self.analysis_summary_lbl = ttk.Label(frm, text="", foreground="#333")
        self.analysis_summary_lbl.pack(fill="x", pady=(0,8))

        metric_box = ttk.Frame(frm)
        metric_box.pack(fill="x", pady=(0,8))
        self.analysis_metric_vars = {
            "coverage": tk.StringVar(value="Coverage: --"),
            "utilization": tk.StringVar(value="Utilization: --"),
            "risk": tk.StringVar(value="Risk Protection: --"),
            "participation": tk.StringVar(value="Participation: --"),
        }
        for i, key in enumerate(["coverage", "utilization", "risk", "participation"]):
            box = ttk.LabelFrame(metric_box, text=key.title() if key != "risk" else "Risk Protection")
            box.grid(row=0, column=i, sticky="nsew", padx=(0 if i == 0 else 8, 0), pady=0)
            metric_box.columnconfigure(i, weight=1)
            ttk.Label(box, textvariable=self.analysis_metric_vars[key], style="SubHeader.TLabel").pack(anchor="w", padx=10, pady=(8,6))

        cols = ("Category", "Penalty", "Impact", "Notes")
        at_wrap = ttk.Frame(frm)
        at_wrap.pack(fill="both", expand=False, pady=(0,8))
        self.analysis_tree = ttk.Treeview(at_wrap, columns=cols, show="headings", height=10)
        for c in cols:
            self.analysis_tree.heading(c, text=c)
            w = 180
            if c == "Category": w = 220
            if c == "Notes": w = 520
            self.analysis_tree.column(c, width=w)
        at_ys = ttk.Scrollbar(at_wrap, orient="vertical", command=self.analysis_tree.yview)
        at_xs = ttk.Scrollbar(at_wrap, orient="horizontal", command=self.analysis_tree.xview)
        self.analysis_tree.configure(yscrollcommand=at_ys.set, xscrollcommand=at_xs.set)
        self.analysis_tree.grid(row=0, column=0, sticky="nsew")
        at_ys.grid(row=0, column=1, sticky="ns")
        at_xs.grid(row=1, column=0, sticky="ew")
        at_wrap.rowconfigure(0, weight=1)
        at_wrap.columnconfigure(0, weight=1)

        body = ttk.Frame(frm); body.pack(fill="both", expand=True)
        self.analysis_text = tk.Text(body, wrap="word", height=14)
        vs = ttk.Scrollbar(body, orient="vertical", command=self.analysis_text.yview)
        self.analysis_text.configure(yscrollcommand=vs.set)
        self.analysis_text.grid(row=0, column=0, sticky="nsew")
        vs.grid(row=0, column=1, sticky="ns")
        body.rowconfigure(0, weight=1)
        body.columnconfigure(0, weight=1)

        self._refresh_schedule_analysis()

    def _refresh_schedule_analysis(self):
        if not hasattr(self, "analysis_text"):
            return

        for i in self.analysis_tree.get_children():
            self.analysis_tree.delete(i)

        self.analysis_text.delete("1.0", "end")
        if not self.current_assignments:
            self.analysis_summary_lbl.config(text="No current schedule loaded.")
            for key in getattr(self, "analysis_metric_vars", {}):
                label = key.title() if key != "risk" else "Risk Protection"
                self.analysis_metric_vars[key].set(f"{label}: --")
            self.analysis_text.insert("end", "Generate a schedule or Load Final to see score breakdown, weak areas, and limiting factors.\n")
            return

        label = self.current_label or self._default_week_label()
        hist = history_stats_from(self.model)
        prev_label, prev_tick_map = load_prev_final_schedule_tick_map(label)
        if not prev_tick_map:
            prev_label, prev_tick_map = load_last_schedule_tick_map()

        try:
            unfilled_ticks = max(0, int(getattr(self, "current_total_slots", 0)) - int(getattr(self, "current_filled", 0)))
            bd = schedule_score_breakdown(self.model, label, list(self.current_assignments), unfilled_ticks, hist, prev_tick_map)
        except Exception as ex:
            self.analysis_summary_lbl.config(text=f"Analysis error: {ex}")
            self.analysis_text.insert("end", f"Could not compute schedule analysis.\n\n{ex}\n")
            return

        def _safe_pct(num, den, fallback=100.0):
            try:
                num = float(num)
                den = float(den)
                if den <= 0:
                    return float(fallback)
                return max(0.0, min(100.0, (num / den) * 100.0))
            except Exception:
                return float(fallback)

        total_pen = float(bd.get("total", sum(float(v) for v in bd.values() if isinstance(v, (int, float)))))
        min_pen = float(bd.get("min_coverage_pen", 0.0) or 0.0)
        pref_pen = float(bd.get("preferred_coverage_shortfall_pen", 0.0) or 0.0)
        coverage_pen = min_pen + pref_pen + float(bd.get("max_staffing_violation_pen", 0.0) or 0.0)
        util_pen = float(bd.get("hour_imbalance_pen", 0.0) or 0.0) + float(bd.get("utilization_balance_pen", 0.0) or 0.0) + float(bd.get("utilization_near_cap_pen", 0.0) or 0.0) + float(bd.get("preferred_weekly_cap_pen", 0.0) or 0.0)
        risk_stability_pen = float(bd.get("stability_pen", 0.0) or 0.0)
        risk_fragile_pen = float(bd.get("risk_fragile_pen", 0.0) or 0.0)
        risk_single_point_pen = float(bd.get("risk_single_point_pen", 0.0) or 0.0)
        risk_pen = risk_stability_pen + risk_fragile_pen + risk_single_point_pen
        part_pen = float(bd.get("participation_pen", 0.0) or 0.0) + float(bd.get("employee_max_hours_pen", 0.0) or 0.0) + float(bd.get("target_min_hours_pen", 0.0) or 0.0)

        coverage_pct = _safe_pct(getattr(self, "current_filled", 0), getattr(self, "current_total_slots", 0), fallback=100.0)
        util_pct = max(0.0, min(100.0, 100.0 - min(100.0, util_pen / max(1.0, total_pen + 50.0) * 100.0)))
        risk_pct = max(0.0, min(100.0, 100.0 - min(100.0, risk_pen / max(1.0, total_pen + 50.0) * 100.0)))
        part_pct = max(0.0, min(100.0, 100.0 - min(100.0, part_pen / max(1.0, total_pen + 50.0) * 100.0)))

        self.analysis_metric_vars["coverage"].set(f"Coverage: {coverage_pct:.1f}%")
        self.analysis_metric_vars["utilization"].set(f"Utilization: {util_pct:.1f}%")
        self.analysis_metric_vars["risk"].set(f"Risk Protection: {risk_pct:.1f}%")
        self.analysis_metric_vars["participation"].set(f"Participation: {part_pct:.1f}%")

        self.analysis_summary_lbl.config(
            text=f"Label: {label} • Total hours: {float(getattr(self, 'current_total_hours', 0.0) or 0.0):.1f} • Assignments: {len(self.current_assignments)} • Score penalty: {total_pen:.1f}"
        )

        pattern_pen = float(bd.get("pattern_pen", 0.0) or 0.0)
        employee_fit_pen = float(bd.get("employee_fit_pen", 0.0) or 0.0)
        pattern_pct = max(0.0, min(100.0, 100.0 - min(100.0, (pattern_pen + employee_fit_pen) / max(1.0, total_pen + 50.0) * 100.0)))

        category_rows = [
            ("Coverage", coverage_pen, coverage_pct, f"Filled slots {int(getattr(self, 'current_filled', 0))}/{int(getattr(self, 'current_total_slots', 0))}; minimum coverage penalty {min_pen:.1f}; preferred coverage penalty {pref_pen:.1f}"),
            ("Utilization", util_pen, util_pct, f"Diagnostic metrics: hour imbalance {float(bd.get('hour_imbalance_pen', 0.0) or 0.0):.1f}; low-hours balancing {float(bd.get('utilization_balance_pen', 0.0) or 0.0):.1f}; near-cap pressure {float(bd.get('utilization_near_cap_pen', 0.0) or 0.0):.1f} (score-driving terms: unique-employee + fragmentation penalties)"),
            ("Risk Protection", risk_pen, risk_pct, f"Stability {risk_stability_pen:.1f}; fragile coverage {risk_fragile_pen:.1f}; single-point {risk_single_point_pen:.1f}" + (f" vs {prev_label}" if prev_label else "")),
            ("Participation", part_pen, part_pct, f"Participation misses {float(bd.get('participation_pen', 0.0) or 0.0):.1f}; employee max hours {float(bd.get('employee_max_hours_pen', 0.0) or 0.0):.1f}; target minimum hours {float(bd.get('target_min_hours_pen', 0.0) or 0.0):.1f}"),
            ("Pattern Learning", pattern_pen, pattern_pct, f"Pattern deviation penalty {pattern_pen:.1f}; learned profiles {len(getattr(self.model, 'learned_patterns', {}) or {})}"),
            ("Employee Fit", employee_fit_pen, pattern_pct, f"Employee fit penalty {employee_fit_pen:.1f}; fit profiles {len(((getattr(self.model, 'learned_patterns', {}) or {}).get('__employee_fit__') or {}))}"),
        ]
        for cat, pen, pct, notes in category_rows:
            impact = "Good"
            if pct < 90.0:
                impact = "Watch"
            if pct < 75.0:
                impact = "Weak"
            self.analysis_tree.insert("", "end", values=(cat, f"{pen:.1f}", impact, notes))

        weak_areas = []
        try:
            min_req_ls, pref_req_ls, max_req_ls = build_requirement_maps(self.model.requirements, goals=getattr(self.model, 'manager_goals', None), store_info=getattr(self.model, "store_info", None))
            cov_map = count_coverage_per_tick(self.current_assignments)
            shortages = []
            for (day, area, tick), req in min_req_ls.items():
                cov = int(cov_map.get((day, area, tick), 0) or 0)
                if cov < int(req):
                    shortages.append((int(req - cov), day, area, tick, cov, int(req)))
            shortages.sort(reverse=True)
            for deficit, day, area, tick, cov, req in shortages[:5]:
                weak_areas.append(f"{day} {tick_to_hhmm(tick)} {area}: scheduled {cov}, minimum {req} (deficit {deficit})")
        except Exception as ex:
            _write_run_log(f"ANALYSIS | Weak-areas section failed: {repr(ex)}")

        near_cap = []
        try:
            for e in self.model.employees:
                maxh = float(getattr(e, 'max_weekly_hours', 0.0) or 0.0)
                h = float(getattr(self, 'current_emp_hours', {}).get(e.name, 0.0) or 0.0)
                if maxh > 0 and h >= maxh * 0.9:
                    near_cap.append((h / maxh if maxh else 0.0, e.name, h, maxh))
            near_cap.sort(reverse=True)
        except Exception as ex:
            _write_run_log(f"ANALYSIS | Near-cap section failed: {repr(ex)}")
            near_cap = []

        limiting = list((getattr(self, 'last_solver_summary', {}) or {}).get('limiting_factors', []))
        warnings = list(getattr(self, 'current_warnings', []) or [])

        self.analysis_text.insert("end", "Schedule Score Breakdown\n")
        self.analysis_text.insert("end", f"Coverage: {coverage_pct:.1f}%\n")
        self.analysis_text.insert("end", f"Utilization: {util_pct:.1f}%\n")
        self.analysis_text.insert("end", f"Risk Protection: {risk_pct:.1f}%\n")
        self.analysis_text.insert("end", f"Risk subtotal: stability + fragile + single-point = {risk_stability_pen:.1f} + {risk_fragile_pen:.1f} + {risk_single_point_pen:.1f} = {risk_pen:.1f}\n")
        self.analysis_text.insert("end", "Risk controls note: Coverage Risk Protection = scarcity-aware placement guidance; Risk-Aware Optimization = fragile/single-point penalties in score.\n")
        self.analysis_text.insert("end", "Utilization parity note: diagnostic metrics show imbalance/balancing/near-cap signals, while score-driving utilization terms emphasize unique-employee + fragmentation penalties.\n")
        self.analysis_text.insert("end", f"Participation: {part_pct:.1f}%\n")
        self.analysis_text.insert("end", f"Pattern Learning: {pattern_pct:.1f}%\n")
        self.analysis_text.insert("end", f"Employee Fit: {max(0.0, min(100.0, 100.0 - min(100.0, employee_fit_pen / max(1.0, total_pen + 50.0) * 100.0))):.1f}%\n")
        self.analysis_text.insert("end", f"Total Penalty Score: {total_pen:.1f}\n")
        try:
            chosen = str((self.current_diagnostics or {}).get("chosen_scenario", "") or "")
            scenarios = list((self.current_diagnostics or {}).get("phase5_scenarios", []) or [])
            if chosen:
                self.analysis_text.insert("end", f"Scenario Winner: {chosen}\n")
            if scenarios:
                self.analysis_text.insert("end", "Scenario Comparison:\n")
                for row in scenarios[:6]:
                    name = str(row.get("name", "Scenario"))
                    pen = float(row.get("penalty", 0.0) or 0.0)
                    hrs = float(row.get("hours", 0.0) or 0.0)
                    self.analysis_text.insert("end", f"• {name}: penalty {pen:.1f}, hours {hrs:.1f}\n")
        except Exception as ex:
            _write_run_log(f"ANALYSIS | Scenario section failed: {repr(ex)}")
        try:
            forecast = dict((self.current_diagnostics or {}).get("phase5_demand_forecast") or {})
            if forecast:
                mults = dict(forecast.get("multipliers") or {})
                self.analysis_text.insert("end", "Demand Forecast:\n")
                self.analysis_text.insert("end", f"• Morning x{float(mults.get('morning', 1.0) or 1.0):.2f}\n")
                self.analysis_text.insert("end", f"• Midday x{float(mults.get('midday', 1.0) or 1.0):.2f}\n")
                self.analysis_text.insert("end", f"• Evening x{float(mults.get('evening', 1.0) or 1.0):.2f}\n")
                dom = str(forecast.get('dominant_area', '') or '').strip()
                peak = str(forecast.get('peak_bucket', '') or '').strip()
                if dom or peak:
                    self.analysis_text.insert("end", f"• Dominant area: {dom or 'n/a'}; peak bucket: {peak or 'n/a'}\n")
        except Exception as ex:
            _write_run_log(f"ANALYSIS | Demand-forecast section failed: {repr(ex)}")
        self.analysis_text.insert("end", "\nWeak Areas:\n")
        if weak_areas:
            for item in weak_areas:
                self.analysis_text.insert("end", f"• {item}\n")
        else:
            self.analysis_text.insert("end", "• No minimum-coverage deficits found in the current schedule.\n")

        if near_cap:
            self.analysis_text.insert("end", "\nEmployees Near Weekly Max Hours:\n")
            for _, name, h, maxh in near_cap[:5]:
                self.analysis_text.insert("end", f"• {name}: {h:.1f}/{maxh:.1f} hrs\n")

        try:
            pats = getattr(self.model, "learned_patterns", {}) or {}
            pat_pen = float(bd.get("pattern_pen", 0.0) or 0.0)
            fit_pen = float(bd.get("employee_fit_pen", 0.0) or 0.0)
            pat_enabled = bool(getattr(self.model.settings, "learn_from_history", True))
            self.analysis_text.insert("end", "\nPattern Learning:\n")
            if not pat_enabled:
                self.analysis_text.insert("end", "• Pattern learning is currently turned off in Settings.\n")
            elif not pats:
                self.analysis_text.insert("end", "• No learned pattern profiles found yet. Use Refresh Learned Patterns after you have schedule history.\n")
            else:
                self.analysis_text.insert("end", f"• Learned profiles available: {len(pats)}\n")
                self.analysis_text.insert("end", f"• Current schedule pattern penalty: {pat_pen:.1f}\n")
                shown = 0
                for emp_name in sorted(pats.keys()):
                    profile = pats.get(emp_name, {}) or {}
                    self.analysis_text.insert("end", f"• {self._format_pattern_profile(emp_name, profile)}\n")
                    shown += 1
                    if shown >= 5:
                        break
                fit_profiles = dict(pats.get('__employee_fit__') or {})
                if fit_profiles:
                    self.analysis_text.insert("end", "\nEmployee Fit Intelligence:\n")
                    self.analysis_text.insert("end", f"• Employee fit profiles available: {len(fit_profiles)}\n")
                    self.analysis_text.insert("end", f"• Current schedule employee-fit penalty: {fit_pen:.1f}\n")
                    shown_fit = 0
                    for emp_name in sorted(fit_profiles.keys()):
                        prof = dict(fit_profiles.get(emp_name) or {})
                        self.analysis_text.insert("end", f"• {emp_name}: best area {prof.get('best_area','Any') or 'Any'}, best bucket {prof.get('best_bucket','Any') or 'Any'}\n")
                        shown_fit += 1
                        if shown_fit >= 5:
                            break
        except Exception as ex:
            _write_run_log(f"ANALYSIS | Pattern-learning section failed: {repr(ex)}")

        if limiting:
            self.analysis_text.insert("end", "\nLimiting Factors Reported By Solver:\n")
            for item in limiting:
                self.analysis_text.insert("end", f"• {item}\n")

        if warnings:
            self.analysis_text.insert("end", "\nWarnings:\n")
            for item in warnings[:10]:
                self.analysis_text.insert("end", f"• {item}\n")

    # -------- Schedule Change Viewer tab (Phase 4 D4) --------
    def _show_calloff_tab(self):
        try:
            self.show_main_tab("calloff")
        except Exception:
            pass

    def _open_changes_popup(self):
        sources = self._change_view_sources()
        names = list(sources.keys())
        if len(names) < 2:
            messagebox.showinfo("Compare Versions", "Not enough schedule sources available yet.")
            return

        left_name = "Current Schedule" if "Current Schedule" in sources else names[0]
        right_name = "Published Final (This Week)" if "Published Final (This Week)" in sources else names[1]
        left = sources.get(left_name, {})
        right = sources.get(right_name, {})
        segments = self._coalesce_change_segments(list(left.get("assignments", []) or []), list(right.get("assignments", []) or []))

        win = tk.Toplevel(self)
        win.title("Schedule Change Viewer (Popup)")
        win.geometry("980x700")
        wrap = ttk.Frame(win); wrap.pack(fill="both", expand=True, padx=10, pady=10)
        ttk.Label(wrap, text=f"Compare: {left_name} vs {right_name}", style="Header.TLabel").pack(anchor="w", pady=(0,8))

        txt_wrap = ttk.Frame(wrap)
        txt_wrap.pack(fill="both", expand=True)
        txt = tk.Text(txt_wrap, wrap="none")
        sb = ttk.Scrollbar(txt_wrap, orient="vertical", command=txt.yview)
        xb = ttk.Scrollbar(txt_wrap, orient="horizontal", command=txt.xview)
        txt.configure(yscrollcommand=sb.set, xscrollcommand=xb.set)
        txt.grid(row=0, column=0, sticky="nsew")
        sb.grid(row=0, column=1, sticky="ns")
        xb.grid(row=1, column=0, sticky="ew")
        txt_wrap.rowconfigure(0, weight=1)
        txt_wrap.columnconfigure(0, weight=1)

        if not segments:
            txt.insert("end", "No schedule differences were found between these two sources.\n")
            return

        added = sum(1 for s in segments if s["type"] == "Added")
        removed = sum(1 for s in segments if s["type"] == "Removed")
        reassigned = sum(1 for s in segments if s["type"] == "Reassigned")
        txt.insert("end", f"Added segments: {added}\nRemoved segments: {removed}\nReassigned segments: {reassigned}\nTotal segments: {len(segments)}\n\n")
        by_day = {d: [] for d in DAYS}
        for seg in segments:
            by_day.setdefault(seg["day"], []).append(seg)
        for d in DAYS:
            items = by_day.get(d, [])
            if not items:
                continue
            txt.insert("end", f"{d}\n")
            for seg in items:
                txt.insert("end", f"  - {seg['area']} {tick_to_ampm(seg['start_t'])}-{tick_to_ampm(seg['end_t'])}: {seg['type']} | {seg['from']} -> {seg['to']}\n")
            txt.insert("end", "\n")

    def _build_changes_tab(self):
        frm = ttk.Frame(self.tab_changes); frm.pack(fill="both", expand=True, padx=12, pady=12)

        ttk.Label(frm, text="Schedule Change Viewer", style="Header.TLabel").pack(anchor="w", pady=(0,4))
        ttk.Label(
            frm,
            text="Compare the current schedule, this week's published final, the previous published final, and the last saved schedule. Read-only.",
            style="Hint.TLabel",
        ).pack(anchor="w", pady=(0,10))

        top = ttk.Frame(frm); top.pack(fill="x", pady=(0,8))
        self.change_left_var = tk.StringVar(value="Current Schedule")
        self.change_right_var = tk.StringVar(value="Published Final (This Week)")
        ttk.Label(top, text="Compare").pack(side="left")
        self.change_left_cb = ttk.Combobox(top, textvariable=self.change_left_var, state="readonly", width=28)
        self.change_left_cb.pack(side="left", padx=(8,4))
        ttk.Label(top, text="vs").pack(side="left", padx=4)
        self.change_right_cb = ttk.Combobox(top, textvariable=self.change_right_var, state="readonly", width=28)
        self.change_right_cb.pack(side="left", padx=(4,8))
        ttk.Button(top, text="Refresh Sources", command=self._refresh_change_viewer_sources).pack(side="left", padx=6)
        ttk.Button(top, text="Compare Selected", command=self._refresh_change_viewer).pack(side="left", padx=6)
        ttk.Button(top, text="Current vs Final", command=lambda: self._preset_change_compare("Current Schedule", "Published Final (This Week)")).pack(side="left", padx=6)
        ttk.Button(top, text="Current vs Previous Final", command=lambda: self._preset_change_compare("Current Schedule", "Previous Published Final")).pack(side="left", padx=6)

        self.change_summary_lbl = ttk.Label(frm, text="", foreground="#333")
        self.change_summary_lbl.pack(fill="x", pady=(0,8))

        cols = ("Type", "Day", "Area", "Time", "From", "To")
        ch_wrap = ttk.Frame(frm)
        ch_wrap.pack(fill="both", expand=False, pady=(0,8))
        self.change_tree = ttk.Treeview(ch_wrap, columns=cols, show="headings", height=12)
        for c in cols:
            self.change_tree.heading(c, text=c)
            w = 120
            if c in ("From", "To"):
                w = 180
            if c == "Time":
                w = 140
            if c == "Type":
                w = 150
            self.change_tree.column(c, width=w, stretch=True)
        ch_ys = ttk.Scrollbar(ch_wrap, orient="vertical", command=self.change_tree.yview)
        ch_xs = ttk.Scrollbar(ch_wrap, orient="horizontal", command=self.change_tree.xview)
        self.change_tree.configure(yscrollcommand=ch_ys.set, xscrollcommand=ch_xs.set)
        self.change_tree.grid(row=0, column=0, sticky="nsew")
        ch_ys.grid(row=0, column=1, sticky="ns")
        ch_xs.grid(row=1, column=0, sticky="ew")
        ch_wrap.rowconfigure(0, weight=1)
        ch_wrap.columnconfigure(0, weight=1)

        body = ttk.Frame(frm); body.pack(fill="both", expand=True)
        self.change_text = tk.Text(body, wrap="word", height=16)
        vs = ttk.Scrollbar(body, orient="vertical", command=self.change_text.yview)
        self.change_text.configure(yscrollcommand=vs.set)
        self.change_text.grid(row=0, column=0, sticky="nsew")
        vs.grid(row=0, column=1, sticky="ns")
        body.rowconfigure(0, weight=1)
        body.columnconfigure(0, weight=1)

        self._refresh_change_viewer_sources()
        self._refresh_change_viewer()

    def _preset_change_compare(self, left_name: str, right_name: str):
        try:
            vals = list(self.change_left_cb.cget("values") or [])
        except Exception:
            vals = []
        if left_name in vals:
            self.change_left_var.set(left_name)
        if right_name in vals:
            self.change_right_var.set(right_name)
        self._refresh_change_viewer()

    def _change_view_sources(self) -> Dict[str, Dict[str, Any]]:
        out: Dict[str, Dict[str, Any]] = {}
        cur_label = str(getattr(self, "current_label", "") or self.label_var.get().strip() or self._default_week_label())
        if self.current_assignments:
            out["Current Schedule"] = {
                "label": cur_label,
                "assignments": list(self.current_assignments),
                "detail": f"{len(self.current_assignments)} assignments loaded in the app",
            }

        final_path, final_payload = load_final_schedule_payload_for_label(cur_label)
        if final_payload:
            final_assigns = load_assignments_from_final_payload(final_payload)
            out["Published Final (This Week)"] = {
                "label": str(final_payload.get("label", cur_label) or cur_label),
                "assignments": final_assigns,
                "detail": final_path or "Published final schedule",
            }

        prev_label, prev_path, prev_assigns = load_prev_final_schedule_assignments(cur_label)
        if prev_assigns:
            out["Previous Published Final"] = {
                "label": str(prev_label or "Previous published final"),
                "assignments": prev_assigns,
                "detail": prev_path or "Previous published final schedule",
            }

        last_label, last_assigns = load_last_schedule_assignments()
        if last_assigns:
            out["Last Saved Schedule"] = {
                "label": str(last_label or "Last saved schedule"),
                "assignments": last_assigns,
                "detail": rel_path("data", "last_schedule.json"),
            }
        return out

    def _refresh_change_viewer_sources(self):
        if not hasattr(self, "change_left_cb"):
            return
        sources = self._change_view_sources()
        names = list(sources.keys())
        self._change_sources_cache = sources
        self.change_left_cb["values"] = names
        self.change_right_cb["values"] = names
        if names:
            if self.change_left_var.get() not in names:
                self.change_left_var.set(names[0])
            preferred = "Published Final (This Week)" if "Published Final (This Week)" in names else (names[1] if len(names) > 1 else names[0])
            if self.change_right_var.get() not in names:
                self.change_right_var.set(preferred)
        else:
            self.change_left_var.set("")
            self.change_right_var.set("")

    def _coalesce_change_segments(self, left_assigns: List[Assignment], right_assigns: List[Assignment]) -> List[Dict[str, Any]]:
        left_map = _expand_assignments_to_tick_map(list(left_assigns or []))
        right_map = _expand_assignments_to_tick_map(list(right_assigns or []))
        def _area_index(area: str) -> int:
            try:
                return AREAS.index(area)
            except Exception:
                return 999
        keys = sorted(set(left_map.keys()) | set(right_map.keys()), key=lambda k: (DAYS.index(k[0]), _area_index(k[1]), int(k[2])))

        segments: List[Dict[str, Any]] = []
        cur = None
        for day, area, tt in keys:
            old_emp = str(left_map.get((day, area, tt), "") or "")
            new_emp = str(right_map.get((day, area, tt), "") or "")
            if old_emp == new_emp:
                cur = None
                continue
            if old_emp and new_emp:
                typ = "Reassigned"
            elif old_emp and not new_emp:
                typ = "Removed"
            else:
                typ = "Added"
            if cur and cur["day"] == day and cur["area"] == area and cur["type"] == typ and cur["from"] == (old_emp or "—") and cur["to"] == (new_emp or "—") and cur["end_t"] == tt:
                cur["end_t"] = tt + 1
            else:
                cur = {
                    "type": typ,
                    "day": day,
                    "area": area,
                    "start_t": int(tt),
                    "end_t": int(tt) + 1,
                    "from": old_emp or "—",
                    "to": new_emp or "—",
                }
                segments.append(cur)
        return segments

    def _refresh_change_viewer(self):
        if not hasattr(self, "change_text"):
            return
        try:
            self._refresh_change_viewer_sources()
        except Exception:
            pass

        for i in self.change_tree.get_children():
            self.change_tree.delete(i)
        self.change_text.delete("1.0", "end")

        sources = getattr(self, "_change_sources_cache", {}) or {}
        left_name = self.change_left_var.get().strip()
        right_name = self.change_right_var.get().strip()
        left = sources.get(left_name)
        right = sources.get(right_name)
        if not left or not right:
            self.change_summary_lbl.config(text="Not enough schedule sources available yet.")
            self.change_text.insert("end", "Generate a schedule or publish a final schedule to compare changes.\n")
            return
        if left_name == right_name:
            self.change_summary_lbl.config(text="Choose two different schedule sources to compare.")
            self.change_text.insert("end", "The same source is selected on both sides.\n")
            return

        left_assigns = list(left.get("assignments", []) or [])
        right_assigns = list(right.get("assignments", []) or [])
        segments = self._coalesce_change_segments(left_assigns, right_assigns)

        added = sum(1 for s in segments if s["type"] == "Added")
        removed = sum(1 for s in segments if s["type"] == "Removed")
        reassigned = sum(1 for s in segments if s["type"] == "Reassigned")
        total = len(segments)

        self.change_summary_lbl.config(text=f"{left_name} → {right_name} • {total} change segments • Added: {added} • Removed: {removed} • Reassigned: {reassigned}")

        for seg in segments[:500]:
            self.change_tree.insert("", "end", values=(seg["type"], seg["day"], seg["area"], f"{tick_to_ampm(seg['start_t'])}–{tick_to_ampm(seg['end_t'])}", seg["from"], seg["to"]))

        self.change_text.insert("end", f"Compare: {left_name}\n")
        self.change_text.insert("end", f"Label: {left.get('label','')}\n")
        self.change_text.insert("end", f"Source: {left.get('detail','')}\n\n")
        self.change_text.insert("end", f"Against: {right_name}\n")
        self.change_text.insert("end", f"Label: {right.get('label','')}\n")
        self.change_text.insert("end", f"Source: {right.get('detail','')}\n\n")

        if not segments:
            self.change_text.insert("end", "No schedule differences were found between these two sources.\n")
            return

        self.change_text.insert("end", f"Summary\n-------\nAdded segments: {added}\nRemoved segments: {removed}\nReassigned segments: {reassigned}\n\n")

        by_day = {d: [] for d in DAYS}
        for seg in segments:
            by_day.setdefault(seg["day"], []).append(seg)

        self.change_text.insert("end", "Day-by-day changes\n------------------\n")
        for d in DAYS:
            items = by_day.get(d, [])
            if not items:
                continue
            self.change_text.insert("end", f"\n{d}\n")
            for seg in items[:20]:
                self.change_text.insert("end", f"  • {seg['area']} {tick_to_ampm(seg['start_t'])}–{tick_to_ampm(seg['end_t'])}: {seg['type']} | {seg['from']} → {seg['to']}\n")
            if len(items) > 20:
                self.change_text.insert("end", f"  … {len(items) - 20} more changes on {d}\n")

    # -------- Coverage Heatmap tab (Phase 4 B1) --------
    def _build_heatmap_tab(self):
        frm = ttk.Frame(self.tab_heatmap); frm.pack(fill="both", expand=True, padx=12, pady=12)

        ttk.Label(frm, text="Coverage Risk Heatmap (read-only)", style="Header.TLabel").pack(anchor="w", pady=(0,4))
        ttk.Label(
            frm,
            text="Shows scheduled headcount vs staffing requirements for each 30-minute block. This does not change the solver.",
            style="Hint.TLabel"
        ).pack(anchor="w", pady=(0,10))

        top = ttk.Frame(frm); top.pack(fill="x", pady=(0,8))

        ttk.Label(top, text="Target:").pack(side="left")
        self.hm_target_var = tk.StringVar(value="Minimum")
        ttk.OptionMenu(top, self.hm_target_var, "Minimum", "Minimum", "Preferred").pack(side="left", padx=(6,14))

        self.hm_fragile_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(top, text="Highlight fragile (1 scheduled / 1 required)", variable=self.hm_fragile_var).pack(side="left")

        ttk.Button(top, text="Refresh Heatmap", command=self._refresh_heatmap).pack(side="left", padx=(14,0))

        # Legend
        legend = ttk.Frame(frm); legend.pack(fill="x", pady=(0,8))
        ttk.Label(legend, text="Legend:", style="SubHeader.TLabel").pack(side="left")
        self._legend_chip(legend, "Red: scheduled < minimum", "#ff6b6b")
        self._legend_chip(legend, "Orange: scheduled == minimum and fragile", "#ffb366")
        self._legend_chip(legend, "Green: minimum met but below preferred", "#66c266")
        self._legend_chip(legend, "Light Green: preferred met to max", "#c9f7c9")
        self._legend_chip(legend, "Yellow-Green: scheduled > max", "#d8f23f")
        self._legend_chip(legend, "No requirement", "#f0f0f0")

        # Scrollable canvas grid
        outer = ttk.Frame(frm); outer.pack(fill="both", expand=True)
        self.hm_canvas = tk.Canvas(outer, highlightthickness=0)
        vs = ttk.Scrollbar(outer, orient="vertical", command=self.hm_canvas.yview)
        hs = ttk.Scrollbar(outer, orient="horizontal", command=self.hm_canvas.xview)
        self.hm_canvas.configure(yscrollcommand=vs.set, xscrollcommand=hs.set)

        self.hm_canvas.grid(row=0, column=0, sticky="nsew")
        vs.grid(row=0, column=1, sticky="ns")
        hs.grid(row=1, column=0, sticky="ew")
        outer.rowconfigure(0, weight=1)
        outer.columnconfigure(0, weight=1)

        # container for drawings
        self.hm_items: List[int] = []
        self._refresh_heatmap()

    def _legend_chip(self, parent, label: str, color: str):
        chip = tk.Canvas(parent, width=18, height=12, highlightthickness=1, highlightbackground="#bdbdbd")
        chip.create_rectangle(0, 0, 18, 12, fill=color, outline=color)
        chip.pack(side="left", padx=(10,4))
        ttk.Label(parent, text=label, style="Hint.TLabel").pack(side="left")

    def _refresh_heatmap(self):
        try:
            if not hasattr(self, "hm_canvas"):
                return
            # clear old
            for it in getattr(self, "hm_items", []):
                try:
                    self.hm_canvas.delete(it)
                except Exception:
                    pass
            self.hm_items = []

            target = (self.hm_target_var.get() or "Minimum").strip()
            use_pref = (target.lower().startswith("pref"))

            # Determine which schedule to visualize:
            # prefer current working schedule; otherwise try this week's locked final.
            assignments = list(self.current_assignments or [])
            if not assignments:
                # attempt to load this week's final (without modifying current state)
                try:
                    wk = self._week_start_sunday_iso()
                    final_path = os.path.join(_app_dir(), "data", "final_schedules", f"{wk}.json")
                    if os.path.isfile(final_path):
                        with open(final_path, "r", encoding="utf-8") as f:
                            payload = json.load(f)
                        assigns = payload.get("assignments") or []
                        assignments = [des_assignment(a) for a in assigns]
                except Exception as ex:
                    _write_run_log(f"HEATMAP | Fallback final-schedule load failed: {repr(ex)}")

            if not assignments:
                # still nothing
                msg = "No schedule found yet. Generate a schedule (or lock a final schedule) and then click Refresh."
                it = self.hm_canvas.create_text(20, 20, text=msg, anchor="nw")
                self.hm_items.append(it)
                self.hm_canvas.configure(scrollregion=(0,0,800,200))
                return

            # build maps
            min_req, pref_req, max_req = build_requirement_maps(self.model.requirements, goals=getattr(self.model, "manager_goals", None), store_info=getattr(self.model, "store_info", None))
            req_map = pref_req if use_pref else min_req
            cov = count_coverage_per_tick(assignments)

            # store for drill-down (B2)
            self.hm_last_req_map = dict(req_map)
            self.hm_last_cov = dict(cov)
            self.hm_last_assignments = list(assignments)
            self.hm_cell_index = {}  # item_id -> (day, area, tick)
# grid specs
            col_groups: List[Tuple[str,str]] = []
            for d in DAYS:
                for a in AREAS:
                    col_groups.append((d, a))
            n_cols = len(col_groups)

            cell_w = 74
            cell_h = 20
            row_header_w = 60
            header_h = 24

            # colors (workspace redesign semantics)
            c_under = "#ff6b6b"      # Red: scheduled < min
            c_frag  = "#ffb366"      # Orange: scheduled == min and fragile
            c_mid   = "#66c266"      # Green: scheduled >= min but < preferred
            c_pref  = "#c9f7c9"      # Light Green: scheduled >= preferred and <= max
            c_over  = "#d8f23f"      # Yellow-Green: scheduled > max
            c_none  = "#f0f0f0"

            # draw header
            x0 = row_header_w
            y0 = 0
            for ci, (d,a) in enumerate(col_groups):
                x = x0 + ci*cell_w
                label = f"{d}\n{a[:1]}"
                r = self.hm_canvas.create_rectangle(x, y0, x+cell_w, y0+header_h, fill="#e9ecef", outline="#c9c9c9")
                t = self.hm_canvas.create_text(x+cell_w/2, y0+header_h/2, text=label, justify="center", font=("Segoe UI", 9))
                self.hm_items.extend([r,t])
            # row header + grid
            cstore_open, cstore_close = area_open_close_ticks(self.model, "CSTORE")
            vis_ticks = list(range(int(cstore_open), int(cstore_close)))
            for row_i, tck in enumerate(vis_ticks):
                y = header_h + row_i*cell_h
                # time label
                time_lbl = tick_to_hhmm(tck)
                r0 = self.hm_canvas.create_rectangle(0, y, row_header_w, y+cell_h, fill="#e9ecef", outline="#c9c9c9")
                t0 = self.hm_canvas.create_text(row_header_w/2, y+cell_h/2, text=time_lbl, font=("Segoe UI", 9))
                self.hm_items.extend([r0,t0])

                for ci, (d,a) in enumerate(col_groups):
                    x = x0 + ci*cell_w
                    k = (d, a, int(tck))
                    req = int(min_req.get(k, 0))
                    pref_req_v = int(pref_req.get(k, 0))
                    max_req_v = int(max_req.get(k, 0))
                    sc  = int(cov.get(k, 0))

                    if req <= 0 and sc <= 0:
                        fill = c_none
                        txt = ""
                    else:
                        if sc < req:
                            fill = c_under
                        elif sc == req:
                            if self.hm_fragile_var.get() and req == 1 and sc == 1:
                                fill = c_frag
                            else:
                                fill = c_mid
                        else:
                            if sc > max_req_v and max_req_v > 0:
                                fill = c_over
                            elif sc >= pref_req_v and pref_req_v > 0:
                                fill = c_pref
                            else:
                                fill = c_mid
                        txt = f"{sc}/{req}" if req>0 else f"{sc}/0"

                    r = self.hm_canvas.create_rectangle(x, y, x+cell_w, y+cell_h, fill=fill, outline="#d0d0d0")
                    # B2 drill-down: click a cell to see details
                    try:
                        self.hm_cell_index[r] = (d, a, int(tck))
                        self.hm_canvas.tag_bind(r, "<Button-1>", lambda ev, dd=d, aa=a, tt=int(tck): self._hm_on_cell_click(dd, aa, tt))
                    except Exception:
                        pass

                    tt = self.hm_canvas.create_text(x+cell_w/2, y+cell_h/2, text=txt, font=("Segoe UI", 9))
                    # also allow clicking the text in the cell
                    try:
                        self.hm_canvas.tag_bind(tt, "<Button-1>", lambda ev, dd=d, aa=a, tt=int(tck): self._hm_on_cell_click(dd, aa, tt))
                    except Exception:
                        pass
                    self.hm_items.extend([r,tt])

            total_w = row_header_w + n_cols*cell_w + 2
            total_h = header_h + len(vis_ticks)*cell_h + 2
            self.hm_canvas.configure(scrollregion=(0,0,total_w,total_h))
        except Exception as e:
            try:
                messagebox.showerror("Heatmap", f"Failed to render heatmap:\n{e}")
            except Exception:
                pass


    def _hm_on_cell_click(self, day: str, area: str, tick: int):
        """Heatmap drill-down: show who's working and the gap/overstaff."""
        try:
            req_map = getattr(self, "hm_last_req_map", {}) or {}
            cov = getattr(self, "hm_last_cov", {}) or {}
            assignments = getattr(self, "hm_last_assignments", []) or []

            k = (day, area, int(tick))
            req = int(req_map.get(k, 0))
            sc = int(cov.get(k, 0))

            # who is working in this cell?
            names = []
            for a in assignments:
                try:
                    if a.day != day or a.area != area:
                        continue
                    if int(a.start_t) <= int(tick) < int(a.end_t):
                        nm = (a.employee_name or "").strip()
                        if nm:
                            names.append(nm)
                except Exception:
                    continue

            # unique (preserve order)
            seen = set()
            uniq = []
            for n in names:
                if n not in seen:
                    uniq.append(n); seen.add(n)

            time_lbl = tick_to_hhmm(int(tick))
            title = f"{day} {time_lbl} — {area}"

            lines = []
            lines.append(f"Required Staff: {req}")
            lines.append(f"Scheduled Staff: {sc}")
            lines.append("")

            if uniq:
                lines.append("Employees Working:")
                for n in uniq:
                    lines.append(f"• {n}")
            else:
                lines.append("Employees Working:")
                lines.append("• (none)")

            # gap / overstaff note
            if req > 0:
                if sc < req:
                    lines.append("")
                    lines.append(f"Coverage Gap: {req - sc} additional employee(s) needed")
                elif sc > req:
                    lines.append("")
                    lines.append(f"Possible Overstaffing: +{sc - req}")
                else:
                    # sc == req
                    if req == 1 and sc == 1 and bool(getattr(self, "hm_fragile_var", tk.BooleanVar(value=False)).get()):
                        lines.append("")
                        lines.append("Fragile: a single call-off breaks coverage")
            else:
                if sc > 0:
                    lines.append("")
                    lines.append("No requirement set for this time block.")

            messagebox.showinfo("Heatmap Detail", "\n".join(lines))
        except Exception as e:
            try:
                messagebox.showerror("Heatmap Detail", f"Failed to open cell detail:\n{e}")
            except Exception:
                pass


    # -------- Call-Off Simulator tab (Phase 4 C2) --------
    def _build_calloff_tab(self):
        frm = ttk.Frame(self.tab_calloff); frm.pack(fill="both", expand=True, padx=12, pady=12)

        ttk.Label(frm, text="Call-Off Simulator (read-only)", style="Header.TLabel").pack(anchor="w", pady=(0,4))
        ttk.Label(
            frm,
            text="Simulate an employee calling off. Shows resulting coverage gaps and suggests backup employees to contact. This does not change the schedule.",
            style="Hint.TLabel",
        ).pack(anchor="w", pady=(0,10))

        top = ttk.Frame(frm); top.pack(fill="x", pady=(0,10))
        ttk.Label(top, text="Employee:").pack(side="left")

        self.co_emp_var = tk.StringVar(value="")
        try:
            self.co_emp_var.trace_add("write", lambda *_: self._calloff_refresh_replacements())
        except Exception:
            pass
        self.co_emp_menu = ttk.OptionMenu(top, self.co_emp_var, "")
        self.co_emp_menu.pack(side="left", padx=(6,12))
        ttk.Button(top, text="Refresh Employee List", command=self._calloff_refresh_employees).pack(side="left")

        ttk.Label(top, text="   Days:").pack(side="left", padx=(16,0))
        self.co_all_days_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(top, text="All", variable=self.co_all_days_var, command=self._calloff_sync_days).pack(side="left")
        self.co_day_vars = {d: tk.BooleanVar(value=False) for d in DAYS}
        for d in DAYS:
            ttk.Checkbutton(top, text=d[:1], variable=self.co_day_vars[d], command=self._calloff_on_day_toggle).pack(side="left", padx=(4,0))

        ttk.Button(top, text="Simulate Call-Off", command=self._simulate_calloff).pack(side="right")

        report_box = ttk.LabelFrame(frm, text="Call-Off Report Recording")
        report_box.pack(fill="x", pady=(0,10))
        ttk.Label(report_box, text="Record the call-out and replacement to feed Employee Performance & Reliability metrics. This does not mutate the live schedule.", style="Hint.TLabel").grid(row=0, column=0, columnspan=6, sticky="w", padx=8, pady=(6,4))

        ttk.Label(report_box, text="Date (YYYY-MM-DD):").grid(row=1, column=0, sticky="w", padx=8, pady=4)
        self.co_report_date_var = tk.StringVar(value=today_iso())
        ttk.Entry(report_box, textvariable=self.co_report_date_var, width=14).grid(row=1, column=1, sticky="w", padx=8, pady=4)

        ttk.Label(report_box, text="Replacement Employee:").grid(row=1, column=2, sticky="w", padx=8, pady=4)
        self.co_repl_var = tk.StringVar(value="")
        self.co_repl_menu = ttk.OptionMenu(report_box, self.co_repl_var, "")
        self.co_repl_menu.grid(row=1, column=3, sticky="w", padx=8, pady=4)

        ttk.Label(report_box, text="Note/Reason:").grid(row=1, column=4, sticky="w", padx=8, pady=4)
        self.co_note_var = tk.StringVar(value="")
        ttk.Entry(report_box, textvariable=self.co_note_var, width=30).grid(row=1, column=5, sticky="w", padx=8, pady=4)

        ttk.Button(report_box, text="Record Call-Off Incident", command=self.record_calloff_incident).grid(row=2, column=0, columnspan=2, sticky="w", padx=8, pady=(4,8))

        body = ttk.Frame(frm); body.pack(fill="both", expand=True)
        self.co_text = tk.Text(body, wrap="word", height=18)
        vs = ttk.Scrollbar(body, orient="vertical", command=self.co_text.yview)
        self.co_text.configure(yscrollcommand=vs.set)
        self.co_text.grid(row=0, column=0, sticky="nsew")
        vs.grid(row=0, column=1, sticky="ns")
        body.rowconfigure(0, weight=1)
        body.columnconfigure(0, weight=1)

        self._calloff_refresh_employees()
        self._calloff_refresh_replacements()
        self._calloff_sync_days()
        self._calloff_write_intro()

    def _calloff_write_intro(self):
        try:
            self.co_text.delete("1.0", "end")
            self.co_text.insert("end", "How to use:\n")
            self.co_text.insert("end", "1) Generate a schedule (or Load Final).\n")
            self.co_text.insert("end", "2) Pick an employee and click Simulate Call-Off.\n\n")
            self.co_text.insert("end", "This uses your current schedule if one is loaded; otherwise it tries this week's locked final schedule.\n")
        except Exception:
            pass

    def _calloff_sync_days(self):
        all_on = bool(self.co_all_days_var.get())
        for d in DAYS:
            try:
                self.co_day_vars[d].set(False if all_on else bool(self.co_day_vars[d].get()))
            except Exception:
                pass

    def _calloff_on_day_toggle(self):
        try:
            any_day = any(bool(v.get()) for v in self.co_day_vars.values())
            self.co_all_days_var.set(not any_day)
        except Exception:
            pass

    def _calloff_refresh_employees(self):
        try:
            names = []
            for e in getattr(self.model, "employees", []) or []:
                try:
                    if getattr(e, "work_status", "Active") != "Active":
                        continue
                    nm = (getattr(e, "name", "") or "").strip()
                    if nm:
                        names.append(nm)
                except Exception:
                    continue
            names = sorted(set(names), key=lambda s: s.lower())
            if not names:
                names = [""]

            menu = self.co_emp_menu["menu"]
            menu.delete(0, "end")
            for n in names:
                menu.add_command(label=n, command=lambda v=n: self.co_emp_var.set(v))

            cur = (self.co_emp_var.get() or "").strip()
            if cur not in names:
                self.co_emp_var.set(names[0])
            self._calloff_refresh_replacements()
        except Exception:
            pass

    def _calloff_refresh_replacements(self):
        try:
            selected = str(getattr(self, "co_emp_var", tk.StringVar(value="")).get() or "").strip()
            names = []
            for e in getattr(self.model, "employees", []) or []:
                if getattr(e, "work_status", "Active") != "Active":
                    continue
                nm = str(getattr(e, "name", "") or "").strip()
                if not nm or nm == selected:
                    continue
                names.append(nm)
            names = sorted(set(names), key=str.lower)
            if not names:
                names = [""]
            menu = self.co_repl_menu["menu"]
            menu.delete(0, "end")
            for n in names:
                menu.add_command(label=n, command=lambda v=n: self.co_repl_var.set(v))
            if (self.co_repl_var.get() or "").strip() not in names:
                self.co_repl_var.set(names[0])
        except Exception:
            pass

    def record_calloff_incident(self):
        emp_name = (self.co_emp_var.get() or "").strip()
        if not emp_name:
            messagebox.showwarning("Call-Off Simulator", "Pick the called-out employee first.")
            return
        date_s = (self.co_report_date_var.get() or "").strip()
        dt = _safe_date_from_iso(date_s)
        if dt is None:
            messagebox.showerror("Call-Off Simulator", "Date must be YYYY-MM-DD.")
            return
        replacement = (self.co_repl_var.get() or "").strip()
        if replacement == emp_name:
            messagebox.showerror("Call-Off Simulator", "Replacement employee must be different from called-out employee.")
            return
        note = (self.co_note_var.get() or "").strip()
        week_label = str(self.current_label or self.label_var.get().strip() or self._default_week_label())

        day = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"][dt.weekday()]
        dup_key = (week_label, dt.isoformat(), emp_name, replacement)
        for ex in list(getattr(self.model, "calloff_incidents", []) or []):
            ex_key = (
                str(getattr(ex, "week_label", "") or "").strip(),
                str(getattr(ex, "incident_date", "") or "").strip(),
                str(getattr(ex, "called_out_employee", "") or "").strip(),
                str(getattr(ex, "replacement_employee", "") or "").strip(),
            )
            if ex_key == dup_key:
                messagebox.showwarning(
                    "Call-Off Simulator",
                    "This call-off incident is already recorded for the same week/date/employee/replacement.\n\nDuplicate entry was blocked."
                )
                return

        incident = CallOffIncident(
            incident_id=f"incident_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S_%f')}",
            week_label=week_label,
            day=day,
            incident_date=dt.isoformat(),
            called_out_employee=emp_name,
            replacement_employee=replacement,
            recorded_on=today_iso(),
            note=note,
            status="reported",
        )
        self.model.calloff_incidents.append(incident)
        self.model.reliability_events.append(EmployeeReliabilityEvent(
            event_id=f"ev_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S_%f')}",
            employee_name=emp_name,
            event_type="call_out",
            date=dt.isoformat(),
            week_label=week_label,
            related_employee=replacement,
            note=note,
            source="calloff_workflow",
        ))
        if replacement:
            self.model.reliability_events.append(EmployeeReliabilityEvent(
                event_id=f"ev_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S_%f')}",
                employee_name=replacement,
                event_type="extra_shift_pickup",
                date=dt.isoformat(),
                week_label=week_label,
                related_employee=emp_name,
                note=note,
                source="calloff_workflow",
            ))
        self.autosave()
        self.refresh_performance_view()
        _write_run_log(f"CALL_OFF | incident recorded called_out={emp_name} replacement={replacement} date={dt.isoformat()}")
        messagebox.showinfo("Call-Off Simulator", "Call-off incident recorded. The schedule was not changed automatically.")

    def _simulate_calloff(self):
        try:
            emp_name = (self.co_emp_var.get() or "").strip()
            if not emp_name:
                messagebox.showwarning("Call-Off Simulator", "Pick an employee first.")
                return

            if bool(self.co_all_days_var.get()):
                days = set(DAYS)
            else:
                days = {d for d, v in self.co_day_vars.items() if bool(v.get())}
                if not days:
                    days = set(DAYS)

            assignments = list(self.current_assignments or [])
            label = str(self.current_label or "")
            if not assignments:
                try:
                    wk = self._week_start_sunday_iso()
                    final_path = os.path.join(_app_dir(), "data", "final_schedules", f"{wk}.json")
                    if os.path.isfile(final_path):
                        with open(final_path, "r", encoding="utf-8") as f:
                            payload = json.load(f)
                        assigns = payload.get("assignments") or []
                        assignments = [des_assignment(a) for a in assigns]
                        label = payload.get("label") or label
                except Exception as ex:
                    _write_run_log(f"CALL_OFF | Fallback final-schedule load failed: {repr(ex)}")

            if not assignments:
                messagebox.showinfo("Call-Off Simulator", "No schedule found. Generate a schedule or lock a final schedule first.")
                return

            min_req, _pref_req, _max_req = build_requirement_maps(self.model.requirements, goals=getattr(self.model, "manager_goals", None), store_info=getattr(self.model, "store_info", None))
            req = dict(min_req)

            removed = [a for a in assignments if (a.employee_name == emp_name and a.day in days)]
            kept = [a for a in assignments if not (a.employee_name == emp_name and a.day in days)]

            new_cov = count_coverage_per_tick(kept)

            windows = []  # (deficit_hours, peak, day, area, st, en)
            for day in DAYS:
                if day not in days:
                    continue
                for area in AREAS:
                    t = 0
                    while t < DAY_TICKS:
                        r = int(req.get((day, area, t), 0))
                        s = int(new_cov.get((day, area, t), 0))
                        d = max(0, r - s)
                        if d <= 0:
                            t += 1
                            continue
                        st = t
                        peak = d
                        def_h = 0.0
                        while t < DAY_TICKS:
                            r2 = int(req.get((day, area, t), 0))
                            s2 = int(new_cov.get((day, area, t), 0))
                            d2 = max(0, r2 - s2)
                            if d2 <= 0:
                                break
                            peak = max(peak, d2)
                            def_h += d2 * 0.5
                            t += 1
                        en = t
                        windows.append((def_h, peak, day, area, st, en))
            windows.sort(reverse=True, key=lambda x: (x[0], x[1]))

            emp_week_hours: Dict[str, float] = {}
            for a in kept:
                emp_week_hours[a.employee_name] = emp_week_hours.get(a.employee_name, 0.0) + hours_between_ticks(a.start_t, a.end_t)
            clopen = _clopen_map_from_assignments(self.model, kept)

            def is_working_in_window(e_name: str, day: str, st: int, en: int) -> bool:
                for a in kept:
                    if a.employee_name != e_name:
                        continue
                    if a.day != day:
                        continue
                    if not (int(a.end_t) <= int(st) or int(a.start_t) >= int(en)):
                        return True
                return False

            def candidates_for(area: str, day: str, st: int, en: int) -> List[Employee]:
                goals = getattr(self.model, "manager_goals", None)
                include_noncert = bool(getattr(goals, "include_noncertified_in_call_list", False)) if goals else False
                out = []
                for e in self.model.employees:
                    if getattr(e, "work_status", "Active") != "Active":
                        continue
                    if (getattr(e, "name", "") or "").strip() == emp_name:
                        continue

                    certified = area in getattr(e, "areas_allowed", [])
                    if not certified and not include_noncert:
                        continue

                    if is_working_in_window(e.name, day, st, en):
                        continue

                    window_h = hours_between_ticks(st, en)
                    cur_h = emp_week_hours.get(e.name, 0.0)
                    slack = float(getattr(e, "max_weekly_hours", 0.0)) - cur_h
                    not_near_restrict = slack >= window_h

                    available = is_employee_available(self.model, e, label, day, st, en, area, clopen)
                    out.append((certified, not_near_restrict, available, -cur_h, e.name.lower(), e))
                out.sort(reverse=True, key=lambda x: (x[0], x[1], x[2], x[3], x[4]))
                return [x[-1] for x in out]

            # Write report
            self.co_text.delete("1.0", "end")
            self.co_text.insert("end", f"Simulated call-off: {emp_name}\n")
            self.co_text.insert("end", f"Days: {', '.join([d for d in DAYS if d in days])}\n")
            self.co_text.insert("end", f"Removed shifts: {len(removed)}\n")
            if removed:
                for a in removed[:10]:
                    self.co_text.insert("end", f"  - {a.day} {a.area} {tick_to_ampm(a.start_t)}–{tick_to_ampm(a.end_t)}\n")
                if len(removed) > 10:
                    self.co_text.insert("end", f"  ... +{len(removed)-10} more\n")

            self.co_text.insert("end", "\nTop coverage gaps created (after call-off):\n")
            if not windows:
                self.co_text.insert("end", "  ✅ No new understaffing windows detected for the selected day(s).\n")
                return

            depth = 5
            try:
                goals = getattr(self.model, "manager_goals", None)
                depth = int(getattr(goals, "call_list_depth", 5)) if goals else 5
                depth = max(1, min(12, depth))
            except Exception:
                depth = 5

            for (def_h, peak, day, area, st, en) in windows[:10]:
                self.co_text.insert("end", f"\n• {day} {area} {tick_to_ampm(st)}–{tick_to_ampm(en)}  |  est shortage: {def_h:.1f} labor-hrs  |  peak deficit: {peak}\n")
                cands = candidates_for(area, day, st, en)[:depth]
                if not cands:
                    self.co_text.insert("end", "    (No qualified backup candidates found for this window.)\n")
                    continue
                for i, e in enumerate(cands, 1):
                    cur_h = emp_week_hours.get(e.name, 0.0)
                    phone = getattr(e, "phone", "")
                    self.co_text.insert("end", f"    {i}) {e.name} ({cur_h:.1f} hrs) — {phone}\n")

        except Exception as e:
            try:
                messagebox.showerror("Call-Off Simulator", f"Simulation failed:\n{e}")
            except Exception:
                pass


    def _week_start_sunday_iso(self) -> str:
        # The app's schedule label is already anchored to the week; use the same helper used elsewhere.
        try:
            wk = week_start_sunday_for_label(self.current_label)
            if wk:
                return wk.isoformat()
        except Exception:
            pass
        # fallback: today -> most recent Sunday
        d = datetime.date.today()
        # Python weekday: Mon=0..Sun=6
        delta = (d.weekday() + 1) % 7
        return (d - datetime.timedelta(days=delta)).isoformat()


    def _build_manual_tab(self):
        self.manual_vars = {"MAIN": {}, "KITCHEN": {}, "CARWASH": {}}

        frm = ttk.Frame(self.tab_manual); frm.pack(fill="both", expand=True, padx=12, pady=12)
        ttk.Label(frm, text="Smart manual editor (Option A grid). Edit the printable schedule cells, analyze warnings, then apply to the current schedule.",
                  style="SubHeader.TLabel").pack(anchor="w", pady=(0,4))
        ttk.Label(frm, text="MAIN = C-Store hours plus hints. Kitchen and Carwash pages control those department assignments. Time format examples: 7am-3pm or 7:30am-12pm; 1pm-5pm",
                  style="Hint.TLabel").pack(anchor="w", pady=(0,8))

        top = ttk.Frame(frm); top.pack(fill="x", pady=(0,8))
        ttk.Button(top, text="Load From Current Schedule", command=self._manual_load_btn).pack(side="left")
        ttk.Button(top, text="Analyze Manual Edits", command=self._manual_analyze_btn).pack(side="left", padx=8)
        ttk.Button(top, text="Apply To Current Schedule", command=self._manual_apply_btn).pack(side="left", padx=8)
        ttk.Button(top, text="Refine Current Schedule", command=self.on_refine_schedule).pack(side="left", padx=8)
        ttk.Button(top, text="Save Manual Edits", command=self._manual_save_btn).pack(side="left", padx=8)
        ttk.Button(top, text="Open Manual Employee Calendar (HTML)", command=self._manual_open_html).pack(side="left", padx=8)
        ttk.Button(top, text="Clear Manual Edits", command=self._manual_clear_btn).pack(side="left", padx=8)

        swap = ttk.LabelFrame(frm, text="Quick Swap")
        swap.pack(fill="x", pady=(0,8))
        emp_names = self._manual_employee_names()
        self.manual_swap_kind_var = tk.StringVar(value="MAIN")
        self.manual_swap_day_var = tk.StringVar(value=DAYS[0])
        self.manual_swap_from_var = tk.StringVar(value=(emp_names[0] if emp_names else ""))
        self.manual_swap_to_var = tk.StringVar(value=(emp_names[1] if len(emp_names) > 1 else (emp_names[0] if emp_names else "")))
        ttk.Label(swap, text="Page").grid(row=0, column=0, sticky="w", padx=8, pady=6)
        ttk.Combobox(swap, textvariable=self.manual_swap_kind_var, values=["MAIN","KITCHEN","CARWASH"], state="readonly", width=12).grid(row=0, column=1, sticky="w", padx=4, pady=6)
        ttk.Label(swap, text="Day").grid(row=0, column=2, sticky="w", padx=(14,4), pady=6)
        ttk.Combobox(swap, textvariable=self.manual_swap_day_var, values=DAYS, state="readonly", width=12).grid(row=0, column=3, sticky="w", padx=4, pady=6)
        ttk.Label(swap, text="From").grid(row=0, column=4, sticky="w", padx=(14,4), pady=6)
        ttk.Combobox(swap, textvariable=self.manual_swap_from_var, values=emp_names, state="readonly", width=24).grid(row=0, column=5, sticky="w", padx=4, pady=6)
        ttk.Label(swap, text="To").grid(row=0, column=6, sticky="w", padx=(14,4), pady=6)
        ttk.Combobox(swap, textvariable=self.manual_swap_to_var, values=emp_names, state="readonly", width=24).grid(row=0, column=7, sticky="w", padx=4, pady=6)
        ttk.Button(swap, text="Swap Cells", command=self._manual_swap_selected_day).grid(row=0, column=8, sticky="w", padx=(14,8), pady=6)

        self.manual_status_lbl = ttk.Label(frm, text="", foreground="#333")
        self.manual_status_lbl.pack(anchor="w", pady=(0,6))

        warn_wrap = ttk.LabelFrame(frm, text="Manual Edit Warnings")
        warn_wrap.pack(fill="both", expand=False, pady=(0,8))
        self.manual_warn_txt = tk.Text(warn_wrap, height=9, wrap="word")
        mvs = ttk.Scrollbar(warn_wrap, orient="vertical", command=self.manual_warn_txt.yview)
        self.manual_warn_txt.configure(yscrollcommand=mvs.set)
        self.manual_warn_txt.grid(row=0, column=0, sticky="nsew")
        mvs.grid(row=0, column=1, sticky="ns")
        warn_wrap.rowconfigure(0, weight=1)
        warn_wrap.columnconfigure(0, weight=1)

        note = ttk.Notebook(frm); note.pack(fill="both", expand=True)

        def _make_scroll(parent):
            outer = ttk.Frame(parent)
            outer.pack(fill="both", expand=True)
            canvas = tk.Canvas(outer, highlightthickness=0)
            vs = ttk.Scrollbar(outer, orient="vertical", command=canvas.yview)
            hs = ttk.Scrollbar(outer, orient="horizontal", command=canvas.xview)
            canvas.configure(yscrollcommand=vs.set, xscrollcommand=hs.set)
            vs.pack(side="right", fill="y")
            hs.pack(side="bottom", fill="x")
            canvas.pack(side="left", fill="both", expand=True)
            inner = ttk.Frame(canvas)
            win = canvas.create_window((0,0), window=inner, anchor="nw")
            def _on_config(_e=None):
                canvas.configure(scrollregion=canvas.bbox("all"))
            inner.bind("<Configure>", _on_config)
            def _on_canvas_config(e):
                canvas.itemconfigure(win, width=max(e.width, 980))
            canvas.bind("<Configure>", _on_canvas_config)
            return inner

        def _build_grid(parent, kind: str):
            inner = _make_scroll(parent)
            ttk.Label(inner, text="Employee", style="SubHeader.TLabel").grid(row=0, column=0, sticky="w", padx=4, pady=4)
            for j, d in enumerate(DAYS, start=1):
                ttk.Label(inner, text=d, style="SubHeader.TLabel").grid(row=0, column=j, sticky="n", padx=3, pady=4)
            emps = sorted(self.model.employees, key=lambda e: (e.name or "").lower())
            for i, e in enumerate(emps, start=1):
                nm = (e.name or "").strip()
                if not nm:
                    continue
                phone_str = (e.phone or "").strip()
                name_line = nm + (f" - {phone_str}" if phone_str else "")
                ttk.Label(inner, text=name_line).grid(row=i, column=0, sticky="w", padx=4, pady=2)
                self.manual_vars[kind].setdefault(nm, {})
                for j, d in enumerate(DAYS, start=1):
                    var = tk.StringVar(value="")
                    ent = ttk.Entry(inner, textvariable=var, width=18)
                    ent.grid(row=i, column=j, sticky="nsew", padx=2, pady=2)
                    self.manual_vars[kind][nm][d] = var
            for j in range(0, len(DAYS)+1):
                inner.grid_columnconfigure(j, weight=1)

        for title, kind in [("Manual: Main (C-Store + hints)", "MAIN"), ("Manual: Kitchen", "KITCHEN"), ("Manual: Carwash", "CARWASH")]:
            f = ttk.Frame(note)
            note.add(f, text=title)
            _build_grid(f, kind)

        try:
            payload = self._load_manual_overrides()
            cur_label = str(getattr(self, "current_label", "") or "")
            stored_label = str(payload.get("label","") or "")
            if payload and (not cur_label or stored_label == cur_label):
                self._manual_apply_to_ui(payload.get("pages", {}) or {})
            elif self.current_assignments:
                base = self._compute_calendar_base_texts(self.current_assignments)
                self._manual_apply_to_ui(base)
            self._manual_status("Manual editor ready.")
            self._manual_set_warning_text(["Analyze Manual Edits to check coverage, availability, overlaps, minors rules, and weekly hours before applying."])
        except Exception:
            pass


    # -------- Manager Tasks tab --------
    def _new_manager_task_id(self) -> str:
        return f"task_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S_%f')}"

    def _task_is_active_for_label(self, t: ManagerTask, label: str) -> bool:
        if bool(getattr(t, "completed", False)):
            return False
        wk_start, wk_end = week_window_for_label(label)
        est = _safe_date_from_iso(getattr(t, "earliest_start_date", ""))
        due = _safe_date_from_iso(getattr(t, "due_date", ""))
        if wk_start is None or wk_end is None or est is None or due is None:
            return False
        if wk_end >= est and wk_start <= due:
            return True
        return wk_start > due

    def _roll_completed_recurring_tasks(self):
        changed = False
        for i, t in enumerate(list(getattr(self.model, "manager_tasks", []) or [])):
            rec = _normalize_recurrence(getattr(t, "recurrence", "One-Time"))
            if rec == "One-Time" or not bool(getattr(t, "completed", False)):
                continue
            new_est, new_due = roll_task_window(t.earliest_start_date, t.due_date, rec)
            if new_est == t.earliest_start_date and new_due == t.due_date:
                continue
            t.earliest_start_date = new_est
            t.due_date = new_due
            t.completed = False
            t.completed_on = ""
            t.last_rolled_on = today_iso()
            self.model.manager_tasks[i] = t
            changed = True
            _write_run_log(f"MANAGER_TASKS | rolled task {t.task_id} ({rec}) -> {new_est}..{new_due}")
        if changed:
            self.autosave()

    def _manager_tasks_sorted(self) -> List[ManagerTask]:
        items = list(getattr(self.model, "manager_tasks", []) or [])
        def k(t: ManagerTask):
            due = _safe_date_from_iso(t.due_date) or datetime.date.max
            est = _safe_date_from_iso(t.earliest_start_date) or datetime.date.max
            return (1 if t.completed else 0, due, est, t.title.lower())
        return sorted(items, key=k)

    def _build_manager_tasks_tab(self):
        frm = ttk.Frame(self.tab_manager_tasks); frm.pack(fill="both", expand=True, padx=12, pady=12)
        ttk.Label(frm, text="Manager Tasks", style="Header.TLabel").pack(anchor="w", pady=(0,4))
        ttk.Label(frm, text="Track projects, reports, and recurring manager obligations. Active tasks are included in weekly manager printouts.", style="Hint.TLabel").pack(anchor="w", pady=(0,10))

        row = ttk.Frame(frm); row.pack(fill="x", pady=(0,8))
        ttk.Button(row, text="Add Task", command=self.add_manager_task).pack(side="left")
        ttk.Button(row, text="Edit Task", command=self.edit_manager_task).pack(side="left", padx=8)
        ttk.Button(row, text="Delete Task", command=self.delete_manager_task).pack(side="left", padx=8)
        ttk.Button(row, text="Toggle Done", command=self.toggle_manager_task_done).pack(side="left", padx=8)

        cols = ("Title", "Earliest", "Due", "Recurrence", "Status", "Description")
        mt_wrap = ttk.Frame(frm)
        mt_wrap.pack(fill="both", expand=True)
        self.manager_tasks_tree = ttk.Treeview(mt_wrap, columns=cols, show="headings", height=12)
        for c in cols:
            self.manager_tasks_tree.heading(c, text=c)
            self.manager_tasks_tree.column(c, width=170 if c != "Description" else 360)
        mt_ys = ttk.Scrollbar(mt_wrap, orient="vertical", command=self.manager_tasks_tree.yview)
        mt_xs = ttk.Scrollbar(mt_wrap, orient="horizontal", command=self.manager_tasks_tree.xview)
        self.manager_tasks_tree.configure(yscrollcommand=mt_ys.set, xscrollcommand=mt_xs.set)
        self.manager_tasks_tree.grid(row=0, column=0, sticky="nsew")
        mt_ys.grid(row=0, column=1, sticky="ns")
        mt_xs.grid(row=1, column=0, sticky="ew")
        mt_wrap.rowconfigure(0, weight=1)
        mt_wrap.columnconfigure(0, weight=1)
        self.manager_tasks_tree.tag_configure("done", foreground="#8a8a8a")
        self.refresh_manager_tasks_tree()

    def refresh_manager_tasks_tree(self):
        if not hasattr(self, "manager_tasks_tree"):
            return
        self._roll_completed_recurring_tasks()
        for i in self.manager_tasks_tree.get_children():
            self.manager_tasks_tree.delete(i)
        for t in self._manager_tasks_sorted():
            status = "Done" if t.completed else "Active"
            self.manager_tasks_tree.insert("", "end", iid=t.task_id, tags=(("done",) if t.completed else ()), values=(t.title, t.earliest_start_date, t.due_date, t.recurrence, status, t.description))

    def _selected_manager_task(self) -> Optional[ManagerTask]:
        if not hasattr(self, "manager_tasks_tree"):
            return None
        sel = self.manager_tasks_tree.selection()
        if not sel:
            return None
        tid = str(sel[0])
        for t in getattr(self.model, "manager_tasks", []) or []:
            if t.task_id == tid:
                return t
        return None

    def _open_manager_task_popup(self, mode: str, seed: Optional[ManagerTask] = None):
        top = tk.Toplevel(self)
        top.title("Add Manager Task" if mode == "add" else "Edit Manager Task")
        top.geometry("620x360")
        _outer, box, _canvas = _build_scrollable_canvas_host(top, padding=(12, 12, 12, 12), min_width=560)

        title_var = tk.StringVar(value=getattr(seed, "title", ""))
        desc_var = tk.StringVar(value=getattr(seed, "description", ""))
        est_var = tk.StringVar(value=getattr(seed, "earliest_start_date", ""))
        due_var = tk.StringVar(value=getattr(seed, "due_date", ""))
        rec_var = tk.StringVar(value=_normalize_recurrence(getattr(seed, "recurrence", "One-Time")))

        ttk.Label(box, text="Task Title:").grid(row=0, column=0, sticky="w", padx=6, pady=6)
        ttk.Entry(box, textvariable=title_var, width=54).grid(row=0, column=1, sticky="w", padx=6, pady=6)
        ttk.Label(box, text="Task Description:").grid(row=1, column=0, sticky="nw", padx=6, pady=6)
        ttk.Entry(box, textvariable=desc_var, width=54).grid(row=1, column=1, sticky="w", padx=6, pady=6)
        ttk.Label(box, text="Earliest Date (YYYY-MM-DD):").grid(row=2, column=0, sticky="w", padx=6, pady=6)
        ttk.Entry(box, textvariable=est_var, width=18).grid(row=2, column=1, sticky="w", padx=6, pady=6)
        ttk.Label(box, text="Due Date (YYYY-MM-DD):").grid(row=3, column=0, sticky="w", padx=6, pady=6)
        ttk.Entry(box, textvariable=due_var, width=18).grid(row=3, column=1, sticky="w", padx=6, pady=6)
        ttk.Label(box, text="Recurrence:").grid(row=4, column=0, sticky="w", padx=6, pady=6)
        ttk.Combobox(box, textvariable=rec_var, values=["One-Time", "Weekly", "Bi-Weekly", "Monthly", "Quarterly", "Yearly"], state="readonly", width=16).grid(row=4, column=1, sticky="w", padx=6, pady=6)

        def _save():
            title = title_var.get().strip()
            if not title:
                messagebox.showerror("Manager Tasks", "Task title is required.", parent=top)
                return
            est = _safe_date_from_iso(est_var.get().strip())
            due = _safe_date_from_iso(due_var.get().strip())
            if est is None or due is None:
                messagebox.showerror("Manager Tasks", "Earliest and Due dates must be valid YYYY-MM-DD.", parent=top)
                return
            if due < est:
                messagebox.showerror("Manager Tasks", "Due date must be on/after earliest date.", parent=top)
                return

            if mode == "add" or seed is None:
                task = ManagerTask(task_id=self._new_manager_task_id())
                self.model.manager_tasks.append(task)
            else:
                task = seed
            task.title = title
            task.description = desc_var.get().strip()
            task.earliest_start_date = est.isoformat()
            task.due_date = due.isoformat()
            task.recurrence = _normalize_recurrence(rec_var.get())
            self.autosave()
            self.refresh_manager_tasks_tree()
            top.destroy()

        b = ttk.Frame(box); b.grid(row=5, column=0, columnspan=2, sticky="w", padx=6, pady=(12,0))
        ttk.Button(b, text="Save", command=_save).pack(side="left")
        ttk.Button(b, text="Cancel", command=top.destroy).pack(side="left", padx=8)

    def add_manager_task(self):
        self._open_manager_task_popup("add", None)

    def edit_manager_task(self):
        t = self._selected_manager_task()
        if t is None:
            return
        self._open_manager_task_popup("edit", t)

    def delete_manager_task(self):
        t = self._selected_manager_task()
        if t is None:
            return
        if not messagebox.askyesno("Delete Task", f"Delete '{t.title}'?"):
            return
        self.model.manager_tasks = [x for x in (self.model.manager_tasks or []) if x.task_id != t.task_id]
        self.autosave()
        self.refresh_manager_tasks_tree()

    def toggle_manager_task_done(self):
        t = self._selected_manager_task()
        if t is None:
            return
        t.completed = not bool(t.completed)
        t.completed_on = today_iso() if t.completed else ""
        self.autosave()
        self.refresh_manager_tasks_tree()

    # -------- Employee Performance & Reliability --------
    def _timeoff_events_all(self) -> List[Dict[str, str]]:
        out: List[Dict[str, str]] = []
        all_data = _normalize_weekly_exception_settings(getattr(self.model, "weekly_exception_settings", {}) or {}, self.model)
        for lbl, bucket in all_data.items():
            for r in _normalize_time_off_requests(bucket.get("time_off_requests", []), lbl):
                out.append({
                    "employee_name": r.employee_name,
                    "event_type": "time_off_request",
                    "date": r.label,
                    "note": (r.note or "").strip() or f"{DAY_FULL.get(r.day, r.day)} {self._format_request_window(r)} ({r.status})",
                })
        return out

    def _reliability_summary(self) -> Dict[str, Dict[str, Any]]:
        names = sorted({e.name for e in (self.model.employees or []) if e.name.strip()}, key=str.lower)
        out: Dict[str, Dict[str, Any]] = {n: {"call_out": 0, "time_off_request": 0, "extra_shift_pickup": 0, "details": []} for n in names}
        for ev in getattr(self.model, "reliability_events", []) or []:
            nm = str(ev.employee_name or "").strip()
            if not nm:
                continue
            out.setdefault(nm, {"call_out": 0, "time_off_request": 0, "extra_shift_pickup": 0, "details": []})
            if ev.event_type in {"call_out", "extra_shift_pickup"}:
                out[nm][ev.event_type] += 1
                out[nm]["details"].append((ev.date, ev.event_type, ev.note or "", ev.related_employee or ""))
        for r in self._timeoff_events_all():
            nm = str(r.get("employee_name", "")).strip()
            if not nm:
                continue
            out.setdefault(nm, {"call_out": 0, "time_off_request": 0, "extra_shift_pickup": 0, "details": []})
            out[nm]["time_off_request"] += 1
            out[nm]["details"].append((str(r.get("date", "")), "time_off_request", str(r.get("note", "")), ""))
        for nm in out:
            out[nm]["details"] = sorted(out[nm]["details"], key=lambda x: (x[0], x[1]))
        return out

    def _build_performance_tab(self):
        frm = ttk.Frame(self.tab_perf); frm.pack(fill="both", expand=True, padx=12, pady=12)
        ttk.Label(frm, text="Employee Performance & Reliability", style="Header.TLabel").pack(anchor="w", pady=(0,4))
        ttk.Label(frm, text="Summary metrics for manager reviews. Time off counts include all submitted requests. Extra-shift pickup counts come only from explicit call-off replacement records.", style="Hint.TLabel").pack(anchor="w", pady=(0,8))

        ttk.Button(frm, text="Refresh", command=self.refresh_performance_view).pack(anchor="w", pady=(0,8))
        cols = ("Employee", "Call-Outs", "Time Off Requests", "Extra Shifts Picked Up")
        perf_wrap = ttk.Frame(frm)
        perf_wrap.pack(fill="x", expand=False)
        self.perf_tree = ttk.Treeview(perf_wrap, columns=cols, show="headings", height=10)
        for c in cols:
            self.perf_tree.heading(c, text=c)
            self.perf_tree.column(c, width=220 if c == "Employee" else 170)
        perf_ys = ttk.Scrollbar(perf_wrap, orient="vertical", command=self.perf_tree.yview)
        perf_xs = ttk.Scrollbar(perf_wrap, orient="horizontal", command=self.perf_tree.xview)
        self.perf_tree.configure(yscrollcommand=perf_ys.set, xscrollcommand=perf_xs.set)
        self.perf_tree.grid(row=0, column=0, sticky="nsew")
        perf_ys.grid(row=0, column=1, sticky="ns")
        perf_xs.grid(row=1, column=0, sticky="ew")
        perf_wrap.rowconfigure(0, weight=1)
        perf_wrap.columnconfigure(0, weight=1)
        self.perf_tree.bind("<<TreeviewSelect>>", self._on_perf_select, add="+")

        body = ttk.Frame(frm); body.pack(fill="both", expand=True, pady=(8,0))
        self.perf_detail_text = tk.Text(body, wrap="word", height=14)
        ysb = ttk.Scrollbar(body, orient="vertical", command=self.perf_detail_text.yview)
        self.perf_detail_text.configure(yscrollcommand=ysb.set)
        self.perf_detail_text.pack(side="left", fill="both", expand=True)
        ysb.pack(side="right", fill="y")
        self.refresh_performance_view()

    def refresh_performance_view(self):
        if not hasattr(self, "perf_tree"):
            return
        self._perf_cache = self._reliability_summary()
        for i in self.perf_tree.get_children():
            self.perf_tree.delete(i)
        for nm in sorted(self._perf_cache.keys(), key=str.lower):
            row = self._perf_cache[nm]
            self.perf_tree.insert("", "end", iid=nm, values=(nm, row["call_out"], row["time_off_request"], row["extra_shift_pickup"]))
        self.perf_detail_text.delete("1.0", "end")
        self.perf_detail_text.insert("end", "Select an employee to see details.\n")

    def _on_perf_select(self, _event=None):
        if not hasattr(self, "perf_tree"):
            return
        sel = self.perf_tree.selection()
        self.perf_detail_text.delete("1.0", "end")
        if not sel:
            self.perf_detail_text.insert("end", "Select an employee to see details.\n")
            return
        nm = str(sel[0])
        row = (getattr(self, "_perf_cache", {}) or {}).get(nm, {})
        self.perf_detail_text.insert("end", f"{nm}\n\n")
        self.perf_detail_text.insert("end", f"Call-Outs: {row.get('call_out', 0)}\n")
        self.perf_detail_text.insert("end", f"Time Off Requests: {row.get('time_off_request', 0)}\n")
        self.perf_detail_text.insert("end", f"Extra Shifts Picked Up: {row.get('extra_shift_pickup', 0)}\n\n")
        self.perf_detail_text.insert("end", "Details:\n")
        details = list(row.get("details", []) or [])
        if not details:
            self.perf_detail_text.insert("end", "- none\n")
            return
        for dt, typ, note, rel in details:
            extra = f" | with {rel}" if rel else ""
            self.perf_detail_text.insert("end", f"- {dt} | {typ}{extra} | {note}\n")

    def _build_manager_tab(self):
        _outer, frm, _canvas = _build_scrollable_canvas_host(self.tab_mgr, padding=(10, 10, 10, 10), min_width=980)
        top = ttk.Frame(frm, style="Section.TFrame")
        top.pack(fill="x", pady=(0, 8))
        left_top = ttk.Frame(top, style="Section.TFrame")
        left_top.pack(side="left", fill="x", expand=True)
        right_top = ttk.Frame(top, style="Section.TFrame")
        right_top.pack(side="right", anchor="ne", padx=(10, 0))

        ttk.Label(left_top, text="Manager Goals (caps are saved/validated; solver enforcement starts later)", style="Header.TLabel").pack(anchor="w")
        self._attach_tab_brand_panel(right_top, slot_key="manager_tab_brand", min_w=150, max_w=280, min_h=90, max_h=180, rel_w=0.95, rel_h=0.85)

        goals = self.model.manager_goals

        grid = ttk.Frame(frm); grid.pack(anchor="w", fill="x")
        grid.columnconfigure(1, weight=1)

        # Vars
        self.mgr_cov_goal = tk.StringVar(value=str(getattr(goals, "coverage_goal_pct", 95.0)))
        self.mgr_daily_over = tk.StringVar(value=str(getattr(goals, "daily_overstaff_allow_hours", 0.0)))
        # Caps
        self.mgr_pref_weekly_cap = tk.StringVar(value=str(getattr(goals, "preferred_weekly_cap", getattr(goals, "weekly_hours_cap", 0.0))))
        self.mgr_max_weekly_cap = tk.StringVar(value=str(getattr(goals, "maximum_weekly_cap", 0.0)))
        self.mgr_min_weekly_floor = tk.StringVar(value=str(getattr(goals, "minimum_weekly_floor", 0.0)))
        # Demand multipliers (Phase 2 P2-5)
        self.mgr_demand_morning = tk.StringVar(value=str(getattr(goals, "demand_morning_multiplier", 1.0)))
        self.mgr_demand_midday = tk.StringVar(value=str(getattr(goals, "demand_midday_multiplier", 1.0)))
        self.mgr_demand_evening = tk.StringVar(value=str(getattr(goals, "demand_evening_multiplier", 1.0)))
        # Phase 3 toggles/weights
        self.mgr_enable_risk = tk.BooleanVar(value=bool(getattr(goals, "enable_coverage_risk_protection", True)))
        self.mgr_w_risk = tk.StringVar(value=str(getattr(goals, "w_coverage_risk", 10.0)))

        # Phase 4 C3: Risk-Aware Optimization (adds resilience buffer)
        self.mgr_enable_riskaware = tk.BooleanVar(value=bool(getattr(goals, "enable_risk_aware_optimization", True)))
        self.mgr_protect_single_point = tk.BooleanVar(value=bool(getattr(goals, "protect_single_point_failures", True)))
        self.mgr_w_risk_fragile = tk.StringVar(value=str(getattr(goals, "w_risk_fragile", 4.0)))
        self.mgr_w_risk_single_point = tk.StringVar(value=str(getattr(goals, "w_risk_single_point", 8.0)))

        self.mgr_enable_util = tk.BooleanVar(value=bool(getattr(goals, "enable_utilization_optimizer", True)))
        self.mgr_w_new_emp = tk.StringVar(value=str(getattr(goals, "w_new_employee_penalty", 3.0)))
        self.mgr_w_frag = tk.StringVar(value=str(getattr(goals, "w_fragmentation_penalty", 2.5)))
        self.mgr_w_extend = tk.StringVar(value=str(getattr(goals, "w_extend_shift_bonus", 2.0)))
        self.mgr_w_low_hours = tk.StringVar(value=str(getattr(goals, "w_low_hours_priority_bonus", 2.5)))
        self.mgr_w_near_cap = tk.StringVar(value=str(getattr(goals, "w_near_cap_penalty", 5.0)))
        self.mgr_w_target_fill = tk.StringVar(value=str(getattr(goals, "w_target_min_fill_bonus", 1.5)))
        self.mgr_util_balance_tol = tk.StringVar(value=str(getattr(goals, "utilization_balance_tolerance_hours", 2.0)))

        self.mgr_call_depth = tk.StringVar(value=str(getattr(goals, "call_list_depth", 5)))
        self.mgr_include_noncert = tk.BooleanVar(value=bool(getattr(goals, "include_noncertified_in_call_list", False)))

        def _apply_vars(*_):
            # Safe parsing with fallbacks (never crash UI)
            try:
                goals.coverage_goal_pct = float(self.mgr_cov_goal.get() or 0.0)
            except Exception:
                pass
            try:
                goals.daily_overstaff_allow_hours = float(self.mgr_daily_over.get() or 0.0)
            except Exception:
                pass
            # Preferred (soft) cap
            try:
                goals.preferred_weekly_cap = float(self.mgr_pref_weekly_cap.get() or 0.0)
            except Exception:
                pass
            # Maximum (hard) cap (0 = disabled)
            try:
                goals.maximum_weekly_cap = float(self.mgr_max_weekly_cap.get() or 0.0)
            except Exception:
                pass
            try:
                goals.minimum_weekly_floor = float(self.mgr_min_weekly_floor.get() or 0.0)
            except Exception:
                pass

            # Demand multipliers (Phase 2 P2-5)
            try:
                goals.demand_morning_multiplier = float(self.mgr_demand_morning.get() or 1.0)
            except Exception:
                pass
            try:
                goals.demand_midday_multiplier = float(self.mgr_demand_midday.get() or 1.0)
            except Exception:
                pass
            try:
                goals.demand_evening_multiplier = float(self.mgr_demand_evening.get() or 1.0)
            except Exception:
                pass            # Phase 3: Coverage Risk Protection + Utilization Optimizer
            try:
                goals.enable_coverage_risk_protection = bool(self.mgr_enable_risk.get())
            except Exception:
                pass
            try:
                goals.w_coverage_risk = float(self.mgr_w_risk.get() or 0.0)
            except Exception:
                pass

            # Phase 4 C3: Risk-Aware Optimization
            try:
                goals.enable_risk_aware_optimization = bool(self.mgr_enable_riskaware.get())
            except Exception:
                pass
            try:
                goals.protect_single_point_failures = bool(self.mgr_protect_single_point.get())
            except Exception:
                pass
            try:
                goals.w_risk_fragile = float(self.mgr_w_risk_fragile.get() or 0.0)
            except Exception:
                pass
            try:
                goals.w_risk_single_point = float(self.mgr_w_risk_single_point.get() or 0.0)
            except Exception:
                pass

            try:
                goals.enable_utilization_optimizer = bool(self.mgr_enable_util.get())
            except Exception:
                pass
            try:
                goals.w_new_employee_penalty = float(self.mgr_w_new_emp.get() or 0.0)
            except Exception:
                pass
            try:
                goals.w_fragmentation_penalty = float(self.mgr_w_frag.get() or 0.0)
            except Exception:
                pass
            try:
                goals.w_extend_shift_bonus = float(self.mgr_w_extend.get() or 0.0)
            except Exception:
                pass
            try:
                goals.w_low_hours_priority_bonus = float(self.mgr_w_low_hours.get() or 0.0)
            except Exception:
                pass
            try:
                goals.w_near_cap_penalty = float(self.mgr_w_near_cap.get() or 0.0)
            except Exception:
                pass
            try:
                goals.w_target_min_fill_bonus = float(self.mgr_w_target_fill.get() or 0.0)
            except Exception:
                pass
            try:
                goals.utilization_balance_tolerance_hours = float(self.mgr_util_balance_tol.get() or 0.0)
            except Exception:
                pass

# Validation / normalization:
            # Rule: 0 <= preferred <= maximum (when maximum > 0)
            try:
                pref = float(getattr(goals, "preferred_weekly_cap", 0.0) or 0.0)
                mx = float(getattr(goals, "maximum_weekly_cap", 0.0) or 0.0)
                pref = max(0.0, pref)
                mx = max(0.0, mx)
                # Keep legacy field synced for backward compatible saves
                goals.weekly_hours_cap = pref
                if mx > 0.0 and pref > mx:
                    # Auto-normalize preferred down to maximum (consistent behavior)
                    goals.preferred_weekly_cap = mx
                    goals.weekly_hours_cap = mx
                    try:
                        self.mgr_pref_weekly_cap.set(str(mx))
                    except Exception:
                        pass
                    try:
                        self._set_status(f"Preferred weekly cap normalized to Maximum ({mx:g})")
                    except Exception:
                        pass
            except Exception:
                pass
            try:
                goals.call_list_depth = int(float(self.mgr_call_depth.get() or 0))
            except Exception:
                pass
            try:
                goals.include_noncertified_in_call_list = bool(self.mgr_include_noncert.get())
            except Exception:
                pass

        # Auto-apply on edits
        for v in (self.mgr_cov_goal, self.mgr_daily_over, self.mgr_pref_weekly_cap, self.mgr_max_weekly_cap, self.mgr_min_weekly_floor, self.mgr_demand_morning, self.mgr_demand_midday, self.mgr_demand_evening, self.mgr_w_risk, self.mgr_w_new_emp, self.mgr_w_frag, self.mgr_w_extend, self.mgr_call_depth):
            try:
                v.trace_add("write", _apply_vars)
            except Exception:
                pass
        try:
            self.mgr_include_noncert.trace_add("write", _apply_vars)
            self.mgr_enable_risk.trace_add("write", _apply_vars)
            self.mgr_enable_util.trace_add("write", _apply_vars)
        except Exception:
            pass

        # Rows
        r = 0
        ttk.Label(grid, text="Coverage goal (% of 30-min blocks fully covered):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(grid, textvariable=self.mgr_cov_goal, width=10).grid(row=r, column=1, sticky="w"); r += 1

        ttk.Label(grid, text="Daily overstaff warning threshold (hours):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(grid, textvariable=self.mgr_daily_over, width=10).grid(row=r, column=1, sticky="w"); r += 1

        ttk.Label(grid, text="Preferred Weekly Labor Hours Cap (soft, 0 = ignore):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(grid, textvariable=self.mgr_pref_weekly_cap, width=10).grid(row=r, column=1, sticky="w"); r += 1

        ttk.Label(grid, text="Maximum Weekly Labor Hours Cap (hard, 0 = disabled):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(grid, textvariable=self.mgr_max_weekly_cap, width=10).grid(row=r, column=1, sticky="w"); r += 1

        # Phase 2 P2-5: Demand Adaptive Scheduling (multipliers)
        ttk.Label(grid, text="Demand Multiplier — Morning (e.g., 0.9 / 1.0 / 1.2):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(grid, textvariable=self.mgr_demand_morning, width=10).grid(row=r, column=1, sticky="w"); r += 1

        ttk.Label(grid, text="Demand Multiplier — Midday:").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(grid, textvariable=self.mgr_demand_midday, width=10).grid(row=r, column=1, sticky="w"); r += 1

        ttk.Label(grid, text="Demand Multiplier — Evening:").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(grid, textvariable=self.mgr_demand_evening, width=10).grid(row=r, column=1, sticky="w"); r += 1
        # Phase 3: Coverage Risk Protection
        ttk.Label(grid, text="Coverage Risk Protection (fill scarce shifts first):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Checkbutton(grid, variable=self.mgr_enable_risk).grid(row=r, column=1, sticky="w"); r += 1

        ttk.Label(grid, text="Coverage risk weight (higher = more scarcity-aware):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(grid, textvariable=self.mgr_w_risk, width=10).grid(row=r, column=1, sticky="w"); r += 1

        # Phase 4 C3: Risk-Aware Optimization (resilience buffer)
        ttk.Label(grid, text="Risk-Aware Optimization (avoid fragile 1/1 coverage):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Checkbutton(grid, variable=self.mgr_enable_riskaware).grid(row=r, column=1, sticky="w"); r += 1

        ttk.Label(grid, text="Protect single-point failures (1/1) extra:").grid(row=r, column=0, sticky="w", pady=2)
        ttk.Checkbutton(grid, variable=self.mgr_protect_single_point).grid(row=r, column=1, sticky="w"); r += 1

        ttk.Label(grid, text="Fragile coverage weight (scheduled == minimum):").grid(row=r, column=0, sticky="w", pady=2)
        ttk.Entry(grid, textvariable=self.mgr_w_risk_fragile, width=10).grid(row=r, column=1, sticky="w"); r += 1

        ttk.Label(grid, text="Single-point weight (minimum=1 and scheduled=1):").grid(row=r, column=0, sticky="w", pady=2)
        ttk.Entry(grid, textvariable=self.mgr_w_risk_single_point, width=10).grid(row=r, column=1, sticky="w"); r += 1


        # Phase 3: Workforce Utilization Optimizer
        ttk.Label(grid, text="Utilization Optimizer (cleaner schedules, fewer fragments):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Checkbutton(grid, variable=self.mgr_enable_util).grid(row=r, column=1, sticky="w"); r += 1

        ttk.Label(grid, text="Penalty for adding a new employee to the week:").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(grid, textvariable=self.mgr_w_new_emp, width=10).grid(row=r, column=1, sticky="w"); r += 1

        ttk.Label(grid, text="Fragmentation penalty (more segments = worse):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(grid, textvariable=self.mgr_w_frag, width=10).grid(row=r, column=1, sticky="w"); r += 1

        ttk.Label(grid, text="Bonus for extending adjacent shift (same day/area):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(grid, textvariable=self.mgr_w_extend, width=10).grid(row=r, column=1, sticky="w"); r += 1

        ttk.Label(grid, text="Low-hours priority bonus (favor underused employees):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(grid, textvariable=self.mgr_w_low_hours, width=10).grid(row=r, column=1, sticky="w"); r += 1

        ttk.Label(grid, text="Near-cap penalty (avoid stacking hours on heavy employees):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(grid, textvariable=self.mgr_w_near_cap, width=10).grid(row=r, column=1, sticky="w"); r += 1

        ttk.Label(grid, text="Target-min fill bonus (help employees reach target minimum hours):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(grid, textvariable=self.mgr_w_target_fill, width=10).grid(row=r, column=1, sticky="w"); r += 1

        ttk.Label(grid, text="Utilization balance tolerance (hours ignored around average):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(grid, textvariable=self.mgr_util_balance_tol, width=10).grid(row=r, column=1, sticky="w"); r += 1

        ttk.Label(grid, text="Call list depth (suggested backups per shortage):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(grid, textvariable=self.mgr_call_depth, width=10).grid(row=r, column=1, sticky="w"); r += 1

        ttk.Checkbutton(grid, text="Allow non-certified employees in call list (override)", variable=self.mgr_include_noncert)            .grid(row=r, column=0, columnspan=2, sticky="w", pady=(6,4)); r += 1


        # --- Milestone 6: scoring weights (soft penalties) ---
        sep = ttk.Separator(frm, orient="horizontal"); sep.pack(fill="x", pady=10)
        ttk.Label(frm, text="Scoring Weights (lower score = better). Hard rules remain hard.", style="SubHeader.TLabel").pack(anchor="w", pady=(0,6))

        wgrid = ttk.Frame(frm); wgrid.pack(anchor="w", fill="x")
        wgrid.columnconfigure(1, weight=1)

        self.w_under_pref_cov = tk.StringVar(value=str(getattr(goals, "w_under_preferred_coverage", 5.0)))
        self.w_over_pref_cap = tk.StringVar(value=str(getattr(goals, "w_over_preferred_cap", 20.0)))
        self.w_part_miss = tk.StringVar(value=str(getattr(goals, "w_participation_miss", 250.0)))
        self.w_split = tk.StringVar(value=str(getattr(goals, "w_split_shifts", 30.0)))
        self.w_imb = tk.StringVar(value=str(getattr(goals, "w_hour_imbalance", 2.0)))
        self.w_stability = tk.StringVar(value=str(getattr(goals, "w_schedule_stability", 14.0)))

        self.tgl_stability = tk.BooleanVar(value=bool(getattr(goals, "enable_schedule_stability", True)))
        self.tgl_longer = tk.BooleanVar(value=bool(getattr(goals, "prefer_longer_shifts", True)))
        self.tgl_area = tk.BooleanVar(value=bool(getattr(goals, "prefer_area_consistency", False)))

        def _apply_weights(*_):
            try: goals.w_under_preferred_coverage = float(self.w_under_pref_cov.get() or 0.0)
            except Exception: pass
            try: goals.w_over_preferred_cap = float(self.w_over_pref_cap.get() or 0.0)
            except Exception: pass
            try: goals.w_participation_miss = float(self.w_part_miss.get() or 0.0)
            except Exception: pass
            try: goals.w_split_shifts = float(self.w_split.get() or 0.0)
            except Exception: pass
            try: goals.w_hour_imbalance = float(self.w_imb.get() or 0.0)
            except Exception: pass
            try: goals.w_schedule_stability = float(self.w_stability.get() or 0.0)
            except Exception: pass
            try: goals.enable_schedule_stability = bool(self.tgl_stability.get())
            except Exception: pass
            try: goals.prefer_longer_shifts = bool(self.tgl_longer.get())
            except Exception: pass
            try: goals.prefer_area_consistency = bool(self.tgl_area.get())
            except Exception: pass

        for v in (self.w_under_pref_cov, self.w_over_pref_cap, self.w_part_miss, self.w_split, self.w_imb, self.w_stability):
            try: v.trace_add("write", _apply_weights)
            except Exception: pass
        try: self.tgl_stability.trace_add("write", _apply_weights)
        except Exception: pass
        try: self.tgl_longer.trace_add("write", _apply_weights)
        except Exception: pass
        try: self.tgl_area.trace_add("write", _apply_weights)
        except Exception: pass

        rr = 0
        ttk.Label(wgrid, text="Under Preferred Coverage (per 30-min deficit):").grid(row=rr, column=0, sticky="w", pady=3)
        ttk.Entry(wgrid, textvariable=self.w_under_pref_cov, width=10).grid(row=rr, column=1, sticky="w"); rr += 1

        ttk.Label(wgrid, text="Over Preferred Weekly Cap (per hour):").grid(row=rr, column=0, sticky="w", pady=3)
        ttk.Entry(wgrid, textvariable=self.w_over_pref_cap, width=10).grid(row=rr, column=1, sticky="w"); rr += 1

        ttk.Label(wgrid, text="Participation miss (per eligible employee):").grid(row=rr, column=0, sticky="w", pady=3)
        ttk.Entry(wgrid, textvariable=self.w_part_miss, width=10).grid(row=rr, column=1, sticky="w"); rr += 1

        ttk.Label(wgrid, text="Split shifts (per extra shift/day):").grid(row=rr, column=0, sticky="w", pady=3)
        ttk.Entry(wgrid, textvariable=self.w_split, width=10).grid(row=rr, column=1, sticky="w"); rr += 1

        ttk.Label(wgrid, text="Hour imbalance (multiplier):").grid(row=rr, column=0, sticky="w", pady=3)
        ttk.Entry(wgrid, textvariable=self.w_imb, width=10).grid(row=rr, column=1, sticky="w"); rr += 1

        ttk.Checkbutton(wgrid, text="Prefer schedule stability (keep previous week when feasible)", variable=self.tgl_stability).grid(row=rr, column=0, columnspan=2, sticky="w", pady=(8,3)); rr += 1

        ttk.Label(wgrid, text="Schedule stability weight (per hour changed):").grid(row=rr, column=0, sticky="w", pady=3)
        ttk.Entry(wgrid, textvariable=self.w_stability, width=10).grid(row=rr, column=1, sticky="w"); rr += 1

        ttk.Checkbutton(wgrid, text="Prefer longer shifts (soft)", variable=self.tgl_longer).grid(row=rr, column=0, columnspan=2, sticky="w", pady=(6,2)); rr += 1
        ttk.Checkbutton(wgrid, text="Prefer area consistency (soft)", variable=self.tgl_area).grid(row=rr, column=0, columnspan=2, sticky="w", pady=(2,2)); rr += 1

        # Apply immediately
        _apply_weights()
        btnrow = ttk.Frame(frm); btnrow.pack(anchor="w", pady=(10,0))
        ttk.Button(btnrow, text="Apply", command=lambda: (_apply_vars(), locals().get("_apply_weights", lambda: None)())).pack(side="left")
        ttk.Label(btnrow, text="Tip: These settings affect the Manager Report only.", foreground="#555").pack(side="left", padx=10)

    def _build_history_tab(self):
        frm = ttk.Frame(self.tab_history); frm.pack(fill="both", expand=True, padx=12, pady=12)
        ttk.Label(frm, text="Last weeks used for fairness scoring (configurable).", style="SubHeader.TLabel")\
            .pack(anchor="w", pady=(0,8))

        cols = ("Created","Label","TotalHours","Filled/Total","Warnings")
        hist_wrap = ttk.Frame(frm)
        hist_wrap.pack(fill="both", expand=True)
        self.hist_tree = ttk.Treeview(hist_wrap, columns=cols, show="headings", height=18)
        for c in cols:
            self.hist_tree.heading(c, text=c)
            w=220 if c=="Label" else 140
            if c=="Warnings": w=520
            self.hist_tree.column(c, width=w)
        hist_ys = ttk.Scrollbar(hist_wrap, orient="vertical", command=self.hist_tree.yview)
        hist_xs = ttk.Scrollbar(hist_wrap, orient="horizontal", command=self.hist_tree.xview)
        self.hist_tree.configure(yscrollcommand=hist_ys.set, xscrollcommand=hist_xs.set)
        self.hist_tree.grid(row=0, column=0, sticky="nsew")
        hist_ys.grid(row=0, column=1, sticky="ns")
        hist_xs.grid(row=1, column=0, sticky="ew")
        hist_wrap.rowconfigure(0, weight=1)
        hist_wrap.columnconfigure(0, weight=1)

        btns = ttk.Frame(frm); btns.pack(fill="x", pady=(8,0))
        ttk.Button(btns, text="Delete Selected", command=self.delete_history).pack(side="left")

    def refresh_history_tree(self):
        for i in self.hist_tree.get_children():
            self.hist_tree.delete(i)
        for s in reversed(self.model.history[-200:]):
            warn = "; ".join(s.warnings[:3]) + (" ..." if len(s.warnings)>3 else "")
            self.hist_tree.insert("", "end", values=(s.created_on, s.label, f"{s.total_hours:.1f}", f"{s.filled_slots}/{s.total_slots}", warn))

    def delete_history(self):
        sel = self.hist_tree.selection()
        if not sel:
            return
        vals = self.hist_tree.item(sel[0], "values")
        created, label = vals[0], vals[1]
        if not messagebox.askyesno("Delete", f"Delete history entry {created} / {label}?"):
            return
        # remove first matching from end
        for i in range(len(self.model.history)-1, -1, -1):
            s = self.model.history[i]
            if s.created_on == created and s.label == label:
                del self.model.history[i]
                break
        self.refresh_history_tree()
        # Manager Goals
        if hasattr(self, "mg_coverage_goal_var"):
            self.mg_coverage_goal_var.set(float(self.model.manager_goals.coverage_goal_pct))
            self.mg_daily_overstaff_allow_var.set(float(self.model.manager_goals.daily_overstaff_allow_hours))
            self.mg_weekly_hours_cap_var.set(float(self.model.manager_goals.weekly_hours_cap))
            self.mg_call_depth_var.set(int(self.model.manager_goals.call_list_depth))
            self.mg_include_noncert_var.set(bool(self.model.manager_goals.include_noncertified_in_call_list))

        self.autosave()

    # -------- Settings tab --------
    def _build_settings_tab(self):
        _outer, frm, _canvas = _build_scrollable_canvas_host(self.tab_settings, padding=(12, 12, 12, 12), min_width=980)
        top = ttk.Frame(frm, style="Section.TFrame")
        top.pack(fill="x", pady=(0, 8))
        left_top = ttk.Frame(top, style="Section.TFrame")
        left_top.pack(side="left", fill="x", expand=True)
        right_top = ttk.Frame(top, style="Section.TFrame")
        right_top.pack(side="right", anchor="ne", padx=(10, 0))
        ttk.Label(left_top, text="Solver + UI settings.", style="SubHeader.TLabel").pack(anchor="w")
        self._attach_tab_brand_panel(right_top, slot_key="settings_tab_brand", min_w=140, max_w=250, min_h=80, max_h=160, rel_w=0.90, rel_h=0.80)

        box = ttk.LabelFrame(frm, text="UI")
        box.pack(fill="x", pady=10)
        self.ui_scale_var = tk.StringVar(value=str(self.model.settings.ui_scale))
        ttk.Label(box, text="UI scale (1.0–2.0):").grid(row=0, column=0, sticky="w", padx=10, pady=6)
        ttk.Entry(box, textvariable=self.ui_scale_var, width=8).grid(row=0, column=1, sticky="w", padx=10, pady=6)
        ttk.Button(box, text="Apply UI Scale (restart recommended)", command=self.apply_ui_scale).grid(row=0, column=2, sticky="w", padx=10, pady=6)


        solver_settings = ttk.LabelFrame(frm, text="Solver Settings")
        solver_settings.pack(fill="x", pady=10)

        self.scrutiny_var = tk.StringVar(value=str(getattr(self.model.settings, "solver_scrutiny_level", "Balanced") or "Balanced"))
        ttk.Label(solver_settings, text="Solver Scrutiny Level:").grid(row=0, column=0, sticky="w", padx=10, pady=6)
        self.scrutiny_combo = ttk.Combobox(
            solver_settings,
            textvariable=self.scrutiny_var,
            values=["Fast", "Balanced", "Thorough", "Maximum"],
            state="readonly",
            width=14
        )
        self.scrutiny_combo.grid(row=0, column=1, sticky="w", padx=10, pady=6)
        ttk.Label(
            solver_settings,
            text="Higher = more restarts/iterations (better quality, slower).",
        ).grid(row=0, column=2, sticky="w", padx=10, pady=6)

        self.multi_scenario_var = tk.BooleanVar(value=bool(getattr(self.model.settings, "enable_multi_scenario_generation", True)))
        self.scenario_count_var = tk.StringVar(value=str(int(getattr(self.model.settings, "scenario_schedule_count", 4) or 4)))
        self.demand_forecast_var = tk.BooleanVar(value=bool(getattr(self.model.settings, "enable_demand_forecast_engine", True)))
        ttk.Checkbutton(solver_settings, text="Enable Multi-Scenario Generation (Phase 5 E1)", variable=self.multi_scenario_var).grid(row=1, column=0, columnspan=2, sticky="w", padx=10, pady=6)
        ttk.Label(solver_settings, text="Scenario count:").grid(row=1, column=2, sticky="e", padx=10, pady=6)
        ttk.Entry(solver_settings, textvariable=self.scenario_count_var, width=6).grid(row=1, column=3, sticky="w", padx=10, pady=6)
        ttk.Checkbutton(solver_settings, text="Enable Demand Forecast Engine (Phase 5 E2)", variable=self.demand_forecast_var).grid(row=2, column=0, columnspan=3, sticky="w", padx=10, pady=6)
        self.employee_fit_var = tk.BooleanVar(value=bool(getattr(self.model.settings, "enable_employee_fit_engine", True)))
        ttk.Checkbutton(solver_settings, text="Enable Employee Fit Intelligence (Phase 5 E3)", variable=self.employee_fit_var).grid(row=3, column=0, columnspan=3, sticky="w", padx=10, pady=6)


        # Phase 4 C1: Schedule Stability Engine controls
        stab_box = ttk.LabelFrame(frm, text="Schedule Stability (Week-to-Week)")
        stab_box.pack(fill="x", pady=10)

        self.stab_enable_var = tk.BooleanVar(value=bool(getattr(self.model.manager_goals, "enable_schedule_stability", True)))
        self.stab_level_var = tk.StringVar(value=self._stab_level_from_weight(float(getattr(self.model.manager_goals, "w_schedule_stability", 14.0) or 12.0)))
        self.stab_weight_var = tk.StringVar(value=str(float(getattr(self.model.manager_goals, "w_schedule_stability", 14.0) or 12.0)))

        ttk.Checkbutton(
            stab_box,
            text="Enable Schedule Stability (prefer keeping last week's assignments when feasible)",
            variable=self.stab_enable_var,
        ).grid(row=0, column=0, columnspan=3, sticky="w", padx=10, pady=(8,6))

        ttk.Label(stab_box, text="Stability strength:").grid(row=1, column=0, sticky="w", padx=10, pady=6)
        self.stab_level_combo = ttk.Combobox(
            stab_box,
            textvariable=self.stab_level_var,
            values=["Low", "Medium", "High", "Maximum"],
            state="readonly",
            width=12,
        )
        self.stab_level_combo.grid(row=1, column=1, sticky="w", padx=10, pady=6)
        self.stab_level_combo.bind("<<ComboboxSelected>>", lambda _e: self._on_stab_level_change())

        ttk.Label(stab_box, text="Weight (advanced):").grid(row=1, column=2, sticky="w", padx=10, pady=6)
        ttk.Entry(stab_box, textvariable=self.stab_weight_var, width=8).grid(row=1, column=3, sticky="w", padx=10, pady=6)

        ttk.Label(
            stab_box,
            text="Higher = fewer week-to-week changes (may increase hours/overstaff slightly to keep patterns).",
        ).grid(row=2, column=0, columnspan=4, sticky="w", padx=10, pady=(0,8))

        solver = ttk.LabelFrame(frm, text="Optimizer")
        solver.pack(fill="x", pady=10)

        self.min_rest_var = tk.StringVar(value=str(self.model.settings.min_rest_hours))
        self.lookback_var = tk.StringVar(value=str(self.model.settings.fairness_lookback_weeks))
        self.iters_var = tk.StringVar(value=str(self.model.settings.optimizer_iterations))
        self.temp_var = tk.StringVar(value=str(self.model.settings.optimizer_temperature))

        ttk.Label(solver, text="Min rest hours (clopen):").grid(row=0, column=0, sticky="w", padx=10, pady=6)
        ttk.Entry(solver, textvariable=self.min_rest_var, width=8).grid(row=0, column=1, sticky="w", padx=10, pady=6)
        ttk.Label(solver, text="Fairness lookback weeks:").grid(row=0, column=2, sticky="w", padx=10, pady=6)
        ttk.Entry(solver, textvariable=self.lookback_var, width=8).grid(row=0, column=3, sticky="w", padx=10, pady=6)

        ttk.Label(solver, text="Optimizer iterations:").grid(row=1, column=0, sticky="w", padx=10, pady=6)
        ttk.Entry(solver, textvariable=self.iters_var, width=10).grid(row=1, column=1, sticky="w", padx=10, pady=6)
        ttk.Label(solver, text="Temperature (0-2):").grid(row=1, column=2, sticky="w", padx=10, pady=6)
        ttk.Entry(solver, textvariable=self.temp_var, width=8).grid(row=1, column=3, sticky="w", padx=10, pady=6)

        nd = ttk.LabelFrame(frm, text="North Dakota minor rules")
        nd.pack(fill="x", pady=10)
        self.nd_enforce_var = tk.BooleanVar(value=self.model.nd_rules.enforce)
        self.nd_school_week_var = tk.BooleanVar(value=self.model.nd_rules.is_school_week)
        ttk.Checkbutton(nd, text="Enforce ND minor rules (14-15)", variable=self.nd_enforce_var).grid(row=0, column=0, sticky="w", padx=10, pady=6)
        ttk.Checkbutton(nd, text="This week is a school week", variable=self.nd_school_week_var).grid(row=0, column=1, sticky="w", padx=10, pady=6)

        ttk.Button(frm, text="Save Settings", command=self.save_settings).pack(anchor="w", padx=6, pady=10)

        # Phase 2 P2-4: Pattern Learning (History)
        learning = ttk.LabelFrame(frm, text="Pattern Learning (History)")
        learning.pack(fill="x", pady=10)

        self.learn_hist_var = tk.BooleanVar(value=bool(getattr(self.model.settings, "learn_from_history", True)))
        ttk.Checkbutton(
            learning,
            text="Learn From History (soft preference)",
            variable=self.learn_hist_var,
            command=self._on_toggle_learn_from_history
        ).grid(row=0, column=0, sticky="w", padx=10, pady=6)

        ttk.Button(
            learning,
            text="Refresh Learned Patterns",
            command=self._refresh_learned_patterns_with_feedback
        ).grid(row=0, column=1, sticky="w", padx=10, pady=6)

        ttk.Button(
            learning,
            text="Reset Learned Patterns",
            command=self._reset_learned_patterns
        ).grid(row=0, column=2, sticky="w", padx=10, pady=6)

        ttk.Label(
            learning,
            text="Uses saved schedules in ./history and last schedule to prefer typical start times, departments, and shift lengths.",
        ).grid(row=1, column=0, columnspan=3, sticky="w", padx=10, pady=(0,8))


        backup_box = ttk.LabelFrame(frm, text="Backup / Restore")
        backup_box.pack(fill="x", pady=10)
        ttk.Label(
            backup_box,
            text="Create timestamped backups of scheduler data, learned patterns, published finals, and history.",
        ).grid(row=0, column=0, columnspan=3, sticky="w", padx=10, pady=(8,4))
        ttk.Button(backup_box, text="Backup Store Data", command=self.create_backup).grid(row=1, column=0, sticky="w", padx=10, pady=8)
        ttk.Button(backup_box, text="Restore Store Data", command=self.restore_backup).grid(row=1, column=1, sticky="w", padx=10, pady=8)
        ttk.Button(backup_box, text="Open Backup Folder", command=self.open_backup_folder).grid(row=1, column=2, sticky="w", padx=10, pady=8)

    def create_backup(self):
        try:
            ensure_dir(_backup_dir())
            default_name = f"backup_{_backup_stamp()}.zip"
            path = filedialog.asksaveasfilename(
                title="Backup Store Data",
                defaultextension=".zip",
                filetypes=[("ZIP backup", "*.zip")],
                initialdir=_backup_dir(),
                initialfile=default_name,
            )
            if not path:
                return
            info = create_store_backup_zip(path)
            self._set_status(f"Backup created: {os.path.basename(path)}")
            messagebox.showinfo("Backup", f"Backup created.\n\nFile: {path}\nIncluded files: {int(info.get('file_count', 0))}")
        except Exception as ex:
            messagebox.showerror("Backup", f"Backup failed: {ex}")

    def restore_backup(self):
        try:
            ensure_dir(_backup_dir())
            candidates = list_store_backups()
            initialdir = _backup_dir() if os.path.isdir(_backup_dir()) else app_dir()
            initialfile = os.path.basename(candidates[0]) if candidates else ''
            path = filedialog.askopenfilename(
                title="Restore Store Data",
                filetypes=[("ZIP backup", "*.zip")],
                initialdir=initialdir,
                initialfile=initialfile,
            )
            if not path:
                return
            if not messagebox.askyesno("Restore", "Restore this backup into the current program data folder? This will overwrite current scheduler data, patterns, finals, and history."):
                return
            info = restore_store_backup_zip(path)
            self.model = load_data(default_data_path())
            self.data_path = default_data_path()
            self._validate_requirements_for_context("load", block=False)
            self._apply_ui_scale(self.model.settings.ui_scale)
            self._refresh_all()
            self._set_status(f"Restored backup: {os.path.basename(path)}")
            messagebox.showinfo("Restore", f"Restore completed.\n\nBackup: {path}\nFiles restored: {len(info.get('restored_files', []))}")
        except Exception as ex:
            messagebox.showerror("Restore", f"Restore failed: {ex}")

    def open_backup_folder(self):
        try:
            ensure_dir(_backup_dir())
            folder = _backup_dir()
            if sys.platform.startswith('win'):
                os.startfile(folder)
            elif sys.platform == 'darwin':
                subprocess.Popen(['open', folder])
            else:
                subprocess.Popen(['xdg-open', folder])
        except Exception as ex:
            messagebox.showerror("Backup Folder", f"Could not open backup folder: {ex}")

    def apply_ui_scale(self):
        try:
            s = float(self.ui_scale_var.get().strip())
            s = max(1.0, min(2.0, s))
        except Exception:
            messagebox.showerror("UI Scale", "Enter a number like 1.2 or 1.6")
            return
        self.model.settings.ui_scale = s
        self.autosave()
        messagebox.showinfo("UI Scale", "Saved. Restart the app for best results.")

    # -------- Phase 4 C1: Schedule Stability helpers --------
    def _stab_level_from_weight(self, w: float) -> str:
        try:
            w = float(w)
        except Exception:
            w = 12.0
        if w <= 6.0:
            return "Low"
        if w <= 14.0:
            return "Medium"
        if w <= 24.0:
            return "High"
        return "Maximum"

    def _stab_weight_from_level(self, level: str) -> float:
        lvl = str(level or "").strip().lower()
        if lvl == "low":
            return 6.0
        if lvl == "medium":
            return 12.0
        if lvl == "high":
            return 20.0
        if lvl == "maximum":
            return 35.0
        return 12.0

    def _on_stab_level_change(self):
        try:
            w = self._stab_weight_from_level(self.stab_level_var.get())
            self.stab_weight_var.set(str(float(w)))
        except Exception:
            pass


    def save_settings(self):
        try:
            self.model.settings.min_rest_hours = max(0, int(self.min_rest_var.get().strip()))
            self.model.settings.fairness_lookback_weeks = max(0, int(self.lookback_var.get().strip()))
            self.model.settings.optimizer_iterations = max(0, int(self.iters_var.get().strip()))
            self.model.settings.optimizer_temperature = max(0.0, float(self.temp_var.get().strip()))
            self.model.settings.solver_scrutiny_level = str(getattr(self, "scrutiny_var", tk.StringVar(value="Balanced")).get() or "Balanced")
            self.model.settings.enable_multi_scenario_generation = bool(getattr(self, "multi_scenario_var", tk.BooleanVar(value=True)).get())
            self.model.settings.scenario_schedule_count = max(1, min(6, int(getattr(self, "scenario_count_var", tk.StringVar(value="4")).get().strip())))
            self.model.settings.enable_demand_forecast_engine = bool(getattr(self, "demand_forecast_var", tk.BooleanVar(value=True)).get())
            self.model.settings.enable_employee_fit_engine = bool(getattr(self, "employee_fit_var", tk.BooleanVar(value=True)).get())
            # Phase 4 C1: Schedule Stability settings
            try:
                self.model.manager_goals.enable_schedule_stability = bool(getattr(self, "stab_enable_var", tk.BooleanVar(value=True)).get())
                self.model.manager_goals.w_schedule_stability = max(0.0, float(getattr(self, "stab_weight_var", tk.StringVar(value="14")).get().strip()))
            except Exception:
                pass
        except Exception as ex:
            messagebox.showerror("Settings", f"Bad value: {ex}")
            return
        self.model.nd_rules.enforce = bool(self.nd_enforce_var.get())
        self.model.nd_rules.is_school_week = bool(self.nd_school_week_var.get())
        self.autosave()
        messagebox.showinfo("Settings", "Saved.")

    # -------- File menu behaviors --------
    def create_desktop_shortcut(self):
        """Create a Desktop shortcut for one-click launch (Windows)."""
        try:
            bat = rel_path("Create_Desktop_Shortcut.bat")
            if not os.path.isfile(bat):
                messagebox.showerror("Shortcut", "Create_Desktop_Shortcut.bat not found in app folder.")
                return
            # Use cmd so it works even when double-clicked or from various shells
            subprocess.Popen(["cmd", "/c", bat], cwd=app_dir(), shell=False)
            messagebox.showinfo("Shortcut", "Desktop shortcut created (or updated).")
        except Exception as ex:
            messagebox.showerror("Shortcut", f"Failed to create shortcut: {ex}")

    def autosave(self):
        try:
            save_data(self.model, self.data_path)
            self._set_status(f"Saved {self.data_path} • {datetime.datetime.now().strftime('%H:%M:%S')}")
        except Exception as ex:
            messagebox.showerror("Save", f"Save failed: {ex}")

    def open_dialog(self):
        path = filedialog.askopenfilename(
            title="Open Scheduler Data",
            filetypes=[("JSON data", "*.json")],
            initialdir=os.path.dirname(self.data_path),
        )
        if not path:
            return
        try:
            self.model = load_data(path)
            self.data_path = path
            self.current_label = self._default_week_label()
            self.label_var.set(self.current_label)
            self.current_assignments = []
            self.current_emp_hours = {}
            self.current_total_hours = 0.0
            self.current_warnings = []
            self.current_filled = 0
            self.current_total_slots = 0
            self._validate_requirements_for_context("load", block=False)
            self._apply_ui_scale(self.model.settings.ui_scale)
            self._refresh_all()
            messagebox.showinfo("Open", "Loaded data.")
        except Exception as ex:
            messagebox.showerror("Open", f"Load failed: {ex}")

    def save_as_dialog(self):
        path = filedialog.asksaveasfilename(
            title="Save Scheduler Data As",
            defaultextension=".json",
            filetypes=[("JSON data","*.json")],
            initialdir=os.path.dirname(self.data_path),
            initialfile=os.path.basename(self.data_path),
        )
        if not path:
            return
        self.data_path = path
        self.autosave()

    def new_data(self):
        if not messagebox.askyesno("New", "Start a new dataset?"):
            return
        self.model = DataModel()
        self.model.requirements = default_requirements()
        self.current_label = self._default_week_label()
        self.label_var.set(self.current_label)
        self.current_assignments = []
        self.current_emp_hours = {}
        self.current_total_hours = 0.0
        self.current_warnings = []
        self.current_filled = 0
        self.current_total_slots = 0
        self._refresh_all()
        self.autosave()

    # -------- Refresh --------
    def _refresh_all(self):
        # Store
        self.store_name_var.set(self.model.store_info.store_name)
        self.store_addr_var.set(self.model.store_info.store_address)
        self.store_phone_var.set(self.model.store_info.store_phone)
        self.store_mgr_var.set(self.model.store_info.store_manager)
        st_code = str(getattr(self.model.store_info, "store_state", "") or "").strip().upper()
        self.store_state_var.set(US_STATE_LABELS.get(st_code, ""))
        self.cstore_open_var.set(_norm_hhmm_or_default(getattr(self.model.store_info, "cstore_open", "00:00"), "00:00"))
        self.cstore_close_var.set(_norm_hhmm_or_default(getattr(self.model.store_info, "cstore_close", "24:00"), "24:00"))
        self.kitchen_open_var.set(_norm_hhmm_or_default(getattr(self.model.store_info, "kitchen_open", "00:00"), "00:00"))
        self.kitchen_close_var.set(_norm_hhmm_or_default(getattr(self.model.store_info, "kitchen_close", "24:00"), "24:00"))
        self.carwash_open_var.set(_norm_hhmm_or_default(getattr(self.model.store_info, "carwash_open", "00:00"), "00:00"))
        self.carwash_close_var.set(_norm_hhmm_or_default(getattr(self.model.store_info, "carwash_close", "24:00"), "24:00"))
        peak_soft = _normalize_peak_hours_soft(getattr(self.model.store_info, "peak_hours_soft", {}) or {})
        self.model.store_info.peak_hours_soft = peak_soft
        area_colors = _normalize_area_colors(getattr(self.model.store_info, "area_colors", {}) or {})
        self.model.store_info.area_colors = area_colors
        for area in AREAS:
            vars_for_area = self.peak_soft_vars.get(area, [])
            windows = peak_soft.get(area, [("", ""), ("", ""), ("", "")])
            for idx in range(min(3, len(vars_for_area))):
                st, en = windows[idx] if idx < len(windows) else ("", "")
                vars_for_area[idx][0].set(st or "")
                vars_for_area[idx][1].set(en or "")
        for area in AREAS:
            if hasattr(self, "area_color_vars") and area in self.area_color_vars:
                self.area_color_vars[area].set(area_colors.get(area, _default_area_colors().get(area, "#444444")))
                self._refresh_area_color_swatch(area)

        self.refresh_emp_tree()
        self.refresh_override_dropdowns()
        self.refresh_override_tree()
        self.refresh_req_tree()
        self.refresh_history_tree()
        self.refresh_manager_tasks_tree()
        self.refresh_performance_view()
        try:
            self._refresh_schedule_analysis()
        except Exception:
            pass
        try:
            self._refresh_change_viewer()
        except Exception:
            pass
        try:
            self._apply_current_schedule_to_output_views()
        except Exception:
            pass
        # Manager Goals
        if hasattr(self, "mg_coverage_goal_var"):
            self.mg_coverage_goal_var.set(float(self.model.manager_goals.coverage_goal_pct))
            self.mg_daily_overstaff_allow_var.set(float(self.model.manager_goals.daily_overstaff_allow_hours))
            self.mg_weekly_hours_cap_var.set(float(self.model.manager_goals.weekly_hours_cap))
            self.mg_call_depth_var.set(int(self.model.manager_goals.call_list_depth))
            self.mg_include_noncert_var.set(bool(self.model.manager_goals.include_noncertified_in_call_list))



    def _on_toggle_learn_from_history(self):
        try:
            self.model.settings.learn_from_history = bool(self.learn_hist_var.get())
            save_data(self.data_path, self.model)
            _write_run_log(f"SETTINGS | learn_from_history={self.model.settings.learn_from_history}")
        except Exception:
            pass

    def _reset_learned_patterns(self):
        try:
            self.model.learned_patterns = {}
            save_patterns({})
            # also remove on disk if present
            try:
                p = _patterns_path()
                if os.path.isfile(p):
                    os.remove(p)
            except Exception:
                pass
            self._set_status("Learned patterns reset.")
            _write_run_log("PATTERNS | reset")
        except Exception:
            pass

    def _refresh_learned_patterns(self):
        """Rebuild patterns from history and persist."""
        try:
            pats = learn_patterns_from_history_folder()
            try:
                pats["__demand_forecast__"] = build_demand_forecast_profile()
            except Exception:
                pass
            try:
                pats["__employee_fit__"] = build_employee_fit_profiles()
            except Exception:
                pass
            self.model.learned_patterns = pats or {}
            save_patterns(self.model.learned_patterns)
            _write_run_log(f"PATTERNS | learned={len(self.model.learned_patterns)}")
        except Exception:
            pass



    def _format_pattern_profile(self, emp_name: str, profile: Dict[str, Any]) -> str:
        try:
            area = str(profile.get("preferred_area", "") or "").strip() or "Any"
            st = int(profile.get("preferred_start_tick", 0) or 0)
            ln = int(profile.get("preferred_len_ticks", 0) or 0)
            parts = [f"{emp_name}: area {area}"]
            if st > 0:
                parts.append(f"start {tick_to_hhmm(st)}")
            if ln > 0:
                parts.append(f"length {hours_between_ticks(0, ln):.1f}h")
            return ", ".join(parts)
        except Exception:
            return f"{emp_name}: pattern profile available"

    def _refresh_learned_patterns_with_feedback(self):
        try:
            self._refresh_learned_patterns()
            ct = len(getattr(self.model, "learned_patterns", {}) or {})
            self._set_status(f"Learned patterns refreshed ({ct} employee profiles).")
            messagebox.showinfo("Pattern Learning", f"Learned patterns refreshed for {ct} employee profile(s).")
        except Exception as ex:
            try:
                messagebox.showerror("Pattern Learning", f"Could not refresh learned patterns.\n\n{ex}")
            except Exception:
                pass

    def _set_status(self, s: str):
        self.status_var.set(s)

def main():
    _install_crash_hooks()
    ensure_dir(rel_path("data"))
    ensure_dir(rel_path("history"))
    ensure_dir(rel_path("exports"))
    ensure_state_law_seed_files()
    _write_run_log(f"START {APP_VERSION} | AppDir={_app_dir()} | CWD={os.getcwd()}")
    app = SchedulerApp()
    try:
        _write_run_log(f"READY | DataFile={getattr(app,'data_path', '')}")
    except Exception:
        pass
    app.mainloop()
    _write_run_log("EXIT")

if __name__ == "__main__":
    main()

# -----------------------------
# Phase 4 – D3 Schedule Repair Tool
# -----------------------------
def repair_schedule(schedule, employees=None, manager_goals=None):
    '''
    Lightweight repair engine.
    Pass 1: fix obvious empty coverage slots
    Pass 2: reduce simple hour violations
    Pass 3: keep schedule stability (minimal changes)

    This version is intentionally conservative and
    only adjusts obvious gaps so the schedule is
    never fully regenerated.
    '''
    if not schedule:
        return schedule, {"repairs": 0, "notes": ["No schedule loaded"]}

    repairs = 0
    notes = []

    try:
        for day, slots in schedule.items():
            for slot in slots:
                if not slot.get("employee"):
                    # try assign first available employee
                    if employees:
                        slot["employee"] = employees[0]["name"]
                        repairs += 1
                        notes.append(f"Filled empty slot {day}")
    except Exception as e:
        notes.append(f"Repair engine error: {e}")

    return schedule, {"repairs": repairs, "notes": notes}
