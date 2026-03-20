import importlib.util
import pathlib
import sys
import tempfile
import unittest
from unittest import mock

MOD_PATH = pathlib.Path(__file__).resolve().parents[1] / "scheduler_app_v3_final.py"
spec = importlib.util.spec_from_file_location("scheduler_app_v3_final", MOD_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["scheduler_app_v3_final"] = mod
spec.loader.exec_module(mod)


class RemainingItemsCompletionTests(unittest.TestCase):
    def test_local_file_uri_uses_file_scheme(self):
        with tempfile.NamedTemporaryFile(suffix=".html", delete=False) as tmp:
            tmp.write(b"ok")
            tmp_path = tmp.name
        try:
            uri = mod._local_file_uri(tmp_path)
            self.assertTrue(uri.startswith("file:"))
            self.assertIn(pathlib.Path(tmp_path).name, uri)
        finally:
            pathlib.Path(tmp_path).unlink(missing_ok=True)

    def test_open_local_export_file_falls_back_to_file_uri(self):
        with tempfile.NamedTemporaryFile(suffix=".html", delete=False) as tmp:
            tmp.write(b"<html></html>")
            tmp_path = tmp.name
        try:
            with mock.patch.object(mod.os, "startfile", side_effect=AttributeError, create=True), \
                 mock.patch.object(mod.subprocess, "Popen", side_effect=OSError("no opener")), \
                 mock.patch.object(mod.webbrowser, "open", side_effect=[True]) as web_open:
                self.assertTrue(mod.open_local_export_file(tmp_path))
                self.assertTrue(str(web_open.call_args[0][0]).startswith("file:"))
        finally:
            pathlib.Path(tmp_path).unlink(missing_ok=True)

    def test_manager_report_includes_publish_readiness_summary(self):
        m = mod.DataModel()
        html = mod.make_manager_report_html(m, "Week", [])
        self.assertIn("Publish Readiness", html)
        self.assertIn("Required gaps", html)

    def test_manager_readiness_summary_marks_required_gaps_not_ready(self):
        m = mod.DataModel()
        summary = mod.build_manager_readiness_summary(
            m,
            "Week",
            [],
            diagnostics={"min_short": 2, "final_schedule_valid": True},
            warnings=[],
            filled_slots=8,
            total_slots=10,
        )
        self.assertEqual(summary["status"], "Not Ready to Publish")
        self.assertIn("Required coverage gaps: 2", summary["plain_text"])

    def test_print_html_has_two_page_layout_markers(self):
        m = mod.DataModel()
        html = mod.make_one_page_html(m, "Week", [])
        self.assertIn("page portrait", html)
        self.assertIn("C-STORE SCHEDULE", html)
        self.assertIn("page landscape", html)
        self.assertIn("KITCHEN", html)
        self.assertIn("CARWASH", html)

    def test_state_profile_applies_selected_state_only(self):
        m = mod.DataModel()
        profile_ca = {
            "state_code": "CA",
            "complete": True,
            "minor_rules": {
                "mode": "core_minors_v1",
                "enforce": True,
                "school_week_default": True,
                "caps": {
                    "MINOR_14_15": {"school_day": 2.5, "nonschool_day": 7.0, "weekly_school": 16.0, "weekly_nonschool": 35.0},
                    "MINOR_16_17": {"school_day": 4.0, "nonschool_day": 8.0, "weekly_school": 25.0, "weekly_nonschool": 40.0},
                },
            },
        }
        ok, _msg = mod.apply_state_law_profile_to_model(m, "CA", profile_ca)
        self.assertTrue(ok)
        self.assertEqual(m.nd_rules.state_code, "CA")
        self.assertEqual(m.nd_rules.mode, "core_minors_v1")
        self.assertAlmostEqual(m.nd_rules.caps_by_minor["MINOR_14_15"]["school_day"], 2.5)

        profile_tx = dict(profile_ca)
        profile_tx["state_code"] = "TX"
        ok2, _msg2 = mod.apply_state_law_profile_to_model(m, "TX", profile_tx)
        self.assertTrue(ok2)
        self.assertEqual(m.nd_rules.state_code, "TX")

    def test_minor_caps_use_runtime_config(self):
        m = mod.DataModel()
        m.nd_rules.enforce = True
        m.nd_rules.mode = "core_minors_v1"
        m.nd_rules.is_school_week = True
        m.nd_rules.caps_by_minor = {
            "MINOR_14_15": {"school_day": 2.0, "nonschool_day": 6.0, "weekly_school": 12.0, "weekly_nonschool": 30.0}
        }
        e = mod.Employee(name="Teen", minor_type="MINOR_14_15")
        self.assertAlmostEqual(mod.nd_minor_daily_hour_cap(m, e, "Mon", ""), 2.0)
        self.assertAlmostEqual(mod.nd_minor_weekly_hour_cap(m, e), 12.0)

    def test_brand_asset_resolution_prefers_store_then_header_then_legacy(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            assets = pathlib.Path(tmpdir) / "Assets"
            legacy = pathlib.Path(tmpdir) / "assets"
            assets.mkdir()
            legacy.mkdir()
            (assets / "header_logo.png").write_bytes(b"h")
            self.assertTrue(mod.resolve_brand_asset_path("store", tmpdir).endswith("header_logo.png"))
            (assets / "store_logo.png").write_bytes(b"s")
            self.assertTrue(mod.resolve_brand_asset_path("store", tmpdir).endswith("store_logo.png"))
            (assets / "store_logo.png").unlink()
            (assets / "header_logo.png").unlink()
            (legacy / "petroserve.png").write_bytes(b"p")
            self.assertTrue(mod.resolve_brand_asset_path("store", tmpdir).endswith("petroserve.png"))

    def test_publish_readiness_checklist_exposes_counts(self):
        m = mod.DataModel()
        checklist = mod.build_publish_readiness_checklist(
            m,
            "Week",
            [],
            diagnostics={"min_short": 1, "pref_short": 2, "override_warning_count": 3, "cap_blocked_attempts": 4},
            warnings=["warning"],
            analyzer_findings_count=7,
        )
        self.assertEqual(checklist["uncovered_minimums"], 1)
        self.assertEqual(checklist["preferred_gaps"], 2)
        self.assertEqual(checklist["override_warnings"], 3)
        self.assertEqual(checklist["labor_cap_warnings"], 4)
        self.assertEqual(checklist["analyzer_findings_count"], 7)

    def test_replacement_assistant_candidate_shape(self):
        m = mod.DataModel()
        av = {d: mod.DayRules(False, 0, mod.DAY_TICKS, []) for d in mod.DAYS}
        m.employees = [
            mod.Employee(name="A", areas_allowed=["CSTORE"], preferred_areas=["CSTORE"], availability=av, hard_availability=av, soft_availability=av),
            mod.Employee(name="B", areas_allowed=["CSTORE"], preferred_areas=["CSTORE"], availability=av, hard_availability=av, soft_availability=av),
        ]
        m.requirements = [mod.RequirementBlock("Mon", "CSTORE", 16, 20, 1, 1, 2)]
        target = mod.Assignment("Mon", "CSTORE", 16, 20, "A", False, mod.ASSIGNMENT_SOURCE_ENGINE)
        payload = mod.build_replacement_assistant_candidates(m, "Week", [target], target)
        self.assertTrue(payload["candidates"])
        self.assertIn("employee", payload["candidates"][0])
        self.assertIn("coverage_impact_ticks", payload["candidates"][0])

    def test_historical_suggestions_output_shape(self):
        m = mod.DataModel()
        m.employees = [mod.Employee(name="A"), mod.Employee(name="B")]
        m.learned_patterns = {
            "A": {"preferred_area": "CSTORE", "preferred_start_tick": 16, "preferred_len_ticks": 8},
            "__demand_forecast__": {"Mon|CSTORE|16": 1.5},
        }
        payload = mod.build_historical_suggestions(m)
        self.assertIn("employee_suggestions", payload)
        self.assertIn("forecast_pressure", payload)
        self.assertEqual(payload["employee_suggestions"][0]["employee"], "A")


if __name__ == "__main__":
    unittest.main()
