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


if __name__ == "__main__":
    unittest.main()
