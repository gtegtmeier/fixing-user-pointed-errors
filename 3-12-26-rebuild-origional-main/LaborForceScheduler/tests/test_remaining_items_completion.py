import importlib.util
import pathlib
import sys
import unittest

MOD_PATH = pathlib.Path(__file__).resolve().parents[1] / "scheduler_app_v3_final.py"
spec = importlib.util.spec_from_file_location("scheduler_app_v3_final", MOD_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["scheduler_app_v3_final"] = mod
spec.loader.exec_module(mod)


class RemainingItemsCompletionTests(unittest.TestCase):
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
