import importlib.util
import pathlib
import sys
import unittest

MOD_PATH = pathlib.Path(__file__).resolve().parents[1] / "scheduler_app_v3_final.py"
spec = importlib.util.spec_from_file_location("scheduler_app_v3_final", MOD_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["scheduler_app_v3_final"] = mod
spec.loader.exec_module(mod)


def _full_availability():
    return {d: mod.DayRules(False, 0, mod.DAY_TICKS, []) for d in mod.DAYS}


def _employee(name, areas, hard_min=0.0, max_weekly=40.0):
    av = _full_availability()
    return mod.Employee(
        name=name,
        phone="",
        max_weekly_hours=max_weekly,
        hard_min_weekly_hours=hard_min,
        areas_allowed=list(areas),
        preferred_areas=[areas[0]] if areas else [],
        availability=av,
        hard_availability=av,
        soft_availability=av,
    )


def _requirements_balanced(area="CSTORE", min_count=1, start=16, end=32):
    return [mod.RequirementBlock(d, area, start, end, min_count, min_count, max(2, min_count + 1)) for d in mod.DAYS]


class SolverBiasRegressionTests(unittest.TestCase):
    def test_no_first_legal_day_bias_telemetry(self):
        model = mod.DataModel()
        model.employees = [_employee("A", ["CSTORE"]), _employee("B", ["CSTORE"])]
        model.requirements = _requirements_balanced("CSTORE", 1)
        diag = mod.generate_schedule(model, "")[-1]
        tel = diag.get("candidate_selection_telemetry", [])
        self.assertTrue(any(int(x.get("feasible_candidates", 0)) > 1 for x in tel))

    def test_sunday_frontload_control_balanced_week(self):
        model = mod.DataModel()
        model.employees = [_employee("A", ["CSTORE"]), _employee("B", ["CSTORE"]), _employee("C", ["CSTORE"])]
        model.requirements = _requirements_balanced("CSTORE", 1)
        diag = mod.generate_schedule(model, "")[-1]
        snap = diag.get("phase_snapshots", {}).get("phase5_cstore_backfill_after_carwash", {})
        sun_share = float(snap.get("sunday_share", 0.0) or 0.0)
        self.assertLess(sun_share, 0.30)

    def test_hard_min_topup_candidate_ranking(self):
        model = mod.DataModel()
        model.employees = [_employee("A", ["CSTORE", "KITCHEN"], hard_min=8.0), _employee("B", ["CSTORE"])]
        model.requirements = _requirements_balanced("CSTORE", 1)
        diag = mod.generate_schedule(model, "")[-1]
        tel = [x for x in diag.get("candidate_selection_telemetry", []) if x.get("selector") == "hard_min_topup"]
        self.assertTrue(len(tel) > 0)
        self.assertTrue(all(len(x.get("chosen_rank", [])) >= 4 for x in tel))

    def test_area_starvation_mitigation(self):
        model = mod.DataModel()
        model.employees = [
            _employee("A", ["CSTORE", "KITCHEN", "CARWASH"], max_weekly=24.0),
            _employee("B", ["CSTORE", "KITCHEN"], max_weekly=24.0),
            _employee("C", ["CSTORE", "CARWASH"], max_weekly=24.0),
        ]
        req = []
        for d in mod.DAYS:
            req += [
                mod.RequirementBlock(d, "CSTORE", 16, 30, 1, 1, 2),
                mod.RequirementBlock(d, "KITCHEN", 18, 26, 1, 1, 2),
                mod.RequirementBlock(d, "CARWASH", 20, 28, 1, 1, 2),
            ]
        model.requirements = req
        diag = mod.generate_schedule(model, "")[-1]
        pd = diag.get("phase_diagnostics", {})
        self.assertGreaterEqual(int(pd.get("phase2_kitchen", {}).get("adds", 0)), 1)
        self.assertGreaterEqual(int(pd.get("phase4_carwash", {}).get("adds", 0)), 1)

    def test_candidate_ranking_explainability_diagnostics(self):
        model = mod.DataModel()
        model.employees = [_employee("A", ["CSTORE"]), _employee("B", ["CSTORE"])]
        model.requirements = _requirements_balanced("CSTORE", 1)
        diag = mod.generate_schedule(model, "")[-1]
        sample = next((x for x in diag.get("candidate_selection_telemetry", []) if x.get("selector") == "open_or_extend_master_envelope"), None)
        self.assertIsNotNone(sample)
        self.assertIn("chosen_rank", sample)
        self.assertIn("feasible_candidates", sample)

    def test_runtime_budget_best_so_far_exit_returns_valid_schedule(self):
        model = mod.DataModel()
        model.employees = [_employee("A", ["CSTORE"]), _employee("B", ["CSTORE"]), _employee("C", ["CSTORE"])]
        model.requirements = _requirements_balanced("CSTORE", 1)
        budget = mod.SolverRuntimeBudget("generate_fresh", 0.0, 0.0)
        assigns, _emp_hours, _total_hours, _warnings, _filled, _total_slots, _iters, _restarts, diag = mod.generate_schedule(model, "", runtime_budget=budget)
        self.assertIsInstance(assigns, list)
        self.assertTrue(diag.get("final_schedule_valid", False))
        self.assertTrue(diag.get("runtime_budget", {}).get("hard_exhausted", False))

    def test_week_shape_diagnostics_include_balance_fields(self):
        model = mod.DataModel()
        model.employees = [_employee("A", ["CSTORE"]), _employee("B", ["CSTORE"]), _employee("C", ["CSTORE"])]
        model.requirements = _requirements_balanced("CSTORE", 1)
        diag = mod.generate_schedule(model, "")[-1]
        week_shape = diag.get("week_shape_diagnostics", {})
        self.assertIn("hours_by_day", week_shape)
        self.assertIn("day_load_variance", week_shape)
        self.assertIn("early_week_share", week_shape)

    def test_refine_runtime_budget_diagnostics(self):
        model = mod.DataModel()
        model.employees = [_employee("A", ["CSTORE"]), _employee("B", ["CSTORE"])]
        model.requirements = [mod.RequirementBlock("Mon", "CSTORE", 16, 24, 1, 1, 2)]
        refined, diag = mod.improve_weak_areas(model, "Week", [], runtime_budget=mod.SolverRuntimeBudget("refine", 0.0, 0.0))
        self.assertEqual(refined, [])
        self.assertIn("notes", diag)

    def test_refine_does_not_introduce_engine_hard_errors(self):
        model = mod.DataModel()
        model.employees = [
            _employee("A", ["CSTORE", "KITCHEN"], max_weekly=32.0),
            _employee("B", ["CSTORE", "CARWASH"], max_weekly=30.0),
            _employee("C", ["CSTORE"], max_weekly=28.0),
            _employee("D", ["CSTORE", "KITCHEN", "CARWASH"], max_weekly=36.0),
            _employee("E", ["KITCHEN", "CSTORE"], max_weekly=24.0, hard_min=8.0),
            _employee("F", ["CARWASH", "CSTORE"], max_weekly=24.0),
        ]
        req = []
        for d in mod.DAYS:
            req += [
                mod.RequirementBlock(d, "CSTORE", 16, 32, 1, 1, 2),
                mod.RequirementBlock(d, "KITCHEN", 18, 28, 1, 1, 2),
                mod.RequirementBlock(d, "CARWASH", 20, 26, 1, 1, 2),
            ]
        model.requirements = req
        baseline, *_rest, diag = mod.generate_schedule_multi_scenario(model, "Week")
        self.assertTrue(diag.get("final_schedule_valid", False))
        working = list(baseline)
        for target in [("Mon", "CSTORE"), ("Thu", "KITCHEN"), ("Sat", "CARWASH")]:
            for a in list(working):
                if a.day == target[0] and a.area == target[1] and a.source == mod.ASSIGNMENT_SOURCE_ENGINE:
                    working.remove(a)
                    break

        def _find_valid_manual():
            for e in model.employees:
                for day in mod.DAYS:
                    for st in range(0, mod.DAY_TICKS - 2, 2):
                        cand = mod.Assignment(day, "CSTORE", st, st + 2, e.name, False, mod.ASSIGNMENT_SOURCE_MANUAL)
                        trial = list(working) + [cand]
                        errs = [
                            v for v in mod.evaluate_schedule_hard_rules(model, "Week", trial, include_override_warnings=False)
                            if v.severity == "error" and mod.is_engine_managed_source(v.assignment_source)
                        ]
                        if not errs:
                            return cand
            return None

        manual = _find_valid_manual()
        self.assertIsNotNone(manual)
        working.append(manual)
        input_errors = [
            v for v in mod.evaluate_schedule_hard_rules(model, "Week", working, include_override_warnings=False)
            if v.severity == "error" and mod.is_engine_managed_source(v.assignment_source)
        ]
        self.assertEqual(input_errors, [])
        refined, ref_diag = mod.improve_weak_areas(model, "Week", working, protect_manual=True, runtime_budget=mod.SolverRuntimeBudget("refine", 50.0, 60.0))
        output_errors = [
            v for v in mod.evaluate_schedule_hard_rules(model, "Week", refined, include_override_warnings=False)
            if v.severity == "error" and mod.is_engine_managed_source(v.assignment_source)
        ]
        self.assertEqual(output_errors, [])
        self.assertIn(manual, refined)
        self.assertTrue(ref_diag.get("protected_preserved", False))

    def test_requirement_parity_intact(self):
        model = mod.DataModel()
        model.employees = [_employee("A", ["CSTORE"])]
        model.requirements = _requirements_balanced("CSTORE", 1)
        diag = mod.generate_schedule(model, "")[-1]
        self.assertTrue(diag.get("requirement_map_parity_ok", False))
        fps = diag.get("requirement_map_fingerprints", {})
        self.assertEqual(fps.get("ui_base"), fps.get("solver_effective"))

    def test_heatmap_solver_coverage_parity(self):
        model = mod.DataModel()
        model.employees = [_employee("A", ["CSTORE"]), _employee("B", ["CSTORE"])]
        model.requirements = _requirements_balanced("CSTORE", 1)
        diag = mod.generate_schedule(model, "")[-1]
        cov = diag.get("coverage_parity", {})
        self.assertTrue(cov.get("parity_ok", False))
        self.assertEqual(cov.get("solver_total_ticks"), cov.get("heatmap_total_ticks"))

    def test_refine_targeting_preserves_manual_assignments(self):
        model = mod.DataModel()
        model.employees = [_employee("A", ["CSTORE"]), _employee("B", ["CSTORE"])]
        model.requirements = [mod.RequirementBlock("Mon", "CSTORE", 16, 24, 1, 1, 2)]
        manual = mod.Assignment("Mon", "CSTORE", 16, 20, "A", False, mod.ASSIGNMENT_SOURCE_MANUAL)
        refined, diag = mod.improve_weak_areas(model, "Week", [manual], protect_manual=True)
        self.assertIn(manual, refined)
        self.assertTrue(diag.get("protected_preserved", False))

    def test_runtime_diagnostics_helper_records_seconds(self):
        diag = mod._set_runtime_metric({}, "refine", 1.2345, passes=2)
        self.assertIn("runtime_diagnostics", diag)
        self.assertAlmostEqual(diag["runtime_diagnostics"]["refine"]["seconds"], 1.2345, places=4)
        self.assertEqual(diag["runtime_diagnostics"]["refine"]["passes"], 2)


if __name__ == "__main__":
    unittest.main()
