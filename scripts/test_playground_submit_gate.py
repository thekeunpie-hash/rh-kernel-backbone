import json, math, os, sys, tempfile, unittest
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import playground_submit_gate as g
T0 = 21641
class T(unittest.TestCase):
    def test_statement_examples(self):
        self.assertAlmostEqual(g.score_from_tokens(T0, T0), 50.0, 6)
        self.assertAlmostEqual(g.score_from_tokens(T0/10, T0), 66.6667, 3)
        self.assertAlmostEqual(g.score_from_tokens(T0/100, T0), 75.0, 6)
        self.assertLess(g.score_from_tokens(T0*2, T0), 50)
    def test_inverse(self):
        for b in (40.0, 47.5, 52.0, 57.0, 70.0449, 75.0):
            t = g.tokens_needed(b, T0)
            self.assertAlmostEqual(g.score_from_tokens(t, T0), b, 6)
    def test_hold_when_not_above_best(self):
        best = {"score": 70.0449, "attempt_id": 101470}
        d = g.decide(57.0, best, T0, 0); self.assertEqual(d["decision"], "HOLD")
        self.assertLess(d["improve"]["target_official_tokens_below"], 1000)
        self.assertEqual(g.decide(70.0449, best, T0, 0)["decision"], "HOLD")  # tie is not a win
        self.assertEqual(g.decide(70.1, best, T0, 0)["decision"], "SUBMIT_OK")
    def test_fail_closed(self):
        self.assertEqual(g.decide(99.0, None, T0, 0)["decision"], "HOLD")
    def test_min_of_predictions_and_ledger(self):
        rows = {"attempts": [{"id": 1, "status": "scored", "scoringState": {"state": "final", "displayScore": 60.0}},
                             {"id": 2, "status": "pending_review", "scoringState": {"state": "failed", "displayScore": 99}}]}
        d = tempfile.mkdtemp(); bj = os.path.join(d, "b.json"); led = os.path.join(d, "l.jsonl")
        json.dump(rows, open(bj, "w"))
        # tokens -> ~66.67 by formula, but Harbor says 57 -> lowest wins -> HOLD
        rc = g.main(["--challenge-id", "x", "--tokens", str(T0/10), "--t0", str(T0), "--predicted", "57",
                     "--ledger", led, "--board-json", bj])
        self.assertEqual(rc, 3)
        rc = g.main(["--challenge-id", "x", "--tokens", str(T0/10), "--t0", str(T0), "--ledger", led, "--board-json", bj])
        self.assertEqual(rc, 0)
        recs = [json.loads(l) for l in open(led)]
        self.assertEqual([r["decision"] for r in recs], ["HOLD", "SUBMIT_OK"]); self.assertEqual(recs[0]["best"]["attempt_id"], 1)
    def test_board_unreadable_exit2(self):
        d = tempfile.mkdtemp(); led = os.path.join(d, "l.jsonl")
        rc = g.main(["--challenge-id", "x", "--tokens", "10", "--t0", str(T0), "--ledger", led, "--board-json", os.path.join(d, "missing.json")])
        self.assertEqual(rc, 2)
    def test_target_is_strictly_better(self):
        t = g.decide(57.0, {"score": 70.0449, "attempt_id": 101470}, T0, 0)["improve"]["target_official_tokens_below"]
        self.assertGreater(g.score_from_tokens(t, T0), 70.0449)
        self.assertLessEqual(g.score_from_tokens(t + 1, T0), 70.0449 + 1e-3)
if __name__ == "__main__":
    unittest.main(verbosity=1)
