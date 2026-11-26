"""--min-interval-minutes guard of fetch_upstream_pr_insights.py (stdlib only, no network).

An unchanged fetch must still restamp an old generated_at, or the stamp ages past the interval in a quiet hour and
every 10-minute periodic run calls the API again (tl_58b03bc15c).
"""
import json, os, sys, tempfile, unittest
from datetime import datetime, timedelta, timezone
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fetch_upstream_pr_insights as f

ISO = "%Y-%m-%dT%H:%M:%SZ"


def stamp(minutes_ago):
    return (datetime.now(timezone.utc) - timedelta(minutes=minutes_ago)).strftime(ISO)


class T(unittest.TestCase):
    def setUp(self):
        self.calls = 0
        self.orig_fetch = f.fetch_via_graphql
        self.orig_argv = sys.argv
        self.orig_token = os.environ.get("GITHUB_TOKEN")
        os.environ["GITHUB_TOKEN"] = "test-token-not-real"

        def fake_fetch(owner, name, cutoff_dt, token):
            self.calls += 1
            return [], []
        f.fetch_via_graphql = fake_fetch
        self.dir = tempfile.mkdtemp()
        self.path = os.path.join(self.dir, "insights.json")

    def tearDown(self):
        f.fetch_via_graphql = self.orig_fetch
        sys.argv = self.orig_argv
        if self.orig_token is None:
            os.environ.pop("GITHUB_TOKEN", None)
        else:
            os.environ["GITHUB_TOKEN"] = self.orig_token

    def run_main(self, *extra):
        sys.argv = ["fetch_upstream_pr_insights.py", "--data", self.path, *extra]
        return f.main()

    def read(self):
        with open(self.path, encoding="utf-8") as fh:
            return json.load(fh)

    def write_with_stamp(self, minutes_ago):
        data = self.read()
        data["generated_at"] = stamp(minutes_ago)
        with open(self.path, "w", encoding="utf-8") as fh:
            json.dump(data, fh)
        return data["generated_at"]

    def test_unchanged_old_stamp_is_refreshed_so_guard_holds(self):
        self.assertEqual(self.run_main(), 0)
        self.assertEqual(self.calls, 1)
        old = self.write_with_stamp(120)
        # Periodic run: stamp 120 min old >= 50 -> fetch, same content -> stamp refreshed
        self.assertEqual(self.run_main("--min-interval-minutes", "50"), 0)
        self.assertEqual(self.calls, 2)
        refreshed = self.read()["generated_at"]
        self.assertNotEqual(refreshed, old)
        age = (datetime.now(timezone.utc) - f.parse_iso(refreshed)).total_seconds()
        self.assertLess(age, 60)
        # The next periodic run inside the interval makes no API call
        self.assertEqual(self.run_main("--min-interval-minutes", "50"), 0)
        self.assertEqual(self.calls, 2)

    def test_unchanged_fresh_stamp_is_not_rewritten(self):
        self.run_main()
        fresh = self.write_with_stamp(5)
        # Push/manual run (no interval): fetches, same content, stamp only 5 min old -> file left as is
        self.assertEqual(self.run_main(), 0)
        self.assertEqual(self.calls, 2)
        self.assertEqual(self.read()["generated_at"], fresh)

    def test_content_kept_when_only_stamp_refreshed(self):
        self.run_main()
        before = self.read()
        self.write_with_stamp(90)
        self.run_main("--min-interval-minutes", "50")
        after = self.read()
        self.assertEqual(f._strip_volatile(after), f._strip_volatile(before))


if __name__ == "__main__":
    unittest.main(verbosity=1)
