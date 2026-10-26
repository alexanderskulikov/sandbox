"""The formulas in bench/: the solver's answer must match bench/answers.csv,
and every answer must be certified (model checked, or DRAT proof checked).
Each formula must be solved within 60 seconds."""

import csv
import os
import time
import unittest

from common import BENCH, TempDir, check, drat_check, run_cli

LIMIT = 60.0


def bench_answers():
    with open(os.path.join(BENCH, 'answers.csv')) as f:
        return {row['file']: row['answer'] for row in csv.DictReader(f)}


class Bench(unittest.TestCase):

    def test_bench(self):
        answers = bench_answers()
        files = sorted(f for f in os.listdir(BENCH) if f.endswith('.cnf'))
        self.assertEqual(sorted(answers), files)
        with TempDir() as tmp:
            for name in files:
                path = os.path.join(BENCH, name)
                proof = os.path.join(tmp, name + '.drat')
                start = time.time()
                code, out = run_cli(path, proof)
                elapsed = time.time() - start
                with self.subTest(name):
                    self.assertLess(elapsed, LIMIT)
                    expected = answers[name]
                    self.assertEqual(code, {'SAT': 10, 'UNSAT': 20}[expected])
                    status, values = check.parse_output(out)
                    n, clauses, _ = check.read_cnf(path)
                    if expected == 'SAT':
                        self.assertEqual(status, 'SATISFIABLE')
                        self.assertIsNone(
                            check.check_model(n, clauses, values))
                    else:
                        self.assertEqual(status, 'UNSATISFIABLE')
                        ok, msg = drat_check.check_proof_file(n, clauses,
                                                              proof)
                        self.assertTrue(ok, msg)


if __name__ == '__main__':
    unittest.main()
