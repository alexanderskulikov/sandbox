"""Random small formulas: the solver against brute force.

Every answer is also certified: models by check.check_model, UNSAT answers
by checking the DRAT proof with drat_check.  Set TEST_SEED to use other
formulas, TEST_SCALE to run more (e.g. TEST_SCALE=10).
"""

import os
import unittest

from common import (brute_force, check, make_rng, random_cnf, random_kcnf,
                    run_cli, solve_in_process, to_dimacs, verify_answer,
                    TempDir)

SCALE = float(os.environ.get('TEST_SCALE', '1'))


def count(n):
    return max(1, int(n * SCALE))


class RandomSmallFormulas(unittest.TestCase):

    def run_family(self, name, gen, how_many):
        rng = make_rng(name)
        stats = {'sat': 0, 'unsat': 0}
        for i in range(how_many):
            num_vars, clauses = gen(rng)
            text = to_dimacs(num_vars, clauses)
            sat, model, proof = solve_in_process(text)
            expected = brute_force(num_vars, clauses)
            with self.subTest(family=name, index=i):
                self.assertEqual(sat, expected is not None,
                                 "wrong answer for:\n" + text)
                problem = verify_answer(text, sat, model, proof)
                self.assertIsNone(problem, "certificate rejected for:\n" +
                                  text + "\nproof:\n" + proof)
            stats['sat' if sat else 'unsat'] += 1
        # make sure each family really exercises both answers
        self.assertGreater(stats['sat'], how_many // 10, stats)
        self.assertGreater(stats['unsat'], how_many // 10, stats)

    def test_mixed_length(self):
        def gen(rng):
            n = rng.randint(1, 12)
            m = rng.randint(1, 7 * n)
            return n, random_cnf(rng, n, m, 1, 5)
        self.run_family('mixed', gen, count(1500))

    def test_random_3cnf(self):
        def gen(rng):
            n = rng.randint(3, 12)
            m = int(n * rng.uniform(3.0, 6.0))
            return n, random_kcnf(rng, n, m, 3)
        self.run_family('3cnf', gen, count(1000))

    def test_long_clauses(self):
        def gen(rng):
            n = rng.randint(4, 12)
            m = int(n * rng.uniform(6.0, 14.0))
            return n, random_kcnf(rng, n, m, 4)
        self.run_family('4cnf', gen, count(400))

    def test_with_empty_and_unit_clauses(self):
        def gen(rng):
            n = rng.randint(1, 10)
            m = rng.randint(0, 5 * n)
            clauses = random_cnf(rng, n, m, 0, 3)
            return n, clauses
        rng = make_rng('empty')
        sat_count = 0
        for i in range(count(400)):
            n, clauses = gen(rng)
            text = to_dimacs(n, clauses)
            sat, model, proof = solve_in_process(text)
            expected = brute_force(n, clauses)
            with self.subTest(index=i):
                self.assertEqual(sat, expected is not None, text)
                self.assertIsNone(verify_answer(text, sat, model, proof),
                                  text)
            sat_count += sat
        self.assertGreater(sat_count, 0)

    def test_command_line(self):
        """A smaller sample through the real command line: exit codes,
        output format (checked by check.py run as a program) and the proof
        file."""
        import subprocess
        import sys
        from common import ROOT
        rng = make_rng('cli')
        with TempDir() as tmp:
            for i in range(count(120)):
                n = rng.randint(1, 12)
                clauses = random_cnf(rng, n, rng.randint(1, 6 * n), 1, 4)
                cnf = os.path.join(tmp, 'f%d.cnf' % i)
                out = os.path.join(tmp, 'f%d.out' % i)
                proof = os.path.join(tmp, 'f%d.drat' % i)
                with open(cnf, 'w') as f:
                    f.write(to_dimacs(n, clauses))
                code, stdout = run_cli(cnf, proof)
                with open(out, 'w') as f:
                    f.write(stdout)
                expected = brute_force(n, clauses)
                with self.subTest(index=i):
                    self.assertEqual(code, 10 if expected else 20, stdout)
                    status, values = check.parse_output(stdout)
                    self.assertEqual(status, 'SATISFIABLE' if expected
                                     else 'UNSATISFIABLE')
                    cmd = [sys.executable, os.path.join(ROOT, 'check.py'),
                           cnf, out]
                    if not expected:
                        cmd += ['--proof', proof]
                    p = subprocess.run(cmd, capture_output=True, text=True)
                    self.assertEqual(p.returncode, 0, p.stdout)
                    self.assertTrue(p.stdout.startswith('VERIFIED'))


class RandomMediumFormulas(unittest.TestCase):
    """Too big for brute force (20-80 variables): every answer must come
    with a certificate that the independent checkers accept."""

    def test_medium_3cnf(self):
        rng = make_rng('medium')
        answers = {True: 0, False: 0}
        for i in range(count(150)):
            n = rng.randint(20, 80)
            m = int(n * rng.uniform(3.8, 4.8))
            clauses = random_kcnf(rng, n, m, 3)
            text = to_dimacs(n, clauses)
            sat, model, proof = solve_in_process(text)
            answers[sat] += 1
            with self.subTest(index=i):
                self.assertIsNone(verify_answer(text, sat, model, proof),
                                  text)
        self.assertGreater(answers[True], 10)
        self.assertGreater(answers[False], 10)


if __name__ == '__main__':
    unittest.main()
