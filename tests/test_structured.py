"""Formulas whose answer is known by construction or by an independent
polynomial-time algorithm, and edge cases of the input format, run
through the command line."""

import os
import unittest

from common import (TempDir, check, coloring, drat_check, horn_sat,
                    make_rng, pigeonhole, planted_kcnf, queens, random_cnf,
                    random_horn, random_xor_system, run_cli,
                    solve_in_process, to_dimacs, two_sat, verify_answer,
                    xor_sat)


class KnownAnswers(unittest.TestCase):

    def expect(self, num_vars, clauses, expected, label):
        text = to_dimacs(num_vars, clauses)
        sat, model, proof = solve_in_process(text)
        with self.subTest(label):
            self.assertEqual(sat, expected, label)
            self.assertIsNone(verify_answer(text, sat, model, proof), label)

    def test_pigeonhole(self):
        for holes in range(1, 8):
            n, c = pigeonhole(holes + 1, holes)
            self.expect(n, c, False, 'php %d->%d' % (holes + 1, holes))
            n, c = pigeonhole(holes, holes)
            self.expect(n, c, True, 'php %d->%d' % (holes, holes))

    def test_queens(self):
        for size in range(1, 21):
            n, c = queens(size)
            self.expect(n, c, size not in (2, 3), 'queens %d' % size)

    def test_coloring(self):
        for k in range(3, 16):
            cycle = [(i, (i + 1) % k) for i in range(k)]
            n, c = coloring(k, cycle, 2)
            self.expect(n, c, k % 2 == 0, 'cycle %d, 2 colours' % k)
        for k in range(2, 8):
            clique = [(i, j) for i in range(k) for j in range(i + 1, k)]
            n, c = coloring(k, clique, k - 1)
            self.expect(n, c, False, 'K%d, %d colours' % (k, k - 1))
            n, c = coloring(k, clique, k)
            self.expect(n, c, True, 'K%d, %d colours' % (k, k))
        petersen = [(i, (i + 1) % 5) for i in range(5)] + \
            [(5 + i, 5 + (i + 2) % 5) for i in range(5)] + \
            [(i, i + 5) for i in range(5)]
        n, c = coloring(10, petersen, 3)
        self.expect(n, c, True, 'Petersen, 3 colours')
        n, c = coloring(10, petersen, 2)
        self.expect(n, c, False, 'Petersen, 2 colours')

    def test_xor_systems(self):
        rng = make_rng('xor')
        seen = set()
        for i in range(120):
            n = rng.randint(5, 60)
            eqs, clauses = random_xor_system(rng, n,
                                             int(n * rng.uniform(0.7, 1.1)))
            expected = xor_sat(n, eqs)
            seen.add(expected)
            self.expect(n, clauses, expected, 'xor %d' % i)
        self.assertEqual(seen, {True, False})

    def test_two_sat(self):
        rng = make_rng('2sat')
        seen = set()
        for i in range(60):
            n = rng.randint(10, 400)
            clauses = random_cnf(rng, n, int(n * rng.uniform(0.6, 1.4)),
                                 2, 2, allow_junk=False)
            expected = two_sat(n, clauses)
            seen.add(expected)
            self.expect(n, clauses, expected, '2sat %d' % i)
        self.assertEqual(seen, {True, False})

    def test_horn(self):
        rng = make_rng('horn')
        seen = set()
        for i in range(80):
            n = rng.randint(5, 300)
            clauses = random_horn(rng, n, int(n * rng.uniform(0.8, 2.5)))
            expected = horn_sat(n, clauses)
            seen.add(expected)
            self.expect(n, clauses, expected, 'horn %d' % i)
        self.assertEqual(seen, {True, False})

    def test_planted_3sat(self):
        rng = make_rng('planted')
        for i in range(25):
            n = rng.randint(50, 300)
            clauses, _ = planted_kcnf(rng, n, int(n * 4.2), 3)
            self.expect(n, clauses, True, 'planted %d' % i)


class CommandLine(unittest.TestCase):
    """Edge cases of the input format and of the output, through the real
    command line, with the output checked by check.py."""

    def run_text(self, text, expected):
        with TempDir() as tmp:
            cnf = os.path.join(tmp, 'f.cnf')
            proof = os.path.join(tmp, 'f.drat')
            with open(cnf, 'w') as f:
                f.write(text)
            code, out = run_cli(cnf, proof)
            self.assertEqual(code, 10 if expected else 20, out)
            status, values = check.parse_output(out)
            n, clauses, _ = check.read_cnf_text(text)
            if expected:
                self.assertEqual(status, 'SATISFIABLE')
                self.assertIsNone(check.check_model(n, clauses, values))
            else:
                self.assertEqual(status, 'UNSATISFIABLE')
                self.assertIsNone(values)
                ok, msg = drat_check.check_proof_file(n, clauses, proof)
                self.assertTrue(ok, msg)
            return out

    def test_empty_formula(self):
        out = self.run_text("p cnf 0 0\n", True)
        self.assertEqual(out.split('\n')[:2], ['s SATISFIABLE', 'v 0'])
        out = self.run_text("p cnf 3 0\n", True)
        self.assertEqual(sorted(abs(x) for x in check.parse_output(out)[1]),
                         [1, 2, 3])

    def test_empty_clause(self):
        self.run_text("p cnf 2 2\n1 2 0\n0\n", False)
        self.run_text("p cnf 0 1\n0\n", False)

    def test_units(self):
        self.run_text("p cnf 1 2\n1 0\n-1 0\n", False)
        self.run_text("p cnf 2 3\n1 0\n-1 2 0\n-2 0\n", False)
        self.run_text("p cnf 2 2\n1 0\n1 0\n", True)

    def test_unused_variables_get_values(self):
        out = self.run_text("p cnf 10 1\n3 -7 0\n", True)
        values = check.parse_output(out)[1]
        self.assertEqual(sorted(abs(x) for x in values), list(range(1, 11)))

    def test_layout(self):
        text = ("c first\nc second\np cnf 3 4\n1 -2\n3 0 -1\n 2 0\n"
                "c between\n\n2 3 0 -3 0\n")
        self.run_text(text, True)
        self.run_text("p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n%\n0\n",
                      False)
        self.run_text("p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n%\n",
                      False)
        # last clause without its 0
        self.run_text("p cnf 2 2\n1 0\n-1", False)

    def test_duplicates_and_tautologies(self):
        self.run_text("p cnf 2 3\n1 1 1 0\n-1 2 -1 0\n-2 2 1 0\n", True)
        self.run_text("p cnf 2 3\n1 1 0\n-1 -1 2 2 0\n-2 -2 0\n", False)

    def test_variable_beyond_header(self):
        text = "p cnf 2 2\n1 5 0\n-5 0\n"
        out = self.run_text(text, True)
        values = check.parse_output(out)[1]
        self.assertEqual(sorted(abs(x) for x in values), [1, 2, 3, 4, 5])

    def test_proof_option_forms(self):
        import subprocess
        import sys
        from common import SOLVER
        with TempDir() as tmp:
            cnf = os.path.join(tmp, 'f.cnf')
            proof = os.path.join(tmp, 'p.drat')
            with open(cnf, 'w') as f:
                f.write("p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n")
            for args in (['--proof', proof, cnf], [cnf, '--proof=' + proof]):
                if os.path.exists(proof):
                    os.remove(proof)
                p = subprocess.run([sys.executable, SOLVER] + args,
                                   capture_output=True, text=True)
                self.assertEqual(p.returncode, 20)
                with open(proof) as f:
                    self.assertTrue(f.read().endswith('0\n'))
            p = subprocess.run([sys.executable, SOLVER, cnf],
                               capture_output=True, text=True)
            self.assertEqual(p.returncode, 20)
            self.assertEqual(p.stdout, 's UNSATISFIABLE\n')

    def test_answer_does_not_depend_on_file_name(self):
        """Same formula under different names gives the same output."""
        text = to_dimacs(*pigeonhole(4, 3))
        outs = set()
        with TempDir() as tmp:
            for name in ('a.cnf', 'sat.cnf', 'n050_00.cnf', 'x'):
                path = os.path.join(tmp, name)
                with open(path, 'w') as f:
                    f.write(text)
                outs.add(run_cli(path))
        self.assertEqual(len(outs), 1)


if __name__ == '__main__':
    unittest.main()
