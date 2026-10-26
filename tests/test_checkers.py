"""Tests of the checkers themselves.

A checker that accepts everything would make every other test worthless,
so these tests feed the checkers wrong answers and broken proofs and
require them to be rejected, and compare drat_check.py with a naive RUP
checker (tests/common.py) on many mutated proofs.
"""

import random
import unittest

from common import (brute_force, check, drat_check, make_rng,
                    naive_rup_check, random_cnf, random_kcnf,
                    solve_in_process, to_dimacs)


def evaluate(clauses, assignment):
    """Independent evaluation: assignment is a dict var -> bool."""
    return all(any(assignment[abs(l)] == (l > 0) for l in c)
               for c in clauses)


class ModelChecker(unittest.TestCase):

    def test_agrees_with_direct_evaluation(self):
        rng = make_rng('model-eval')
        accepted = rejected = 0
        for _ in range(3000):
            n = rng.randint(1, 8)
            clauses = random_cnf(rng, n, rng.randint(0, 3 * n), 1, 3)
            values = [v if rng.random() < 0.5 else -v
                      for v in range(1, n + 1)]
            rng.shuffle(values)
            expected = evaluate(clauses, {abs(l): l > 0 for l in values})
            got = check.check_model(n, clauses, values) is None
            self.assertEqual(got, expected, (n, clauses, values))
            accepted += got
            rejected += not got
        self.assertGreater(accepted, 300)
        self.assertGreater(rejected, 300)

    def test_rejects_incomplete_or_inconsistent_values(self):
        clauses = [[1, 2], [-1, 3]]
        self.assertIsNone(check.check_model(3, clauses, [1, 2, 3]))
        self.assertIsNotNone(check.check_model(3, clauses, [1, 3]))
        self.assertIsNotNone(check.check_model(3, clauses, [1, 2, 3, -1]))
        self.assertIsNotNone(check.check_model(3, clauses, [1, 2, 3, 3]))
        self.assertIsNotNone(check.check_model(3, clauses, [1, 2, 3, 4]))
        self.assertIsNotNone(check.check_model(3, clauses, None))
        # empty clause: never satisfied
        self.assertIsNotNone(check.check_model(1, [[]], [1]))

    def test_output_parser(self):
        ok = "c hello\ns SATISFIABLE\nv 1 -2\nv 3 0\n"
        self.assertEqual(check.parse_output(ok), ('SATISFIABLE', [1, -2, 3]))
        self.assertEqual(check.parse_output("s UNSATISFIABLE\n"),
                         ('UNSATISFIABLE', None))
        bad = [
            "v 1 0\n",                                   # no s line
            "s SATISFIABLE\ns SATISFIABLE\nv 1 0\n",     # two s lines
            "s SATISFIABLE\nv 1 2\n",                    # no final 0
            "s SATISFIABLE\nv 1 0 2\n",                  # value after 0
            "s SATISFIABLE\nv 1 x 0\n",                  # junk
            "s SATISFIABLE\nv 1 --2 0\n",                # junk
            "s SAT\nv 1 0\n",                            # wrong word
            "s SATISFIABLE\n1 2 0\n",                    # line without v
        ]
        for text in bad:
            with self.subTest(text=text):
                with self.assertRaises(check.FormatError):
                    check.parse_output(text)

    def test_formula_parser(self):
        text = "c comment\np cnf 4 3\n1 -2\n 3 0\nc inside\n-4 0 2 3 0\n%\n0\n"
        n, clauses, warnings = check.read_cnf_text(text)
        self.assertEqual(n, 4)
        self.assertEqual(clauses, [[1, -2, 3], [-4], [2, 3]])
        self.assertEqual(warnings, [])
        n, clauses, warnings = check.read_cnf_text("p cnf 2 1\n1 5 0\n")
        self.assertEqual(n, 5)
        self.assertTrue(warnings)
        for text in ["1 2 0\n", "p cnf 2 1\n1 a 0\n", "p cnf x 1\n1 0\n",
                     "p cnf 2 1\np cnf 2 1\n1 0\n"]:
            with self.subTest(text=text):
                with self.assertRaises(check.FormatError):
                    check.read_cnf_text(text)

    def test_solver_and_checker_parsers_agree(self):
        """Both readers must see the same clauses (up to the variable
        count, where both take the larger of header and actual)."""
        import solver
        rng = make_rng('parsers')
        for _ in range(300):
            n = rng.randint(1, 30)
            clauses = random_cnf(rng, n, rng.randint(0, 40), 0, 5)
            # random layout: clauses split over lines, comments between
            parts = ['c random layout', 'p cnf %d %d' % (n, len(clauses))]
            for c in clauses:
                toks = [str(l) for l in c] + ['0']
                while toks:
                    k = rng.randint(1, len(toks))
                    parts.append('  '.join(toks[:k]))
                    toks = toks[k:]
                    if rng.random() < 0.1:
                        parts.append('c between')
            text = '\n'.join(parts) + '\n'
            n1, c1 = solver.parse_dimacs(text)
            n2, c2, _ = check.read_cnf_text(text)
            self.assertEqual(c1, c2)
            self.assertEqual(c1, clauses)
            self.assertEqual(n1, n2)


class DratChecker(unittest.TestCase):

    def assertAccepted(self, n, clauses, proof):
        ok, msg = drat_check.check_proof(n, clauses, proof)
        self.assertTrue(ok, msg)

    def assertRejected(self, n, clauses, proof):
        ok, msg = drat_check.check_proof(n, clauses, proof)
        self.assertFalse(ok, msg)

    def test_hand_written(self):
        # (x1 v x2) (x1 v -x2) (-x1 v x2) (-x1 v -x2)
        f = [[1, 2], [1, -2], [-1, 2], [-1, -2]]
        self.assertAccepted(2, f, "1 0\n0\n")
        self.assertAccepted(2, f, "1 0\nd 1 2 0\n2 0\n0\n")
        self.assertRejected(2, f, "0\n")             # empty clause not RUP
        self.assertRejected(2, f, "1 0\n")           # no empty clause
        self.assertRejected(2, f, "")
        self.assertRejected(2, f, "1 0\n2 0\n")      # still no empty clause
        # deleting the clauses the lemma needs makes it non-RUP
        self.assertRejected(2, f, "d 1 2 0\nd 1 -2 0\n1 0\n0\n")
        # the formula is satisfiable without its last clause
        self.assertRejected(2, f[:3], "1 0\n0\n")
        self.assertRejected(2, f[:3], "1 0\n2 0\n0\n")
        # malformed lines
        self.assertRejected(2, f, "1\n0\n")
        self.assertRejected(2, f, "1 x 0\n0\n")
        # formula with an empty clause: "0" is RUP immediately
        self.assertAccepted(1, [[1], []], "0\n")
        # complementary units
        self.assertAccepted(1, [[1], [-1]], "0\n")
        # lines after the empty clause are ignored
        self.assertAccepted(1, [[1], [-1]], "0\n5 0\n")
        # tautological and duplicate-literal lemmas are fine
        self.assertAccepted(2, f, "1 -1 0\n1 1 0\n0\n")

    def test_rup_lemmas(self):
        f = [[1, 2, 3], [-1, 4], [-2, 4], [-3, 4]]
        # "1 2 0" is not implied (1=2=0, 3=4=1 satisfies f): rejected
        ok, msg = drat_check.check_proof(4, f, "1 2 0\n0\n")
        self.assertFalse(ok)
        self.assertIn('line 1 is not RUP', msg)
        # "4 0" is RUP: -4 gives -1 -2 -3, falsifying (1 v 2 v 3).  The
        # proof still fails, at the empty clause (f is satisfiable).
        ok, msg = drat_check.check_proof(4, f, "4 0\n0\n")
        self.assertFalse(ok)
        self.assertIn('line 2 is not RUP', msg)
        self.assertAccepted(4, f + [[-4]], "4 0\n0\n")

    def test_implied_but_not_rup_is_rejected(self):
        # Unsatisfiable, so the empty clause is implied, but unit
        # propagation alone finds no conflict: the empty clause is not RUP
        # without the intermediate lemma.
        f = [[1, 2], [1, -2], [-1, 3], [-1, -3]]
        self.assertRejected(3, f, "0\n")
        self.assertAccepted(3, f, "1 0\n0\n")
        # Every clause is implied by an unsatisfiable formula, e.g. "4 0"
        # with a variable that does not occur; it is not RUP.
        ok, msg = drat_check.check_proof(3, f, "4 0\n1 0\n0\n")
        self.assertFalse(ok)
        self.assertIn('line 1 is not RUP', msg)

    def test_never_accepts_a_proof_for_a_satisfiable_formula(self):
        """Soundness: whatever the proof, a satisfiable formula must not
        be 'refuted'.  Proofs are built from the solver's learned clauses
        on the formula, random clauses and the empty clause."""
        rng = make_rng('sound')
        tried = 0
        while tried < 400:
            n = rng.randint(2, 10)
            clauses = random_kcnf(rng, n, int(n * rng.uniform(2, 4.2)),
                                  min(3, n))
            if brute_force(n, clauses) is None:
                continue
            tried += 1
            sat, model, proof = solve_in_process(to_dimacs(n, clauses))
            self.assertTrue(sat)
            lines = [l for l in proof.split('\n') if l]
            for _ in range(rng.randint(0, 6)):
                k = rng.randint(1, 3)
                lem = [rng.choice([1, -1]) * rng.randint(1, n)
                       for _ in range(k)]
                lines.insert(rng.randint(0, len(lines)),
                             ' '.join(map(str, lem)) + ' 0')
            lines.append('0')
            text = '\n'.join(lines) + '\n'
            self.assertRejected(n, clauses, text)

    def test_matches_naive_checker_on_mutated_proofs(self):
        """drat_check.py against the naive RUP checker in common.py.

        Without deletions both must give exactly the same verdict at the
        same lemma.  With deletions drat_check keeps top-level units whose
        reason was deleted (as drat-trim does), so it may accept more than
        the naive checker that honours deletions, but never more than the
        naive checker that ignores them."""
        rng = make_rng('mutate')
        checked = {'accept': 0, 'reject': 0}
        formulas = 0
        while formulas < 150:
            n = rng.randint(3, 11)
            clauses = random_kcnf(rng, n, int(n * rng.uniform(4.5, 7)),
                                  3)
            sat, _, proof = solve_in_process(to_dimacs(n, clauses))
            if sat:
                continue
            formulas += 1
            lines = [l for l in proof.split('\n') if l]
            for _ in range(8):
                mutated = mutate(rng, lines, n, clauses)
                text = '\n'.join(mutated) + '\n'
                fast_ok, fast_msg = drat_check.check_proof(n, clauses, text)
                has_del = any(l.startswith('d') for l in mutated)
                strict_ok, _ = naive_rup_check(n, clauses, text, True)
                loose_ok, _ = naive_rup_check(n, clauses, text, False)
                if not has_del:
                    self.assertEqual(fast_ok, strict_ok, (clauses, text))
                    self.assertEqual(fast_ok, loose_ok, (clauses, text))
                else:
                    if strict_ok:
                        self.assertTrue(fast_ok, (clauses, text, fast_msg))
                    if fast_ok:
                        self.assertTrue(loose_ok, (clauses, text))
                checked['accept' if fast_ok else 'reject'] += 1
        self.assertGreater(checked['accept'], 100, checked)
        self.assertGreater(checked['reject'], 100, checked)


def mutate(rng, lines, n, clauses):
    """One random change to a proof (a list of lines)."""
    out = list(lines)
    kind = rng.randrange(8)
    lemma_idx = [i for i, l in enumerate(out) if not l.startswith('d')]
    if kind == 0 and len(lemma_idx) > 1:          # drop a lemma
        del out[rng.choice(lemma_idx[:-1])]
    elif kind == 1 and lemma_idx:                 # flip a literal
        i = rng.choice(lemma_idx)
        lits = out[i].split()[:-1]
        if lits:
            j = rng.randrange(len(lits))
            lits[j] = str(-int(lits[j]))
            out[i] = ' '.join(lits + ['0'])
    elif kind == 2 and lemma_idx:                 # drop a literal
        i = rng.choice(lemma_idx)
        lits = out[i].split()[:-1]
        if lits:
            del lits[rng.randrange(len(lits))]
            out[i] = ' '.join(lits + ['0'])
    elif kind == 3:                               # insert a random lemma
        lem = [rng.choice([1, -1]) * rng.randint(1, n)
               for _ in range(rng.randint(1, 3))]
        out.insert(rng.randint(0, len(out)), ' '.join(map(str, lem)) + ' 0')
    elif kind == 4:                               # delete an original clause
        c = rng.choice(clauses)
        out.insert(rng.randint(0, len(out)),
                   'd ' + ' '.join(map(str, c)) + ' 0')
    elif kind == 5 and len(lemma_idx) > 2:        # swap two lemmas
        i, j = rng.sample(lemma_idx, 2)
        out[i], out[j] = out[j], out[i]
    elif kind == 6:                               # drop the final 0
        if out and out[-1] == '0':
            out.pop()
    else:                                         # delete a learned lemma
        if lemma_idx:
            i = rng.choice(lemma_idx)
            if out[i] != '0':
                out.insert(rng.randint(i + 1, len(out)), 'd ' + out[i])
    return out


if __name__ == '__main__':
    unittest.main()
