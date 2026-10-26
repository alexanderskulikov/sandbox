"""Helpers shared by the tests.

Everything that decides the "true" answer here (brute force, 2-SAT by
strongly connected components, Horn-SAT by forward chaining, XOR-SAT by
Gaussian elimination, a naive RUP checker) is written independently of
solver.py, check.py and drat_check.py.
"""

import io
import os
import random
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BENCH = os.path.join(ROOT, 'bench')
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

import check        # noqa: E402
import drat_check   # noqa: E402
import solver       # noqa: E402

SOLVER = os.path.join(ROOT, 'solver.py')
SEED = int(os.environ.get('TEST_SEED', '12345'))


def to_dimacs(num_vars, clauses, comment=None):
    lines = []
    if comment:
        lines.append('c ' + comment)
    lines.append('p cnf %d %d' % (num_vars, len(clauses)))
    for c in clauses:
        lines.append(' '.join(map(str, c)) + ' 0')
    return '\n'.join(lines) + '\n'


# ---------------------------------------------------------------------------
# Running the solver

def solve_in_process(text):
    """Parse and solve DIMACS text with the solver's own code, without a
    subprocess.  Returns (sat, model_literals_or_None, proof_text)."""
    n, clauses = solver.parse_dimacs(text)
    proof = io.StringIO()
    s = solver.Solver(n, clauses, proof)
    sat = s.solve()
    return sat, (s.model() if sat else None), proof.getvalue()


def run_cli(cnf_path, proof_path=None, timeout=300):
    """Run solver.py as a separate process.  Returns (exit code, stdout)."""
    cmd = [sys.executable, SOLVER, cnf_path]
    if proof_path:
        cmd += ['--proof', proof_path]
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    return p.returncode, p.stdout


class TempDir:
    def __enter__(self):
        self.tmp = tempfile.TemporaryDirectory()
        return self.tmp.name

    def __exit__(self, *exc):
        self.tmp.cleanup()


def verify_answer(text, sat, model, proof_text):
    """Check a solver answer with the independent checkers.  Returns None if
    verified, else a description of the problem."""
    n, clauses, _ = check.read_cnf_text(text)
    if sat:
        return check.check_model(n, clauses, model)
    ok, msg = drat_check.check_proof(n, clauses, proof_text)
    return None if ok else msg


# ---------------------------------------------------------------------------
# Ground truth

def brute_force(num_vars, clauses):
    """Return a satisfying assignment as a list of literals, or None.
    Plain enumeration of all 2^n assignments using bit masks."""
    masks = []
    for c in clauses:
        pos = neg = 0
        for lit in c:
            if lit > 0:
                pos |= 1 << (lit - 1)
            else:
                neg |= 1 << (-lit - 1)
        masks.append((pos, neg))
    full = (1 << num_vars) - 1
    for a in range(1 << num_vars):
        na = full ^ a
        for pos, neg in masks:
            if not (a & pos or na & neg):
                break
        else:
            return [v if a >> (v - 1) & 1 else -v
                    for v in range(1, num_vars + 1)]
    return None


def two_sat(num_vars, clauses):
    """Satisfiability of a 2-CNF (clauses of length 1 or 2) by Tarjan's
    strongly connected components on the implication graph.  Returns
    True/False."""
    def node(lit):
        return 2 * (abs(lit) - 1) + (lit < 0)
    size = 2 * num_vars
    graph = [[] for _ in range(size)]
    for c in clauses:
        if len(c) == 1:
            a = b = c[0]
        else:
            a, b = c
        graph[node(-a)].append(node(b))
        graph[node(-b)].append(node(a))
    index = [None] * size
    low = [0] * size
    comp = [None] * size
    on_stack = [False] * size
    stack = []
    counter = 0
    ncomp = 0
    for root in range(size):
        if index[root] is not None:
            continue
        work = [(root, 0)]
        while work:
            v, i = work.pop()
            if i == 0:
                index[v] = low[v] = counter
                counter += 1
                stack.append(v)
                on_stack[v] = True
            recurse = False
            while i < len(graph[v]):
                w = graph[v][i]
                i += 1
                if index[w] is None:
                    work.append((v, i))
                    work.append((w, 0))
                    recurse = True
                    break
                if on_stack[w]:
                    low[v] = min(low[v], index[w])
            if recurse:
                continue
            if low[v] == index[v]:
                while True:
                    w = stack.pop()
                    on_stack[w] = False
                    comp[w] = ncomp
                    if w == v:
                        break
                ncomp += 1
            if work:
                u = work[-1][0]
                low[u] = min(low[u], low[v])
    return all(comp[2 * v] != comp[2 * v + 1] for v in range(num_vars))


def horn_sat(num_vars, clauses):
    """Satisfiability of a Horn formula (at most one positive literal per
    clause) by forward chaining from the all-false assignment."""
    true = set()
    changed = True
    while changed:
        changed = False
        for c in clauses:
            positives = [l for l in c if l > 0]
            if any(l in true for l in positives):
                continue
            if all(-l in true for l in c if l < 0):
                if not positives:
                    return False
                true.add(positives[0])
                changed = True
    return True


def xor_sat(num_vars, equations):
    """Solvability of a system of XOR equations over GF(2) by Gaussian
    elimination.  equations: list of (variables, parity)."""
    rows = []
    for vs, parity in equations:
        mask = 0
        for v in vs:
            mask ^= 1 << v
        rows.append(mask | (parity << (num_vars + 1)))
    pivots = {}
    rhs_bit = 1 << (num_vars + 1)
    for r in rows:
        for bit in range(num_vars + 1):
            if r >> bit & 1 and bit in pivots:
                r ^= pivots[bit]
        low = r & (rhs_bit - 1)
        if low == 0:
            if r & rhs_bit:
                return False
            continue
        b = low.bit_length() - 1
        for k in list(pivots):
            if pivots[k] >> b & 1:
                pivots[k] ^= r
        pivots[b] = r
    return True


# ---------------------------------------------------------------------------
# A deliberately naive RUP checker, used to test drat_check.py.

def naive_rup_check(num_vars, clauses, proof_text, honour_deletions=True):
    """Return (accepted, index of the first failing lemma or None).

    For every lemma, unit propagation is recomputed from scratch by
    repeatedly scanning all clauses.  Deleting a clause removes one copy
    with the same set of literals."""
    db = [list(c) for c in clauses]
    lemma_no = 0
    for raw in proof_text.split('\n'):
        words = raw.split()
        if not words or words[0].startswith('c'):
            continue
        deletion = words[0] == 'd'
        if deletion:
            words = words[1:]
        lits = [int(w) for w in words[:-1]]
        if deletion:
            if honour_deletions:
                key = set(lits)
                for i in range(len(db) - 1, -1, -1):
                    if set(db[i]) == key:
                        del db[i]
                        break
            continue
        lemma_no += 1
        true = set(-l for l in lits)
        conflict = any(-l in true for l in true)
        while not conflict:
            progress = False
            for c in db:
                if any(l in true for l in c):
                    continue
                open_lits = [l for l in c if -l not in true]
                if not open_lits:
                    conflict = True
                    break
                if len(set(open_lits)) == 1:
                    true.add(open_lits[0])
                    progress = True
            if not progress:
                break
        if not conflict:
            return False, lemma_no
        if not lits:
            return True, None
        db.append(lits)
    return False, None


# ---------------------------------------------------------------------------
# Formula generators

def random_cnf(rng, num_vars, num_clauses, min_len=1, max_len=4,
               allow_junk=True):
    """Random clauses of mixed length; with allow_junk, occasionally
    duplicate literals and tautologies."""
    clauses = []
    for _ in range(num_clauses):
        k = rng.randint(min_len, max_len)
        c = []
        for _ in range(k):
            v = rng.randint(1, num_vars)
            c.append(v if rng.random() < 0.5 else -v)
        if allow_junk and rng.random() < 0.03 and c:
            c.append(c[0])                       # duplicate literal
        if allow_junk and rng.random() < 0.02 and c:
            c.append(-c[0])                      # tautology
        clauses.append(c)
    return clauses


def random_kcnf(rng, num_vars, num_clauses, k=3):
    """Uniform random k-CNF: k distinct variables per clause."""
    clauses = []
    for _ in range(num_clauses):
        vs = rng.sample(range(1, num_vars + 1), k)
        clauses.append([v if rng.random() < 0.5 else -v for v in vs])
    return clauses


def planted_kcnf(rng, num_vars, num_clauses, k=3):
    """Random k-CNF satisfied by a hidden assignment.  Returns
    (clauses, hidden assignment as a set of true literals)."""
    hidden = [v if rng.random() < 0.5 else -v
              for v in range(1, num_vars + 1)]
    truth = set(hidden)
    clauses = []
    while len(clauses) < num_clauses:
        vs = rng.sample(range(1, num_vars + 1), k)
        c = [v if rng.random() < 0.5 else -v for v in vs]
        if any(l in truth for l in c):
            clauses.append(c)
    return clauses, truth


def pigeonhole(pigeons, holes):
    """Pigeons into holes, at most one pigeon per hole.  Satisfiable iff
    pigeons <= holes."""
    def x(p, h):
        return p * holes + h + 1
    clauses = [[x(p, h) for h in range(holes)] for p in range(pigeons)]
    for h in range(holes):
        for p in range(pigeons):
            for q in range(p + 1, pigeons):
                clauses.append([-x(p, h), -x(q, h)])
    return pigeons * holes, clauses


def queens(n):
    """n non-attacking queens.  Satisfiable iff n not in (2, 3)."""
    def x(r, c):
        return r * n + c + 1
    clauses = [[x(r, c) for c in range(n)] for r in range(n)]
    cells = [(r, c) for r in range(n) for c in range(n)]
    for i, (r1, c1) in enumerate(cells):
        for r2, c2 in cells[i + 1:]:
            if r1 == r2 or c1 == c2 or abs(r1 - r2) == abs(c1 - c2):
                clauses.append([-x(r1, c1), -x(r2, c2)])
    return n * n, clauses


def coloring(num_nodes, edges, colors):
    def x(v, c):
        return v * colors + c + 1
    clauses = [[x(v, c) for c in range(colors)] for v in range(num_nodes)]
    for v in range(num_nodes):
        for c in range(colors):
            for d in range(c + 1, colors):
                clauses.append([-x(v, c), -x(v, d)])
    for u, v in edges:
        for c in range(colors):
            clauses.append([-x(u, c), -x(v, c)])
    return num_nodes * colors, clauses


def xor_clauses(vs, parity):
    """CNF for XOR(vs) == parity (vs are positive variable numbers)."""
    out = []
    k = len(vs)
    for bits in range(1 << k):
        # forbid the assignment where variable i has value bit i
        if bin(bits).count('1') % 2 != parity:
            out.append([-v if bits >> i & 1 else v
                        for i, v in enumerate(vs)])
    return out


def random_xor_system(rng, num_vars, num_eqs, width=3):
    eqs = []
    clauses = []
    for _ in range(num_eqs):
        vs = rng.sample(range(1, num_vars + 1), width)
        parity = rng.randint(0, 1)
        eqs.append((vs, parity))
        clauses.extend(xor_clauses(vs, parity))
    return eqs, clauses


def random_horn(rng, num_vars, num_clauses):
    clauses = []
    for _ in range(num_clauses):
        k = rng.randint(1, 3)
        vs = rng.sample(range(1, num_vars + 1), min(k, num_vars))
        c = [-v for v in vs]
        if rng.random() < 0.8:
            c[0] = -c[0]                         # one positive literal
        clauses.append(c)
    return clauses


def make_rng(*salt):
    return random.Random('%d-%s' % (SEED, '-'.join(map(str, salt))))
