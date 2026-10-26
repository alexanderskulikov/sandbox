#!/usr/bin/env python3
"""A CDCL SAT solver in pure Python (standard library only).

Usage:
    python3 solver.py FORMULA.cnf [--proof PROOF.drat] [-v]

Output follows the SAT Competition conventions:
    s SATISFIABLE   + "v ..." lines ending with 0   (exit code 10)
    s UNSATISFIABLE                                 (exit code 20)

Algorithm: conflict-driven clause learning with
  * two watched literals per clause,
  * first-UIP learning with recursive clause minimisation and
    non-chronological backjumping,
  * VSIDS variable activities (binary heap with lazy deletion),
  * Luby restarts,
  * phase saving,
  * LBD-based deletion of learned clauses.

With --proof every learned clause is written to a DRAT file in the order it
was learned, deleted learned clauses are written as "d" lines, and an
unsatisfiable run ends with the empty clause "0".

Internal literal encoding: variable v (1-based) has the positive literal 2*v
and the negative literal 2*v+1, so negation is "lit ^ 1" and the variable
is "lit >> 1".  val[lit] is 1 (true), -1 (false) or 0 (unassigned).
"""

import sys
import heapq


class ParseError(Exception):
    pass


def parse_dimacs(text):
    """Parse DIMACS CNF text.  Returns (num_vars, clauses).

    Clauses are lists of non-zero ints.  The parser is lenient: comment
    lines ("c ...") anywhere, clauses spanning several lines, several
    clauses on one line, and a SATLIB-style "%" end marker are accepted.
    The number of variables is the maximum of the header value and the
    largest variable that occurs.  A final clause without its terminating
    0 is accepted as a clause.
    """
    num_vars = 0
    header_seen = False
    clauses = []
    cur = []
    for line in text.splitlines():
        s = line.strip()
        if not s or s[0] == 'c':
            continue
        if s[0] == '%':
            break
        if s[0] == 'p':
            parts = s.split()
            if header_seen or len(parts) < 4 or parts[1] != 'cnf':
                raise ParseError("bad header line: %r" % line)
            try:
                num_vars = int(parts[2])
                int(parts[3])
            except ValueError:
                raise ParseError("bad header line: %r" % line)
            if num_vars < 0:
                raise ParseError("bad header line: %r" % line)
            header_seen = True
            continue
        for tok in s.split():
            try:
                x = int(tok)
            except ValueError:
                raise ParseError("bad token %r" % tok)
            if x == 0:
                clauses.append(cur)
                cur = []
            else:
                cur.append(x)
                ax = -x if x < 0 else x
                if ax > num_vars:
                    num_vars = ax
    if cur:
        clauses.append(cur)
    return num_vars, clauses


def luby(i):
    """i-th element (0-based) of the Luby sequence 1,1,2,1,1,2,4,..."""
    size, seq = 1, 0
    while size < i + 1:
        seq += 1
        size = 2 * size + 1
    while size - 1 != i:
        size = (size - 1) >> 1
        seq -= 1
        i %= size
    return 1 << seq


class Solver:
    def __init__(self, num_vars, clauses, proof=None):
        n = num_vars
        self.n = n
        self.val = [0] * (2 * n + 2)
        self.level = [0] * (n + 1)
        self.reason = [None] * (n + 1)
        self.phase = [1] * (n + 1)          # 1: try the negative literal first
        self.activity = [0.0] * (n + 1)
        self.var_inc = 1.0
        self.var_decay = 0.95
        self.seen = [0] * (n + 1)
        self.watches = [[] for _ in range(2 * n + 2)]
        self.trail = []
        self.trail_lim = []
        self.qhead = 0
        self.heap = [(0.0, v) for v in range(1, n + 1)]
        heapq.heapify(self.heap)
        self.learnts = []                    # learned clauses (lists)
        self.lbd = {}                        # id(clause) -> LBD
        self.proof = proof
        self.lit_str = ['0', '0'] + [str(x) for v in range(1, n + 1)
                                     for x in (v, -v)]
        self.ok = True
        # statistics
        self.conflicts = 0
        self.decisions = 0
        self.propagations = 0
        self.restarts = 0
        self.reductions = 0

        units = []
        for cl in clauses:
            lits = set()
            taut = False
            for x in cl:
                lit = 2 * x if x > 0 else -2 * x + 1
                if lit ^ 1 in lits:
                    taut = True
                    break
                lits.add(lit)
            if taut:
                continue
            if not lits:
                self.ok = False             # empty clause in the input
                continue
            lits = list(lits)
            if len(lits) == 1:
                units.append(lits[0])
            else:
                self.watches[lits[0]].append(lits)
                self.watches[lits[1]].append(lits)
        if self.ok:
            for lit in units:
                v = self.val[lit]
                if v == -1:
                    self.ok = False
                    break
                if v == 0:
                    self.assign(lit, None)

    # ------------------------------------------------------------------
    def write_proof(self, lits, delete=False):
        if self.proof is None:
            return
        ls = self.lit_str
        line = " ".join([ls[l] for l in lits])
        if delete:
            self.proof.write("d " + line + " 0\n")
        elif line:
            self.proof.write(line + " 0\n")
        else:
            self.proof.write("0\n")

    def assign(self, lit, reason):
        self.val[lit] = 1
        self.val[lit ^ 1] = -1
        v = lit >> 1
        self.level[v] = len(self.trail_lim)
        self.reason[v] = reason
        self.trail.append(lit)

    # ------------------------------------------------------------------
    def propagate(self):
        """Unit propagation with two watched literals.

        The watched literals of a clause are c[0] and c[1]; the clause is in
        watches[c[0]] and watches[c[1]].  watches[l] is visited when l
        becomes false.  A clause that becomes unit implies c[0].
        Returns a conflicting clause or None.
        """
        val = self.val
        watches = self.watches
        trail = self.trail
        level = self.level
        reason = self.reason
        lvl = len(self.trail_lim)
        qhead = self.qhead
        start = qhead
        confl = None
        while qhead < len(trail):
            fl = trail[qhead] ^ 1           # literal that has become false
            qhead += 1
            ws = watches[fl]
            i = j = 0
            n = len(ws)
            while i < n:
                c = ws[i]
                i += 1
                c0 = c[0]
                if c0 == fl:
                    c0 = c[1]
                    c[0] = c0
                    c[1] = fl
                if val[c0] == 1:
                    ws[j] = c
                    j += 1
                    continue
                for k in range(2, len(c)):
                    lk = c[k]
                    if val[lk] != -1:
                        c[1] = lk
                        c[k] = fl
                        watches[lk].append(c)
                        break
                else:
                    ws[j] = c
                    j += 1
                    if val[c0] == -1:
                        confl = c
                        break
                    val[c0] = 1
                    val[c0 ^ 1] = -1
                    v = c0 >> 1
                    level[v] = lvl
                    reason[v] = c
                    trail.append(c0)
            del ws[j:i]
            if confl is not None:
                break
        self.propagations += qhead - start
        self.qhead = len(trail) if confl is not None else qhead
        return confl

    # ------------------------------------------------------------------
    def rescale(self):
        act = self.activity
        for v in range(1, self.n + 1):
            act[v] *= 1e-100
        self.var_inc *= 1e-100
        self.rebuild_heap()

    def rebuild_heap(self):
        act = self.activity
        val = self.val
        self.heap = [(-act[v], v) for v in range(1, self.n + 1)
                     if val[2 * v] == 0]
        heapq.heapify(self.heap)

    def analyze(self, confl):
        """First-UIP conflict analysis with recursive minimisation.

        Returns (learnt clause, backjump level, LBD).  learnt[0] is the
        asserting literal and learnt[1] has the highest level among the rest.
        """
        seen = self.seen
        level = self.level
        reason = self.reason
        trail = self.trail
        act = self.activity
        cur = len(self.trail_lim)
        learnt = [0]
        path = 0
        idx = len(trail) - 1
        c = confl
        first = True
        while True:
            inc = self.var_inc
            for q in (c if first else c[1:]):
                v = q >> 1
                if not seen[v]:
                    lv = level[v]
                    if lv > 0:
                        seen[v] = 1
                        a = act[v] + inc
                        act[v] = a
                        if a > 1e100:
                            self.rescale()
                            inc = self.var_inc
                        if lv >= cur:
                            path += 1
                        else:
                            learnt.append(q)
            first = False
            while not seen[trail[idx] >> 1]:
                idx -= 1
            p = trail[idx]
            idx -= 1
            v = p >> 1
            seen[v] = 0
            path -= 1
            if path == 0:
                break
            c = reason[v]
        learnt[0] = p ^ 1

        # Recursive minimisation (MiniSat style): drop a literal if it is
        # implied by the other literals of the clause via reason clauses.
        abstract = 0
        for q in learnt[1:]:
            abstract |= 1 << (level[q >> 1] & 31)
        to_clear = learnt[1:]
        out = [learnt[0]]
        for q in learnt[1:]:
            if reason[q >> 1] is None or not self.redundant(q, abstract,
                                                           to_clear):
                out.append(q)
        for q in to_clear:
            seen[q >> 1] = 0

        if len(out) == 1:
            bt = 0
        else:
            mi = 1
            ml = level[out[1] >> 1]
            for i in range(2, len(out)):
                lv = level[out[i] >> 1]
                if lv > ml:
                    ml = lv
                    mi = i
            out[1], out[mi] = out[mi], out[1]
            bt = ml
        lbd = len({level[q >> 1] for q in out})
        return out, bt, lbd

    def redundant(self, p, abstract, to_clear):
        seen = self.seen
        level = self.level
        reason = self.reason
        stack = [p]
        top = len(to_clear)
        while stack:
            q = stack.pop()
            c = reason[q >> 1]
            for i in range(1, len(c)):
                l = c[i]
                v = l >> 1
                if not seen[v] and level[v] > 0:
                    if reason[v] is not None and \
                            (abstract >> (level[v] & 31)) & 1:
                        seen[v] = 1
                        stack.append(l)
                        to_clear.append(l)
                    else:
                        for l2 in to_clear[top:]:
                            seen[l2 >> 1] = 0
                        del to_clear[top:]
                        return False
        return True

    # ------------------------------------------------------------------
    def backtrack(self, lvl):
        if len(self.trail_lim) <= lvl:
            return
        trail = self.trail
        val = self.val
        phase = self.phase
        act = self.activity
        heap = self.heap
        push = heapq.heappush
        lim = self.trail_lim[lvl]
        for i in range(len(trail) - 1, lim - 1, -1):
            lit = trail[i]
            v = lit >> 1
            val[lit] = 0
            val[lit ^ 1] = 0
            phase[v] = lit & 1
            push(heap, (-act[v], v))
        del trail[lim:]
        del self.trail_lim[lvl:]
        self.qhead = lim
        if len(heap) > 4 * self.n + 1000:
            self.rebuild_heap()

    def pick_branch(self):
        heap = self.heap
        val = self.val
        act = self.activity
        pop = heapq.heappop
        while heap:
            a, v = pop(heap)
            if val[2 * v] == 0 and -a == act[v]:
                return v
        return 0

    def locked(self, c):
        c0 = c[0]
        return self.val[c0] == 1 and self.reason[c0 >> 1] is c

    def reduce_db(self):
        """Delete about half of the learned clauses with LBD > 2,
        preferring to delete those with high LBD and older ones."""
        self.reductions += 1
        lbd = self.lbd
        learnts = self.learnts
        n = len(learnts)
        order = sorted(range(n), key=lambda i: (lbd[id(learnts[i])], -i))
        dead = set()
        target = n // 2
        for i in reversed(order):
            if len(dead) >= target:
                break
            c = learnts[i]
            if lbd[id(c)] <= 2 or self.locked(c):
                continue
            dead.add(id(c))
        if not dead:
            return
        watches = self.watches
        touched = set()
        keep = []
        for c in learnts:
            if id(c) in dead:
                touched.add(c[0])
                touched.add(c[1])
                self.write_proof(c, delete=True)
                del lbd[id(c)]
            else:
                keep.append(c)
        for l in touched:
            watches[l] = [c for c in watches[l] if id(c) not in dead]
        self.learnts = keep

    # ------------------------------------------------------------------
    def solve(self):
        if not self.ok or self.propagate() is not None:
            self.ok = False
            self.write_proof([])
            return False
        restart_unit = 100
        restart_idx = 0
        restart_limit = luby(0) * restart_unit
        conflicts_since_restart = 0
        next_reduce = 2000
        reduce_inc = 300
        decay = self.var_decay
        while True:
            confl = self.propagate()
            if confl is not None:
                self.conflicts += 1
                conflicts_since_restart += 1
                if not self.trail_lim:
                    self.ok = False
                    self.write_proof([])
                    return False
                learnt, bt, lbd = self.analyze(confl)
                self.backtrack(bt)
                self.write_proof(learnt)
                if len(learnt) == 1:
                    self.assign(learnt[0], None)
                else:
                    self.watches[learnt[0]].append(learnt)
                    self.watches[learnt[1]].append(learnt)
                    self.learnts.append(learnt)
                    self.lbd[id(learnt)] = lbd
                    self.assign(learnt[0], learnt)
                self.var_inc /= decay
                if self.var_inc > 1e100:
                    self.rescale()
            else:
                if conflicts_since_restart >= restart_limit:
                    self.restarts += 1
                    restart_idx += 1
                    restart_limit = luby(restart_idx) * restart_unit
                    conflicts_since_restart = 0
                    self.backtrack(0)
                if self.conflicts >= next_reduce:
                    next_reduce = self.conflicts + 2000 + reduce_inc * \
                        self.reductions
                    self.reduce_db()
                v = self.pick_branch()
                if v == 0:
                    return True
                self.decisions += 1
                self.trail_lim.append(len(self.trail))
                self.assign(2 * v + self.phase[v], None)

    def model(self):
        """Values of variables 1..n as DIMACS literals."""
        val = self.val
        return [v if val[2 * v] == 1 else -v for v in range(1, self.n + 1)]


def format_model(lits, per_line=20):
    out = []
    for i in range(0, len(lits), per_line):
        out.append("v " + " ".join(str(x) for x in lits[i:i + per_line]))
    out.append("v 0")
    return "\n".join(out)


def main(argv):
    args = argv[1:]
    proof_path = None
    verbose = False
    files = []
    i = 0
    while i < len(args):
        a = args[i]
        if a == '--proof':
            if i + 1 >= len(args):
                sys.stderr.write("--proof needs a file name\n")
                return 1
            proof_path = args[i + 1]
            i += 2
            continue
        if a.startswith('--proof='):
            proof_path = a[len('--proof='):]
        elif a in ('-v', '--verbose'):
            verbose = True
        else:
            files.append(a)
        i += 1
    if len(files) != 1:
        sys.stderr.write(
            "usage: solver.py FORMULA.cnf [--proof PROOF.drat] [-v]\n")
        return 1
    try:
        with open(files[0], 'rb') as f:
            text = f.read().decode('utf-8', errors='replace')
        num_vars, clauses = parse_dimacs(text)
    except (OSError, ParseError) as e:
        sys.stdout.write("c error: %s\ns UNKNOWN\n" % e)
        return 1

    proof = None
    if proof_path is not None:
        proof = open(proof_path, 'w', buffering=1 << 20)
    try:
        solver = Solver(num_vars, clauses, proof)
        sat = solver.solve()
    finally:
        if proof is not None:
            proof.close()
    if verbose:
        sys.stdout.write(
            "c vars %d clauses %d conflicts %d decisions %d "
            "propagations %d restarts %d reductions %d\n"
            % (num_vars, len(clauses), solver.conflicts, solver.decisions,
               solver.propagations, solver.restarts, solver.reductions))
    if sat:
        sys.stdout.write("s SATISFIABLE\n" + format_model(solver.model())
                         + "\n")
        sys.stdout.flush()
        return 10
    sys.stdout.write("s UNSATISFIABLE\n")
    sys.stdout.flush()
    return 20


if __name__ == '__main__':
    sys.exit(main(sys.argv))
