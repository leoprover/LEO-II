#!/usr/bin/env python3
"""Run LEO-II over the TPTP THF problems and look for answers that contradict
the recorded status.

Usage: test/tptp_check.py --tptp ~/tmp/tptp/TPTP-v9.2.1 [--set unsound|all|theorems]
                         [--timeout 10] [--jobs 4] [--atp <eprover>] [--out FILE]

Every TPTP problem records what is known about it.  An answer that contradicts
that record is a bug, and the two directions are not equally interesting: a
proof of something known to have a countermodel is an unsoundness, which is the
thing this is here to catch.  `--set unsound` runs only the problems that can
witness one, which is the cheap net to run after every change; `--set all` runs
everything.

Exit status is 1 if any contradiction was found, so it can gate a commit."""
import argparse, csv, glob, os, re, signal, subprocess, sys, threading, time
from concurrent.futures import ThreadPoolExecutor

SZS = re.compile(r'SZS status (\w+)')
STATUS = re.compile(r'^% Status\s*:\s*(\w+)', re.M)

# what LEO-II may answer, and what it may never answer, for a given record
PROVED = {'Theorem', 'Unsatisfiable', 'ContradictoryAxioms'}
REFUTED = {'CounterSatisfiable', 'Satisfiable'}
LOCK = threading.Lock()


def expected(path):
    try:
        m = STATUS.search(open(path, encoding='utf-8', errors='replace').read(8192))
    except OSError:
        return None
    return m.group(1) if m else None


def contradiction(exp, got):
    if exp in PROVED and got in REFUTED:
        return 'claims a countermodel for a theorem'
    if exp in REFUTED and got in PROVED:
        return 'claims a proof of a non-theorem'
    return None


def run_one(leo, atp, problem, tptp, timeout, counter, writer, fh):
    env = dict(os.environ, TPTP=tptp)
    args = [leo] + (['--atp', 'e=' + atp] if atp else []) + ['-t', str(timeout), problem]
    t0 = time.time()
    try:
        p = subprocess.Popen(args, cwd=tptp, env=env, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, text=True, start_new_session=True)
        try:
            out = p.communicate(timeout=timeout + 15)[0]
        except subprocess.TimeoutExpired:
            try: os.killpg(os.getpgid(p.pid), signal.SIGKILL)
            except ProcessLookupError: pass
            p.wait(); out = 'SZS status Timeout'
    except OSError as ex:
        out = 'error %s' % ex
    m = SZS.search(out or '')
    got = m.group(1) if m else 'Unknown'
    exp = expected(problem)
    bad = contradiction(exp, got)
    row = (os.path.relpath(problem, tptp), exp or '?', got, round(time.time() - t0, 1),
           bad or '')
    with LOCK:
        writer.writerow(row); fh.flush()
        counter[0] += 1
        if bad:
            counter[2] += 1
            print('  !! %s: recorded %s, answered %s -- %s' % (row[0], exp, got, bad),
                  flush=True)
        elif counter[0] % 50 == 0:
            print('  %d/%d' % (counter[0], counter[1]), flush=True)
    return row


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--tptp', required=True)
    ap.add_argument('--leo', default=os.path.expanduser('~/GITHUBS/LEO-II/bin/leo'))
    ap.add_argument('--atp', default='')
    ap.add_argument('--set', default='unsound', choices=('unsound', 'theorems', 'all'))
    ap.add_argument('--timeout', type=int, default=10)
    ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--out', default='/tmp/tptp-check.csv')
    a = ap.parse_args()

    tptp = os.path.abspath(os.path.expanduser(a.tptp))
    problems = sorted(glob.glob(os.path.join(tptp, 'Problems', '*', '*^*.p')))
    if a.set == 'unsound':
        problems = [p for p in problems if expected(p) in REFUTED]
    elif a.set == 'theorems':
        problems = [p for p in problems if expected(p) in PROVED]
    if a.limit:
        problems = problems[:a.limit]

    print('%d problems, %ds each, %d at a time' % (len(problems), a.timeout, a.jobs))
    counter = [0, len(problems), 0]
    with open(a.out, 'w', newline='', encoding='utf-8') as fh:
        w = csv.writer(fh)
        w.writerow(['problem', 'recorded', 'answered', 'seconds', 'contradiction'])
        with ThreadPoolExecutor(max_workers=a.jobs) as ex:
            rows = list(ex.map(lambda p: run_one(a.leo, a.atp, p, tptp, a.timeout,
                                                 counter, w, fh), problems))

    agreed = sum(1 for r in rows if not r[4] and r[2] in PROVED | REFUTED)
    print('\n-- %d problems' % len(rows))
    print('   answered, agreeing with the record : %d' % agreed)
    print('   contradicting the record           : %d' % counter[2])
    if counter[2]:
        print('\nCONTRADICTIONS FOUND -- do not ship this build.')
        sys.exit(1)
    print('   no contradiction found')


main()
