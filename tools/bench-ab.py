#!/usr/bin/env python3
"""Compare criterion benchmarks between two revisions of this repository.

    python3 tools/bench-ab.py --base master --head HEAD -p kovan-map --bench hopscotch_ops
        [--bench perf ...] [--filter REGEX] [--rounds 5] [--warm-up 1] [--measure 3]
        [--features recycle] [--head-features recycle] [--cpus 0-15]

Each revision is checked out into a temporary worktree and its bench executables are built
once. The rounds then alternate the two builds (base then head, head then base, ...), so drift
on a shared machine lands on both sides. Each row reports the median of the per-round
criterion medians for each side, the change, and the spread between rounds, the noise a
change has to clear. A row is called slower only when every head round is slower than every
base round, the same for faster; anything else is a tie. Prints a Markdown table.

The base and the head may be the same revision with different features (`--features` for
both, `--head-features` for the head only), to measure what a feature costs.
"""

import argparse
import json
import os
import shutil
import statistics
import subprocess
import sys
import tempfile


def sh(cmd, **kw):
    return subprocess.run(cmd, check=True, text=True, **kw)


def build(repo, rev, work, crate, benches, features):
    tree = os.path.join(work, 'tree-' + rev.replace('/', '_'))
    target = os.path.join(work, 'target-' + rev.replace('/', '_') + ('-' + features if features else ''))
    if not os.path.isdir(tree):
        sh(['git', '-C', repo, 'worktree', 'add', '--detach', '--quiet', tree, rev])
    cmd = ['cargo', 'bench', '-p', crate, '--no-run', '--message-format=json']
    for b in benches:
        cmd += ['--bench', b]
    if features:
        cmd += ['--features', features]
    out = sh(cmd, cwd=tree, capture_output=True, env={**os.environ, 'CARGO_TARGET_DIR': target}).stdout
    exes = {}
    for line in out.splitlines():
        msg = json.loads(line)
        if msg.get('reason') == 'compiler-artifact' and 'bench' in msg['target']['kind'] and msg.get('executable'):
            exes[msg['target']['name']] = msg['executable']
    missing = [b for b in benches if b not in exes]
    if missing:
        sys.exit(f'no bench executable for {missing} at {rev}')
    return tree, exes


def run_round(exes, home, args):
    for name, exe in exes.items():
        cmd = [exe, '--bench', '--noplot', '--warm-up-time', str(args.warm_up),
               '--measurement-time', str(args.measure)]
        if args.filter:
            cmd.append(args.filter)
        if args.cpus:
            cmd = ['taskset', '-c', args.cpus] + cmd
        sh(cmd, env={**os.environ, 'CRITERION_HOME': home}, stdout=subprocess.DEVNULL,
           stderr=subprocess.DEVNULL)


def collect(home):
    found = {}
    for root, _, files in os.walk(home):
        if os.path.basename(root) == 'new' and 'estimates.json' in files and 'benchmark.json' in files:
            ident = json.load(open(os.path.join(root, 'benchmark.json')))['full_id']
            found[ident] = json.load(open(os.path.join(root, 'estimates.json')))['median']['point_estimate']
    return found


def fmt(ns):
    for unit, scale in (('s', 1e9), ('ms', 1e6), ('us', 1e3)):
        if ns >= scale:
            return f'{ns / scale:.3f} {unit}'
    return f'{ns:.2f} ns'


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    ap.add_argument('--base', required=True)
    ap.add_argument('--head', required=True)
    ap.add_argument('-p', '--crate', required=True)
    ap.add_argument('--bench', action='append', required=True)
    ap.add_argument('--filter')
    ap.add_argument('--rounds', type=int, default=5)
    ap.add_argument('--warm-up', type=float, default=1)
    ap.add_argument('--measure', type=float, default=3)
    ap.add_argument('--features', default='')
    ap.add_argument('--head-features', default=None)
    ap.add_argument('--cpus')
    ap.add_argument('--keep', action='store_true', help='keep the worktrees and builds')
    args = ap.parse_args()

    repo = sh(['git', 'rev-parse', '--show-toplevel'], capture_output=True).stdout.strip()
    work = tempfile.mkdtemp(prefix='bench-ab-', dir=os.environ.get('BENCH_AB_DIR'))
    head_features = args.features if args.head_features is None else args.head_features
    sides = {'base': (args.base, args.features), 'head': (args.head, head_features)}
    trees = []
    try:
        exes = {}
        for side, (rev, feats) in sides.items():
            tree, exes[side] = build(repo, rev, work, args.crate, args.bench, feats)
            trees.append(tree)
        rounds = {'base': [], 'head': []}
        for r in range(args.rounds):
            order = ('base', 'head') if r % 2 == 0 else ('head', 'base')
            for side in order:
                home = os.path.join(work, f'crit-{side}-{r}')
                run_round(exes[side], home, args)
                rounds[side].append(collect(home))
        ids = sorted(set().union(*rounds['base']) & set().union(*rounds['head']))
        print(f"base `{args.base}`{' +' + args.features if args.features else ''}, "
              f"head `{args.head}`{' +' + head_features if head_features else ''}; "
              f"{args.rounds} interleaved rounds, criterion --warm-up-time {args.warm_up} "
              f"--measurement-time {args.measure}{', cpus ' + args.cpus if args.cpus else ''}\n")
        print('| bench | base | head | change | spread between rounds | verdict |')
        print('|---|---|---|---|---|---|')
        for i in ids:
            b = [x[i] for x in rounds['base'] if i in x]
            h = [x[i] for x in rounds['head'] if i in x]
            mb, mh = statistics.median(b), statistics.median(h)
            spread = max((max(b) - min(b)) / mb, (max(h) - min(h)) / mh) * 100
            verdict = 'slower' if min(h) > max(b) else 'faster' if max(h) < min(b) else 'tie'
            print(f'| {i} | {fmt(mb)} | {fmt(mh)} | {(mh / mb - 1) * 100:+.2f}% | {spread:.1f}% | {verdict} |')
    finally:
        if not args.keep:
            for tree in trees:
                subprocess.run(['git', '-C', repo, 'worktree', 'remove', '--force', tree],
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            shutil.rmtree(work, ignore_errors=True)


if __name__ == '__main__':
    main()
