#!/usr/bin/env python3
"""Verify the standalone 3.178 Lean review bundle with Python's standard library."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
TARGET = 'SmpMax.General.stableCount_lt_3178_pow'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_sources():
    index = json.loads((ROOT / 'source-index.json').read_text())
    for item in index['modules']:
        path = ROOT / item['path']
        if digest(path) != item['sha256']:
            raise RuntimeError('Source hash mismatch: ' + item['path'])
        # Axioms are also audited from the compiled declarations below.
        if re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s', path.read_text(), re.M):
            raise RuntimeError('Unexpected proof escape or declaration: ' + item['path'])
    manifest = ROOT / 'bundle-manifest.json'
    if manifest.exists():
        for item in json.loads(manifest.read_text())['files']:
            path = ROOT / item['path']
            if path.stat().st_size != item['bytes'] or digest(path) != item['sha256']:
                raise RuntimeError('Bundle hash mismatch: ' + item['path'])
    return index


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fetch', action='store_true', help='Download the pinned dependencies and Mathlib cache first')
    parser.add_argument('--kernel', choices=('none', 'final', 'all'), default='final',
                        help='Independent replay: final module (default) or all 45 target dependency modules')
    parser.add_argument('--sources-only', action='store_true', help='Check packaged hashes without invoking Lean')
    args = parser.parse_args()
    index = check_sources()
    print('Verified source identity for %d original Lean modules.' % len(index['modules']), flush=True)
    if args.sources_only:
        return
    output = ROOT / 'verification-local'
    output.mkdir(exist_ok=True)
    results = []
    total_start = time.monotonic()

    def run(name, command, cwd=ROOT / 'lean'):
        started = time.monotonic()
        log = output / (name + '.txt')
        with log.open('w') as stream:
            process = subprocess.run(command, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT)
        elapsed = time.monotonic() - started
        record = {'step': name, 'command': command, 'exit_code': process.returncode,
                  'elapsed_seconds': elapsed, 'log': log.name}
        results.append(record)
        (output / 'progress.json').write_text(json.dumps({'completed_steps': results}, indent=2) + '\n')
        print('%s: exit %d, %.3f s' % (name, process.returncode, elapsed), flush=True)
        if process.returncode:
            print(log.read_text()[-10000:], file=sys.stderr)
            raise RuntimeError('Verification failed: ' + name)
        return log.read_text()

    if args.fetch:
        run('fetch-cache', ['lake', 'exe', 'cache', 'get'])
    version = run('lean-version', ['lake', 'env', 'lean', '--version'])
    if '4.33.1' not in version:
        raise RuntimeError('Unexpected Lean version')
    run('build', ['lake', 'build', 'SmpMax'])
    dependency_manifest = json.loads((ROOT / 'lean/lake-manifest.json').read_text())
    dependency_revisions = []
    for package in dependency_manifest['packages']:
        path = ROOT / 'lean/.lake/packages' / package['name']
        actual = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
        if actual != package['rev']:
            raise RuntimeError('Unexpected dependency revision: ' + package['name'])
        dependency_revisions.append({'name': package['name'], 'rev': actual})
    theorem_text = run('theorem', ['lake', 'env', 'lean', 'Check3178.lean'])
    axiom_pattern = r"'([^']+)' depends on axioms: \[([^]]*)\]"
    theorem_axioms = re.findall(axiom_pattern, theorem_text)
    if len(theorem_axioms) != 1 or theorem_axioms[0][0] != TARGET:
        raise RuntimeError('Missing or duplicate target theorem audit')
    if set(re.split(r',\s*', theorem_axioms[0][1])) != ALLOWED:
        raise RuntimeError('Unexpected target theorem axioms')
    general_text = run('general-audit', ['lake', 'env', 'lean', 'checks/GeneralEntropy.lean'])
    audited = re.findall(axiom_pattern, general_text)
    expected = set(re.findall(r'^#print axioms ([\w.]+)',
                             (ROOT / 'lean/checks/GeneralEntropy.lean').read_text(), re.M))
    if len(audited) != 112 or len(expected) != 112 or {n for n, _ in audited} != expected:
        raise RuntimeError('Missing, duplicate, or unexpected general theorem audit')
    if any(not set(filter(None, re.split(r',\s*', a))) <= ALLOWED for _, a in audited):
        raise RuntimeError('Unexpected general theorem axiom')
    modules = []
    if args.kernel == 'final':
        modules = ['SmpMax.General.JointEntropyUpperBound']
    elif args.kernel == 'all':
        modules = index['target_dependency_order']
    for i, module in enumerate(modules):
        run('kernel-%02d-%s' % (i + 1, module.rsplit('.', 1)[-1]), ['lake', 'env', 'leanchecker', module])
    check_sources()
    report = {
        'success': True, 'target': TARGET, 'exact_base': '1589/500',
        'theorem_axioms': sorted(ALLOWED), 'general_audits': len(audited),
        'source_modules': len(index['modules']), 'kernel_replayed_modules': modules,
        'dependency_revisions': dependency_revisions, 'steps': results,
        'elapsed_seconds': time.monotonic() - total_start,
        'max_child_rss_bytes': resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss *
            (1 if sys.platform == 'darwin' else 1024),
    }
    (output / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print('PASS: complete unconditional stableCount < (1589/500)^n theorem, n > 0.', flush=True)


if __name__ == '__main__':
    main()
