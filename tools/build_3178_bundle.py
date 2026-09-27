#!/usr/bin/env python3
"""Prepare or seal the English standalone review bundle for the 3.178 theorem."""
import argparse
from datetime import date
import hashlib
import json
from pathlib import Path
import re
import shutil
import zipfile

ROOT = Path(__file__).resolve().parents[1]
CHECKPOINT = ROOT / 'results/entropy-joint-saving-2026-09-23'
TEMPLATES = ROOT / 'packaging/3178'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def prepare(output):
    output.mkdir(parents=True, exist_ok=False)
    sources = json.loads((CHECKPOINT / 'source-snapshots.json').read_text())['sources']
    modules = []
    imports = {}
    for path, record in sorted(sources.items()):
        if not path.startswith('lean/SmpMax/General/'):
            continue
        data = (ROOT / path).read_bytes()
        if sha(data) != record['sha256']:
            raise RuntimeError('Proof source differs from retained checkpoint: ' + path)
        destination = output / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)
        name = 'SmpMax.General.' + destination.stem
        imports[name] = re.findall(r'^import ([\w.]+)', data.decode(), re.M)
        modules.append({'name': name, 'path': path, 'bytes': len(data), 'sha256': sha(data)})
    assert len(modules) == 56
    order, seen = [], set()
    def visit(name):
        if name in seen:
            return
        seen.add(name)
        for parent in imports[name]:
            if parent.startswith('SmpMax.'):
                visit(parent)
        order.append(name)
    visit('SmpMax.General.JointEntropyUpperBound')
    assert len(order) == 45
    (output / 'source-index.json').write_text(json.dumps({
        'origin': 'The complete 2026-09-23 3.178 proof checkpoint; original theorem bytes preserved.',
        'modules': modules, 'target_dependency_order': order,
    }, indent=2) + '\n')
    (output / 'lean/SmpMax.lean').write_text(''.join('import ' + m['name'] + '\n' for m in modules))
    for name in ('lean-toolchain', 'lake-manifest.json'):
        shutil.copyfile(ROOT / 'lean' / name, output / 'lean' / name)
    lakefile = (ROOT / 'lean/lakefile.toml').read_text().split('[[lean_exe]]')[0].rstrip() + '\n'
    (output / 'lean/lakefile.toml').write_text(lakefile)
    audit = sources['lean/checks/GeneralEntropy.lean']
    (output / 'lean/checks').mkdir()
    (output / 'lean/checks/GeneralEntropy.lean').write_text(audit['content'])
    assert sha((output / 'lean/checks/GeneralEntropy.lean').read_bytes()) == audit['sha256']
    (output / 'tools').mkdir()
    shutil.copyfile(TEMPLATES / 'verify.py', output / 'tools/verify.py')
    shutil.copyfile(TEMPLATES / 'Check3178.lean', output / 'lean/Check3178.lean')
    (output / '.gitignore').write_text('.lake/\nbuild/\nverification-local/\n__pycache__/\n')
    print(json.dumps({'prepared': str(output), 'proof_modules': 56, 'target_dependency_modules': 45}))


def seal(output, archive, archive_date):
    required = ('README.md', 'PROOF.md', 'PROOF.tex', 'PROOF.pdf', 'SOURCE_MAP.md',
                'evidence/verification.json', 'PACKAGE_PROVENANCE.json')
    for name in required:
        if not (output / name).is_file():
            raise RuntimeError('Incomplete bundle: ' + name)
    manifest_path = output / 'bundle-manifest.json'
    files = []
    for path in sorted(output.rglob('*')):
        rel = path.relative_to(output)
        if any(part in ('.lake', 'build', 'verification-local', '__pycache__') for part in rel.parts):
            continue
        if not path.is_file() or path == manifest_path:
            continue
        if path.is_symlink():
            raise RuntimeError('Unexpected symlink in archive: ' + str(rel))
        data = path.read_bytes()
        files.append({'path': rel.as_posix(), 'bytes': len(data), 'sha256': sha(data)})
    manifest_path.write_text(json.dumps({'format_version': 1, 'files': files}, indent=2) + '\n')
    paths = [output / item['path'] for item in files] + [manifest_path]
    archive.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(archive, 'x', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as zipped:
        for path in sorted(paths):
            info = zipfile.ZipInfo(output.name + '/' + path.relative_to(output).as_posix(),
                                   date_time=(archive_date.year, archive_date.month,
                                              archive_date.day, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            zipped.writestr(info, path.read_bytes())
    checksum = sha(archive.read_bytes())
    archive.with_suffix(archive.suffix + '.sha256').write_text(checksum + '  ' + archive.name + '\n')
    print(json.dumps({'archive': str(archive), 'bytes': archive.stat().st_size,
                      'sha256': checksum, 'payload_files': len(paths)}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('prepare', 'seal'))
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--archive', type=Path)
    parser.add_argument('--archive-date', type=date.fromisoformat,
                        default=date(2026, 9, 26), help='ZIP timestamp date (YYYY-MM-DD)')
    args = parser.parse_args()
    if args.mode == 'prepare':
        prepare(args.output)
    else:
        if not args.archive:
            parser.error('--archive is required for seal')
        seal(args.output, args.archive, args.archive_date)


if __name__ == '__main__':
    main()
