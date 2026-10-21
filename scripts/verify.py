#!/usr/bin/env python3
"""Reproducible source-coverage, independent-target and proof-graph gate.

Exit 1 means incomplete/failed verification; missing targets never become passes.
Fresh builds share pinned dependency artifacts only, never old project artifacts.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

from contracts import Contracts
from runner_support import mask_comments

ROOT = Path(__file__).resolve().parents[1]


def freeze(root=ROOT):
    paths = [*root.glob('*.lean'), *root.glob('LogGas/**/*.lean'),
             *root.glob('verification/**/*.md'),
             *root.glob('verification/*.json'), *root.glob('notes/*'),
             *root.glob('scripts/**/*.py'), *root.glob('scripts/*.sh'), *root.glob('scripts/pipeline.conf*'),
             *root.glob('prompts/*.md'),
             root/'README.md', root/'.gitignore',
             root / 'lakefile.toml', root / 'lean-toolchain', root / 'lake-manifest.json']
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(set(paths)) if p.is_file() and 'verification/reviews/' not in str(p.relative_to(root))}


def review_valid(path, hashes, role):
    if not path.exists():
        return False
    data = json.loads(path.read_text())
    # Review receipts themselves are excluded to avoid self-referential hashes.
    return (data.get('role') == role and data.get('verdict') == 'passed' and
            data.get('reviewer') and data.get('reviewed_files') == hashes)


def fresh_paths_valid(text, root, build_dir, toolchain_prefix=None):
    """Normalize relative paths and symlinks, accepting only fresh/project dependencies."""
    if (root/build_dir).is_symlink():
        return False
    allowed = [(root/build_dir).resolve()]
    lock = root/'verification/dependency-lock.json'
    if lock.exists():
        allowed += [(root/'.lake/packages'/p['name']/'.lake/build/lib/lean').resolve()
                    for p in json.loads(lock.read_text())['packages']]
    if toolchain_prefix:
        allowed.append((Path(toolchain_prefix)/'lib/lean').resolve())
    entries = [Path(s.strip()) for s in text.strip().split(os.pathsep) if s.strip()]
    resolved = [(p if p.is_absolute() else root/p).resolve() for p in entries]
    return bool(resolved) and all(any(p == a or a in p.parents for a in allowed) for p in resolved)


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument('--fresh', action='store_true')
    parser.add_argument('--structural-only', action='store_true')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--comparator-argv', help='JSON argv array for an installed genuine Comparator runner; executed without a shell')
    args = parser.parse_args()
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    output = args.output or ROOT / 'logs/verification' / stamp
    output.mkdir(parents=True, exist_ok=True)
    hashes = freeze()
    (output / 'freeze.json').write_text(json.dumps(hashes, indent=2) + '\n')
    checks = []
    def record(name, ok, detail, status=None):
        checks.append(dict(name=name, status=status or ('passed' if ok else 'failed'), detail=detail))
        print(f'{checks[-1]["status"].upper()}: {name}: {detail}', flush=True)
    def run(name, command, timeout=7200):
        started = time.time()
        try:
            with (output / (name + '.log')).open('w') as stream:
                process = subprocess.Popen(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT,
                                           start_new_session=True)
                try:
                    code = process.wait(timeout=timeout)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                    code = 124
        except subprocess.TimeoutExpired:
            code = 124
        record(name, code == 0, dict(command=command, exit_code=code,
                                    seconds=round(time.time()-started, 2)))
        return code == 0
    contract = Contracts(ROOT)
    missing = contract.missing()
    record('source-coverage', not missing, {'missing': missing, 'milestones': len(contract.nodes)})
    changed = [p for p, h in contract.data.get('sources', {}).items()
               if not (ROOT / p).exists() or hashlib.sha256((ROOT / p).read_bytes()).hexdigest() != h]
    record('source-provenance', not changed, {'changed_sources': changed})
    bad_locators = [n['id'] for n in contract.nodes.values()
                    if not (ROOT/n['source']).exists() or
                    ('\\label{'+n['label']+'}') not in (ROOT/n['source']).read_text()]
    record('source-locators', not bad_locators, {'invalid': bad_locators})
    raw = (ROOT / 'Challenge.lean').read_text() + '\n' + (ROOT / 'PaperChallenge.lean').read_text()
    imports = re.findall(r'^import\s+(\S+)', mask_comments(raw), re.M)
    record('challenge-direct-imports', bool(imports) and all(m == 'Mathlib' or m.startswith('Mathlib.') for m in imports), imports)
    proof_text = '\n'.join(mask_comments(p.read_text()) for p in [ROOT/'LogGas.lean', *sorted((ROOT/'LogGas').rglob('*.lean')), ROOT/'Solution.lean', ROOT/'Challenge.lean', ROOT/'PaperSolution.lean', ROOT/'PaperChallenge.lean'])
    forbidden = re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b|skipKernelTC', proof_text)
    record('source-admissions', not forbidden, forbidden)
    lock = ROOT/'verification/dependency-lock.json'
    runtime_manifest = ROOT/'lake-manifest.json'
    record('dependency-lock', lock.exists() and runtime_manifest.exists() and lock.read_bytes() == runtime_manifest.read_bytes(),
           'Runtime dependency manifest must equal the preserved Dell3 lock')
    if args.structural_only:
        record('lean-verification', False, 'Structural-only mode does not check compilation, types or transitive axioms', 'unperformed')
    if not args.structural_only:
        pins = []
        if lock.exists():
            for package in json.loads(lock.read_text())['packages']:
                path = ROOT/'.lake/packages'/package['name']
                result = subprocess.run(['git','-C',str(path),'rev-parse','HEAD'], text=True, capture_output=True)
                pins.append(dict(name=package['name'], expected=package['rev'], actual=result.stdout.strip(), exit_code=result.returncode))
        record('installed-dependency-revisions', bool(pins) and all(p['exit_code']==0 and p['expected']==p['actual'] for p in pins), pins)
        lake = ['lake']
        if args.fresh:
            config = (ROOT/'lakefile.toml').read_text()
            if 'defaultTargets = ["LogGas"]' not in config or re.search(r'^buildDir\s*=', config, re.M):
                raise ValueError('Fresh configuration requires the reviewed defaultTargets and no existing buildDir')
            build_dir = '.lake/build-verification-' + stamp + '-' + str(os.getpid())
            if (ROOT/build_dir).exists():
                raise RuntimeError('Fresh build directory already exists')
            config = config.replace('defaultTargets = ["LogGas"]',
                                    'defaultTargets = ["LogGas"]\nbuildDir = "' + build_dir + '"')
            fresh_config = ROOT/('lakefile.verification-'+stamp+'.toml')
            fresh_config.write_text(config)
            lake += ['-f', str(fresh_config)]
            record('fresh-directory', True, {'build_dir': build_dir, 'initially_exists': False})
        run('lean-version', lake + ['env','lean','--version'])
        built = run('project-build', lake + ['build','LogGas','Challenge','Solution','PaperChallenge','PaperSolution','VerificationAudit'])
        if built:
            if args.fresh:
                run('fresh-lean-path', lake + ['env','printenv','LEAN_PATH'])
                run('toolchain-prefix', lake + ['env','lean','--print-prefix'])
                prefix = (output/'toolchain-prefix.log').read_text().strip()
                lean_path = (output/'fresh-lean-path.log').read_text()
                record('no-old-project-artifacts', fresh_paths_valid(lean_path, ROOT, build_dir, prefix), lean_path.strip())
                record('fresh-project-artifacts', bool(list((ROOT/build_dir).rglob('*.olean'))),
                       {'count': len(list((ROOT/build_dir).rglob('*.olean')))})
            envs = {}
            for module in ['Mathlib', 'Challenge', 'Solution', 'PaperChallenge', 'PaperSolution']:
                source = ROOT/'.lake'/('Verify'+module+'.lean')
                source.write_text(f'import {module}\nimport VerificationAudit\nrun_cmd LogGasAudit.audit `{module}\n')
                if run(module.lower()+'-environment', lake + ['env','lean',str(source)]):
                    log = (output/(module.lower()+'-environment.log')).read_text()
                    match = re.search(r'VERIFICATION_JSON (\{[^\n]*\})', log)
                    if match:
                        envs[module] = json.loads(match[1])
            if 'Challenge' in envs and 'Solution' in envs:
                left = {x['name']: x for x in envs['Challenge']['definitions']}
                right = {x['name']: x for x in envs['Solution']['definitions']}
                record('independent-definition-parity', bool(left) and all(right.get(n) == v for n,v in left.items()),
                       {'challenge_declarations': len(left), 'solution_declarations': len(right),
                        'different': sorted(n for n in left if left.get(n) != right.get(n))})
                (output/'environments.json').write_text(json.dumps(envs,indent=2)+'\n')
            else:
                record('independent-definition-parity', False, 'Environment export missing')
            if 'PaperChallenge' in envs and 'PaperSolution' in envs:
                left = {x['name']: x for x in envs['PaperChallenge']['definitions']}
                right = {x['name']: x for x in envs['PaperSolution']['definitions']}
                record('paper-definition-parity', bool(left) and all(right.get(n) == v for n,v in left.items()),
                       {'different': sorted(n for n in left if left[n] != right.get(n))})
                extra = set(envs['PaperChallenge']['modules']) - set(envs.get('Mathlib',{}).get('modules',[])) - {'PaperChallenge'}
                record('paper-challenge-mathlib-closure', not extra, sorted(extra))
            else:
                record('paper-definition-parity', False, 'Paper environment export missing')
            if 'Mathlib' in envs and 'Challenge' in envs:
                extra = set(envs['Challenge']['modules']) - set(envs['Mathlib']['modules']) - {'Challenge'}
                record('challenge-mathlib-closure', not extra, {'extra_modules': sorted(extra)})
            else:
                record('challenge-mathlib-closure', False, 'Environment export missing')
            source = ROOT/'.lake'/'VerifyTargets.lean'
            source.write_text('import Solution\n' +
                'example : LogGasChallenge.principalStatement := LogGasChallenge.principal\n' +
                'example : LogGasChallenge.bulkStatement := LogGasChallenge.bulk\n' +
                '#print axioms LogGasChallenge.principal\n#print axioms LogGasChallenge.bulk\n')
            run('target-proof-contracts', lake + ['env','lean',str(source)])
            source = ROOT/'.lake'/'VerifyPaperTargets.lean'
            source.write_text('import PaperSolution\n' +
                'example : LogGasPaper.PaperTheorem := LogGasPaper.main\n' +
                'example : LogGasPaper.LogKernelExists := LogGasPaper.kernel_exists\n' +
                '#print axioms LogGasPaper.main\n#print axioms LogGasPaper.kernel_exists\n')
            run('paper-proof-contracts', lake + ['env','lean',str(source)])
            run('lean-kernel-replay', lake + ['env','leanchecker','Solution'])
            run('paper-kernel-replay', lake + ['env','leanchecker','PaperSolution'])
            # The environment scan includes generated/private local declarations.
            # Source parser counts are supplementary, never the whole-graph count.
        if args.comparator_argv:
            command = json.loads(args.comparator_argv)
            if not isinstance(command, list) or not command or not all(isinstance(s,str) for s in command):
                raise ValueError('Comparator command must be a nonempty JSON string array')
            run('external-comparator', command)
        else:
            record('external-comparator', False, 'No genuine Comparator runner configured; no external comparison pass is claimed.', 'unperformed')
    reviewed = {p: h for p,h in hashes.items() if not p.startswith('verification/reviews/')}
    identities = []
    for role in ['mathematical-fidelity', 'lean-verification']:
        path = ROOT/'verification/reviews'/(role+'.json')
        valid = review_valid(path, reviewed, role)
        receipt = json.loads(path.read_text()) if path.exists() else {}
        current = receipt.get('role') == role and receipt.get('reviewed_files') == reviewed
        if current and receipt.get('reviewer'):
            identities.append(receipt['reviewer'])
        record('review-'+role, valid, {'reviewer': receipt.get('reviewer'), 'verdict': receipt.get('verdict'),
                                      'matches_freeze': current})
    record('distinct-reviewers', len(identities) == 2 and len(set(identities)) == 2, identities)
    record('frozen-inputs-unchanged', freeze() == hashes, 'Rehashed source, contracts, configuration, prompts and harness')
    result = dict(recorded_utc=stamp, overall='passed' if all(c['status']=='passed' for c in checks) else 'incomplete',
                  checks=checks, scope='Conditional H1/H2 theorem plus full paper theorem and normalized-kernel existence; independent fidelity review required.')
    (output/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    lines = ['# Final verification', '', 'Overall: **'+result['overall']+'**.', '',
             *[f'- {c["status"]}: {c["name"]}' for c in checks], '',
             'Missing declarations:', *['- '+n for n in missing], '',
             'Closed queue entries are not a proof of missing bulk/main statements.']
    (output/'report.md').write_text('\n'.join(lines)+'\n')
    print('Evidence: '+str(output), flush=True)
    return 0 if result['overall'] == 'passed' else 1


if __name__ == '__main__':
    sys.exit(main())
