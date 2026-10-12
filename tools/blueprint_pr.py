#!/usr/bin/env python3
"""Text-only DAG comparison and blueprint refinement; Python 3.11+, no Lean."""
from __future__ import annotations
import argparse
import collections
import contextlib
import hashlib
import json
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib

ROOT = pathlib.Path(__file__).resolve().parents[1]
FORBIDDEN = re.compile(r'(?i)\b(?:delivery|landing|stage\s*[123]|blueprint_pr|upstream-bp|[A-Z][123]\s+(?:group|worker))\b|(?:\d{1,3}\.){3}\d{1,3}|-----BEGIN .*PRIVATE KEY|[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}|(?:gh[pousr]_|sk-proj-)[A-Za-z0-9]+')


def load_nodes():
    result = {}
    for path in sorted((ROOT / 'dag/nodes').glob('*/*.json')):
        node = json.loads(path.read_text())
        ident = node['id']
        if ident in result:
            raise ValueError(f'duplicate DAG id: {ident}')
        result[ident] = node
    # Public identifiers describe mathematics, rather than local work stages.
    mapping = {ident: ident.replace('stage3', 'aux') for ident, node in result.items()
               if 'stage3' in ident and not (node.get('blueprint') or {}).get('is')}
    for old, new in mapping.items():
        if new in result:
            raise ValueError(f'public id collision: {old} -> {new}')
    def remap(value):
        if isinstance(value, str):
            for old, new in mapping.items():
                value = value.replace(old, new)
            return value
        if isinstance(value, list):
            return [remap(v) for v in value]
        if isinstance(value, dict):
            return {k: (v if k in ('lean', 'mathlib_match') else remap(v)) for k, v in value.items()}
        return value
    load_nodes.aliases = mapping
    return {mapping.get(ident, ident): remap(node) for ident, node in result.items()}


@contextlib.contextmanager
def blueprint_tree(value):
    path = pathlib.Path(value).resolve()
    if (path / 'blueprint').is_dir():
        yield path
        return
    with tempfile.TemporaryDirectory(prefix='blueprint-text-') as name:
        out = pathlib.Path(name)
        refs = subprocess.check_output(['git', '--git-dir', str(path), 'for-each-ref', '--format=%(refname)'], text=True).splitlines()
        ref = next((r for r in ('refs/heads/up-slop-now', 'refs/heads/blueprint-main', 'refs/heads/main') if r in refs), None)
        if ref is None:
            raise ValueError('blueprint bare repository has no upstream main reference')
        archive = subprocess.check_output(['git', '--git-dir', str(path), 'archive', ref])
        subprocess.run(['tar', '-xf', '-', '-C', name], input=archive, check=True)
        yield out


def parse(path):
    text = path.read_text()
    parts = text.split('+++', 2)
    if len(parts) != 3 or parts[0].strip():
        raise ValueError(f'{path}: missing TOML front matter')
    return tomllib.loads(parts[1]), parts[2].strip()


def scan(tree):
    result = {}
    for path in sorted((tree / 'blueprint').rglob('*.md')):
        front, body = parse(path)
        ident = front.get('id')
        if not ident:
            if front.get('kind') != 'proof' or not front.get('of'):
                raise ValueError(f'{path}: no id or proof of')
            ident = front['of'] + '.proof'
        if ident in result:
            raise ValueError(f'duplicate blueprint id {ident}')
        result[ident] = (path.relative_to(tree), front, body)
    return result


def high(path):
    # blueprint/sec/_section.md and blueprint/sec/sk/_section.md.
    return len(path.parts) <= 3 or (path.name == '_section.md' and len(path.parts) <= 4) or (len(path.parts) == 4 and path.name == path.parent.name + '.proof.md')


def fields(data):
    return '+++\n' + '\n'.join(f'{k} = {json.dumps(v, ensure_ascii=False)}' for k, v in data.items()) + '\n+++\n'


def proof_body(node):
    paras = []
    for step in node.get('proof') or []:
        if isinstance(step, str):
            paras.append(step)
            continue
        text = step.get('text', '')
        missing = [i for i in step.get('uses', []) if '[' + i + ']' not in text]
        if missing:
            text += ' (' + ', '.join('[' + i + ']' for i in missing) + ').'
        paras.append(text)
    return '\n\n'.join(paras)


def correction(node):
    value = node.get('statement_change')
    if not value and isinstance(node.get('split_report'), dict):
        value = node['split_report'].get('statement_change')
    return value


def classify(ns, bp):
    rows = []
    for ident, node in sorted(ns.items()):
        imported = bool((node.get('blueprint') or {}).get('is'))
        present = bp.get(ident)
        state = None
        if node.get('status') == 'merged':
            state = 'merged-omitted'
        elif not imported and not present:
            state = 'mathlib-omitted' if node.get('status') == 'mathlib' else 'new'
        elif imported and not present:
            state = 'upstream-absent'
        elif present:
            if correction(node) and rendered(node.get('statement', '').strip(), ns) != present[2]:
                state = 'ask-statement' if high(present[0]) else 'statement'
            if not state and node.get('proof'):
                proof = bp.get(ident + '.proof')
                if rendered(proof_body(node), ns).strip() != (proof[2] if proof else ''):
                    state = 'ask-proof' if high(present[0]) else 'proof'
        if state:
            rows.append({'chapter': node.get('chapter', ''), 'sketch': node.get('unit', ''), 'id': ident, 'kind': node.get('kind', ''), 'change': state})
    for ident, entry in sorted(bp.items()):
        if not ident.endswith('.proof') and ident not in ns:
            rows.append({'chapter': entry[0].parts[1], 'sketch': entry[0].parts[2] if len(entry[0].parts) > 3 else '', 'id': ident, 'kind': entry[1].get('kind'), 'change': 'blueprint-only'})
    return rows


def diff(args):
    with blueprint_tree(args.blueprint) as tree:
        rows = classify(load_nodes(), scan(tree))
    counts = collections.Counter(r['change'] for r in rows)
    if args.json:
        print(json.dumps({'counts': dict(sorted(counts.items())), 'rows': rows}, indent=2))
        return
    print('Counts: ' + ', '.join(f'{k}={v}' for k, v in sorted(counts.items())))
    grouped = collections.defaultdict(collections.Counter)
    for row in rows:
        grouped[(row['chapter'], row['sketch'])][row['change'] + (':' + row['kind'] if row['change'] == 'new' else '')] += 1
    for (chapter, sketch), count in sorted(grouped.items()):
        print(chapter, sketch, ' '.join(f'{k}={v}' for k, v in sorted(count.items())), sep='\t')


def write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    if not path.exists() or path.read_text() != text:
        path.write_text(text)


def forbidden(text):
    # Mathematical uses of 'landing in' and numbered equations are not
    # process terminology or host addresses. Preserve them verbatim.
    clean = re.sub(r'(?i)\blanding(?= in\b)', 'taking values', text)
    clean = re.sub(r'(?i)\bequations?\s*\(?\d+(?:\.\d+){3}\)?(?:\s+and\s+\(?\d+(?:\.\d+){3}\)?)*', 'equation reference', clean)
    return FORBIDDEN.search(clean)


def rendered(text, ns):
    # Mathlib leaves remain source citations, never blueprint objects.
    def reference(ident):
        node = ns.get(ident, {})
        if node.get('status') != 'mathlib' or (node.get('blueprint') or {}).get('is'):
            return '[' + ident + ']'
        found = node.get('mathlib_match') or {}
        if isinstance(found, list):
            found = found[0] if found else {}
        if not isinstance(found, dict):
            found = {}
        decl = found.get('declaration') or ident
        paths = sorted(set(re.findall(r'Mathlib/[A-Za-z0-9_/]+\.lean', str(found.get('file', '')))))
        label = '`' + str(decl).replace('`', '') + '`'
        if paths:
            links = ', '.join('[Mathlib source](https://github.com/leanprover-community/mathlib4/blob/master/' + path + ')' for path in paths)
            return label + ' (' + links + ')'
        return label + ' (Mathlib)'
    def citation(match):
        content, suffix = match.group(1), match.group(2)
        if suffix and (re.match(r'(?:https?://|#|/)', suffix) or re.search(r'\.(?:md|html|lean|pdf)(?:#|$)', suffix)):
            return match.group(0)
        tokens = re.findall(r'[A-Za-z0-9_.-]+', content)
        if not any(token in ns for token in tokens):
            return match.group(0)
        # Preserve semicolons, commas, and clause qualifiers verbatim.
        value = re.sub(r'[A-Za-z0-9_.-]+', lambda m: reference(m.group()) if m.group() in ns or re.match(r'^(?:def|lem|prop|thm|cor|sk|sec|aux)-', m.group()) else m.group(), content)
        return value + ('(' + suffix + ')' if suffix is not None else '')
    return re.sub(r'\[([^\]\n]+)\](?:\(([^)\n]*)\))?', citation, text)


def dependencies(values, ns):
    return sorted({ident for ident in values if not (ident in ns and ns[ident].get('status') == 'mathlib' and not (ns[ident].get('blueprint') or {}).get('is'))})


def node_text(node, ns):
    meta = {'id': node['id'], 'kind': 'definition' if node['kind'] == 'definition' else 'lemma'}
    if node.get('title'):
        meta['title'] = node['title']
    deps = []
    for ident in node.get('stmt_deps') or []:
        if ident in ns and ns[ident].get('status') == 'mathlib' and not (ns[ident].get('blueprint') or {}).get('is'):
            continue
        deps.append(ident)
    if deps:
        meta['uses'] = sorted(set(deps))
    lean = node.get('lean') or {}
    if lean.get('declaration'):
        meta['lean'] = [lean['declaration']]
    source = node.get('source') or {}
    if source:
        meta['source'] = (str(source.get('document', '')) + ', ' + str(source.get('place', ''))).strip(', ')
    return fields(meta) + rendered(node.get('statement', '').strip(), ns) + '\n'


def cut(args):
    ns = load_nodes()
    out = pathlib.Path(args.out).resolve()
    with blueprint_tree(args.blueprint) as tree:
        bp = scan(tree)
        baseline = {str(p.relative_to(tree)): p.read_text() for p in (tree / 'blueprint').rglob('*.md')}
        # Seed absent files only: rerunning a cut preserves existing changes.
        for rel, text in baseline.items():
            path = out / rel
            if not path.exists():
                write(path, text)
        selected = [r for r in classify(ns, bp) if r['chapter'] == args.chapter and (not args.sketch or r['sketch'] == args.sketch)]
        if getattr(args, 'ids', None):
            chosen = set(json.loads(pathlib.Path(args.ids).read_text()))
            selected = [r for r in selected if r['id'] in chosen]
        ask = []
        for row in selected:
            ident, mode = row['id'], row['change']
            if mode.startswith('ask-'):
                ask.append({'id': ident, 'proposal': mode, 'reason': correction(ns[ident]), 'statement': ns[ident]['statement']})
                continue
            if mode not in ('new', 'statement', 'proof'):
                continue
            node = ns[ident]
            if mode == 'new':
                ancestor = (node.get('blueprint') or {}).get('from') or {}
                target = ancestor.get('node') if isinstance(ancestor, dict) else ancestor
                seen = set()
                while target in ns and target not in bp and target not in seen:
                    seen.add(target)
                    a = (ns[target].get('blueprint') or {}).get('from') or {}
                    target = a.get('node') if isinstance(a, dict) else a
                if target not in bp and node.get('unit') in bp:
                    target = node['unit']
                if target not in bp:
                    ask.append({'id': ident, 'proposal': 'placement', 'reason': 'No existing blueprint ancestor', 'statement': node['statement']})
                    continue
                path, front, body = bp[target]
                if high(path):
                    parent = path.parent
                elif path.name == '_section.md':
                    parent = path.parent
                else:
                    # Keep the statement file intact; its refinements use a deeper folder.
                    parent = path.parent
                dest = parent / (ident + '.md')
                write(out / dest, node_text(node, ns))
                if node.get('proof'):
                    uses = dependencies(node.get('proof_deps') or [], ns)
                    meta = {'kind': 'proof', 'of': ident}
                    if uses: meta['uses'] = uses
                    write(out / dest.with_name(ident + '.proof.md'), fields(meta) + rendered(proof_body(node), ns) + '\n')
            else:
                path, front, body = bp[ident]
                if mode == 'statement':
                    write(out / path, fields(front) + node['statement'].strip() + '\n')
                if node.get('proof'):
                    proof_path = bp.get(ident + '.proof', (path.with_name(ident + '.proof.md'),))[0]
                    uses = dependencies(node.get('proof_deps') or [], ns)
                    meta = {'kind': 'proof', 'of': ident}
                    if uses: meta['uses'] = uses
                    write(out / proof_path, fields(meta) + rendered(proof_body(node), ns) + '\n')
        outside = {str(p.relative_to(tree)): hashlib.sha256(p.read_bytes()).hexdigest()
                   for p in tree.rglob('*') if p.is_file() and 'blueprint' not in p.relative_to(tree).parts[:1] and '.git' not in p.relative_to(tree).parts}
        manifest = {'id_aliases': getattr(load_nodes, 'aliases', {}), 'mathlib_leaves': [ident for ident, node in ns.items() if node.get('status') == 'mathlib' and not (node.get('blueprint') or {}).get('is')], 'outside': outside, 'baseline': baseline, 'chapter': args.chapter, 'sketch': args.sketch, 'asks': ask}
        write(out / '.blueprint-cut.json', json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')
    changed = [str(p.relative_to(out)) for p in (out / 'blueprint').rglob('*.md') if baseline.get(str(p.relative_to(out))) != p.read_text()]
    print(json.dumps({'changed_files': len(changed), 'proposals': len(ask), 'files': sorted(changed)}, indent=2))


def graph(bp):
    result = {}
    for ident, (_, front, _) in bp.items():
        result[ident] = set(front.get('uses', []))
        if front.get('of'):
            result[ident].add(front['of'])
    return result


def cycles(edges):
    done, active, found = set(), [], set()
    def visit(ident):
        if ident in active:
            found.add(tuple(sorted(active[active.index(ident):])))
            return
        if ident in done:
            return
        active.append(ident)
        for target in sorted(edges.get(ident, set())):
            visit(target)
        active.pop(); done.add(ident)
    for ident in sorted(edges):
        visit(ident)
    return found


def tex_errors(text):
    clean = re.sub(r'```.*?```|`[^`]*`', '', text, flags=re.S)
    clean = re.sub(r'\\\$', '', clean)
    errors = []
    if len(re.findall(r'\$\$', clean)) % 2:
        errors.append('display dollars unbalanced')
    if clean.replace('$$', '').count('$') % 2:
        errors.append('inline dollars unbalanced')
    for start, end in (('\\(', '\\)'), ('\\[', '\\]')):
        if clean.count(start) != clean.count(end):
            errors.append('TeX delimiters unbalanced')
    return errors


def check(args):
    root = pathlib.Path(args.dir).resolve()
    manifest = json.loads((root / '.blueprint-cut.json').read_text()) if (root / '.blueprint-cut.json').exists() else None
    if not manifest:
        raise ValueError('check needs .blueprint-cut.json baseline from cut to enforce protected layers')
    baseline = manifest['baseline']
    errors = []
    try:
        bp = scan(root)
    except (ValueError, tomllib.TOMLDecodeError) as ex:
        print('FAIL:', ex); return 1
    edges = graph(bp)
    omitted = set(manifest.get('mathlib_leaves', []))
    changed = []
    for ident, (path, front, body) in bp.items():
        actual = (root / path).read_text()
        if baseline.get(str(path)) == actual:
            continue
        changed.append(path)
        expected = path.parent.name if path.name == '_section.md' else path.name.removesuffix('.md')
        if front.get('kind') == 'proof' and path.name != front.get('of', '') + '.proof.md':
            errors.append(f'{path}: proof filename must match of target')
        if expected != ident and front.get('kind') != 'proof':
            errors.append(f'{path}: id {ident} != filename {expected}')
        if high(path) or (front.get('of') in bp and high(bp[front['of']][0])):
            errors.append(f'protected layer changed: {path}')
        if forbidden(actual):
            errors.append(f'forbidden text: {path}: {forbidden(actual).group()}')
        for citation in re.finditer(r'\[([^\]\n]+)\](?:\(([^)\n]*)\))?', body):
            if citation.group(2) and re.match(r'https?://', citation.group(2)):
                continue
            for token in re.findall(r'[A-Za-z0-9_.-]+', citation.group(1)):
                if token in omitted:
                    errors.append(f'{path}: omitted Mathlib leaf remains an internal citation: {token}')
        for error in tex_errors(body):
            errors.append(f'{path}: {error}')
        for target in edges[ident]:
            if target not in bp:
                errors.append(f'{path}: missing dependency {target}')
        for target in re.findall(r'\[((?:def|lem|prop|thm|cor|sk|sec|d-|p-|l-|aux)[A-Za-z0-9_.-]*)\](?!\()', body):
            if target not in bp:
                errors.append(f'{path}: unresolved citation {target}')
    # A directory newly introduced by this cut is a section in the renderer.
    # Its index must state the section, rather than merely label a container.
    base_dirs = {pathlib.Path(rel).parent for rel in baseline}
    for folder in sorted((root / 'blueprint').rglob('*')):
        if not folder.is_dir() or folder.relative_to(root) in base_dirs:
            continue
        section = folder / '_section.md'
        if not section.is_file():
            errors.append(f'{folder.relative_to(root)}: new section missing _section.md')
            continue
        try:
            front, body = parse(section)
            if front.get('id') != folder.name or not body or front.get('kind') == 'proof':
                errors.append(f'{section.relative_to(root)}: section must hold its statement')
        except (ValueError, tomllib.TOMLDecodeError) as ex:
            errors.append(str(ex))
    for rel in baseline:
        if not (root / rel).exists():
            errors.append('blueprint file removed: ' + rel)
    # Compare cycles to the original graph, without materializing a second tree.
    base_graph = {}
    for text in baseline.values():
        parts = text.split('+++', 2); front = tomllib.loads(parts[1])
        ident = front.get('id') or (front.get('of', '') + '.proof')
        base_graph[ident] = set(front.get('uses', [])) | ({front['of']} if front.get('of') else set())
    for cycle in cycles(edges) - cycles(base_graph):
        errors.append('new cycle: ' + ', '.join(cycle))
    if 'outside' in manifest:
        for file in root.rglob('*'):
            rel = file.relative_to(root)
            if not file.is_file() or rel.parts[0] in ('blueprint', '.git') or str(rel) == '.blueprint-cut.json':
                continue
            if manifest['outside'].get(str(rel)) != hashlib.sha256(file.read_bytes()).hexdigest():
                errors.append('changed outside blueprint/: ' + str(rel))
    if (root / '.git').exists():
        paths = subprocess.check_output(['git', '-C', str(root), 'diff', '--name-only', 'HEAD'], text=True).splitlines()
        paths += subprocess.check_output(['git', '-C', str(root), 'ls-files', '--others', '--exclude-standard'], text=True).splitlines()
        for path in paths:
            if not path.startswith('blueprint/') and path != '.blueprint-cut.json':
                errors.append('changed outside blueprint/: ' + path)
    for error in sorted(set(errors)):
        print('ERROR ' + error)
    print(f'{"FAIL" if errors else "PASS"}: {len(bp)} objects, {len(changed)} changed files, {len(set(errors))} errors')
    return int(bool(errors))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    cmd = commands.add_parser('diff'); cmd.add_argument('--blueprint', required=True); cmd.add_argument('--json', action='store_true'); cmd.set_defaults(fn=diff)
    cmd = commands.add_parser('cut'); cmd.add_argument('chapter'); cmd.add_argument('--sketch'); cmd.add_argument('--ids', help='JSON list of ids for a dependency-ordered part'); cmd.add_argument('--blueprint', required=True); cmd.add_argument('--out', required=True); cmd.set_defaults(fn=cut)
    cmd = commands.add_parser('check'); cmd.add_argument('dir'); cmd.set_defaults(fn=check)
    args = parser.parse_args()
    try:
        return args.fn(args)
    except (ValueError, OSError, subprocess.CalledProcessError) as ex:
        print(str(ex), file=sys.stderr); return 1

if __name__ == '__main__':
    sys.exit(main())
