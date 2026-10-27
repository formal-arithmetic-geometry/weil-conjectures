"""Read-only replay of the real packet; try a proposed fix only in memory.

Run on the Weil server with a JSON mapping of packet paths to their contents.
This never writes project files, refs, commits, or Lean artifacts.
"""
import copy
import hashlib
import json
import pathlib
import sys
import types

ROOT = pathlib.Path('/home/ubuntu/weil-conjectures-sheaf')
sys.path.insert(0, str(ROOT / 'tools'))
import stage2_delivery as original
import nt_preflight2

ITEM = 'lem-trf-supported-taylor-presentation-pivots'
CONSUMER = 'lem-trf-formal-hilbert-stratum-minors'
PACKET_REF = 'maintenance-packet-in-memory'
packet = json.load(open(sys.argv[1]))
real_git = original.Git(ROOT)
base = real_git.run('rev-parse', 'sheaf-dag')
before = original.nodes_at(real_git, base)
paths = real_git.run('ls-tree', '-r', '--name-only', base, '--', 'dag/nodes')


class Snapshot:
    root = ROOT

    def ok(self, *args):
        if args[0] == 'rev-parse':
            return True
        raise AssertionError(args)

    def run(self, *args, **kwargs):
        if args[0] == 'merge-base':
            return base
        if args[0] == 'rev-parse':
            return base
        if args[0] == 'rev-list':
            return PACKET_REF
        if args[:3] == ('ls-tree', '-r', '--name-only'):
            return paths
        if args[:2] == ('diff', '--name-status'):
            return '\n'.join(
                ('M' if real_git.show(base, path) is not None else 'A') + '\t' + path
                for path, text in packet.items() if text != real_git.show(base, path))
        raise AssertionError(args)

    def show(self, ref, path):
        if ref == PACKET_REF and path in packet:
            return packet[path]
        return real_git.show(base, path)

    def node_path(self, ref, item):
        return next(path for path in packet if path.endswith('/' + item + '.json'))


source_path = ROOT / 'tools/stage2_delivery.py'
source = source_path.read_text()
needle = ('                       "and dependency nodes of the item")\n'
          '                continue\n'
          '            bd = json.loads(git.show(base, p) or "{}")')
replacement = needle.replace('                continue\n', '')
assert source.count(needle) == 1
candidate = types.ModuleType('maintenance_scope_candidate')
candidate.__file__ = str(source_path)
exec(compile(source.replace(needle, replacement), str(source_path), 'exec'), candidate.__dict__)


def replay(reader, overrides=None):
    old_nodes_at = reader.nodes_at
    reader.nodes_at = lambda git, ref: before
    try:
        return reader.read_delivery(Snapshot(), PACKET_REF, base, 'Q02', ITEM,
                                    overrides=overrides)
    finally:
        reader.nodes_at = old_nodes_at


baseline = replay(original)
assert len(baseline['fails']) == 1, baseline['fails']
assert 'no node of the delivery has it as lean.file' in baseline['fails'][0][1]
assert CONSUMER not in baseline['deps']
print('BASE', base)
print('TOOL_SHA256', hashlib.sha256(source.encode()).hexdigest())
print('CURRENT_READER', baseline['fails'])
fixed = replay(candidate)
assert not fixed['fails'], fixed['fails']
assert CONSUMER in fixed['deps']
assert len(fixed['modules']) == 5
assert any(CONSUMER in message for letter, message in fixed['advisory'])
assert nt_preflight2.graph_findings(fixed, before) == []
print('IN_MEMORY_CANDIDATE: 5 modules, both owner nodes retained, scope advisory retained, DAG clean')

consumer_path = fixed['deps'][CONSUMER]['path']
consumer_file = fixed['deps'][CONSUMER]['node']['lean']['file']
unowned = copy.deepcopy(fixed['deps'][CONSUMER]['node'])
unowned['lean'] = None
negative = replay(candidate, {consumer_path: json.dumps(unowned)})
assert any('no node of the delivery has it as lean.file' in text
           for letter, text in negative['fails'])
print('NEGATIVE: genuinely unowned module remains rejected')

bad_signature = copy.deepcopy(fixed['deps'][CONSUMER]['node'])
bad_signature['lean']['statement'] = 'theorem intentionally_wrong : False'
negative = replay(candidate, {consumer_path: json.dumps(bad_signature)})
assert any('lean.statement differs' in text for letter, text in negative['fails'])
print('NEGATIVE: wrong recorded signature remains rejected')

negative = replay(candidate, {consumer_file: packet[consumer_file] +
                            '\naxiom maintenanceForbiddenAxiom : False\n'})
assert any('an axiom' in text for letter, text in negative['fails'])
print('NEGATIVE: axiom remains rejected')

cyclic = copy.deepcopy(fixed)
cyclic['added_deps'].append(CONSUMER)
assert any('cycles:' in text for text in nt_preflight2.graph_findings(cyclic, before))
print('NEGATIVE: adding the downstream theorem as a dependency still produces a cycle')
print('NO PRODUCTION FILES OR REFS MODIFIED; candidate exists only in this process')
