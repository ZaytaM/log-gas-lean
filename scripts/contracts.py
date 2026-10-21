"""Source contracts and a conservative mathematical prerequisite graph.

No model calls. Missing declarations are obligations, never synthetic proofs.
"""
import hashlib
import json
from pathlib import Path

from runner_support import declarations


class Contracts:
    def __init__(self, root):
        self.root = Path(root)
        path = self.root / 'verification/contracts.json'
        self.data = json.loads(path.read_text()) if path.exists() else {'nodes': [], 'roots': []}
        self.nodes = {n['id']: n for n in self.data['nodes']}
        if len(self.nodes) != len(self.data['nodes']):
            raise ValueError('Duplicate contract IDs')
        visiting, visited = set(), set()
        def visit(key):
            if key not in self.nodes:
                raise ValueError('Unknown prerequisite: ' + key)
            if key in visiting:
                raise ValueError('Cyclic mathematical prerequisites: ' + key)
            if key in visited:
                return
            visiting.add(key)
            for dep in self.nodes[key]['depends_on']:
                visit(dep)
            visiting.remove(key)
            visited.add(key)
        for key in self.nodes:
            visit(key)
        for key in self.data['roots']:
            if key not in self.nodes:
                raise ValueError('Unknown verification root: ' + key)
        self.by_name = {name: n for n in self.nodes.values() for name in n['declarations']}

    def inventory(self):
        return {d.name: (str(p.relative_to(self.root)), d)
                for p in [*sorted((self.root / 'LogGas').rglob('*.lean')),
                          *[self.root/n for n in ('Solution.lean','PaperSolution.lean') if (self.root/n).exists()]]
                for d in declarations(p.read_text())}

    def missing(self):
        present = self.inventory()
        return [name for name in self.by_name if name not in present]

    def prerequisites(self, name):
        node = self.by_name.get(name)
        if not node:
            return []
        return [n for key in node['depends_on'] for n in self.nodes[key]['declarations']]

    def waiting(self, name, closed):
        return [n for n in self.prerequisites(name) if n not in closed]

    def packet(self, name):
        node = self.by_name.get(name)
        if not node:
            # Auxiliary workers still receive the source contract for their module.
            module = name.rsplit('.', 1)[0]
            peers = [n for n in self.nodes.values() if n['module'] == module]
        else:
            peers = [node]
        if not peers:
            return ''
        lines = ['\nSource and dependency contract (read before proving):']
        for n in peers:
            path = self.root / n['source']
            digest = hashlib.sha256(path.read_bytes()).hexdigest() if path.exists() else 'MISSING'
            lines += [f"- {n['id']}: {n['source']} / {n['label']}; SHA256={digest}",
                      f"  Scope: {n['scope']}. {n['statement']}",
                      '  Prerequisite declarations: ' + ', '.join(self.prerequisites(n['declarations'][0]))]
        lines += ['H1/H2 are the only authorized external mathematical inputs; read notes/hypotheses.md.',
                  'Do not replace an unproved model instance by an extra premise supplying its conclusion.',
                  'If a prerequisite is missing, preserve your checkpoint and report that dependency.']
        return '\n'.join(lines) + '\n'
