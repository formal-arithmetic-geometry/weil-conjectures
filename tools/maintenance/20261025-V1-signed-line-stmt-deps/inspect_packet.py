"""Read the retained V1 packet and check its repaired dependency against current main."""
import hashlib
import json
import os
from pathlib import Path
import sys

repo = Path(os.environ.get("SHEAF_REPO", "/home/ubuntu/weil-conjectures-sheaf-shared"))
sb = Path(os.environ.get("SHEAF_SANDBOX", "/home/ubuntu/weil-sandbox/V1/"
                       "Sheaf.Algebra.Homology.SignedLineDerivedBaseChange"))
sys.path.insert(0, str(repo / "tools"))
import stage2_delivery as s2
import stage3_delivery as s3

git = s2.Git(repo)
commit = git.run("rev-parse", "HEAD")
base = s2.nodes_at(git, commit)
nodes = {}
for p in sorted(sb.glob("dag/nodes/*/*.json")):
    d = json.loads(p.read_text())
    nodes[d["id"]] = {"node": d, "base_node": base.get(d["id"]),
                       "path": str(p.relative_to(sb)),
                       "role": "changed" if d["id"] in base else "new"}

nid = "lem-pur-signed-line-derived-base-change"
owner = "def-pur-signed-line-derived-action-data"
replacement = "lem-pur-normalized-signed-line-pullback-exists"
old = "lem-pur-signed-line-pullback-existence"
item = nodes[nid]["node"]
assert item["statement"] == base[nid]["statement"]
assert owner in item["stmt_deps"] and owner in nodes
assert replacement in base and replacement in item["proof_deps"]
assert replacement in item["proof"][1]["uses"]
assert old not in nodes and old not in item["proof_deps"]
assert not (sb / "lean/Sheaf/Algebra/Homology/SignedLinePullbackExistence.lean").exists()
source = sb / "lean/Sheaf/Algebra/Homology/SignedLineDerivedBaseChange.lean"
text = source.read_text()
assert "import Sheaf.Paper.SignedLinePullbackExistence" in text
assert "exists_signedLinePullbackNormalized _hcover a P Q _hP t" in text
findings = s3.edge_fails({"nodes": nodes}, base)
assert not findings, findings
print(json.dumps({
    "base": commit,
    "statement_unchanged": True,
    "required_stmt_dep_present": owner,
    "replacement_proof_dep_present": replacement,
    "duplicate_files_absent": True,
    "lean_modules": len(list((sb / "lean").rglob("*.lean"))),
    "new_nodes": sum(n["role"] == "new" for n in nodes.values()),
    "dependency_findings": findings,
    "item_source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
}, indent=2))
