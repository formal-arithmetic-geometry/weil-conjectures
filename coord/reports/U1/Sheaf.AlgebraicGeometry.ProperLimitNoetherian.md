## What changed

The target module now assembles `AlgebraicGeometry.exists_proper_limit_noetherian` from
`exists_proper_limit_noetherian_core` and `proper_limit_noetherian_affine_clause` in
`ProperLimitNoetherianCore.lean`. The target signature and all existing declarations are
unchanged. The core import is proof-only and remains a plain `import`.

## Proved and sorry left

The target theorem `AlgebraicGeometry.exists_proper_limit_noetherian` is proved. The two
strictly smaller construction statements remain named `sorry`s:
`AlgebraicGeometry.exists_proper_limit_noetherian_core` (node
`lem-weil-pbc-proper-limit-noetherian-core`) and
`AlgebraicGeometry.proper_limit_noetherian_affine_clause` (node
`lem-weil-pbc-proper-limit-noetherian-affine-clause`).

## No longer needed

The old direct proof dependencies are no longer used by the target proof: `lem-weil-pbc-proper-closed-in-proper-fp`, `prop-nagata-noetherian-inverse-system`, `def-nagata-noetherian-inverse-system`, `lem-weil-pbc-cofiltered-limit-directed-reindex`, `def-weil-finite-type-morphism`, `pqf-def-affine-morphism`, `lem-weil-pbc-limit-affine-transition`, `lemma-nagata-noetherian-inverse-system-affine`, `thm-pd-spreading-out`, `def-pc-fibre-product`, `lem-weil-pbc-eventually-proper`, `lem-weil-pbc-colimit-initial-full-subcategory`, `lem-weil-pbc-proper-base-change`, `lem-weil-pbc-scheme-image-qc-kernel`, `lem-weil-pbc-closed-immersion-proper`, `lem-weil-pbc-closed-immersion-from-composite`, `lem-weil-pbc-spec-colimit-limit`, and `def-weil-pbc-category-colimit`. They are replaced in the item's DAG proof dependencies by the two split nodes.

## Where the brief, the DAG or earlier work was wrong

The original nine-step geometric route has no Lean declarations for its central construction.
The reduction therefore leaves the missing mathematics in two named, strictly smaller
statements and proves the target by their composition. No target statement or definition was
changed.

## Second reading by U1

1. Diff check: the target signature is byte-for-byte unchanged; only its proof and the
proof-only core module import are present, and the new core module is added.
2. Both files compile with `lcompile.py`; the only remaining `sorry`s are the two named
split-off theorems, with no hollow definitions or forbidden declarations.
3. The split statements are proper subclaims: the core theorem supplies the common inverse
system, while the affine clause supplies only the affine-base conclusion after that system is
fixed. Their docstrings cite Tag 0A0P and describe the omitted mathematical arguments; each
has a matching DAG node.
4. The proof uses the shortest available route in Lean (the two imported split declarations);
all former direct dependencies are pruned from the item node. No shorter library declaration
was found, and the target is not a realized statement or step of the unit.
5. The item node's `proof`, `proof_deps`, and `proof_origin` now match the Lean proof, and the
unit metadata remains unchanged.

Changed during this second reading: synchronized the item DAG proof metadata and replaced the
minimal earlier report with the required five-point review record.

## New nodes

`lem-weil-pbc-proper-limit-noetherian-core` and
`lem-weil-pbc-proper-limit-noetherian-affine-clause` are the two named split statements in
`lean/Sheaf/AlgebraicGeometry/ProperLimitNoetherianCore.lean`; their node files are in
`dag/nodes/sec-proper-base-change/`.
