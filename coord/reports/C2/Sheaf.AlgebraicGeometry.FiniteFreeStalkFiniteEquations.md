## What changed

Proved AlgebraicGeometry.Scheme.Modules.exists_shrink_finite_free_map_eq in
Sheaf.AlgebraicGeometry.FiniteFreeStalkFiniteEquations without changing its signature.
Added the proof-only import Sheaf.AlgebraicGeometry.FiniteFreeStalkMapEquality and the
proved private helper restrict_eq_trans. The proof is finite-set induction: zero sources
and targets need no shrinking; free sources use the existing single-map neighbourhood
lemma; naturality of the restriction-composition isomorphism propagates earlier equalities.
Updated the item's docstring and DAG proof, proof_deps, and proof_origin to this route.
The unit record has no realized nodes here; no unit statement or step is bypassed.
The final single-file compile passes without warnings.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.Scheme.Modules.exists_shrink_finite_free_map_eq
(node lem-pc-finite-free-stalk-finite-equations).
Proved the private helper restrict_eq_trans. No holes remain in the delivered module,
and no holes or modules were added. The proof uses the already-stated theorem
AlgebraicGeometry.Scheme.Modules.exists_restrict_eq_of_pullback_eq
(node lem-pc-finite-free-stalk-map-eq-shrink), which still contains sorry in the existing
module Sheaf.AlgebraicGeometry.FiniteFreeStalkMapEquality; this delivery does not prove it.
Thus this closes an upper hole from an existing lower statement, not the entire closure.

## No longer needed

No imports were removed, and no existing modules or nodes are claimed globally pruned.
The planned freeMatrix_pullback calculation, coefficient germ comparisons and finite
matrix-entry intersections are not needed in this module. The finite-generator local
equality argument is delegated to the existing single-map theorem, with arbitrary target.
The definitions def-pc-module-pullback and def-weil-pbc-free-module cease to be direct
proof_deps of this node, but remain statement dependencies and dependencies of the
single-map lemma; they must not be removed from the project.

## Where the brief, the DAG or earlier work was wrong

The original plan named only definition nodes, although it required substantial map
and germ theory. The library already has the strictly smaller single-map local equality
statement needed here. Its module can be imported without a cycle (import_direction.py
returned yes). No statement error was found. Empty indexing types use U; zero sources
or targets are handled by morphism uniqueness; rank zero is allowed by the imported lemma.
Searches: leanfinder returned hom_ext_iff, hom_ext and elementwise stalk ingredients,
not this neighbourhood theorem; loogle found IsZero; rg of both library roots located
FiniteFreeStalkMapEquality and freeMatrix_pullback. Read the existing lemma and its node.
The source blueprint file cited by the node is not installed in this clone; the existing
node and lemma docstrings provide the finite germ argument followed here.

## Second reading by C2

1. **Diff and interfaces.** Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only the proof, proof-only import, and documentation changed. The DAG node records the same statement and the actual proof dependency.

2. **Compilation and axioms.** Compiled the module with `lcompile.py`; it passes without errors or warnings. The module contains no `sorry`, axiom, unsafe, opaque, extern, or implemented_by declaration. The imported single-map theorem remains an explicitly documented open lower node, as reported.

3. **Statements and split-offs.** No new public statements or split-off holes were added. The private restriction-transitivity helper is an implementation lemma, and the finite-family theorem is exactly the existing target statement. The zero-object and empty-index cases are handled directly, and the finite-free source case delegates to the existing theorem without weakening hypotheses or conclusions.

4. **Route and pruning.** The proof uses finite-set induction and `exists_restrict_eq_of_pullback_eq`, then transports prior equalities through the restriction-composition isomorphism. This is shorter than the planned matrix expansion and preserves the unit route; no imports were removable beyond the proof-only import already added, and no realized unit node is bypassed.

5. **DAG agreement.** The node's `proof`, `proof_deps`, and `proof_origin` agree with the Lean proof and identify the existing lower theorem. No statement or definition change record is needed.

Changed in this second reading: no Lean proof or statement changes were necessary; this report section records the checks above.
