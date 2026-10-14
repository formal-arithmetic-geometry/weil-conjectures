## What changed

Implemented the change-of-resolution argument in
`AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.moduleCohomologyExtResolutionEquiv_normalization`.
The module comparison square follows from Mathlib derived-resolution naturality and exact-forgetting
homology naturality. The inverse abelian comparison square follows from
`CategoryTheory.acyclicComparison_naturality` and `forgottenInjectiveAcyclic`.
The identity is lifted from the supplied resolution to the standard resolution. Composing the two
squares transports the standard computation to the supplied resolution; the final inverse-hom
identity proves the asserted normalization. Existing signatures and definitions are unchanged.

Added a proof-only import of `Sheaf.AlgebraicGeometry.ModuleCohomologyExtStandardResolutionFormula`.
That module isolates the computation on the chosen standard resolution. It asserts only the
explicit evaluation of the fixed comparison, with no arbitrary-resolution naturality assertion.
Its supplied quasi-isomorphism hypothesis is proved in the normalization module from exact
forgetting. Updated both DAG proof records to reflect this route.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.moduleCohomologyExtResolutionEquiv_normalization`.
The official delivery dry run successfully compiled the complete original sandbox proof.
The private helpers `moduleResolutionIso_naturality` and `abelianResolutionIso_inv_naturality`
prove the two comparison squares; neither has a hole.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.standard_resolution_formula`
(node `new-module-cohomology-ext-standard-resolution-formula`).
It computes only the selected standard resolution and is strictly a part of the argument.
This is a decomposition: one upper hole closed, one lower hole added, net zero holes.
There are no holes left in the item's module and no changes to data definitions.

## No longer needed

No pre-existing imports, DAG nodes or modules were pruned. The second reader removed the
redundant public import of
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian` from the new standard-formula
module; that module compiles without it. The original proof's separate proof that
the section homology map is invertible is unnecessary: the two inverse comparison squares
compose directly. No homotopy-equivalence or extra cancellation module is imported.
The blueprint unit's statement and steps remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the statement or its dependencies was found. The original DAG's
invertibility/cancellation subargument can be omitted by lifting in the opposite direction and
working with inverse comparisons. Generic Mathlib application lemmas exist, but the direct
standard-resolution computation required more Lean glue than the time allowed. The delivered
standard formula has a complete proof in words and a node, rather than an anonymous hole.

## New nodes

`new-module-cohomology-ext-standard-resolution-formula`, in
`dag/nodes/sec-proper-base-change/new-module-cohomology-ext-standard-resolution-formula.json`,
is realized by `Sheaf.AlgebraicGeometry.ModuleCohomologyExtStandardResolutionFormula` and
`AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.standard_resolution_formula`.
It evaluates the fixed equivalence only when the supplied resolution equals Mathlib's standard
resolution. The arbitrary-resolution transport is proved separately in the original module.
No change records or forced adaptations are needed.

## Earlier second reading (a previous round; superseded)

1. Compared the full normalization-module diff and the parsed declarations against the repository.
   All five existing signatures are byte for byte unchanged; both abbreviations and both
   isomorphism definitions are unchanged. No target, definition, visibility or hypothesis changes,
   and no change record or forced adaptation is needed. Verdict: pass.
2. The new standard-formula module compiles without its redundant public import. Its explicit
   `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound` and the expected
   `sorryAx`. Text inspection finds exactly one hole, in the public named theorem
   `AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.standard_resolution_formula`; no forbidden
   declarations or hollow definitions. The official delivery dry run successfully compiled both
   delivery modules in import order; the original sandbox proof was retained. Earlier single-file
   runs timed out, and experimental alternative proofs exposed transparency mismatches, but none
   of those variants was adopted. Public statements, definitions and helper proofs remain as the
   worker wrote them. The delivery tool runs its complete axiom probe before accepting the set.
   The complete axiom probe and preflight passed in the official dry run (commit a4f5877a48).
   Verdict: pass.
3. Read the standard formula against the constructed equivalence. Substituting the resolution and
   isomorphism equations leaves the same composite of inverse maps, including the Ext source
   precomposition. Degree zero, the zero module and the empty scheme require no additional
   hypothesis; proof irrelevance handles the supplied quasi-isomorphism proof. This is the fixed
   resolution computation alone, strictly smaller than arbitrary-resolution normalization, with
   a complete docstring argument and matching node. Repeated searches using Loogle
   `"Iso.trans_inv"`, LeanFinder's inverse-composite evaluation query and Mathlib grep for
   `symm_trans_apply|toAddCommGrpIso.*inv|trans_inv`, plus project-source searches, found generic
   evaluation lemmas but no duplicate project formula. Direct unfolding attempts reached Lean's
   heartbeat limit, so this remains the one split-off statement. Verdict: pass.
4. Checked the top-down reduction: Mathlib resolution naturality and exact-forgetting homology
   naturality give the first square; the existing acyclic-comparison theorem gives the second;
   composing their inverse forms reduces to the fixed-resolution computation. No artificial
   restatement, unnecessary homotopy-equivalence proof or cancellation dependency is introduced.
   Checked `dag/units/sk-thm-p1.json` and its `realized` routes: this changes only a lower tool
   argument and preserves every unit step. All four original proof dependencies remain used;
   no pre-existing import or node is pruned. Verdict: pass.
5. Compared both nodes' proofs, dependency unions, proof origins and Lean statement records with
   the code. Restored the direct construction dependency
   `new-module-cohomology-ext-resolution-naturality` in the normalization node's last step and
   `proof_deps`, alongside the new computation dependency. The new node has its source, searches,
   creation record, blueprint origin, chapter, unit and verbatim Lean statement. Verdict: pass.

Changes by the second reader: corrected the normalization docstring to describe the actual lift
from I to the standard resolution and direct composition of inverse comparisons; restored the
construction dependency in the DAG; removed the new module's redundant public import.

Final verification status: the official delivery dry run printed OK at commit a4f5877a48:
both modules compiled, the complete axiom probe ran, and preflight passed. Experimental variants remain
in scratchpad and are excluded from delivery. The adopted changes are the corrected docstring,
restored DAG dependency and removed redundant import.

## Second reading by D2

1. Compared the delivered normalization module with the repository version. Existing declaration signatures and definitions are unchanged; only the proof, its proof-only import, and explanatory docstring changed. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. The normalization theorem is closed; the only remaining `sorry` is the named public theorem `standard_resolution_formula`, with its matching DAG node and proof docstring. No forbidden declarations or hollow definitions occur. Verdict: pass.
3. Checked the split-off standard-resolution formula against the explicit construction. It is the fixed-resolution computation, strictly smaller than arbitrary-resolution naturality, and its hypotheses are exactly the supplied defining equations. Verdict: pass.
4. Checked the proof route and pruning. The proof uses the stated naturality, acyclic-comparison, and standard-formula dependencies, while avoiding an unnecessary invertibility/cancellation argument. The unit route and realized steps remain intact. Verdict: pass.
5. Checked both DAG records against the Lean declarations, including proof steps, dependencies, origins, and the new node metadata. Verdict: pass.

Changed only the normalization proof/docstring, added the proof-only standard-formula import, and retained the single named split-off theorem and node. No additional pruning or statement changes were made.
