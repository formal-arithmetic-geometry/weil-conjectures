## What changed

Replaced the proof of `Scheme.isClosedImmersion_specMap_tensor_functionField`
with the geometric pullback reduction: the spectrum of the canonical tensor
lift is a base change of the diagonal, which is closed by separatedness.
Mathlib's `MorphismProperty.of_isPullback` proves the conclusion.
All existing signatures, docstrings, definitions, and public imports are unchanged.
`surjective_of_isClosedImmersion_specMap` was already proved and is unchanged.

The first worker's new `SeparatedAffineFunctionFieldSurjectiveCoreAux` module
and `Scheme.tensor_functionField_surjective_aux` were removed. Their surjectivity
statement duplicated `Scheme.separated_affine_functionField_surjective` in the
parent module, and their node cited the item itself as a proof dependency.
Replaced them with `Sheaf.AlgebraicGeometry.AffineLocalFunctionFieldDiagonalPullback`,
imported privately for the proof. Its statement uses no separatedness assumption
and asserts the explicit cartesian square before the closedness step.
Updated the item's node to record this actual route.

## Proved and sorry left

Hole closed (conditionally on the geometric lemma):
`AlgebraicGeometry.Scheme.isClosedImmersion_specMap_tensor_functionField`.
Hole added:
`AlgebraicGeometry.Scheme.isPullback_affine_local_functionField_diagonal`, node
`lem-sc-affine-local-function-field-diagonal-pullback`.
This is a decomposition: one original hole closed, one lower geometric hole
added, net zero holes. It is not a completed axiom-free proof of the item.
The existing `AlgebraicGeometry.surjective_of_isClosedImmersion_specMap` proof
was retained, not counted as a newly closed hole.
There are no other delivered holes and no data definitions.

Both delivered modules compile without warnings through `lcompile.py --all`.
A scratch-copy `#print axioms` check gives only `propext`, `Classical.choice`,
and `Quot.sound` for `surjective_of_isClosedImmersion_specMap`; the parent theorem
and geometric lemma additionally use `sorryAx`, exactly because of that named hole.

## No longer needed

Removed the first worker's proof-only import
`Sheaf.AlgebraicGeometry.SeparatedAffineFunctionFieldSurjectiveCoreAux`, its
undelivered module, and node
`lem-sc-separated-affine-function-field-surjective-core-aux`.
Removed the item's old proof-dependency edge to
`lem-sc-separated-affine-function-field-surjective`: that is the caller, whose
proof itself uses this item. It is still needed above this item and is not a
pruned module or globally unnecessary node.
No original imports were removed; they expose notions in the unchanged signatures.
No existing library module is claimed pruned. The new geometric module's imports
supply function fields, stalk morphisms, products/pullbacks and tensor maps;
a redundant direct tensor-maps import was removed after recompiling.

## Where the brief, the DAG or earlier work was wrong

The first worker's claimed strict intermediate was an equivalent affine
closed-immersion criterion and duplicated the caller's surjectivity theorem.
Its node depended on the statement it purported to help prove; it also lacked
a complete natural-language proof of the geometric identification.
The original item node likewise cited its caller as its proof dependency.
The revised item depends on the geometric pullback identity and the existing
closed-immersion base-change leaf, with no such proof cycle.

The source was read at https://stacks.math.columbia.edu/tag/09NB because the
local `literature/stacks-project/varieties.tex` is absent on this machine.
Its opening paragraph identifies the open pullback with Spec K; the next
paragraph separately invokes separatedness. The revision follows those steps.
The existing local-domain localization lemma and canonical local-scheme lemma
are tools for the remaining geometry; affine-spectrum and open-immersion
base-change facts are already Mathlib leaves. No unit route was replaced.

## New nodes

`lem-sc-affine-local-function-field-diagonal-pullback`, in
`dag/nodes/sec-curve-estimates/lem-sc-affine-local-function-field-diagonal-pullback.json`,
states the explicit diagonal square for an integral scheme, a nonempty affine
open, and a Noetherian dimension-one stalk outside the open. It is the
geometric part of the 09NB argument before separatedness. Its docstring and
node give the prime-chain argument, principal localization identification,
canonical projections, and cartesian diagonal square. LeanFinder, Loogle,
LeanSearch and grep were actually run with `msearch.py`; LeanSearch was
unavailable (HTTP 500), the other searches found no exact statement.
No statement-change record is needed because all existing signatures are unchanged.

## Second reading by T2

1. PASS: diffed the delivered item against the repository. Both existing theorem
   signatures are byte-for-byte unchanged, as are their docstrings and the
   existing second proof. Only the first proof and a proof-only import changed. No target or existing definition changed.
2. PASS for a decomposition: both delivered files compile without warnings.
   Inspected every delivered declaration and searched for forbidden mechanisms.
   The sole sorry is the named geometric theorem. The scratch axiom check gives
   only the three standard axioms and, where that open theorem is used, sorryAx.
   There is no data construction from an unproved existence statement.
3. REPAIRED: refused the original split as an equivalent restatement and duplicate
   of the caller. The replacement is the cartesian geometric square without
   separatedness; closedness is proved separately in the item. Checked the
   dimension-one prime calculation and the example X = Spec k[t], U = D(t),
   x = (t), where B[1/t] = k(t). Empty U is excluded by Nonempty; a generic
   point x cannot meet the dimension-one hypothesis. For nonseparated integral
   schemes the geometric identity still holds while the closedness conclusion
   need not hold, confirming that this is a distinct part of the argument.
   Searched Mathlib, lean/Sheaf and lean/WeilConjectures by fibre-product,
   stalk and function-field concepts. The remaining result is not a duplicate.
4. PASS after repair: used Mathlib's closed-immersion base-change theorem directly.
   The remaining geometric calculation is not a few-minute proof from an exact
   available lemma. Removed the duplicate auxiliary and redundant import.
   Checked dag/units/sk-thm-curveestimate.json: realized.statement remains
   thm-sc-proper-cohomology and realized.steps is empty; this subordinate 09NB
   route is retained. No unit realization or chapter route changed.
5. REPAIRED: supplied the modified original node and the new geometric node.
   The original proof_deps now match the geometric reduction and base change;
   the new node's proof_deps are precisely the union of its step uses. Checked
   all referenced nodes exist, the verbatim Lean signature, source, searches,
   created fields, chapter, unit, blueprint provenance and proof_origin.

Second reading changed: replaced the duplicate surjectivity auxiliary with the
explicit geometric pullback lemma; simplified the parent to diagonal base change;
repaired circular DAG bookkeeping; corrected hole accounting and the report.
