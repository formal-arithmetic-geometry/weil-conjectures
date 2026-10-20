## What changed

The item module keeps all six public signatures and all original public imports.
Four proof-only imports supply ordinary bounded-below qcqs coproduct continuity,
the two geometric inputs described below, and triangulated right-derived functors.

The private lemma `properLowerStarHeartHypotheses_of_uniformBound` proves the
coproduct comparison for degree-zero modules from
`condensed_boundedBelow_preservesCoproduct`. This part needs only qcqs, and neither
constructibility nor properness. It combines that proved comparison with the
uniform heart bound to give all three original heart-hypothesis theorems.

The private lemma `bounded_rightDerivedLowerStar_of_uniformBound` uses the
right-derived lower-bound theorem and finite truncation devissage
(`DerivedCategory.isLE_obj_of_isLE_of_homologyProperty`) to prove boundedness of
proper images. The constructible input embeds into its weak Serre coproduct
closure by its universal property. Combining boundedness with proper-image
constructibility proves each of the three original bounded-constructible
statements. No witness of an unproved existence theorem is used to define data.

Two separate geometric results are stated in new modules, with source proofs in
words and DAG nodes. They separate amplitude from constructibility, rather than
renaming any original theorem. The proper case of Bhatt--Scholze Theorem 6.7.1,
Lemma 6.7.2 and Remark 6.8.15 is the source for the Noetherian setting. The source
paper was read, including the distinction between proper pushforward and the
nonproper case requiring quasi-excellence.

Validation: `lcompile.py --all` compiled all three sandbox modules without errors
or warnings. The last observed compile times were 6.5, 6.4 and 8.2 seconds.

## Proved and sorry left

This is a decomposition of six original holes into two strictly partial geometric
inputs, not a claim that all transitive geometric proofs are complete.

The following original declarations now have complete Lean proof bodies and no
local `sorry` (namespace `AlgebraicGeometry.ProEtale.CondensedRing`):

- `boundedConstructible_rightDerivedLowerStar_obj_of_isProper_continuousMapRingObj`
- `properLowerStarHeartHypotheses_continuousMapRingObj`
- `boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicIntegersRingObj`
- `properLowerStarHeartHypotheses_padicIntegersRingObj`
- `boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicAlgClRingObj`
- `properLowerStarHeartHypotheses_padicAlgClRingObj`

Both private helpers are proved. Original holes closed: 6 of 6. New holes added: 2:

- `AlgebraicGeometry.ProEtale.CondensedRing.properLowerStar_uniformBound_ellAdic`,
  node `lem-sfb-noetherian-proper-heart-uniform-bound`, module
  `Sheaf.AlgebraicGeometry.EllAdicProperHeartUniformBound`.
- `AlgebraicGeometry.ProEtale.CondensedRing.properLowerStar_constructible_cohomology_ellAdic`,
  node `lem-sfb-noetherian-proper-constructible-cohomology`, module
  `Sheaf.AlgebraicGeometry.EllAdicProperConstructibleCohomology`.

The first input has no coproduct comparison or constructibility conclusion. The
second input asserts only constructibility of individual cohomology modules and
has no boundedness or uniform-amplitude conclusion. Both are needed. The uniform
bound is shared by all six original results; the constructibility input is shared
by the three bounded-constructible results. The packet has exactly two direct
`sorry`s, both named public theorems with source proofs in their docstrings.
The syntactic net is four holes closed; the pinned ledger determines the actual
net in the targets' import closure.

## No longer needed

No original public import was removed. The proof uses
`Sheaf.AlgebraicGeometry.EllAdicProperBoundedBelowCoproducts` directly for coproducts,
so it does not need the planned detour through ind-heart Ext/sum closure:

- `sk-lem-proper-heart-bound` / `Sheaf.Paper.ProperHeartBound` is not directly
  imported: its standing finite-type, separated, positive-characteristic setting
  is too narrow for the original signatures. Its geometric amplitude argument is
  retained as the source plan of the new amplitude input.
- `det-ind-heart-kernels-cokernels` / `Sheaf.Paper.IndHeartKernelsCokernels` is not
  imported by the item's proof.
- `det-ind-heart-extensions` / `Sheaf.Paper.IndConstructibleExtensions` is not
  imported by the item's proof.
- `det-ind-heart-ii-sums` / `Sheaf.Paper.DetIndHeartIISums` is not imported:
  the existing common-lower-bound coproduct theorem already proves the actual
  comparison required here, for arbitrary degree-zero module objects.

These are removals from this item's direct proof route, not assertions that the
modules are unused elsewhere. The geometric amplitude proof still needs the
coherent ind-closure argument, recorded in its new node. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned dependencies do not specialize to the full original signatures.
`ProperHeartBound` assumes positive characteristic and separated finite-type
schemes over k; this item assumes only a Noetherian target with a map to Spec k,
and permits characteristic zero. The input coefficient fields are arbitrary
presentations of finite extensions, not only named finite intermediate fields.
The constant-model constructibility predicates in several planned dependencies
also require comparison with this item's stratified local-finite-presentation
predicate. No missing hypothesis was silently inferred, and no original signature
was strengthened or weakened.

In the current shared snapshot, searching all `dag/nodes` for the item's module or
its six declaration names finds no attached node, and the previously read
`lem-sfb-proper-serre-heart-qbar.json` is absent. Therefore this packet does not
recreate or overwrite an absent existing-node record. The new nodes record the
two actual geometric inputs; the report records the complete combining route.
The original module-level historical text still says all six inputs are sorried;
the public declarations and this report give the actual status of this delivery.

## New nodes

`lem-sfb-noetherian-proper-heart-uniform-bound` isolates finite upper amplitude
on the weak Serre coproduct closure. Its proof plan first bounds relative fibre
dimensions, then uses torsion proper cohomological dimension and the integral
Milnor estimate, followed by rational coefficient change and qcqs continuity on
ind-constructibles. It keeps the Noetherian hypothesis and characteristic-zero
case of the original item. The bound is independent of the input module.

`lem-sfb-noetherian-proper-constructible-cohomology` isolates proper-image
constructibility without asserting amplitude. Its proof plan uses torsion
finiteness, derived completeness, coefficient descent/localization, then bounded
truncation devissage and constructible Serre closure. It is independent of the
uniform bound and is genuinely the constructibility clause of proper finiteness.

No existing statement, definition or visible interface changed, so there are no
change records and no forced consumer adaptations.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
