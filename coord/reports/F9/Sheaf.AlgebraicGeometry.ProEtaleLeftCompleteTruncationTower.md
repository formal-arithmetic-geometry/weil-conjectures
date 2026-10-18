## What changed

Proved `AlgebraicGeometry.Scheme.ProEt.truncation_tower_cohomology` in
`lean/Sheaf/AlgebraicGeometry/ProEtaleLeftCompleteTruncationTower.lean`, preserving its
signature and the existing three-step proof route. Added the proof-only import
`Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant`.

Mathlib's `CochainComplex.isZero_of_isGE` and `quasiIsoAt_πTruncGE` compute the
cohomology of the truncations. Naturality of `πTruncGE` and cancellation of its
invertible further truncation prove compatibility of the canonical quotient maps.
The transition maps are epic because their targets are zero below the cutoff and
both quotient-induced homology maps are invertible above it. The first conclusion
of the existing `AlgebraicGeometry.ProEtale.milnor_epimorphic` proves that `1-T` is
epic; `isZero_cokernel_of_epi` gives the required Milnor cokernel vanishing.
For the final clause, construct the quotient-map cone with `NatTrans.ofOpSequence`.
At `N = (-q).toNat`, its components are isomorphisms at every later index, so
`Functor.IsEventuallyConstantTo.isLimitOfIsIso` proves it is limiting. The unique
isomorphism to the chosen limit has exactly the required projection formulas.

Read the blueprint statement and proof, the item's node and unit, the recorded
proof dependencies, and Stacks Tag 0118 in `literature/stacks-project/homology.tex`.
Searches used msearch leanfinder (truncation cohomology and eventually constant
limits), loogle (`CochainComplex.πTruncGE`), msearch grep
(`IsEventuallyConstantTo|quasiIsoAt_πTruncGE|isZero_of_isGE`), and local rg over
Mathlib and both project roots. No full duplicate theorem was found.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.ProEt.truncation_tower_cohomology`
(node `det-pe-left-complete-truncation-tower`). Proved 1 of 1 original sorries;
zero sorries remain in the delivered module, zero added, zero split off.
The proof deliberately uses the existing stated dependency
`AlgebraicGeometry.ProEtale.milnor_epimorphic`, whose proof remains a separate
stage-3 obligation; it is not claimed to have been proved here.

The full proof compiled in 6.6 seconds; the final delivery checks compile and
probe the cleaned file again. Index cases q positive, zero and negative are
handled uniformly by `(-q).toNat`; its defining inequality follows without any
assumption that q is nonpositive. The zero complex and empty scheme need no
special case, and coefficients remain arbitrary ring sheaves in the given
universes.

## No longer needed

None. No imports, nodes or modules are pruned. The proof uses the recorded
truncation and cohomology constructions and `det-pe-milnor-epimorphic` as planned.
No DAG copy is included because the proof follows the existing steps and
`proof_deps` unchanged; the eventual-constancy Mathlib lemma implements the
universal-property argument in step 3.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. No definition, signature, target or consumer changes.
The parent module's pre-existing import direction needs no change for this item.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
