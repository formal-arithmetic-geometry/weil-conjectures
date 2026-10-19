## What changed

Proved `AlgebraicGeometry.Etale.openImmersion_higherDirectImages_constructible_vanishing`
in `Sheaf.AlgebraicGeometry.OpenImmersionHigherDirectImages`, with its full existing signature
and all three public imports unchanged. Converted constructibility with the existing comparison,
proved that F[0] is bounded constructible with interval [0,0], and applied the assigned
finite-coefficient open-image corollary. Its upper interval endpoint supplies eventual vanishing.
The source library already proves the support clause of this very blueprint theorem as
`isZero_upperStar_homology_rightDerivedLowerStar_singleFunctor`; apply it at q>0.
The finite-coefficient engine required by the unit route remains used.

Updated the node's proof, proof dependencies and proof origin to describe this implementation.
No definitions, existing theorem signatures, consumers, or target statements changed.
The complete module compiled through lcompile.py in 10.0 seconds without diagnostics.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Etale.openImmersion_higherDirectImages_constructible_vanishing`
(node `thm-fin-open-immersion`). Proved 1 of 1 original sorries; 0 remain in the delivered module.
Added 0 holes, split off 0 statements, and introduced 0 declarations.
This is a proof from existing library declarations, with their existing upstream dependencies.

## No longer needed

Removed these proof-only imports:

- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.OpenImmersionRestriction`
- `Sheaf.Paper.SfCommonStageWeilCohomology`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

The retired bounded-constructible wrapper is replaced by its source-library module.
Added proof-only imports of the constructibility comparison and source finiteness module.
The following planned nodes are not needed as separate dependencies of this proof:
`lem-kun-open-immersion-restriction`, `prop-weil-pbc-inverse-image-modules-exact`,
and `def-weil-derived-cohomology-sheaves`. The source support clause works directly with
ModuleCat-valued sheaves, the fully faithful open pushforward and the exact upperStar API;
it does not use the unfinished Leray clause or transport through SheafOfModules.
Cohomology is the existing DerivedCategory.homologyFunctor, and no common-stage Weil
cohomology construction is used. Removed obsolete top-level tool approvals for
`lem-kun-open-immersion-restriction` and `prop-weil-pbc-inverse-image-modules-exact`.
The finite-coefficient open-image corollary stays used, and no unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan predates the source library's proved support clause of this exact blueprint
node. Reusing it replaces the unfinished abelian restriction/Leray package and the much larger
module-transport theorem, while following the same K-injective counit and exactness argument.
The cohomology dependency's current primary attachment is a common-stage Weil construction,
which is irrelevant to this ordinary small-etale derived-category statement; the standard
Mathlib cohomology functor is already present. No mathematical statement was changed.

The case q=0 is deliberately excluded only in the restriction clause; constructibility is proved
for every integer q. The proof applies also to the zero sheaf, zero coefficient ring and empty
schemes: it never chooses a point or assumes a nonzero coefficient. No new edge-case-sensitive
lemma was introduced.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
