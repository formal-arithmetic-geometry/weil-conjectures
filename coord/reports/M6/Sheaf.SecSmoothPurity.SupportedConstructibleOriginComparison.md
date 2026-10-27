## What changed

Filled `AlgebraicGeometry.ProEtale.SupportedConstructibleOriginComparison.supported_constructible_origin_comparison` without changing its statement. On each stratum, `Scheme.finite_models_of_fixed_lisse` converts local constancy and finite geometric stalks to finite constant models. Existing fixed-module sheaf descent and `DerivedCategory.boundedConstructible_of_homology` then supply the bounded constructible etale origin. The existing etale constructibility equivalence translates the cohomology predicate. Both extension bounds follow directly from `Functor.bounded_mapDerivedCategory_obj`, applied to the original bounds.

Replaced the four unused private proof imports with the three modules containing these declarations. Updated the existing node's proof, proof dependencies and proof origin to record the actual fixed-module route. Reused `comparisonUpperStarConstantSheafIso A T` in `constantModuleComparison` with its original signature and irreducibility attribute. Its adjunction construction is identical to the previous expanded body (terminal-object witnesses are unique), so the constant-section normalization is preserved. Added its public import, `WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf`. The other three canonical comparison definitions stay verbatim. The change record is `coord/changes/supported-origin-constant-comparison-reuse.md`. No downstream consumer needs adaptation.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.ProEtale.SupportedConstructibleOriginComparison.supported_constructible_origin_comparison` (node `lem-sp-supported-constructible-origin-comparison`). Added 0 holes; 0 split off; no sorry remains in the delivered module. Existing imported declarations retain their own independent proof obligations.

## No longer needed

Removed private imports:

- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`: the fixed-module descent theorem avoids transporting through the intrinsic constant-ring realization and its coefficient-universe restriction. The corresponding direct dependency `lem-weil-pbc-finite-ring-constructible-derived-origin` is replaced by the already recorded finite-model, fixed-module sheaf-origin, bounded-origin and etale constructibility-comparison nodes.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`: exactness instances are already available from the public comparison imports. Its node remains relevant to the canonical comparison definitions, but this extra import is unnecessary.
- `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`: the definition of tensorComparison already uses the exact fixed-module derived comparison. No general ringed-topos transport or K-flat computation is required here. Removed the direct dependency `lem-weil-pbc-ringed-topoi-derived-pullback`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`: the existing source-library canonical unbounded tensor comparison already constructs the required factor. Removed the direct dependency `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`; the derived tensor definition nodes record the existing fixed-module API.

These dependencies are pruned from this module's direct proof route only; no declaration or module is withdrawn. No unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned first step used an intrinsic ringed-coefficient origin theorem stated for coefficients `ULift B` with `B : Type u`, while this theorem permits arbitrary finite `A : Type (u + 1)`. The already proved fixed-module descent theorem works directly in the required universe and avoids that conversion. The planned general ringed-topos tensor constructions had already been supplied by the module's explicit source-library comparison definitions, so their private imports were redundant.

The bounds for every origin use only the boundedness of L and M. No constructibility, chosen origin isomorphism, flatness, finite Tor amplitude, noetherian scheme assumption, or boundedness of the coefficient tensor is required for this part. The proof includes the empty scheme, zero complex and zero ring cases because the applied declarations impose no exclusions.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
