# AlgebraicGeometry.affine_open_localized_tensor_exact

## Reason

Restore the three-module quarantine cluster after upstream sync 5f7b33eac.
The recorded root error is an import collision: the environment already contains
AlgebraicGeometry.schemeDerivedTensorCohomologyVanishes from the Sheaf twin when
WeilConjectures.AlgebraicGeometry.DerivedTensorCohomologyVanishes is imported by
AffineTorAmplitudeCriterion. Use the upstream definition consistently on this path.
No adopted source-library file is changed.

## Old

In AffineOpenLocalizedTensorExact, PrincipalLocalizationSheafTorBounds and
PrincipalLocalizationRestrictionModel, the public statement dependency was:

```lean
public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
```

PrincipalLocalizationSheafTorBounds used this private proof dependency:

```lean
import Sheaf.AlgebraicGeometry.OpenImmersionTensorVanishing
```

Its proof called openImmersion_tensor_vanishing with an exact functor naturally
isomorphic to open restriction.

## New

All three files use the adopted upstream definition:

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedTensorCohomologyVanishes
```

PrincipalLocalizationSheafTorBounds uses these private proof imports:

```lean
import WeilConjectures.AlgebraicGeometry.OpenImmersionTensorVanishingTest
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
```

Its proof applies openImmersion_tensor_vanishing_test to the direct image of the
test sheaf. It transports the representing isomorphism to the exact functor R
using mapDerivedCategoryNatIso, then composes with the existing localization
comparison. The K-flat representative and homology-vanishing proof are retained.
Finite-limit preservation of open restriction is transported from R by
preservesFiniteLimits_of_natIso.

All declaration signatures remain textually identical. The two vanishing
predicates have the same construction: the only difference is the K-flat
predicate name, IsAcyclicTensorKFlat versus upstream IsKFlatTensor; their bodies
are identical. Thus hypotheses and conclusions retain their mathematical meaning.
The changed public imports expose the upstream API in place of the duplicate
Sheaf API. No target text or definition body changes.

## Users

The downstream.py declaration-use and downstream checks report only
PrincipalLocalizationSheafTorBounds as an active consumer of
PrincipalLocalizationRestrictionModel, and no active consumers of
PrincipalLocalizationSheafTorBounds. The quarantine source search adds the root
and its two consumers listed below. No other active or quarantined module imports
either changed dependency. All five files compile together in dependency order.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PrincipalLocalizationRestrictionModel | unclaimed | Public import selects the upstream vanishing definition; statement and existing proof hole unchanged. |
| Sheaf.AlgebraicGeometry.PrincipalLocalizationSheafTorBounds | unclaimed | Public import selects the same definition; proof uses the upstream open-immersion test. |
| Sheaf.AlgebraicGeometry.AffineOpenLocalizedTensorExact | F5 | Root restored with the canonical public import; theorem proof unchanged. |
| Sheaf.AlgebraicGeometry.AffineTruncationKernelFlat | unclaimed | Quarantined consumer restored verbatim and compiled. |
| Sheaf.AlgebraicGeometry.AffineTruncationKernelFiniteLocallyFree | unclaimed | Quarantined consumer restored verbatim and compiled. |

## Status

landed 20261020T145507-L-2401800 2026-10-20 (merge of deliver/F5/Sheaf.AlgebraicGeometry.AffineOpenLocalizedTensorExact)
