# AlgebraicGeometry.Scheme.finite_pullback_localization_cohomology

## Reason

Remove imports unused by the completed proof and by its unchanged public statements.
The existing exactness of intrinsic finite pullback transfers along the normalized
module isomorphism, so no separate slice exactness theorem is required. The intrinsic
derived pullback is already termwise descent, and the existing source-library API
supplies the derived comparison and its cohomology normalization.

## Old

```lean
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
```

## New

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
public import Sheaf.NumberTheory.Padics.CoefficientExtension
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
```

The structure, theorem signature, visibility, attributes and existing file options
are unchanged. Three proved private coefficient compatibility lemmas implement the
unit and counit scalar equations for the site adjunction. They reproduce the needed
private calculations in ProEtaleObjectInverseImageRestriction without changing that
module's public interface. No target statement or underlying definition changes.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.FinitePullbackLocalizationCohomology
--uses ProEtaleFiniteLocalizationComparison finite_pullback_localization_cohomology`
reports zero downstream modules and only the declarations in this item as text users.
The DAG parent remains needed; this delivery proves, rather than withdraws, the item.
No consumer adaptations are required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FinitePullbackLocalizationCohomology | V7 | Complete proof; unchanged public signatures; remove unused imports. |

## Status

landed 20261021T140939-L-2778401 2026-10-21 (merge of deliver/V7/Sheaf.AlgebraicGeometry.FinitePullbackLocalizationCohomology)
