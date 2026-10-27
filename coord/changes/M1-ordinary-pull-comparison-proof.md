# CategoryTheory.ConstantCompletion.ordinaryPullComparison_existsUnique

## Reason

Complete the ordinary scalar-insertion comparison and prune imports inherited from
its former combined module. All declarations added are proved private helpers.
Local transparency commands are only for their proofs; existing public declaration
signatures and data definitions are unchanged. No target interpretation changes.

## Old

The import header was:

```lean
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Sheaf.Paper.FlatRingedIdealCompleteEquivalence
public import Sheaf.CategoryTheory.RingedKoszulSystem
public import Sheaf.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Sheaf.Paper.RingedSiteIdeal
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Sites.Over
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Sheaf.Algebra.Homology.FlatScalarRestrictionKFlat
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Finiteness.Defs
import Sheaf.Paper.RingedTopoiTensorSections
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
import all Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Adjunction.Additive
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Sheaf.Paper.ConstantCompletionInverseImage
```

The theorem had its current unchanged signature and proof `by sorry`.

## New

The import header is:

```lean
public import Sheaf.Paper.ConstantCompletionInverseImage
import Sheaf.Paper.RingedTopoiTensorSections
import all Sheaf.Paper.ConstantCompletionCore
import all Sheaf.Paper.RingedCoefficientPullbackComparison
import all Sheaf.CategoryTheory.GeometricModuleTransport
```

The theorem now has a complete proof via the scalar-extension adjunction. All
former public imports are public imports of `ConstantCompletionInverseImage`
itself, so the public transitive import closure is identical. Added proof imports
are private. Additional local transparency commands expose `completed` only while
checking the finite-projection square and expose `pull` and `change` only for
ordinary adjunction computations. The extra section context and all private
helpers have no effect on consumers.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantCompletionOrdinaryPullComparison | M1 | Completes the sole proof; no signature or data change. |
| Sheaf.Paper.ConstantCompletionDerivedPull | unclaimed in shared snapshot | Sole direct importer; public import closure and theorem type preserved; no adaptation. |

No existing module is adapted.

## Status

landed 20261027T180706-L-3891770 2026-10-27 (merge of deliver/M1/Sheaf.Paper.ConstantCompletionOrdinaryPullComparison)
