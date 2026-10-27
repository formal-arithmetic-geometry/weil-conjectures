# Sheaf.Paper.RoosIntrinsicUnitComparison public imports and proof context

## Reason

The completed proof uses the normalized completion on slices and primitive strict Roos
quasi-isomorphism results. Remove unused planned proof imports and redundant public imports;
the coefficient-extension unit-route module remains publicly imported through
PrincipalIntrinsicCompletion and PrincipalKoszulStrictReplacement.
The generic categorical identities and local transparency attributes prevent repeated
expansion of chosen limits and derived localization during compilation. The cokernel identity computes the degree-zero Koszul augmentation. The tensor comparison
uses a targeted rewrite on its generator formula. The main proof uses the
individual quotient-tower maps directly, avoiding a redundant functor construction.

The complete existing theorem signature and the quotient unit and augmentation predicate are unchanged.
The quotient tower and comparison have explicit, definitionally equal result types; their
bodies are unchanged. No definition changes its data or meaning. The separate record
`h6-principal-intrinsic-result-types.md` describes the same return-type repair to the
unclaimed principal tower and fiber. No adopted WeilConjectures module changes.

## Old

Original imports, verbatim:

```lean
public import Sheaf.Paper.PrincipalIntrinsicCompletion
public import Sheaf.Paper.IntegralOperationsWellDefined
public import Sheaf.CategoryTheory.StrictRoosComparison
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Paper.PrincipalKoszulStrictReplacement
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.Paper.IntegralScalarExtensionWellDefined
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.IntegralReductionTowerCanonical
import Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted
```

Original opening context, verbatim:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.RoosIntrinsicUnitComparison
open PrincipalKoszulStrictReplacement PrincipalIntrinsicCompletion

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : AlgebraicGeometry.Scheme.{t})
```

## New

Delivered imports, verbatim:

```lean
public import Sheaf.Paper.PrincipalIntrinsicCompletion
import all Sheaf.CategoryTheory.StrictRoosDerivation
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import all Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.AlgebraicGeometry.ProEtaleProductsExact
import Sheaf.Paper.QuotientTensorScalarTowerComparison
import Sheaf.Paper.RoosIntrinsicCompletenessEquivalence
import all Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
import Sheaf.Algebra.Homology.SitePerfectModelRestriction
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
```

Delivered opening context, verbatim:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory

namespace WeilConjectures.RoosIntrinsicUnitComparison
open PrincipalKoszulStrictReplacement PrincipalIntrinsicCompletion

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : AlgebraicGeometry.Scheme.{t})
```

All further attributes and options for the helper API are local to closed sections.
New helper declarations are private and fully proved. They support the existing theorem;
they do not appear in its public signature. The additional monoidal notation scope only
supports writing the new proof. The new public tensor/scalar comparison is recorded by
`lem-a1-quotient-tensor-scalar-tower-comparison` in its own new module.

The quotient tower and its comparison also receive explicit result types. Their bodies
remain exactly as before.

Old:

```lean
abbrev quotientTower (P : CochainComplex (Modules l E W) ℤ) :=
  koszulTowerComplex (completedIntegralCommRingSheafUnrestricted l E W) (targetTower l E W P)

abbrev towerMap (P : CochainComplex (Modules l E W) ℤ) :=
  koszulTowerComplexMap (completedIntegralCommRingSheafUnrestricted l E W) (comparison l E W P)
```

New:

```lean
abbrev quotientTower (P : CochainComplex (Modules l E W) ℤ) :
    CochainComplex (ℕᵒᵖ ⥤ Modules l E W) ℤ :=
  koszulTowerComplex (completedIntegralCommRingSheafUnrestricted l E W) (targetTower l E W P)

abbrev towerMap (P : CochainComplex (Modules l E W) ℤ) :
    tower l E W P ⟶ quotientTower l E W P :=
  koszulTowerComplexMap (completedIntegralCommRingSheafUnrestricted l E W) (comparison l E W P)
```

## Users

`tools/downstream.py Sheaf.Paper.RoosIntrinsicUnitComparison` reports zero downstream
Lean modules. With `--uses` and the existing theorem's full name, its only textual user is
this module itself. Pending DAG parents still need the unchanged theorem; none is withdrawn.
No consumer adaptation is required. The remaining public APIs needed by the statement are
reexported by PrincipalIntrinsicCompletion. The coefficient-extension unit-route module
remains a public transitive import:
PrincipalIntrinsicCompletion publicly imports PrincipalKoszulStrictReplacement, which
publicly imports CoefficientExtensionFinite. Its coefficient datum is used in the
completeness proof. Removing the redundant direct import bypasses no unit statement
or proof step.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RoosIntrinsicUnitComparison | H6 | Theorem statement and definition bodies unchanged; two result types annotated; proof and imports updated. |
| Sheaf.Paper.QuotientTensorScalarTowerComparison | H6 (new) | Proved independent tensor/scalar tower normalization used by the item. |

## Status

landed 20261022T114205-L-583187 2026-10-22 (merge of deliver/H6/Sheaf.Paper.RoosIntrinsicUnitComparison)
