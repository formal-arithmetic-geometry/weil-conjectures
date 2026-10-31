/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Pur.PurSequenceAdjointResolutionData
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

/-! # Data for quotient-sequence K-flat comparisons and coherent shifts

Source: Stacks, sites-cohomology.tex, Tags 06YY, 06YS and 0G7D; homology.tex,
Tag 012Z; blueprint `sec-six-functors/sk-thm-sf-compatibility/`
`fix-prop-coherence.proof.md`, coefficient-comparison paragraph
(blueprint: def-pur-sequence-kflat-comparison-data).

The index `n : ℕ` denotes exponent `n + 1`. All models live in the ordinary
unbounded derived category of the actual strict quotient systems.

## Main definitions

- `PurSequenceKFlatComparison`: the universal, representative-normalized comparison.
- `PurSequenceKFlatResolutionComparison`: its maps and three-resolution identities.
- `PurSequenceKFlatShiftComparison`: its prescribed coherent shift squares.
- `purSequenceTensorRight`: the existing total tensor with its first input fixed.
- `PurSequenceTensorShiftFormula`: the second-factor shift sign on tensor generators.

The existence theorem is in `PurSequenceKFlatComparisonShifts`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory
namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  coefficientSequenceEvaluation coefficientFiniteDerivedExtension scalarReductionExtension
  coefficientFiniteReductionModel purSequenceShiftIso

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The universal left-derived pair and its comparison with the supplied reduction.
The representative equation uses the actual strict pullback complex and the recorded
finite comparisons and quotient transitions, through `CoefficientReductionPresentation`.
Source: Stacks 06YY, 06YS, 0G7D
(blueprint: def-pur-sequence-kflat-comparison-data). -/
structure PurSequenceKFlatComparison
    (S : CoefficientDerivedSystemCalculus l E W)
    (O : PurSequenceOrdinaryAdjoints l E W) where
  L : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W
  ε : DerivedCategory.Q ⋙ L ⟶
    O.pullback.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : L.IsLeftDerivedFunctor ε
    (HomologicalComplex.quasiIso (scalarReductionSource l E W) (.up ℤ))
  α : L ≅ S.reduction
  reductionCounit : DerivedCategory.Q ⋙ S.reduction ⟶
    O.pullback.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  comparison : ε = Functor.whiskerLeft DerivedCategory.Q α.hom ≫ reductionCounit
  reductionUniversal : S.reduction.IsLeftDerivedFunctor reductionCounit
    (HomologicalComplex.quasiIso (scalarReductionSource l E W) (.up ℤ))
  representative : ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q),
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W)
        (Q.X i)) →
    ∃ e : S.reduction.obj (DerivedCategory.Q.obj Q) ≅
        DerivedCategory.Q.obj ((O.pullback.mapHomologicalComplex (.up ℤ)).obj Q),
      reductionCounit.app Q = e.hom ∧
      CoefficientReductionPresentation l E W S.toCoefficientDerivedSystemReduction Q hQ
        ((O.pullback.mapHomologicalComplex (.up ℤ)).obj Q) e
        (fun n ↦ (NatIso.mapHomologicalComplex (O.tensor n) (.up ℤ)).app Q)
  unique : ∀ β : L ≅ S.reduction,
    ε = Functor.whiskerLeft DerivedCategory.Q β.hom ≫ reductionCounit → β = α

end WeilConjectures
