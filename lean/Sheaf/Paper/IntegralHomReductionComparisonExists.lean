/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralHomReductionModels
import all Sheaf.Algebra.Homology.ScalarTensorComparisonTransport
import all Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction

/-! # Derived tensor comparison component for integral reduction

This isolates the comparison-isomorphism field required by
`ReductionPresentation`.
(blueprint: lem-sf-integral-hom-reduction-normalization).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

private noncomputable def tensorModelIso
    [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{max u (t + 1)}]
    [(AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)}]
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (a : TensorPresentation.{t, u} Y R)
    (S : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{t + 1, t, u, (max u (t + 1)) + 1}
        (AlgebraicGeometry.Scheme.ProEt.topology Y) R))
    (T : CoefficientTensorModels.{u, t + 1, t, (max u (t + 1)) + 1}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R S) : a.tensor ≅ S.tensor := by
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  let i := coefficientKFlatInclusion.{u, t + 1, t} J R
  let L := i ⋙ DerivedCategory.Q
  let W := (HomologicalComplex.quasiIso (Modules.{t, u} Y R) (.up ℤ)).inverseImage i
  letI := RingedDerivedNative.kFlatLocalization.{t + 1, t, u, (max u (t + 1)) + 1} J R
  -- Both tensor models compute the same total tensor on K-flat representatives.
  let e : (L.prod L) ⋙ a.tensor ≅ (L.prod L) ⋙ S.tensor :=
    a.representative.symm ≪≫ T.comparison
  -- Restriction along the product localization is fully faithful.
  exact (Localization.fullyFaithfulWhiskeringLeft (L.prod L) (W.prod W)
    (Derived.{t, u} Y R)).preimageIso e

/-- The derived tensor comparison is available for any fixed finite target.

Source: Stacks Tag 07A4; blueprint order 2478, proof step 3.
Proof: extend both factors to the finite coefficient sheaf on K-flat
representatives. Balanced tensor associativity gives mutually inverse maps;
deriving this comparison yields the displayed natural isomorphism.
-/
theorem reduction_comparison_exists
    (a : TensorPresentation.{t, u} Y
      (completedIntegralCommRingSheaf l E Y D hl)) (n : ℕ)
    (target : TensorPresentation.{t, u} Y
      (integralCoefficientCommRingSheaf l E Y n)) :
    Nonempty (a.tensor ⋙ integralDerivedReduction l E Y D hl n ≅
      ((integralDerivedReduction l E Y D hl n).prod
        (integralDerivedReduction l E Y D hl n)) ⋙ target.tensor) := by
  classical
  let : EssentiallySmall.{t + 1} Y.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} Y
  let : (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} Y
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  let c := completedIntegralCommRingProjection l E Y D hl n
  let : ∀ R : Sheaf J CommRingCat.{max u (t + 1)},
      HasDerivedCategory.{(max u (t + 1)) + 1}
        (SheafOfModules.scalarModules.{t + 1, t, max u (t + 1)} J R) :=
    fun R ↦ HasDerivedCategory.standard _
  obtain ⟨M, μ, _⟩ :=
    scalarInternalHomAdjunction_exists.{t + 1, t, u, (max u (t + 1)) + 1} (J := J)
  let hobj := (integralReductionExistence l E Y D hl n).choose_spec.choose
  have he := ScalarTensorTransport.extension_eq.{t + 1, t, u, (max u (t + 1)) + 1}
    J c (M.scalar c) (integralReductionChangeOfRings l E Y D hl n) hobj
    (integralReductionExistence l E Y D hl n).choose_spec.choose_spec.choose
  obtain ⟨b⟩ :=
    ScalarTensorTransport.fixedScalarTensorComparison_exists.{t + 1, t, u,
      (max u (t + 1)) + 1} J c M (μ c)
      (integralReductionChangeOfRings l E Y D hl n) (reductionAdditive l E Y D hl n)
      hobj he (integralDerivedReduction l E Y D hl n)
      (integralDerivedReductionCounit l E Y D hl n)
      (by with_unfolding_all exact integralDerivedReductionUniversal l E Y D hl n)
  -- Conjugate the fixed scalar comparison by the two tensor-model identifications.
  let e := tensorModelIso Y _ a (M.closed _) (M.model _)
  let e' := tensorModelIso Y _ target (M.closed _) (M.model _)
  exact ⟨Functor.isoWhiskerRight e (integralDerivedReduction l E Y D hl n) ≪≫ b.iso ≪≫
    Functor.isoWhiskerLeft ((integralDerivedReduction l E Y D hl n).prod
      (integralDerivedReduction l E Y D hl n)) e'.symm⟩

end WeilConjectures.IntegralHom
