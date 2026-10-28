/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralHomReductionModels
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Paper.FiniteTensorPresentationEvaluation

/-! # Target and comparison components of an integral reduction presentation

This isolates the target tensor presentation and its derived comparison from the
normalization field of `ReductionPresentation`.
(blueprint: lem-sf-integral-hom-reduction-target).
(blueprint: lem-sf-integral-hom-models-exist-reduction-components).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)


/-- The finite-level target tensor presentation exists.

Source: Stacks Tags 07A4 and 07A6; blueprint order 2478, proof step 3.
Proof: construct the finite-level tensor presentation by scalar extension and
restriction, then use balanced tensor associativity and the derived universal
property to obtain the comparison isomorphism. The remaining sectionwise
normalization is stated separately.
-/
theorem reduction_target_exists
    (n : ℕ) :
    Nonempty (TensorPresentation.{t, u} Y
      (integralCoefficientCommRingSheaf l E Y n)) := by
  classical
  letI : EssentiallySmall.{t + 1} Y.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  letI : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} Y
  letI : (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} Y
  obtain ⟨S, T, β, hcoh⟩ :=
    CategoryTheory.ringedDerived_closed_symmetric_monoidal.{t + 1, t, u,
      (max u (t + 1)) + 1} (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y n)
  letI := S.monoidal
  letI := β
  let adj : ∀ K : Derived.{t, u} Y
      (integralCoefficientCommRingSheaf l E Y n),
      (Functor.curry.obj S.tensor).obj K ⊣
        (Functor.curry.obj (hom.{t, u} Y
          (integralCoefficientCommRingSheaf l E Y n))).obj (op K) := by
    intro K
    have hfun : (Functor.curry.obj S.tensor).obj K =
        MonoidalCategory.tensorLeft K := by
      fapply CategoryTheory.Functor.ext
      · intro X
        rfl
      · intro X Y f
        simp [CoefficientClosedStructure.tensor,
          MonoidalCategory.tensorHom_def, MonoidalCategory.id_whiskerRight]
    let e : MonoidalCategory.tensorRight K ≅
        (Functor.curry.obj S.tensor).obj K :=
      (BraidedCategory.tensorLeftIsoTensorRight K).symm ≪≫ eqToIso hfun.symm
    exact (S.adjunction K).ofNatIsoLeft e
  exact ⟨TensorPresentation.mk S.tensor T.comparison adj
    (finite_tensor_presentation_evaluation l E Y n S T adj)⟩

end WeilConjectures.IntegralHom
