/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralHomReductionModels
import Sheaf.Paper.IntegralHomReductionComparisonExists

/-! # Sectionwise normalization data for integral reduction

This isolates the representative normalization field required by
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
  [EssentiallySmall.{max u (t + 1)} Y.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
    AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}]
  

/-- The sectionwise and counit-square normalization data exists for a fixed
finite target and source presentation.

Source: Stacks Tags 07A4 and 07A6; blueprint order 2478, proof step 3.
Proof: on K-flat representatives use the scalar-extension unit
`x ↦ 1 ⊗ x`. Balanced tensor associativity gives an invertible chain map and
its pure-tensor formula. The left-derived universal property transports this
map to the displayed counit square.
-/
theorem reduction_normalization_data_exists
    (a : TensorPresentation.{t, u} Y
      (completedIntegralCommRingSheaf l E Y D hl)) (n : ℕ)
    (target : TensorPresentation.{t, u} Y
      (integralCoefficientCommRingSheaf l E Y n))
    (mu : a.tensor ⋙ integralDerivedReduction l E Y D hl n ≅
      ((integralDerivedReduction l E Y D hl n).prod
        (integralDerivedReduction l E Y D hl n)) ⋙ target.tensor) :
    letI : HasDerivedCategory (Modules.{t, u} Y
      (completedIntegralCommRingSheaf l E Y D hl)) := HasDerivedCategory.standard _
    letI : HasDerivedCategory (Modules.{t, u} Y
      (integralCoefficientCommRingSheaf l E Y n)) := HasDerivedCategory.standard _
    ∀ (P Q : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
      (hp : flat.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl) P)
      (hq : flat.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl) Q),
      ∃ (hp' : flat.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)
          (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj P))
        (hq' : flat.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)
          (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj Q))
        (beta : ((totalTensor.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)).obj
          (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj P)).obj
          (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj Q) ⟶
        ((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex (.up ℤ)).obj
          (((totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj P).obj Q)),
        IsIso beta ∧
        (∀ (i j : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
          (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
          (beta.f (i + j)).val.app U
              (totalPair.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)
                (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex
                  (.up ℤ)).obj P)
                (((integralReductionChangeOfRings l E Y D hl n).mapHomologicalComplex
                  (.up ℤ)).obj Q)
                i j U ((reductionUnit l E Y D hl n (P.X i)).val.app U x)
                  ((reductionUnit l E Y D hl n (Q.X j)).val.app U y)) =
            (reductionUnit l E Y D hl n
              ((((totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj P).obj Q).X
                (i + j))).val.app U
              (totalPair.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl) P Q i j U x y)) ∧
        (integralDerivedReduction l E Y D hl n).map
            (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
          mu.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          target.tensor.map (Prod.mkHom (reductionCounit l E Y D hl n P)
            (reductionCounit l E Y D hl n Q)) ≫
          target.representative.inv.app (⟨_, hp'⟩, ⟨_, hq'⟩) ≫ DerivedCategory.Q.map beta =
        reductionCounit l E Y D hl n
          (((totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj P).obj Q) := by
  dsimp
  sorry

end WeilConjectures.IntegralHom
