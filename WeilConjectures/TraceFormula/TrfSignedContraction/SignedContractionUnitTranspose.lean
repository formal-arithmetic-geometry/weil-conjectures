/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.ExternalIhom
import WeilConjectures.CategoryTheory.Monoidal.Closed.ExternalHom

/-! # Unit cancellation for the native external internal-Hom map

Source: the diagonal-pairing proof, Step 3(b), expanding beta and kappa
(blueprint: lem-trf-signed-contraction-unit-transpose). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace WeilConjectures.TrfSignedContraction

variable {C₁ C₂ C : Type*} [Category C₁] [Category C₂] [Category C]
  [MonoidalCategory C₁] [MonoidalCategory C₂] [MonoidalCategory C]
  [MonoidalClosed C₁] [MonoidalClosed C₂] [BraidedCategory C] [MonoidalClosed C]
  (P : C₁ ⥤ C) (Q : C₂ ⥤ C) [P.Monoidal] [Q.LaxMonoidal]

/-- Transposing beta at the unit leaves the second evaluation and the chosen alpha.
Source: diagonal-pairing proof Step 3(b), the unit in the first beta input
(blueprint: lem-trf-signed-contraction-unit-transpose).
Proof: the native externalIhomMap is the curried externalHomPairing: tensor
composition identifies their two formulas. Apply the proved generic unit calculation
curry_eq_externalHomMap_comp. It contracts the first evaluation with the unit
identification, retaining the braiding, the second tensorator/evaluation and alpha. -/
theorem unit_external_transpose (M : C₁) (N W : C₂) {Z : C}
    (a : P.obj M ⊗ Q.obj W ⟶ Z) :
    (P.map (unitNatIso.hom.app M) ▷ _ ≫
      externalIhomMap P Q (𝟙_ C₁) M N W ≫
      (pre ((λ_ (Q.obj N)).inv ≫
        (Functor.LaxMonoidal.ε P ▷ Q.obj N))).app _) ≫ (ihom _).map a =
    curry ((α_ _ _ _).inv ≫ (β_ (Q.obj N) (P.obj M)).hom ▷ _ ≫
      (α_ _ _ _).hom ≫ P.obj M ◁ Functor.LaxMonoidal.μ Q N ((ihom N).obj W) ≫
      P.obj M ◁ Q.map ((ihom.ev N).app W) ≫ a) := by
  have h : externalIhomMap P Q (𝟙_ C₁) M N W =
      externalHomMap P Q (𝟙_ C₁) M N W := by
    unfold externalIhomMap externalHomMap externalHomPairing
    rw [tensorHom_comp_tensorHom]
  rw [h]
  exact (curry_eq_externalHomMap_comp P Q M N W a).symm

end WeilConjectures.TrfSignedContraction
