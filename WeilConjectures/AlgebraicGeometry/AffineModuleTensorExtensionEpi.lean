/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
/-! # Surjectivity of the second affine tensor unit

Source: Stacks Project, Morphisms, Lemma 01SB.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {U X : Scheme.{u}} (f : U ⟶ X)

set_option hygiene false in
local notation "𝓙" T => Opens.grothendieckTopology T
set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a
set_option hygiene false in
local notation "A" => (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf
set_option hygiene false in
local notation "ρ" => (show X.sheaf ⟶ A from ⟨f.c⟩)
set_option hygiene false in
local notation "S" => SheafOfModules.restrictScalars.{u} (𝓻 ρ)
-- Object transports and sheafified tensor instances require additional elaboration steps.
/-- The second tensor operation is a quotient of the underlying first operation
(Stacks, Tags 01SB and 008A). -/
theorem affine_module_tensor_extension_epi
    (B : U.toTopCat.Sheaf CommRingCat.{u}) (b : U.sheaf ⟶ B)
    (ε : B ⟶ U.sheaf)
    (P : SheafOfModules.{u} (𝓡 A) ⥤ SheafOfModules.{u} (𝓡 B))
    (κ : P ⋙ SheafOfModules.restrictScalars (𝓻 b) ≅ S ⋙ tensorPullback f)
    (H : SheafOfModules.{u} (𝓡 A) ⥤ U.Modules)
    (hobj : ∀ G, H.obj G = SheafOfModules.changeOfRings.{u, u, u} ε (P.obj G))
    (γ : S ⋙ tensorPullback f ⟶ H)
    (hunit : ∀ (G : SheafOfModules.{u} (𝓡 A)) (W : (Opens U)ᵒᵖ)
        (p : (P.obj G).val.obj W),
      ((eqToHom (hobj G)).val.app W)
        ((γ.app G).val.app W ((κ.hom.app G).val.app W p)) =
        ((PresheafOfModules.sheafificationAdjunction (𝟙 U.ringCatSheaf.obj)).unit.app
          (SheafOfModules.changeOfRingsPresheaf.{u, u, u} ε (P.obj G))).app W
            ((1 : U.sheaf.obj.obj W) ⊗ₜ[B.obj.obj W,(ε.hom.app W).hom] p)) :
    ∀ G, Epi (γ.app G) := by
  intro G
  constructor
  intro N q r h
  apply (cancel_epi (eqToHom (hobj G).symm)).mp
  apply (PresheafOfModules.sheafificationHomEquiv
    (𝟙 U.ringCatSheaf.obj)).injective
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.ExtendScalars.hom_ext
  intro p
  have hc := congrArg (fun a ↦ a.val.app W ((κ.hom.app G).val.app W p)) h
  have hu := hunit G W p
  change q.val.app W ((eqToHom (hobj G).symm).val.app W
    (((PresheafOfModules.sheafificationAdjunction (𝟙 U.ringCatSheaf.obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{u, u, u} ε (P.obj G))).app W
        ((1 : U.sheaf.obj.obj W) ⊗ₜ[B.obj.obj W,(ε.hom.app W).hom] p))) =
    r.val.app W ((eqToHom (hobj G).symm).val.app W
    (((PresheafOfModules.sheafificationAdjunction (𝟙 U.ringCatSheaf.obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{u, u, u} ε (P.obj G))).app W
        ((1 : U.sheaf.obj.obj W) ⊗ₜ[B.obj.obj W,(ε.hom.app W).hom] p)))
  rw [← hu]
  have ht (x : (H.obj G).val.obj W) :
      (eqToHom (hobj G).symm).val.app W ((eqToHom (hobj G)).val.app W x) = x := by
    change ((eqToHom (hobj G) ≫ eqToHom (hobj G).symm).val.app W) x = x
    rw [eqToHom_trans]
    rfl
  rw [ht]
  exact hc

end
end AlgebraicGeometry.Scheme.Modules
