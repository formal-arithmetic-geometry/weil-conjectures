/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
/-! # Hom bijection for the two affine-module tensor operations

Source: Stacks Project, Morphisms, Lemma 01SB.
(blueprint: lem-sc-affine-module-tensor-hom-bijective).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite
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
local notation "R" => SheafOfModules.pushforward.{u} (F := Opens.map f.base)
  (S := 𝓡 A) (R := U.ringCatSheaf) (𝟙 (𝓡 A))
set_option hygiene false in
local notation "S" => SheafOfModules.restrictScalars.{u} (𝓻 ρ)
set_option hygiene false in
local notation "I" => TopCat.Sheaf.inverseImageModule f.base A
set_option hygiene false in
local notation "IA" => TopCat.Sheaf.inverseImageRing f.base A
set_option hygiene false in
local notation "e₀" =>
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f.base) CommRingCat.{u} (𝓙 X) (𝓙 U)).homEquiv A U.sheaf).symm (𝟙 A)
set_option hygiene false in
local notation "adj₀" => Classical.choose (exists_tensorPullbackAdjunction f)
/-- The canonical tensor-unit map induces a Hom bijection for the two scalar extensions.
Source: Stacks Project, Tags 01SB (elucidation), 008A and 008Y.
(blueprint: lem-sc-affine-module-tensor-hom-bijective).

Proof: For G and F, transport along hobj and apply the change-of-rings Hom bijection
for ε to identify Hom(HG,F) with Hom(PG,Res_ε F). Transport along pobj and apply
the change-of-rings bijection for t, obtaining Hom(f⁻¹G,Res_t Res_ε F).
Apply the inverse-image module Hom bijection. Its target scalar action is through
η_A followed by f_*(t ε). By ht and the ring adjunction identity this is the identity
of A, so the target is Hom(G,RF). Each operation is a bijection on all module sheaves.
On a section g over V the composite sends a to a applied to the sheafification of
1 tensor the sheafification of 1 tensor η_G(g). The unit formula hP identifies the
inner section with κ inverse applied to the ordinary tensor-pullback unit, after
pobj. The formula hH identifies the outer section with γ applied to that same unit,
after hobj. Cancel κ with its inverse and both equality transports. By hβ and the
ordinary adjunction formula this section is β_G(g). Postcomposing with a gives
β_G followed by R(a), so this explicitly specified function is bijective.
This argument applies to zero rings, zero modules, empty schemes and empty opens;
it uses no affineness or quasi-coherence. -/
theorem affine_module_tensor_hom_bijective
    (B : U.toTopCat.Sheaf CommRingCat.{u}) (b : U.sheaf ⟶ B) (t : IA ⟶ B)
    (ε : B ⟶ U.sheaf)
    (ht : t ≫ ε = e₀)
    (P : SheafOfModules.{u} (𝓡 A) ⥤ SheafOfModules.{u} (𝓡 B))
        (pobj : ∀ G, P.obj G = SheafOfModules.changeOfRings.{u, u, u} t (I G))
        (κ : P ⋙ SheafOfModules.restrictScalars (𝓻 b) ≅ S ⋙ tensorPullback f)
    (H : SheafOfModules.{u} (𝓡 A) ⥤ U.Modules)
          (hobj : ∀ G, H.obj G = SheafOfModules.changeOfRings.{u, u, u} ε (P.obj G))
          (γ : S ⋙ tensorPullback f ⟶ H)
    (hP :
        (∀ (G : SheafOfModules.{u} (𝓡 A)) (V : (Opens X)ᵒᵖ) (g : G.val.obj V),
          ((eqToHom (pobj G)).val.app ((Opens.map f.base).op.obj V))
            ((κ.inv.app G).val.app ((Opens.map f.base).op.obj V)
              (((adj₀).unit.app ((S).obj G)).val.app V g)) =
            ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
              (SheafOfModules.changeOfRingsPresheaf.{u, u, u} t (I G))).app
                ((Opens.map f.base).op.obj V)
                ((1 : B.obj.obj ((Opens.map f.base).op.obj V))
                  ⊗ₜ[(IA).obj.obj ((Opens.map f.base).op.obj V),(t.hom.app
                    ((Opens.map f.base).op.obj V)).hom]
                  (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                    (Opens.map f.base) AddCommGrpCat.{u} (𝓙 X) (𝓙 U)).unit.app
                      ((SheafOfModules.toSheaf (𝓡 A)).obj G)).hom.app V g))))
    (hH :
        (∀ (G : SheafOfModules.{u} (𝓡 A)) (W : (Opens U)ᵒᵖ)
              (p : (P.obj G).val.obj W),
            ((eqToHom (hobj G)).val.app W)
              ((γ.app G).val.app W ((κ.hom.app G).val.app W p)) =
              ((PresheafOfModules.sheafificationAdjunction (𝟙 U.ringCatSheaf.obj)).unit.app
                (SheafOfModules.changeOfRingsPresheaf.{u, u, u} ε (P.obj G))).app W
                  ((1 : U.sheaf.obj.obj W) ⊗ₜ[B.obj.obj W,(ε.hom.app W).hom] p)))
    (β : 𝟭 (SheafOfModules.{u} (𝓡 A)) ⟶ H ⋙ R)
    (hβ : ∀ G : SheafOfModules.{u} (𝓡 A),
      (S).map (β.app G) = ((adj₀).homEquiv ((S).obj G) (H.obj G)) (γ.app G)) :
    ∀ (G : SheafOfModules.{u} (𝓡 A)) (F : U.Modules),
      Function.Bijective (fun a : H.obj G ⟶ F ↦ β.app G ≫ (R).map a) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
