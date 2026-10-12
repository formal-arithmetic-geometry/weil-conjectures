/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsAdjunction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TopologicalPullback
/-! # Affine module tensor CoherenceComparisons

Source: Stacks Project, Morphisms, Lemma 01SB.
(blueprint: lem-weil-pbc-affine-module-tensor-unit-lift).
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
local notation "R" => SheafOfModules.pushforward.{u} (F := Opens.map f.base)
  (S := 𝓡 A) (R := U.ringCatSheaf) (𝟙 (𝓡 A))
set_option hygiene false in
local notation "S" => SheafOfModules.restrictScalars.{u} (𝓻 ρ)
set_option hygiene false in
local notation "I" => TopCat.Sheaf.inverseImageModule f.base A
set_option hygiene false in
local notation "IA" => TopCat.Sheaf.inverseImageRing f.base A
set_option hygiene false in
local notation "r₀" => tensorPullbackRingMap f
set_option hygiene false in
local notation "t₀" => (TopCat.Sheaf.inverseImageConstruction f.base CommRingCat.{u}).map ρ
set_option hygiene false in
local notation "e₀" =>
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f.base) CommRingCat.{u} (𝓙 X) (𝓙 U)).homEquiv A U.sheaf).symm (𝟙 A)
set_option hygiene false in
local notation "adj₀" => Classical.choose (exists_tensorPullbackAdjunction f)
set_option hygiene false in
local notation "qU" => SheafOfModules.isQuasicoherent U.ringCatSheaf
set_option hygiene false in
local notation "qA" => SheafOfModules.isQuasicoherent (𝓡 A)

set_option maxHeartbeats 800000 in
-- The two transported tensor adjunctions require extra definitional-equality checks.
/-- The adjoint of γ is linear over the affine direct-image algebra, objectwise.
Source: Stacks Project, Morphisms, Lemma 01SB, construction of h and elucidation.
(blueprint: lem-weil-pbc-affine-module-tensor-unit-lift).

Proof: The adjoint of γ is the pullback unit followed by pushforward of γ.
Its component on a section g over V is γ applied to the pullback-unit section.
Apply κ inverse and the hP unit formula to identify this section with the
sheafification of 1 tensor η(g). Apply the hH formula to obtain the second
scalar-extension unit. For a section a of A(V), η(a g) is η(a) η(g), by
linearity of inverse-image modules. The balanced relation first moves η(a)
onto the B tensor factor through t, and then across the ε extension. Since
t ε = e, and the inverse-image ring counit composed with its unit is the
identity, the result is a times the section computed for g in R(HG).
Additivity and compatibility with restrictions already hold for the adjoint.
These equalities therefore equip the same component maps with A-linearity,
producing the desired morphism a. Forgetting A scalars gives exactly the
original adjoint. No affineness or quasi-coherence is used, and the calculation
still holds for the zero ring, zero module and empty opens. -/
theorem affine_module_tensor_unitLift
    (B : U.toTopCat.Sheaf CommRingCat.{u}) (b : U.sheaf ⟶ B) (t : IA ⟶ B)
    (ε : B ⟶ U.sheaf) (hpush : IsPushout r₀ t₀ b t)
    (hb : b ≫ ε = 𝟙 U.sheaf) (ht : t ≫ ε = e₀)
    (P : SheafOfModules.{u} (𝓡 A) ⥤ SheafOfModules.{u} (𝓡 B))
        (pobj : ∀ G, P.obj G = SheafOfModules.changeOfRings.{u, u, u} t (I G))
        (κ : P ⋙ SheafOfModules.restrictScalars (𝓻 b) ≅ S ⋙ tensorPullback f)
    (H : SheafOfModules.{u} (𝓡 A) ⥤ U.Modules)
          (hobj : ∀ G, H.obj G = SheafOfModules.changeOfRings.{u, u, u} ε (P.obj G))
          (γ : S ⋙ tensorPullback f ⟶ H)
    (hP :
        (∀ (G G' : SheafOfModules.{u} (𝓡 A)) (a : G ⟶ G'),
          P.map a = eqToHom (pobj G) ≫
            SheafOfModules.changeOfRingsHom.{u, u, u} t (I G)
              (TopCat.Sheaf.inverseImageModuleMap f.base A G a) ≫
            eqToHom (pobj G').symm) ∧
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
          (∀ (G G' : SheafOfModules.{u} (𝓡 A)) (a : G ⟶ G'),
            H.map a = eqToHom (hobj G) ≫
              SheafOfModules.changeOfRingsHom.{u, u, u} ε (P.obj G) (P.map a) ≫
              eqToHom (hobj G').symm) ∧
          (∀ (G : SheafOfModules.{u} (𝓡 A)) (W : (Opens U)ᵒᵖ)
              (p : (P.obj G).val.obj W),
            ((eqToHom (hobj G)).val.app W)
              ((γ.app G).val.app W ((κ.hom.app G).val.app W p)) =
              ((PresheafOfModules.sheafificationAdjunction (𝟙 U.ringCatSheaf.obj)).unit.app
                (SheafOfModules.changeOfRingsPresheaf.{u, u, u} ε (P.obj G))).app W
                  ((1 : U.sheaf.obj.obj W) ⊗ₜ[B.obj.obj W,(ε.hom.app W).hom] p))) :
    ∀ G : SheafOfModules.{u} (𝓡 A),
      ∃ a : G ⟶ (R).obj (H.obj G),
        (S).map a = ((adj₀).homEquiv ((S).obj G) (H.obj G)) (γ.app G) := by
  classical
  have _ := hpush
  have _ := hb
  intro G
  -- The second extension unit is B-linear and agrees with γ after κ.
  obtain ⟨Eε, heε, adjε, hε⟩ :=
    SheafOfModules.exists_changeOfRingsAdjunction U.toTopCat B U.sheaf ε
  let z : P.obj G ⟶ (SheafOfModules.restrictScalars (𝓻 ε)).obj (H.obj G) :=
    adjε.homEquiv (P.obj G) (H.obj G)
      (eqToHom (heε (P.obj G)) ≫ eqToHom (hobj G).symm)
  have hz (W : (Opens U)ᵒᵖ) (p : (P.obj G).val.obj W) :
      z.val.app W p = (γ.app G).val.app W ((κ.hom.app G).val.app W p) := by
    have hz₀ := hε (P.obj G) (H.obj G) (eqToHom (hobj G).symm) W p
    change z.val.app W p = _ at hz₀
    rw [hz₀]
    erw [← hH.2 G W p]
    change ((eqToHom (hobj G) ≫ eqToHom (hobj G).symm).val.app W)
      ((γ.app G).val.app W ((κ.hom.app G).val.app W p)) = _
    simp only [eqToHom_trans, eqToHom_refl]
    rfl
  -- Composing the two tensor units gives an IA-linear map.
  obtain ⟨Et, het, adjt, hunit⟩ :=
    SheafOfModules.exists_changeOfRingsAdjunction U.toTopCat IA B t
  let q : I G ⟶ (SheafOfModules.restrictScalars (𝓻 t)).obj
      ((SheafOfModules.restrictScalars (𝓻 ε)).obj (H.obj G)) :=
    adjt.homEquiv (I G) ((SheafOfModules.restrictScalars (𝓻 ε)).obj (H.obj G))
      (eqToHom (het (I G)) ≫ eqToHom (pobj G).symm ≫ z)
  let adjAb := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f.base) AddCommGrpCat.{u} (𝓙 X) (𝓙 U)
  let d := (adj₀).homEquiv ((S).obj G) (H.obj G) (γ.app G)
  -- The prescribed unit formulas identify its adjunct with the original adjunct.
  have hd (V : (Opens X)ᵒᵖ) (g : G.val.obj V) :
      d.val.app V g = q.val.app ((Opens.map f.base).op.obj V)
        ((adjAb.unit.app ((SheafOfModules.toSheaf (𝓡 A)).obj G)).hom.app V g) := by
    let W := (Opens.map f.base).op.obj V
    have hq₀ := hunit (I G)
      ((SheafOfModules.restrictScalars (𝓻 ε)).obj (H.obj G))
      (eqToHom (pobj G).symm ≫ z) W
      ((adjAb.unit.app ((SheafOfModules.toSheaf (𝓡 A)).obj G)).hom.app V g)
    change q.val.app W _ = _ at hq₀
    rw [hq₀]
    change d.val.app V g = z.val.app W ((eqToHom (pobj G).symm).val.app W _)
    erw [← hP.2 G V g]
    change d.val.app V g = z.val.app W
      ((eqToHom (pobj G) ≫ eqToHom (pobj G).symm).val.app W
        ((κ.inv.app G).val.app W (((adj₀).unit.app ((S).obj G)).val.app V g)))
    simp only [eqToHom_trans, eqToHom_refl]
    change d.val.app V g = z.val.app W
      ((κ.inv.app G).val.app W (((adj₀).unit.app ((S).obj G)).val.app V g))
    rw [hz]
    change d.val.app V g = (γ.app G).val.app W
      ((κ.inv.app G ≫ κ.hom.app G).val.app W
        (((adj₀).unit.app ((S).obj G)).val.app V g))
    rw [κ.inv_hom_id_app]
    dsimp [d]
    rw [Adjunction.homEquiv_unit]
    rfl
  -- Semilinearity of inverse image and the ring triangle give A-linearity.
  have hscalar (V : (Opens X)ᵒᵖ) (r : (A).obj.obj V) (g : G.val.obj V) :
      d.val.app V (r • g) =
        @SMul.smul _ _ (((R).obj (H.obj G)).val.obj V).isModule.toSMul r
          (d.val.app V g) := by
    rw [hd, hd]
    rw [(Classical.choose_spec
      (TopCat.Sheaf.exists_inverseImageModuleInstances f.base A G)).2]
    erw [(q.val.app ((Opens.map f.base).op.obj V)).hom.map_smul]
    let adjRing := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map f.base) CommRingCat.{u} (𝓙 X) (𝓙 U)
    have htriangle : adjRing.unit.app A ≫
        ((Opens.map f.base).sheafPushforwardContinuous CommRingCat.{u}
          (𝓙 X) (𝓙 U)).map e₀ = 𝟙 A := by
      erw [← Adjunction.homEquiv_unit]
      exact (adjRing.homEquiv A U.sheaf).apply_symm_apply (𝟙 A)
    have hr : ε.hom.app ((Opens.map f.base).op.obj V)
        (t.hom.app ((Opens.map f.base).op.obj V)
          ((adjRing.unit.app A).hom.app V r)) = r := by
      have he := congrArg (fun a ↦ a.hom.app ((Opens.map f.base).op.obj V)
        ((adjRing.unit.app A).hom.app V r)) ht
      have hu := congrArg (fun a ↦ a.hom.app V r) htriangle
      exact he.trans hu
    change @SMul.smul _ _
      ((H.obj G).val.obj ((Opens.map f.base).op.obj V)).isModule.toSMul
      (ε.hom.app ((Opens.map f.base).op.obj V)
        (t.hom.app ((Opens.map f.base).op.obj V)
          ((adjRing.unit.app A).hom.app V r))) _ =
      @SMul.smul _ _
        ((H.obj G).val.obj ((Opens.map f.base).op.obj V)).isModule.toSMul r _
    rw [hr]
  let a : G ⟶ (R).obj (H.obj G) :=
    ⟨PresheafOfModules.homMk
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map d.val) hscalar⟩
  refine ⟨a, ?_⟩
  ext V g
  rfl

end
end AlgebraicGeometry.Scheme.Modules
