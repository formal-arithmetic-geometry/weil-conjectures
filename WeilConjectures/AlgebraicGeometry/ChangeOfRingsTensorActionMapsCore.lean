/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.ChangeOfRingsTensorActionMapsActions
import WeilConjectures.AlgebraicGeometry.ChangeOfRingsTensorActionMapsMap

@[expose] public section
universe u
open CategoryTheory Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme.Modules
set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a

/-- The three sectionwise formulas for the action and change-of-rings maps.
Source: Stacks Project, Morphisms, proof of Lemma 01SB.
-/
def ChangeOfRingsTensorActionFormulas (Y : Scheme.{u})
    (B C : Y.CommAlgebraSheaf) (φ : B ⟶ C)
    (P : SheafOfModules.{u} (𝓡 B.right))
    (a d : tensorObj B.toModule (tensorObj C.toModule
      ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P)) ⟶
      tensorObj C.toModule ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P))
    (g : tensorObj C.toModule ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) ⟶
      (SheafOfModules.restrictScalars (𝓻 C.hom)).obj
        (SheafOfModules.changeOfRings.{u, u, u} φ.right P)) : Prop :=
  (∀ (W : Y.Opens) (b : B.right.obj.obj (op W))
      (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
    a.app W (tmulSection (M := B.toModule) b
      (tmulSection (M := C.toModule)
        (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) c p)) =
      tmulSection (M := C.toModule)
        (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) c (b • p)) ∧
  (∀ (W : Y.Opens) (b : B.right.obj.obj (op W))
      (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
    d.app W (tmulSection (M := B.toModule) b
      (tmulSection (M := C.toModule)
        (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) c p)) =
      tmulSection (M := C.toModule)
        (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P)
        (φ.right.hom.app (op W) b * c) p) ∧
  (∀ (W : Y.Opens) (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
    g.app W (tmulSection (M := C.toModule)
      (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) c p) =
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 C.right).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ.right P)).app (op W))
        (c ⊗ₜ[B.right.obj.obj (op W), (φ.right.hom.app (op W)).hom] p))

/-- Existence of maps satisfying the three elementary section formulas.
Source: Stacks Project, Morphisms, proof of Lemma 01SB; Sheaves, Lemma 0089. -/
theorem exists_changeOfRings_tensor_action_maps_core (Y : Scheme.{u})
    (B C : Y.CommAlgebraSheaf) (φ : B ⟶ C)
    (P : SheafOfModules.{u} (𝓡 B.right)) :
    ∃ (a d : tensorObj B.toModule (tensorObj C.toModule
      ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P)) ⟶
      tensorObj C.toModule ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P))
      (g : tensorObj C.toModule ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) ⟶
      (SheafOfModules.restrictScalars (𝓻 C.hom)).obj
        (SheafOfModules.changeOfRings.{u, u, u} φ.right P)),
      ChangeOfRingsTensorActionFormulas Y B C φ P a d g := by
  obtain ⟨a, d, ha, hd⟩ :=
    exists_changeOfRings_tensor_action_maps_actions Y B C φ P
  let P₀ := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P
  let T := (SheafOfModules.restrictScalars (𝓻 C.hom)).obj
    (SheafOfModules.changeOfRings.{u, u, u} φ.right P)
  let := presheafMonoidalCategory Y
  obtain ⟨h, hh⟩ := exists_changeOfRings_tensor_presheaf_map Y B C φ P
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)
  let g := (SheafOfModules.tensorObjIsoSheafification C.toModule P₀).hom ≫
    (adj.homEquiv _ T).symm h
  refine ⟨a, d, g, ha, hd, ?_⟩
  intro W c p
  have he := (adj.homEquiv _ T).apply_symm_apply h
  have he' := congrArg (fun q ↦ q.app (op W)
    (c ⊗ₜ[Y.presheaf.obj (op W)] p)) he
  dsimp [g, tmulSection]
  rw [Hom.comp_app, ConcreteCategory.comp_apply]
  have hi := inv_app_hom_app_apply_of_iso
    (SheafOfModules.tensorObjIsoSheafification C.toModule P₀).symm
    ((toSheafifyTensor C.toModule P₀).app (op W)
      (c ⊗ₜ[Y.presheaf.obj (op W)] p))
  dsimp only [Iso.symm_hom, Iso.symm_inv] at hi
  erw [hi]
  rw [Adjunction.homEquiv_unit] at he'
  exact he'.trans (hh W c p)

end AlgebraicGeometry.Scheme.Modules
