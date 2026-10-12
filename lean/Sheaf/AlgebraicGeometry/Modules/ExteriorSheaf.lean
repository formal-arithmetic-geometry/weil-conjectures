/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Exterior powers of sheaves of modules

Source: blueprint, `sec-picard-framework/sk-thm-picard-rr/lem-sc-riemann-roch.md`,
determinant paragraph (blueprint: def-sc-sheaf-exterior-power).

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.exteriorSheaf`: sheafification of sectionwise exterior powers.
- `AlgebraicGeometry.Scheme.Modules.exteriorSheafSection`: the wedge of local sections.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Sectionwise exterior power, using Mathlib's exterior power over `O_X(U)`.
Source: blueprint, Riemann--Roch determinant paragraph (blueprint: def-sc-sheaf-exterior-power). -/
noncomputable abbrev exteriorSheafObj (M : X.Modules) (n : ℕ) (U : X.Opensᵒᵖ) :
    ModuleCat.{u} (X.ringCatSheaf.obj.obj U) :=
  ModuleCat.of _ (⋀[X.presheaf.obj U]^n (M.val.obj U))

set_option maxHeartbeats 800000 in
-- The scheme and ring-sheaf module interfaces require additional elaboration.
set_option backward.isDefEq.respectTransparency false in
/-- Restrictions extend uniquely from wedges of sections. Apply the universal property of the
exterior power to the alternating map taking a tuple to the wedge of its restrictions, with
scalars restricted along `O_X(U) → O_X(V)`. Uniqueness follows because pure wedges span.
Source: blueprint, Riemann--Roch determinant paragraph (blueprint: def-sc-sheaf-exterior-power). -/
theorem exteriorSheafRestriction_existsUnique (M : X.Modules) (n : ℕ)
    {U V : X.Opensᵒᵖ} (f : U ⟶ V) :
    ∃! r : exteriorSheafObj M n U ⟶
        (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map f).hom).obj
          (exteriorSheafObj M n V),
      ∀ a : Fin n → M.val.obj U,
        r (exteriorPower.ιMulti (X.presheaf.obj U) n a) =
          exteriorPower.ιMulti (X.presheaf.obj V) n (fun i => M.val.map f (a i)) := by
  classical
  let A : (M.val.obj U) [⋀^Fin n]→ₗ[X.presheaf.obj U]
      ((ModuleCat.restrictScalars (X.ringCatSheaf.obj.map f).hom).obj
        (exteriorSheafObj M n V)) :=
    { toFun := fun a ↦ exteriorPower.ιMulti (X.presheaf.obj V) n (M := M.val.obj V)
        (fun i ↦ M.val.map f (a i))
      map_update_add' := by
        intro _ a i x y
        simp only [← Function.comp_def, Function.comp_update]
        exact (congrArg (fun z ↦ exteriorPower.ιMulti (X.presheaf.obj V) n (M := M.val.obj V)
          (Function.update (fun j ↦ M.val.map f (a j)) i z))
          ((M.val.map f).hom.map_add x y)).trans
          ((exteriorPower.ιMulti (X.presheaf.obj V) n (M := M.val.obj V)).map_update_add _ _ _ _)
      map_update_smul' := by
        intro _ a i c x
        simp only [← Function.comp_def, Function.comp_update]
        exact (congrArg (fun z ↦ exteriorPower.ιMulti (X.presheaf.obj V) n (M := M.val.obj V)
          (Function.update (fun j ↦ M.val.map f (a j)) i z))
          (M.val.map_smul f c x)).trans
          ((exteriorPower.ιMulti (X.presheaf.obj V) n (M := M.val.obj V)).map_update_smul _ _ _ _)
      map_eq_zero_of_eq' := by
        intro a i j hij hne
        exact (exteriorPower.ιMulti (X.presheaf.obj V) n (M := M.val.obj V)).map_eq_zero_of_eq
          _ (congrArg (fun x ↦ M.val.map f x) hij) hne }
  refine ⟨ModuleCat.ofHom (X := exteriorSheafObj M n U)
    (Y := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map f).hom).obj
      (exteriorSheafObj M n V))
    (exteriorPower.alternatingMapLinearEquiv (R := X.presheaf.obj U) A), ?_, ?_⟩
  · intro a
    exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti (R := X.presheaf.obj U) A a
  · intro r hr
    apply ModuleCat.hom_ext
    apply exteriorPower.linearMap_ext (R := X.presheaf.obj U)
      (N := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map f).hom).obj
        (exteriorSheafObj M n V))
    apply DFunLike.ext
    intro a
    exact (hr a).trans
      (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
        (R := X.presheaf.obj U)
        (N := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map f).hom).obj
          (exteriorSheafObj M n V)) A a).symm

/-- The unique exterior-power restriction characterized on pure wedges.
Source: blueprint, Riemann--Roch determinant paragraph (blueprint: def-sc-sheaf-exterior-power). -/
noncomputable def exteriorSheafRestriction (M : X.Modules) (n : ℕ)
    {U V : X.Opensᵒᵖ} (f : U ⟶ V) :=
  Classical.choose (exteriorSheafRestriction_existsUnique M n f)

private theorem exteriorSheafRestriction_wedge (M : X.Modules) (n : ℕ)
    {U V : X.Opensᵒᵖ} (f : U ⟶ V) (a : Fin n → M.val.obj U) :
    (exteriorSheafRestriction M n f).hom
        (exteriorPower.ιMulti (X.presheaf.obj U) n (M := M.val.obj U) a) =
      exteriorPower.ιMulti (X.presheaf.obj V) n (M := M.val.obj V)
        (fun i ↦ M.val.map f (a i)) :=
  (Classical.choose_spec (exteriorSheafRestriction_existsUnique M n f)).1 a

set_option maxHeartbeats 800000 in
-- The scheme and ring-sheaf module interfaces require additional elaboration.
/-- Restriction preserves identities and composition. Check both equalities on pure wedges,
where they reduce to the presheaf laws of `M` and the structure sheaf; then use uniqueness in
`exteriorSheafRestriction_existsUnique`.
Source: blueprint, Riemann--Roch determinant paragraph (blueprint: def-sc-sheaf-exterior-power). -/
theorem exteriorSheafRestriction_laws (M : X.Modules) (n : ℕ) :
    (∀ U : X.Opensᵒᵖ, exteriorSheafRestriction M n (𝟙 U) =
      (ModuleCat.restrictScalarsId' (X.ringCatSheaf.obj.map (𝟙 U)).hom
        (congrArg RingCat.Hom.hom (X.ringCatSheaf.obj.map_id U))).inv.app _) ∧
    (∀ (U V W : X.Opensᵒᵖ) (f : U ⟶ V) (g : V ⟶ W),
      exteriorSheafRestriction M n (f ≫ g) = exteriorSheafRestriction M n f ≫
        (ModuleCat.restrictScalars _).map (exteriorSheafRestriction M n g) ≫
        (ModuleCat.restrictScalarsComp' _ _ _
          (congrArg RingCat.Hom.hom (X.ringCatSheaf.obj.map_comp f g))).inv.app _) := by
  constructor
  · intro U
    apply ((Classical.choose_spec (exteriorSheafRestriction_existsUnique M n (𝟙 U))).2
      _ ?_).symm
    intro a
    change exteriorPower.ιMulti (X.presheaf.obj U) n (M := M.val.obj U) a =
      exteriorPower.ιMulti (X.presheaf.obj U) n (M := M.val.obj U)
        (fun i ↦ M.val.map (𝟙 U) (a i))
    apply congrArg (exteriorPower.ιMulti (X.presheaf.obj U) n (M := M.val.obj U))
    funext i
    exact (CategoryTheory.congr_fun (M.val.map_id U) (a i)).symm
  · intro U V W f g
    apply ((Classical.choose_spec (exteriorSheafRestriction_existsUnique M n (f ≫ g))).2
      _ ?_).symm
    intro a
    change (exteriorSheafRestriction M n g).hom
        ((exteriorSheafRestriction M n f).hom
          (exteriorPower.ιMulti (X.presheaf.obj U) n (M := M.val.obj U) a)) =
      exteriorPower.ιMulti (X.presheaf.obj W) n (M := M.val.obj W)
        (fun i ↦ M.val.map (f ≫ g) (a i))
    rw [exteriorSheafRestriction_wedge, exteriorSheafRestriction_wedge]
    apply congrArg (exteriorPower.ιMulti (X.presheaf.obj W) n (M := M.val.obj W))
    funext i
    exact (M.val.map_comp_apply f g (a i)).symm

/-- The presheaf `U ↦ ⋀^n M(U)`, with the uniquely induced semilinear restrictions.
Source: blueprint, Riemann--Roch determinant paragraph (blueprint: def-sc-sheaf-exterior-power). -/
noncomputable def exteriorSheafPresheaf (M : X.Modules) (n : ℕ) :
    _root_.PresheafOfModules.{u} X.ringCatSheaf.obj where
  obj U := exteriorSheafObj M n U
  map f := exteriorSheafRestriction M n f
  map_id U := (exteriorSheafRestriction_laws M n).1 U
  map_comp f g := (exteriorSheafRestriction_laws M n).2 _ _ _ f g

/-- The exterior power sheaf: sheafification of the sectionwise exterior-power presheaf.
For a finite locally free sheaf of constant rank `r`, its determinant is `exteriorSheaf M r`.
Source: blueprint, Riemann--Roch determinant paragraph (blueprint: def-sc-sheaf-exterior-power). -/
noncomputable def exteriorSheaf (M : X.Modules) (n : ℕ) : X.Modules :=
  (PresheafOfModules.sheafification.{u} (𝟙 X.ringCatSheaf.obj)).obj
    (exteriorSheafPresheaf M n)

/-- The wedge of local sections, followed by the canonical map into sheafification.
Source: blueprint, Riemann--Roch determinant paragraph (blueprint: def-sc-sheaf-exterior-power). -/
noncomputable def exteriorSheafSection (M : X.Modules) (n : ℕ) (U : X.Opens)
    (a : Fin n → M.val.obj (op U)) : (exteriorSheaf M n).val.obj (op U) :=
  ((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 X.ringCatSheaf.obj)).unit.app
    (exteriorSheafPresheaf M n)).app (op U) (exteriorPower.ιMulti (X.presheaf.obj (op U)) n a)

set_option maxHeartbeats 800000 in
-- The scheme and ring-sheaf module interfaces require additional elaboration.
/-- Degree zero is the structure sheaf. Sectionwise, the empty wedge generates the zeroth
exterior power freely over `O_X(U)`; these identifications commute with restrictions and
therefore sheafify to an isomorphism with `O_X`, already a sheaf. The empty wedge maps
to 1, which characterizes the map uniquely because it generates locally.
Source: blueprint, Riemann--Roch determinant paragraph, convention `det(0) = O_X`
(blueprint: def-sc-sheaf-exterior-power). -/
theorem exteriorSheaf_zero_iso (M : X.Modules) :
    ∃! e : exteriorSheaf M 0 ≅ SheafOfModules.unit X.ringCatSheaf,
      ∀ U : X.Opens, e.hom.val.app (op U) (exteriorSheafSection M 0 U Fin.elim0) =
        (1 : X.presheaf.obj (op U)) := by
  let e₀ : exteriorSheafPresheaf M 0 ≅ (SheafOfModules.unit X.ringCatSheaf).val :=
    PresheafOfModules.isoMk
      (fun U ↦ (exteriorPower.zeroEquiv (X.presheaf.obj U) (M.val.obj U)).toModuleIso)
      (by
        intro U V f
        apply ModuleCat.hom_ext
        apply exteriorPower.linearMap_ext (R := X.presheaf.obj U)
        apply AlternatingMap.ext
        intro a
        change exteriorPower.zeroEquiv (X.presheaf.obj V) (M.val.obj V)
            (exteriorSheafRestriction M 0 f
              (exteriorPower.ιMulti (X.presheaf.obj U) 0 a)) =
          X.presheaf.map f
            (exteriorPower.zeroEquiv (X.presheaf.obj U) (M.val.obj U)
              (exteriorPower.ιMulti (X.presheaf.obj U) 0 a))
        exact (congrArg (exteriorPower.zeroEquiv (X.presheaf.obj V) (M.val.obj V))
          ((Classical.choose_spec (exteriorSheafRestriction_existsUnique M 0 f)).1 a)).trans
          ((exteriorPower.zeroEquiv_ιMulti _).trans
            ((congrArg (fun x ↦ X.presheaf.map f x)
              (exteriorPower.zeroEquiv_ιMulti a)).trans
              (X.presheaf.map f).hom.map_one).symm))
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 X.ringCatSheaf.obj)
  let e : exteriorSheaf M 0 ≅ SheafOfModules.unit X.ringCatSheaf :=
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso e₀ ≪≫
      asIso (C := SheafOfModules.{u} X.ringCatSheaf)
        (adj.counit.app (SheafOfModules.unit X.ringCatSheaf))
  have he : adj.homEquiv _ _ e.hom = e₀.hom := by
    apply (adj.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, adj.homEquiv_counit]
    rfl
  refine ⟨e, ?_, ?_⟩
  · intro U
    have h := congrArg
      (fun k ↦ k.app (op U) (exteriorPower.ιMulti (X.presheaf.obj (op U)) 0
        (M := M.val.obj (op U)) Fin.elim0)) he
    change e.hom.val.app (op U) (exteriorSheafSection M 0 U Fin.elim0) =
      exteriorPower.zeroEquiv (X.presheaf.obj (op U)) (M.val.obj (op U))
        (exteriorPower.ιMulti (X.presheaf.obj (op U)) 0 Fin.elim0) at h
    exact h.trans (exteriorPower.zeroEquiv_ιMulti
      (R := X.presheaf.obj (op U)) (M := M.val.obj (op U)) _)
  · intro e' he'
    apply Iso.ext
    apply (adj.homEquiv _ _).injective
    rw [he]
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply exteriorPower.linearMap_ext (R := X.presheaf.obj U)
    apply DFunLike.ext
    intro a
    change e'.hom.val.app U
        (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (exteriorSheafPresheaf M 0)).app U
          (exteriorPower.ιMulti (X.presheaf.obj U) 0 a)) =
      exteriorPower.zeroEquiv (X.presheaf.obj U) (M.val.obj U)
        (exteriorPower.ιMulti (X.presheaf.obj U) 0 a)
    have ha : a = Fin.elim0 := Subsingleton.elim _ _
    subst a
    exact (he' U.unop).trans
      (exteriorPower.zeroEquiv_ιMulti (R := X.presheaf.obj U) (M := M.val.obj U) _).symm

end AlgebraicGeometry.Scheme.Modules
