/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P7
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorTensorLiftHomExt

/-!
# Comparison of the two exterior sheaf constructions

The restriction maps agree by the uniqueness of their extension from pure wedges.
This identifies the sheafifications and transfers the official extensionality API.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph; retirement
compatibility for the two implementations (blueprint: lem-sc-exterior-sheaf-power-comparison).
-/

@[expose] public section

universe v
open CategoryTheory Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison, induced by identity maps on sectionwise exterior powers.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
Proof: both restrictions have the same pure-wedge formula, hence uniqueness identifies
them. The identity components form a presheaf isomorphism; sheafify this isomorphism.
(blueprint: lem-sc-exterior-sheaf-power-comparison). -/
@[irreducible]
noncomputable def exteriorSheafPowerIso {X : Scheme.{v}} (M : X.Modules) (n : ℕ) :
    exteriorSheaf M n ≅ exteriorPower M n :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
      intro U V f
      change exteriorSheafRestriction M n f ≫ 𝟙 _ =
        𝟙 _ ≫ (M.val.exteriorPower (R := X.presheaf) n).map f
      rw [Category.comp_id, Category.id_comp]
      symm
      apply (Classical.choose_spec (exteriorSheafRestriction_existsUnique M n f)).2
      intro a
      exact _root_.PresheafOfModules.exteriorPower_map_ιMulti M.val n f a))

set_option backward.isDefEq.respectTransparency false in
/-- The inverse comparison preserves pure wedge sections.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
Proof: apply naturality of the sheafification-adjunction unit to the inverse presheaf
isomorphism, whose components are identities. Evaluate on the sectionwise pure wedge.
(blueprint: lem-sc-exterior-sheaf-power-comparison). -/
theorem exteriorSheafPowerIso_inv_wedge {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) (a : Fin n → M.val.obj (op U)) :
    (exteriorSheafPowerIso M n).inv.app U (wedge a) =
      exteriorSheafSection M n U a := by
  let e₀ : exteriorSheafPresheaf M n ≅ M.val.exteriorPower (R := X.presheaf) n :=
    PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
      intro U V f
      change exteriorSheafRestriction M n f ≫ 𝟙 _ =
        𝟙 _ ≫ (M.val.exteriorPower (R := X.presheaf) n).map f
      rw [Category.comp_id, Category.id_comp]
      symm
      apply (Classical.choose_spec (exteriorSheafRestriction_existsUnique M n f)).2
      intro a
      exact _root_.PresheafOfModules.exteriorPower_map_ιMulti M.val n f a)
  let adj := PresheafOfModules.sheafificationAdjunction.{v} (𝟙 X.ringCatSheaf.obj)
  have h := congrArg (fun k ↦ k.app (op U)
    (_root_.exteriorPower.ιMulti (X.presheaf.obj (op U)) n a))
    (adj.unit.naturality e₀.inv).symm
  unfold exteriorSheafPowerIso
  exact h


set_option backward.isDefEq.respectTransparency false in
/-- Extensionality for the older exterior sheaves, transported to the official theorem.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
Proof: precompose with the inverse tensor of the two comparison isomorphisms. Apply
the official extensionality theorem. Naturality of tensor sections and the inverse
wedge formulas give its hypothesis. Cancel the inverse isomorphism. The argument
also applies to degree zero, the empty scheme, and zero section rings.
(blueprint: lem-sc-exterior-sheaf-power-comparison). -/
theorem exteriorSheafTensor_lift_hom_ext {X : Scheme.{v}} {A B C D : X.Modules}
    (g : B ⟶ C) [Epi g] (r s : ℕ)
    (φ ψ : exteriorSheaf A r ⊗ exteriorSheaf C s ⟶ D)
    (h : ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
      (c : Fin s → B.val.obj (op U)),
      φ.val.app (op U)
          (tmulSection (exteriorSheafSection A r U a)
            (exteriorSheafSection C s U (fun i ↦ g.val.app (op U) (c i)))) =
        ψ.val.app (op U)
          (tmulSection (exteriorSheafSection A r U a)
            (exteriorSheafSection C s U (fun i ↦ g.val.app (op U) (c i))))) :
    φ = ψ := by
  apply (cancel_epi ((exteriorSheafPowerIso A r).inv ⊗ₘ
    (exteriorSheafPowerIso C s).inv)).mp
  apply exteriorTensor_lift_hom_ext g r s
  intro U a c
  change φ.app U (((exteriorSheafPowerIso A r).inv ⊗ₘ
      (exteriorSheafPowerIso C s).inv).app U _) =
    ψ.app U (((exteriorSheafPowerIso A r).inv ⊗ₘ
      (exteriorSheafPowerIso C s).inv).app U _)
  have ht := tensorHom_app_tmulSection
    (M := exteriorPower A r) (N := exteriorPower C s)
    (M' := exteriorSheaf A r) (N' := exteriorSheaf C s) (U := U)
    (exteriorSheafPowerIso A r).inv (exteriorSheafPowerIso C s).inv
    (wedge (M := A) (r := r) a)
    (wedge (M := C) (r := s) (fun i ↦ g.val.app (op U) (c i)))
  have ha := exteriorSheafPowerIso_inv_wedge A r U a
  have hc := exteriorSheafPowerIso_inv_wedge C s U (fun i ↦ g.val.app (op U) (c i))
  have ht' := ht.trans (congrArg₂ (fun x y ↦
    tmulSection (M := exteriorSheaf A r) (N := exteriorSheaf C s) x y) ha hc)
  exact (congrArg (φ.app U) ht').trans
    ((h U a c).trans (congrArg (ψ.app U) ht').symm)

end AlgebraicGeometry.Scheme.Modules
