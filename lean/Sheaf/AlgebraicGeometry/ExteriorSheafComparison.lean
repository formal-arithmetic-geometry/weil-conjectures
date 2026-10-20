/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.ExteriorSheafDualExt

/-! # Comparison of the two exterior sheaf constructions

Both constructions sheafify the sectionwise exterior power, with restrictions uniquely
characterized on pure wedges. Source: Stacks Project, Tag 03CY.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The identity on sectionwise exterior powers identifies the two presheaves.
Source: Stacks Project, Tag 03CY; the exterior-power universal property.
(blueprint: lem-sc-exterior-sheaf-comparison). -/
noncomputable def exteriorSheafPresheafIso (M : X.Modules) (n : ℕ) :
    exteriorSheafPresheaf M n ≅
      _root_.PresheafOfModules.exteriorPower (R := X.presheaf) M.val n :=
  PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
    intro U V f
    apply ModuleCat.hom_ext
    apply exteriorPower.linearMap_ext (R := X.presheaf.obj U)
    ext a
    exact ((Classical.choose_spec (exteriorSheafRestriction_existsUnique M n f)).1 a).trans
      (PresheafOfModules.exteriorPower_map_ιMulti M.val n f a).symm)

/-- Sheafifying the identity comparison gives the canonical exterior sheaf isomorphism.
Source: Stacks Project, Tag 03CY.
(blueprint: lem-sc-exterior-sheaf-comparison). -/
noncomputable def exteriorSheafIsoExteriorPower (M : X.Modules) (n : ℕ) :
    exteriorSheaf M n ≅ exteriorPower M n :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (exteriorSheafPresheafIso M n)

set_option backward.isDefEq.respectTransparency false in
/-- The comparison preserves wedges, by naturality of the sheafification unit.
Source: Stacks Project, Tag 03CY.
(blueprint: lem-sc-exterior-sheaf-comparison). -/
theorem exteriorSheafIsoExteriorPower_hom_wedge (M : X.Modules) (n : ℕ)
    (U : X.Opens) (a : Fin n → M.val.obj (op U)) :
    (exteriorSheafIsoExteriorPower M n).hom.val.app (op U)
        (exteriorSheafSection M n U a) = wedge a := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have h := adj.unit.naturality (exteriorSheafPresheafIso M n).hom
  exact (CategoryTheory.congr_fun (congrArg (fun f ↦ f.app (op U)) h)
    (exteriorPower.ιMulti (X.presheaf.obj (op U)) n a)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The inverse comparison preserves wedges as well.
Source: Stacks Project, Tag 03CY.
(blueprint: lem-sc-exterior-sheaf-comparison). -/
theorem exteriorSheafIsoExteriorPower_inv_wedge (M : X.Modules) (n : ℕ)
    (U : X.Opens) (a : Fin n → M.val.obj (op U)) :
    (exteriorSheafIsoExteriorPower M n).inv.val.app (op U) (wedge a) =
      exteriorSheafSection M n U a := by
  rw [← exteriorSheafIsoExteriorPower_hom_wedge M n U a]
  exact CategoryTheory.congr_fun (congrArg (fun f ↦ f.val.app (op U))
    (exteriorSheafIsoExteriorPower M n).hom_inv_id) _

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The upstream dual extensionality theorem, transported across the canonical comparison.
Source: Stacks Project, Tag 03CY.
(blueprint: lem-sc-exterior-sheaf-comparison). -/
theorem exteriorSheaf_dual_ext_compat (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (U : X.Opens)
    (q r : (Scheme.Modules.dual (Scheme.Modules.exteriorSheaf M n)).val.obj (op U))
    (h : ∀ (V : X.Opens) (g : V ⟶ U) (a : Fin n → M.val.obj (op V)),
      q.app (op (Over.mk g)) (Scheme.Modules.exteriorSheafSection M n V a) =
        r.app (op (Over.mk g)) (Scheme.Modules.exteriorSheafSection M n V a)) :
    q = r := by
  let e := Scheme.Modules.exteriorSheafIsoExteriorPower M n
  let F := PresheafOfModules.restrictOver X.sheaf.obj U
  have heq : F.map e.inv.val ≫ q = F.map e.inv.val ≫ r := by
    apply exteriorSheaf_dual_ext X M n U
    intro V g a
    change q.app (op (Over.mk g)) (e.inv.val.app (op V) (Scheme.Modules.wedge a)) =
      r.app (op (Over.mk g)) (e.inv.val.app (op V) (Scheme.Modules.wedge a))
    rw [Scheme.Modules.exteriorSheafIsoExteriorPower_inv_wedge]
    exact h V g a
  have : IsIso e.inv.val :=
    inferInstanceAs (IsIso ((SheafOfModules.forget X.ringCatSheaf).map e.inv))
  exact (cancel_epi (F.map e.inv.val)).mp heq

end AlgebraicGeometry
