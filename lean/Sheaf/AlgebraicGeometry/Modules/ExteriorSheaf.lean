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
  sorry

/-- The unique exterior-power restriction characterized on pure wedges.
Source: blueprint, Riemann--Roch determinant paragraph (blueprint: def-sc-sheaf-exterior-power). -/
noncomputable def exteriorSheafRestriction (M : X.Modules) (n : ℕ)
    {U V : X.Opensᵒᵖ} (f : U ⟶ V) :=
  Classical.choose (exteriorSheafRestriction_existsUnique M n f)

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
  sorry

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
  sorry

end AlgebraicGeometry.Scheme.Modules
