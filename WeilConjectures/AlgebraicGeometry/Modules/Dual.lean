/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-!
# The dual of a sheaf of modules on a scheme

For sheaves of modules `M` and `N` on a scheme `X`, `Hom(M, N)` is the internal hom sheaf
`U ↦ Hom_{𝒪_U}(M|_U, N|_U)`, and the dual of `M` is `M^∨ = Hom(M, 𝒪_X)`.

Both are abbreviations for `SheafOfModules.homObj`, so its API (`SheafOfModules.homObj_val`,
`SheafOfModules.homObjSectionsEquiv`, `SheafOfModules.homObjMap`, ...) applies directly.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.homObj`: the internal hom `Hom(M, N)`.
- `AlgebraicGeometry.Scheme.Modules.dual`: the dual `M^∨ = Hom(M, 𝒪_X)`, with notation `Mᵛ`.
- `AlgebraicGeometry.Scheme.Modules.dualMap`: the transpose `Nᵛ ⟶ Mᵛ` of `f : M ⟶ N`.
- `AlgebraicGeometry.Scheme.Modules.dualFunctor`: `M ↦ Mᵛ` as a contravariant functor.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.nonempty_dual_unit_iso`: `𝒪_Xᵛ ≅ 𝒪_X`.
- `AlgebraicGeometry.Scheme.Modules.nonempty_tensorObj_dual_iso_unit`: for an invertible `M`,
  `M ⊗ Mᵛ ≅ 𝒪_X`, so that `Mᵛ` is a tensor inverse of `M`.
- `AlgebraicGeometry.Scheme.Modules.nonempty_iso_unit_of_tensorObj_iso`: cancellation of an
  invertible module, `M ⊗ N ≅ M` implies `N ≅ 𝒪_X`.
- `AlgebraicGeometry.Scheme.Modules.isInvertible_dual`,
  `AlgebraicGeometry.Scheme.Modules.nonempty_iso_dual_dual`: the dual of an invertible module is
  invertible, and an invertible module is its own double dual
  (blueprint `lem-pc-tensor-dual-invertible`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The internal hom `Hom(M, N)` of sheaves of modules on a scheme, the sheaf of modules
`U ↦ Hom_{𝒪_U}(M|_U, N|_U)`. -/
noncomputable abbrev homObj (M N : X.Modules) : X.Modules :=
  SheafOfModules.homObj (R := X.sheaf) M N

/-- The dual `M^∨ = Hom(M, 𝒪_X)` of a sheaf of modules on a scheme. -/
noncomputable abbrev dual (M : X.Modules) : X.Modules :=
  homObj M (SheafOfModules.unit _)

@[inherit_doc] scoped postfix:max "ᵛ" => AlgebraicGeometry.Scheme.Modules.dual

/-- The transpose `Nᵛ ⟶ Mᵛ` of a morphism `f : M ⟶ N` of sheaves of modules on a scheme. -/
noncomputable abbrev dualMap {M N : X.Modules} (f : M ⟶ N) : Nᵛ ⟶ Mᵛ :=
  SheafOfModules.homObjMap (R := X.sheaf) f (𝟙 _)

variable (X) in
/-- The dual `M ↦ Mᵛ` as a contravariant functor on sheaves of modules on a scheme. -/
noncomputable abbrev dualFunctor : X.Modulesᵒᵖ ⥤ X.Modules :=
  (SheafOfModules.homFunctor X.sheaf).flip.obj (SheafOfModules.unit _)

/-- The dual of the structure sheaf is the structure sheaf: `Hom(𝒪_X, 𝒪_X) ≅ 𝒪_X`. -/
theorem nonempty_dual_unit_iso :
    Nonempty ((SheafOfModules.unit X.ringCatSheaf : X.Modules)ᵛ ≅
      SheafOfModules.unit X.ringCatSheaf) :=
  sorry

/-- **The dual of an invertible module is its tensor inverse.** For an invertible `𝒪_X`-module
`M`, the evaluation `M ⊗ Mᵛ ⟶ 𝒪_X` is an isomorphism: this is local on `X`, and for `M = 𝒪_X` it
is `𝒪_X ⊗ 𝒪_X ≅ 𝒪_X`. This is what makes the isomorphism classes of invertible modules a group,
the Picard group (blueprint `def-sc-picard-group`). -/
theorem nonempty_tensorObj_dual_iso_unit (M : X.Modules) [M.IsInvertible] :
    Nonempty (M ⊗ Mᵛ ≅ 𝟙_ X.Modules) :=
  sorry

/-- **Cancellation of an invertible module.** If `M` is invertible and `M ⊗ N ≅ M`, then
`N ≅ 𝒪_X`: tensor with the inverse `Mᵛ` of `M`. -/
lemma nonempty_iso_unit_of_tensorObj_iso (M N : X.Modules) [M.IsInvertible] (e : M ⊗ N ≅ M) :
    Nonempty (N ≅ 𝟙_ X.Modules) := by
  obtain ⟨d⟩ := nonempty_tensorObj_dual_iso_unit M
  exact ⟨(λ_ N).symm ≪≫ (((β_ _ _) ≪≫ d).symm ⊗ᵢ Iso.refl N) ≪≫ α_ _ _ _ ≪≫
    (Iso.refl _ ⊗ᵢ e) ≪≫ (β_ _ _) ≪≫ d⟩

/-- **Restriction to an open commutes with the internal hom.** Both sides are the sheaf
`V ↦ Hom_{𝒪_V}(M|_V, N|_V)` on opens `V ⊆ U`, since restriction along an open immersion is
restriction to the slice site. -/
theorem nonempty_pullback_ι_homObj_iso (U : X.Opens) (M N : X.Modules) :
    Nonempty ((pullback U.ι).obj (homObj M N) ≅
      homObj ((pullback U.ι).obj M) ((pullback U.ι).obj N)) :=
  sorry

/-- The internal hom is functorial in isomorphisms of both arguments. -/
noncomputable def homObjIsoOfIso {M M' N N' : X.Modules} (e : M ≅ M') (e' : N ≅ N') :
    homObj M N ≅ homObj M' N' where
  hom := SheafOfModules.homObjMap (R := X.sheaf) e.inv e'.hom
  inv := SheafOfModules.homObjMap (R := X.sheaf) e.hom e'.inv
  hom_inv_id := by
    refine (SheafOfModules.homObjMap_comp_homObjMap.{u, u, u, u}
      e.inv e.hom e'.hom e'.inv).trans ?_
    rw [Iso.hom_inv_id, Iso.hom_inv_id]
    exact SheafOfModules.homObjMap_id.{u, u, u, u}
  inv_hom_id := by
    refine (SheafOfModules.homObjMap_comp_homObjMap.{u, u, u, u}
      e.hom e.inv e'.inv e'.hom).trans ?_
    rw [Iso.inv_hom_id, Iso.inv_hom_id]
    exact SheafOfModules.homObjMap_id.{u, u, u, u}

/-- **The dual of an invertible module is invertible.** This is local on `X`, and
`𝒪_Xᵛ ≅ 𝒪_X`. Together with `AlgebraicGeometry.Scheme.Modules.IsInvertible.tensorObj` and
`AlgebraicGeometry.Scheme.Modules.nonempty_tensorObj_dual_iso_unit` this is the first half of
blueprint `lem-pc-tensor-dual-invertible`.

(blueprint: `lem-pc-tensor-dual-invertible`) -/
theorem isInvertible_dual (M : X.Modules) [M.IsInvertible] : Mᵛ.IsInvertible where
  exists_isoUnit x := by
    obtain ⟨U, hx, ⟨e⟩⟩ := IsInvertible.exists_isoUnit (M := M) x
    obtain ⟨r⟩ := nonempty_pullback_ι_homObj_iso U M (SheafOfModules.unit _)
    obtain ⟨d⟩ := nonempty_dual_unit_iso (X := U.toScheme)
    exact ⟨U, hx, ⟨r ≪≫ homObjIsoOfIso e (pullbackObjUnitIso U.ι) ≪≫ d⟩⟩

/-- **An invertible module is its own double dual.** For an invertible `M`, `M ≅ Mᵛᵛ`:
`M ≅ M ⊗ (Mᵛ ⊗ Mᵛᵛ) ≅ (M ⊗ Mᵛ) ⊗ Mᵛᵛ ≅ Mᵛᵛ`.

(blueprint: `lem-pc-tensor-dual-invertible`) -/
theorem nonempty_iso_dual_dual (M : X.Modules) [M.IsInvertible] : Nonempty (M ≅ Mᵛᵛ) := by
  have := isInvertible_dual M
  obtain ⟨d⟩ := nonempty_tensorObj_dual_iso_unit M
  obtain ⟨d'⟩ := nonempty_tensorObj_dual_iso_unit Mᵛ
  exact ⟨(ρ_ M).symm ≪≫ (Iso.refl M ⊗ᵢ d'.symm) ≪≫ (α_ _ _ _).symm ≪≫ (d ⊗ᵢ Iso.refl _) ≪≫
    λ_ _⟩

end AlgebraicGeometry.Scheme.Modules
