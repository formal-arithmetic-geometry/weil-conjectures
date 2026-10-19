/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import WeilConjectures.AlgebraicGeometry.FlatTelescopeStageMap
import Sheaf.AlgebraicGeometry.FlatTelescopeStageMapRefinement

/-! # Naturality from flat telescope stage maps

Source: common-refinement cancellation in step 3 of
lem-sc-flat-telescope-bounded-normalization-extension. -/

@[expose] public section
set_option autoImplicit false
universe u w v v'
open CategoryTheory
namespace AlgebraicGeometry

/-- Stage naturality implies naturality for arbitrary maps between the indicated
representatives when the source functor factors through derived localization.

Source: step 3 of lem-sc-flat-telescope-bounded-normalization-extension,
Stacks Tags 06YS and 06YJ for the flat refinements, with the explicit refinement
statement supplied by lem-sc-flat-telescope-stage-map-refinement.

Proof. Refine a map s through a telescope R with stage maps a and b, where
 a is a quasi-isomorphism and a;s=b. Localization and then F send a to an
isomorphism. Precompose the desired equality with that invertible map.
Functoriality rewrites its left side using a;s=b, and stage naturality for
b and a identifies both sides. Cancel the invertible precomposition.
(blueprint: lem-sc-flat-telescope-stage-naturality). -/
theorem flat_telescope_stage_naturality
    {Y : Scheme.{u}} [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {D : Type v} [Category.{v'} D]
    (F : schemeDerivedCategory Y ⥤ D)
    (G : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ) ⥤ D)
    (α : ∀ X : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
      flatTelescopeShiftRepresentative Y X →
        ((DerivedCategory.Qh ⋙ F).obj X ⟶ G.obj X))
    (hα : ∀ (X X' : HomotopyCategory
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
      (hX : flatTelescopeShiftRepresentative Y X)
      (hX' : flatTelescopeShiftRepresentative Y X') (s : X ⟶ X'),
      flatTelescopeStageMap Y s →
        (DerivedCategory.Qh ⋙ F).map s ≫ α X' hX' = α X hX ≫ G.map s) :
    ∀ (X X' : HomotopyCategory
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
      (hX : flatTelescopeShiftRepresentative Y X)
      (hX' : flatTelescopeShiftRepresentative Y X') (s : X ⟶ X'),
      (DerivedCategory.Qh ⋙ F).map s ≫ α X' hX' = α X hX ≫ G.map s := by
  intro X X' hX hX' s
  obtain ⟨R, a, b, hR, ha, hstageA, hstageB, hab⟩ :=
    exists_flat_telescope_stage_map_refinement Y hX hX' s
  let L := DerivedCategory.Qh ⋙ F
  have : IsIso (DerivedCategory.Qh.map a) :=
    Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) a ha
  have : IsIso (L.map a) := F.map_isIso (DerivedCategory.Qh.map a)
  apply (cancel_epi (L.map a)).1
  change L.map a ≫ (L.map s ≫ α X' hX') = L.map a ≫ (α X hX ≫ G.map s)
  calc
    L.map a ≫ (L.map s ≫ α X' hX') = L.map b ≫ α X' hX' := by
      rw [← Category.assoc, ← Functor.map_comp, hab]
    _ = α R hR ≫ G.map b := hα R X' hR hX' b hstageB
    _ = L.map a ≫ (α X hX ≫ G.map s) := by
      rw [← hab, G.map_comp, ← Category.assoc, ← hα R X hR hX a hstageA,
        Category.assoc]

end AlgebraicGeometry
