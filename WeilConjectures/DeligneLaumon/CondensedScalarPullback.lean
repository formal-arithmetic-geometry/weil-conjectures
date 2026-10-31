/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LisseQlbarRepresentations
import WeilConjectures.CategoryTheory.ModuleObjects.Linear
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars

/-! # Multiplication by constant condensed scalars and inverse image -/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.LisseQlbar

/-- Pullback of multiplication by a constant scalar, using the underlying-object
identification of extension of scalars along the coefficient isomorphism.
Source: blueprint `thm-lisse-qlbar-representations`, normalized reductions;
monoidality of inverse image.
(blueprint: lem-dl-a1-condensed-scalar-pullback).

Proof: multiplication by a global section is natural in module maps. Restriction
along the inverse coefficient isomorphism changes the section by that inverse.
Monoidality of the coefficient comparison identifies the resulting section with
its inverse image, and `globalSmul_mapMod` gives the asserted equation. -/
theorem scalarEnd_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U C : Scheme.{u}} (j : U ⟶ C)
    (a : condensedScalarRing Λ)
    (N : Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1}) (condensedRingObj Λ C)) :
    let T := ((ProEtale.upperStar Ab.{u + 1} j).mapMod (condensedRingObj Λ C)).obj N
    let e := (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ j)).app T
    scalarEnd Λ U a ((CondensedRing.upperStar Λ j).obj N) ≫ e.hom.hom =
      e.hom.hom ≫ (ProEtale.upperStar Ab.{u + 1} j).map (scalarEnd Λ C a N) := by
  dsimp only
  let F := ProEtale.upperStar Ab.{u + 1} j
  let T := (F.mapMod (condensedRingObj Λ C)).obj N
  let φ := condensedPullbackHom Λ j
  let e := (Mod.extendScalarsIsoComapInv φ).app T
  let sC := Functor.LaxMonoidal.ε (upperStarFromPoint C) ≫
    (upperStarFromPoint C).map (constantSection Λ a)
  let sU := Functor.LaxMonoidal.ε (upperStarFromPoint U) ≫
    (upperStarFromPoint U).map (constantSection Λ a)
  have hs : sU ≫ inv φ = Functor.LaxMonoidal.ε F ≫ F.map sC := by
    apply (cancel_mono φ).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have h := NatTrans.IsMonoidal.ε_comp_map_comp_app
      (upperStarFromPointComp j).hom (constantSection Λ a)
    simpa only [sU, sC, φ, F, Functor.LaxMonoidal.comp_ε,
      Functor.comp_map, Functor.map_comp,
      Category.assoc] using h.symm
  unfold scalarEnd
  change Mod.globalSmul sU _ ≫ e.hom.hom = e.hom.hom ≫ F.map (Mod.globalSmul sC N)
  calc
    _ = e.hom.hom ≫ Mod.globalSmul sU ((Mod.comap (inv φ)).obj T) :=
      Mod.smulHom_naturality sU e.hom
    _ = _ := by
      rw [Mod.globalSmul_comap (inv φ) sU T, hs, Mod.globalSmul_mapMod]

end AlgebraicGeometry.ProEtale.LisseQlbar
