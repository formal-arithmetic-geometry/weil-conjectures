/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.HigherImageCohomologySquareRawMap
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
/-- Expanded free-representable source-map formula for the higher-image square.
Source: Stacks Project, Tags 03CB and 03Q8.
(blueprint: lem-sf-higher-image-cohomology-square-transition-compatibility-source-formula). -/
theorem higherImageCohomologySquare_rawSource_formula
    {Y Y' S S' : Scheme.{u}}
    {h : Y ⟶ S} {h' : Y' ⟶ S'} {a : Y' ⟶ Y} {b : S' ⟶ S}
    (sq : CommSq a h' h b) {W : S.Etale} {W' : S'.Etale}
    (v : W'.left ⟶ W.left) (hv : v ≫ W.hom = W'.hom ≫ b) :
    higherImageCohomologySquareRawSource sq v hv =
      let A := (abelianComparisonFree S).obj W
      let U := (MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) b).obj W
      let l : W' ⟶ U := MorphismProperty.Over.homMk
        (Limits.pullback.lift v W'.hom (by simpa [U] using hv)) (by simp [U])
      let ψ := (abelianComparisonFree S').map l ≫
        (abelianFreeRepresentablePullbackIso b W).inv
      (upperStar AddCommGrpCat.{u + 1} h').map ψ ≫
        (upperStarComp AddCommGrpCat.{u + 1} h' b (h' ≫ b) rfl).inv.app A ≫
        (eqToIso (congrArg (fun k : Y' ⟶ S =>
          (upperStar AddCommGrpCat.{u + 1} k).obj A) sq.w.symm)).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} a h (a ≫ h) rfl).hom.app A := by
  rfl
end AlgebraicGeometry.Etale
