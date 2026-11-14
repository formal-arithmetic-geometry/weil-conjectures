/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Ordered affine space and the iterated affine line
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

-- Coordinate recursion unfolds the affine-line tower and its section pullbacks.
/-- A map to the affine tower is determined by its base map and ordered coordinates. -/
theorem iteratedAffineLine.hom_ext {S X : Scheme.{u}} :
    ∀ {r : ℕ} {f g : X ⟶ iteratedAffineLine S r},
      f ≫ iteratedAffineLineProj S r = g ≫ iteratedAffineLineProj S r →
      (∀ i, f.appTop (coord S r i) = g.appTop (coord S r i)) → f = g := by
  intro r
  induction r with
  | zero => intro f g h _; simpa using h
  | succ r ih =>
    intro f g h hc
    apply AffineSpace.hom_ext
    · apply ih
      · simpa only [Category.assoc, iteratedAffineLineProj_succ] using h
      · intro i
        have hi := hc i.succ
        rw [iteratedAffineLine.coord_succ_succ] at hi
        erw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop] at hi
        exact hi
    · intro i
      cases i
      exact hc 0

/-- Affine space and the ordered affine tower are canonically isomorphic with
identical coordinates and base map. -/
def AffineSpace.iteratedIso (S : Scheme.{u}) (r : ℕ) :
    AffineSpace (ULift.{u} (Fin r)) S ≅ iteratedAffineLine S r where
  hom := Scheme.Hom.toIteratedAffineLine (AffineSpace (ULift.{u} (Fin r)) S ↘ S)
    (fun i ↦ AffineSpace.coord S (ULift.up i))
  inv := AffineSpace.homOfVector (iteratedAffineLineProj S r)
    (fun i ↦ iteratedAffineLine.coord S r i.down)
  hom_inv_id := by
    apply AffineSpace.hom_ext
    · simp [Category.assoc, Scheme.Hom.toIteratedAffineLine_proj]
    · intro i
      simp [Scheme.Hom.toIteratedAffineLine_appTop_coord]
  inv_hom_id := by
    apply iteratedAffineLine.hom_ext
    · simp [Category.assoc, Scheme.Hom.toIteratedAffineLine_proj]
    · intro i
      simp [Scheme.Hom.toIteratedAffineLine_appTop_coord]

/-- The ordered comparison preserves the structural projection. -/
@[reassoc (attr := simp)]
theorem AffineSpace.iteratedIso_hom_proj (S : Scheme.{u}) (r : ℕ) :
    (iteratedIso S r).hom ≫ iteratedAffineLineProj S r =
      (AffineSpace (ULift.{u} (Fin r)) S ↘ S) :=
  Scheme.Hom.toIteratedAffineLine_proj _ _

/-- The ordered comparison preserves the zero section. -/
theorem AffineSpace.zeroSection_iteratedIso (S : Scheme.{u}) (r : ℕ) :
    zeroSection (ULift.{u} (Fin r)) S ≫ (iteratedIso S r).hom =
      Scheme.Hom.toIteratedAffineLine (𝟙 S) (fun _ : Fin r ↦ 0) := by
  apply iteratedAffineLine.hom_ext
  · simp [Category.assoc]
  · intro i
    simp [iteratedIso, Scheme.Hom.toIteratedAffineLine_appTop_coord]

end AlgebraicGeometry
