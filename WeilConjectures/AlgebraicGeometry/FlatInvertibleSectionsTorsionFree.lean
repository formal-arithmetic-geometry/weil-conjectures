/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Torsion-freeness of sections of an invertible module

## References

* [Stacks Project, Tag 0EX8](https://stacks.math.columbia.edu/tag/0EX8)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- Nonzero base scalars act injectively on sections of an invertible module
(Stacks, More on Morphisms, Tag 0EX8). -/
theorem injective_smul_sections_of_flat
    (A : Type u) [CommRing A] [IsDomain A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [Flat f]
    (L : X.Modules) [L.IsInvertible] (a : A) (ha : a ≠ 0) :
    Function.Injective (fun s : Γ(L, ⊤) ↦
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom a • s) := by
  classical
  intro s t h
  have := IsInvertible.sheafOfModules_isInvertible L
  choose U hxU hU e he using fun x : X ↦
    exists_isFreeGenerator L (TopologicalSpace.Opens.mem_top x)
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨L.presheaf, L.isSheaf⟩ (fun x ↦ (U x).1) ⊤
    (fun x ↦ homOfLE le_top)
    (fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩) s t fun x ↦ ?_
  let ρ := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ (U x).1 le_top
  let : Algebra A Γ(X, (U x).1) := ρ.hom.toAlgebra
  have hflat : ρ.hom.Flat :=
    (RingHom.Flat.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.bijective).comp
        (f.flat_appLE (isAffineOpen_top _) (U x).2 le_top)
  have : Module.Flat A Γ(X, (U x).1) := RingHom.flat_algebraMap_iff.mp hflat
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors
    (M := Γ(X, (U x).1)) (mem_nonZeroDivisors_iff_ne_zero.mpr ha)
  obtain ⟨b, hb⟩ := (he x).exists_smul_eq
    (L.presheaf.map (homOfLE (le_top : (U x).1 ≤ ⊤)).op s)
  obtain ⟨c, hc⟩ := (he x).exists_smul_eq
    (L.presheaf.map (homOfLE (le_top : (U x).1 ≤ ⊤)).op t)
  have hres := congrArg (L.presheaf.map (homOfLE (le_top : (U x).1 ≤ ⊤)).op) h
  simp only [map_smul] at hres
  change ρ.hom a • L.presheaf.map (homOfLE le_top).op s =
    ρ.hom a • L.presheaf.map (homOfLE le_top).op t at hres
  rw [← hb, ← hc, smul_smul, smul_smul] at hres
  have hbc : b = c := hreg ((he x).smul_left_injective hres)
  rw [← hb, ← hc, hbc]

end AlgebraicGeometry.Scheme.Modules
