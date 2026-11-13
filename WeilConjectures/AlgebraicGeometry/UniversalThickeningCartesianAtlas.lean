/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickening
import WeilConjectures.AlgebraicGeometry.UniversalThickeningCartesianAtlasCore
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Cartesian charts for glued local universal thickenings

## References

* [Stacks Project, Tag 04F3](https://stacks.math.columbia.edu/tag/04F3)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The geometric part of gluing local universal thickenings: open chart maps
jointly cover a scheme over `X`, and each original source chart is their pullback.
No assertion about the global immersion's kernel or its universal property is made. -/
theorem universalFirstOrderThickening_cartesianAtlas
    {Z X : Scheme.{u}} (h : Z ⟶ X) (C : Z.OpenCover.{u})
    (Z' : C.I₀ → Scheme.{u}) (i : ∀ k, C.X k ⟶ Z' k)
    (h' : ∀ k, Z' k ⟶ X)
    (H : ∀ k, IsUniversalFirstOrderThickening (C.f k ≫ h) (i k) (h' k)) :
    ∃ (W : Scheme.{u}) (j : Z ⟶ W) (p : W ⟶ X) (e : ∀ k, Z' k ⟶ W),
      (∀ k, IsOpenImmersion (e k)) ∧ (∀ w : W, ∃ k z, e k z = w) ∧
      j ≫ p = h ∧ (∀ k, e k ≫ p = h' k) ∧
      ∀ k, IsPullback (i k) (C.f k) (e k) j := by
  obtain ⟨W, e, he, hc, hh, hi, ho⟩ :=
    universalFirstOrderThickening_cartesianAtlas_core h C Z' i h' H
  let : ∀ k, IsOpenImmersion (e k) := he
  let D : W.OpenCover.{u} :=
    { I₀ := C.I₀
      X := Z'
      f := e
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨hc, he⟩ }
  let p : W ⟶ X := D.glueMorphisms h' hh
  let j : Z ⟶ W := C.glueMorphisms (fun k ↦ i k ≫ e k) hi
  have hep (k) : e k ≫ p = h' k := D.ι_glueMorphisms h' hh k
  have hij (k) : C.f k ≫ j = i k ≫ e k :=
    C.ι_glueMorphisms (fun k ↦ i k ≫ e k) hi k
  refine ⟨W, j, p, e, he, hc, ?_, hep, ?_⟩
  · apply C.hom_ext
    intro k
    rw [← Category.assoc, hij, Category.assoc, hep, (H k).2.1]
  · intro k
    apply IsOpenImmersion.isPullback (i k) (C.f k) (e k) j (hij k)
    ext z
    obtain ⟨l, z, rfl⟩ := C.exists_eq z
    have hjz : j (C.f l z) = e l (i l z) := by
      exact congrArg (fun f : C.X l ⟶ W ↦ f z) (hij l)
    change j (C.f l z) ∈ Set.range (e k) ↔ C.f l z ∈ Set.range (C.f k)
    rw [hjz]
    exact ho k l z

end AlgebraicGeometry
