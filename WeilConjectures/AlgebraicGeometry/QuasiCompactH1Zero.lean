/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.PQFCohomology

import WeilConjectures.AlgebraicGeometry.H1ClosedPointAffineBasicOpen
import WeilConjectures.AlgebraicGeometry.H1FiniteBasicCoverUnitIdeal

/-! # Serre's quasi-compact vanishing criterion

## References

* [Stacks Project, Tag 01XF](https://stacks.math.columbia.edu/tag/01XF)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A quasi-compact scheme whose first cohomology vanishes on every
quasi-coherent ideal sheaf is affine.
-/
theorem quasiCompact_affine_of_h1_ideal_zero (X : Scheme.{u})
    [CompactSpace X]
    (hI : ∀ (I : X.IdealSheafData), I.toModules.IsQuasicoherent →
      Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I.toModules)) :
    IsAffine X := by
  classical
  let s : Set Γ(X, ⊤) := {f | IsAffineOpen (X.basicOpen f)}
  let W : Set X := ⋃ f ∈ s, (X.basicOpen f : Set X)
  have hW : IsOpen W := isOpen_iUnion fun f ↦ isOpen_iUnion fun _ ↦
    (X.basicOpen f).isOpen
  have hcover : (Set.univ : Set X) ⊆ W := by
    intro x _
    by_contra hx
    obtain ⟨y, hy, hyclosed⟩ := hW.isClosed_compl.exists_closed_singleton ⟨x, hx⟩
    obtain ⟨f, hyf, hf⟩ :=
      exists_affineBasicOpen_of_isClosed_singleton_of_h1_ideal_zero X hI y hyclosed
    exact hy (Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨hf, hyf⟩⟩)
  obtain ⟨t, hts, htfinite, htcover⟩ := isCompact_univ.elim_finite_subcover_image
    (fun f (_ : f ∈ s) ↦ (X.basicOpen f).isOpen) hcover
  have ht : Ideal.span t = ⊤ :=
    span_eq_top_of_finite_basicOpen_cover_of_h1_ideal_zero X hI t htfinite (by
      intro x
      rcases Set.mem_iUnion.mp (htcover (Set.mem_univ x)) with ⟨f, hf⟩
      rcases Set.mem_iUnion.mp hf with ⟨hft, hxf⟩
      exact ⟨f, hft, hxf⟩)
  exact isAffine_of_isAffineOpen_basicOpen t ht (fun f hf ↦ hts hf)

end AlgebraicGeometry
