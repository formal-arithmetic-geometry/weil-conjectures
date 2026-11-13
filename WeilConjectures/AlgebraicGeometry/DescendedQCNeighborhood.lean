/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.AlgebraicGeometry.PicardFunctor
import WeilConjectures.AlgebraicGeometry.DescendedQCNeighborhoodCore
/-!
# Finite type descent of compact opens
Source: Stacks Project, Varieties, Lemma Tag 0388.
-/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
/-- A point in an arbitrary open after base change has a descended compact neighborhood.
(Stacks, Tag 0388) -/
theorem exists_descended_qc_neighborhood (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (A : Type u) [CommRing A] [Algebra k A]
    (V : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Opens)
    (x : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A)))))
    (hx : x ∈ V) :
    ∃ (B : Subalgebra k A), B.FG ∧
      ∃ (W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).Opens),
        IsCompact W.1 ∧
        let π := baseChangeMap f
          (Over.homMk (Spec.map (CommRingCat.ofHom (Subalgebra.val B)))
            (by
              change Spec.map (CommRingCat.ofHom (Subalgebra.val B)) ≫
                  Spec.map (CommRingCat.ofHom (algebraMap k B)) =
                Spec.map (CommRingCat.ofHom (algebraMap k A))
              rw [← Spec.map_comp]
              congr 1) :
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶
              Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k B))))
        x ∈ π ⁻¹ᵁ W ∧ π ⁻¹ᵁ W ≤ V := by
  obtain ⟨B, hB, W, hW, hxW, hWV⟩ :=
    exists_descended_qc_neighborhood_core k X f A V x hx
  refine ⟨B, hB, W, hW, ?_⟩
  dsimp only
  simpa [canonicalProjection] using And.intro hxW hWV

end AlgebraicGeometry
