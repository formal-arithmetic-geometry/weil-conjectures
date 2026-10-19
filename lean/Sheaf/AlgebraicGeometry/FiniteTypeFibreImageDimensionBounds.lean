/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.Topology.KrullDimension

import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ClosurePointDimension
import WeilConjectures.AlgebraicGeometry.FiberDimension
import WeilConjectures.Topology.KrullDimension.Specialization

/-!
# Fibre and image dimension bounds over a field

Source: Stacks Project, `varieties.tex`, Tag 0B2L,
`lemma-dimension-fibres-locally-algebraic`, (2)(a) and its proof, applied to the finitely
many irreducible components (blueprint: lem-zl-finite-type-fibre-image-dimension-bounds).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Source: Stacks Project, `varieties.tex`, Tag 0B2L,
`lemma-dimension-fibres-locally-algebraic`, (2)(a) and proof
(blueprint: lem-zl-finite-type-fibre-image-dimension-bounds).

For a morphism of finite-type schemes over a field, the closure of the image has dimension
at most that of the source. If the target has dimension at most `d` and all scheme-theoretic
fibres have dimension at most `n`, then the source has dimension at most `d + n`.
All dimensions are topological Krull dimensions, with the empty space having dimension `⊥`.

Proof.
Finite type over a field makes `X` Noetherian and `Y` locally Noetherian. Since `f` is
an over-morphism, its composite with the structure map is locally of finite type, hence
`f` itself is locally of finite type.

Choose finitely many generic points whose specializations cover `X`. Continuity shows
that the closure of the image lies in the finite union of the closures of their images.
The existing theorem `Scheme.Hom.topologicalKrullDim_closure_singleton_apply_le` bounds
each image-point closure by its source-point closure, hence by the dimension of `X`.
The dimension bound for a closed subset covered by closures of points proves the first clause.

For the second clause, `f.fiberHomeo` transfers the fibre hypothesis to topological fibres.
Apply the existing theorem `Scheme.Hom.topologicalKrullDim_le_add`, whose affine argument
is the height inequality of Stacks Tag 00OM (`algebra.tex`,
`lemma-dimension-base-fibre-total`), then use the bound on the dimension of `Y`.
Both arguments include empty schemes without a separate nonemptiness hypothesis.
-/
theorem Scheme.Hom.finiteType_fibre_image_dimension_bounds
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] :
    topologicalKrullDim (closure (Set.range f)) ≤ topologicalKrullDim X ∧
      ∀ (d n : ℕ), topologicalKrullDim Y ≤ (d : WithBot ℕ∞) →
        (∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (n : WithBot ℕ∞)) →
        topologicalKrullDim X ≤ ((d + n : ℕ) : WithBot ℕ∞) := by
  classical
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have : LocallyOfFiniteType (f ≫ (Y ↘ Spec (.of k))) := by
    rw [CategoryTheory.comp_over f (Spec (.of k))]
    infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (Y ↘ Spec (.of k))
  constructor
  · obtain ⟨G, hG, -, hcover⟩ :=
      IsClosed.exists_finite_forall_exists_specializes (X := X) isClosed_univ
    have hclosed : IsClosed (⋃ y ∈ f '' G, closure ({y} : Set Y)) :=
      (hG.image f).isClosed_biUnion fun _ _ ↦ isClosed_closure
    refine topologicalKrullDim_le_of_subset_iUnion_closure_singleton isClosed_closure
      (closure_minimal ?_ hclosed) ?_
    · rintro _ ⟨x, rfl⟩
      obtain ⟨ξ, hξ, hξx⟩ := hcover x (Set.mem_univ x)
      exact Set.mem_iUnion₂.mpr
        ⟨f ξ, Set.mem_image_of_mem f hξ,
          specializes_iff_mem_closure.mp (hξx.map f.continuous)⟩
    · rintro _ ⟨x, -, rfl⟩
      exact (Scheme.Hom.topologicalKrullDim_closure_singleton_apply_le
        (Y ↘ Spec (.of k)) f x).trans
        (topologicalKrullDim_subspace_le X _)
  · intro d n hd hn
    have hfib (y : Y) : topologicalKrullDim (f ⁻¹' {y}) ≤ (n : WithBot ℕ∞) := by
      rw [← (f.fiberHomeo y).isHomeomorph.topologicalKrullDim_eq]
      exact hn y
    calc topologicalKrullDim X ≤ topologicalKrullDim Y + (n : WithBot ℕ∞) :=
          f.topologicalKrullDim_le_add _ hfib
      _ ≤ (d : WithBot ℕ∞) + (n : WithBot ℕ∞) := add_le_add hd le_rfl
      _ = ((d + n : ℕ) : WithBot ℕ∞) := by norm_cast

end AlgebraicGeometry
