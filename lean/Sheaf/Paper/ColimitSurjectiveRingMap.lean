/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.FiniteType

/-!
# Descent of surjectivity along a directed colimit of rings

Source: Stacks Project, Algebra, Tag 07RH, Lemma `lemma-colimit-surjective`
(blueprint: lem-weil-pbc-colimit-surjective-ring-map).
-/

@[expose] public section

universe v w x

open CategoryTheory CategoryTheory.Limits

namespace RingHom

/-- Surjectivity of a finite type algebra map descends to a stage of a directed colimit.
The algebra structures on the colimit and on each stage above `i₀` are induced by the
coprojection and the transition map, respectively; the tensor maps are `id ⊗ φ₀`.

Source: Stacks Project, Algebra, Tag 07RH (blueprint: lem-weil-pbc-colimit-surjective-ring-map).

Proof:
1. The tensor transition maps and coprojections are ring homomorphisms and commute with
   `id ⊗ φ₀`, as checked on pure tensors
   [lem-weil-pbc-algebra-tensor-map-ring-hom, def-weil-module-base-change,
   def-weil-pbc-category-colimit].
2. Choose finitely many generators of `C₀` over `B₀` and, by surjectivity at the colimit,
   preimages of their tensors `1 ⊗ x`.
3. Lift these finitely many preimages to one common stage above `i₀`, using directedness
   and [lem-weil-pbc-directed-colimit-base-change-elementwise](1).
4. Their images differ from `1 ⊗ x` by elements vanishing at the colimit. By
   [lem-weil-pbc-directed-colimit-base-change-elementwise](2), increase the stage so all
   these differences vanish; compatibility keeps them zero at a common upper stage.
5. The image subring then contains `a ⊗ 1`, `1 ⊗ φ₀(b)`, and `1 ⊗ x` for each generator.
   Finite generation gives every `1 ⊗ c`, multiplication gives every `a ⊗ c`, and pure
   tensors span the tensor product additively [def-weil-module-base-change]. Hence the
   stage map is surjective. With no generators, take the initial stage. -/
theorem exists_surjective_tensorProduct_map_of_surjective
    (I : Type v) [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F] (i₀ : I)
    (B₀ : Type w) (C₀ : Type x) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀) (hfinite : φ₀.FiniteType)
    (hsurj : letI := (colimit.ι F i₀).hom.toAlgebra
      Function.Surjective
        (Algebra.TensorProduct.map
          (AlgHom.id (F.obj i₀) ((colimit F : CommRingCat.{v}) : Type v)) φ₀)) :
    ∃ (i : I) (hi : i₀ ≤ i),
      letI := (F.map (homOfLE hi)).hom.toAlgebra
      Function.Surjective
        (Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) (F.obj i)) φ₀) := by
  sorry

end RingHom
