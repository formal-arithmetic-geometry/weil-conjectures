/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Order.Directed
import WeilConjectures.Paper.DirectedColimitBaseChangeElementwise

/-! # Maps of finitely presented algebras over a directed colimit

Source: Stacks Project, Algebra, Lemma Tag 05N9, parts (2) and (3)
(blueprint: lem-weil-pbc-colimit-category-fp-algebras).
-/

@[expose] public section

universe v w z

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace RingHom

/-- Source: Stacks Project, Algebra, Lemma Tag 05N9, parts (2) and (3)
(blueprint: lem-weil-pbc-colimit-category-fp-algebras).

Maps between finitely presented algebras descend to a stage, and equality of two maps
holds at a stage if it holds over the colimit. The first clause uses the commuting square
with the canonical maps to the colimit tensors to express equality after base change.

Proof:
1. Restrict to the cofinal directed upper set of `i`. By the tensor pushout universal
property (lem-weil-pbc-algebra-tensor-pushout-universal-property), the target tensor
`A' ⊗[S] R` is the colimit of `A' ⊗[S] F.obj μ`. This is also a ring colimit by
lem-weil-pbc-filtered-colimit-algebras-elementwise.
2. Restrict the given map to `A`. Finite presentation gives a factorization through
one target tensor by lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit.
The base-change adjunction (lem-weil-pbc-algebra-tensor-base-change-universal-property)
extends it to the desired stage map. Its extension agrees with the given map on `a ⊗ 1`
and on the coefficient ring, hence everywhere.
3. Choose finitely many algebra generators of `A`. Equality over `R` kills the finitely
many differences of their images. By lem-weil-pbc-directed-colimit-base-change-elementwise
each difference vanishes at a stage. A common upper bound kills them all, so the maps
agree there. If there are no generators, take `μ = i`.
-/
theorem exists_map_of_finitePresentation_colimit
    {Λ : Type v} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (F : Λ ⥤ CommRingCat.{v}) [HasColimit F]
    (i : Λ) (A : Type w) (A' : Type z) [CommRing A] [CommRing A']
    [Algebra (F.obj i) A] [Algebra (F.obj i) A']
    [Algebra.FinitePresentation (F.obj i) A]
    [Algebra.FinitePresentation (F.obj i) A'] :
    let S := F.obj i
    let R := colimit F
    letI : Algebra S R := (colimit.ι F i).hom.toAlgebra
    letI : Algebra R (A ⊗[S] R) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra R (A' ⊗[S] R) := Algebra.TensorProduct.rightAlgebra
    (∀ u : (A ⊗[S] R) →ₐ[R] (A' ⊗[S] R), ∃ (μ : Λ) (h : i ≤ μ),
      letI : Algebra S (F.obj μ) := (F.map (homOfLE h)).hom.toAlgebra
      let t : F.obj μ →ₐ[S] R :=
        { (colimit.ι F μ).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i ⟶ colimit F ↦ f s) (colimit.w F (homOfLE h)) }
      letI : Algebra (F.obj μ) (A ⊗[S] (F.obj μ)) := Algebra.TensorProduct.rightAlgebra
      letI : Algebra (F.obj μ) (A' ⊗[S] (F.obj μ)) := Algebra.TensorProduct.rightAlgebra
      ∃ uμ : (A ⊗[S] (F.obj μ)) →ₐ[F.obj μ] (A' ⊗[S] (F.obj μ)),
        ∀ x : A ⊗[S] (F.obj μ),
          Algebra.TensorProduct.map (AlgHom.id S A') t (uμ x) =
            u (Algebra.TensorProduct.map (AlgHom.id S A) t x)) ∧
    (∀ v w : A →ₐ[S] A',
      Algebra.TensorProduct.map v (AlgHom.id S R) =
        Algebra.TensorProduct.map w (AlgHom.id S R) →
      ∃ (μ : Λ) (h : i ≤ μ),
        letI : Algebra S (F.obj μ) := (F.map (homOfLE h)).hom.toAlgebra
        Algebra.TensorProduct.map v (AlgHom.id S (F.obj μ)) =
          Algebra.TensorProduct.map w (AlgHom.id S (F.obj μ))) := by
  sorry

end RingHom
