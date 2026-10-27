/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q154
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Sheaf.AlgebraicGeometry.AffineFormallySmooth

/-!
# Graded square-zero lifting for a smooth affine algebra

Source: Stacks Project, Algebra, Tags 00TI and 00TN, with the homogeneous-component
refinement in the DAG proof, used for Conrad, Theorem 4.1.7(4), pp. 113–114
(blueprint: lem-sfb-graded-square-zero-smooth-lifting).
-/

@[expose] public section

universe u v

namespace GradedAlgebra

/-- A degree-preserving map from a finitely presented smooth integer-graded algebra lifts
through a homogeneous square-zero ideal. The quotient's degree `n` piece is the image of
`𝒟 n` under the canonical quotient map, expressed by `Submodule.map`.

Source: Stacks Project, Algebra, Tags 00TI and 00TN, and More on Morphisms, Tag 02H4;
the graded refinement is the DAG argument for Conrad, Theorem 4.1.7(4), pp. 113–114
(blueprint: lem-sfb-graded-square-zero-smooth-lifting).

Proof:
1. Forget the gradings. Smoothness implies formal smoothness. Apply
   `lem-weil-pbc-affine-formally-smooth-iff-ring-lifting` to obtain an ordinary
   `R`-algebra lift `f` of `h` modulo `J`.
2. Write `πᵢ` for the `R`-linear homogeneous projections on `D`. Homogeneity of `J`
   implies that the quotient map commutes with homogeneous components. For `x ∈ 𝒞 n`,
   every component `πᵢ (f x)` with `i ≠ n` belongs to `J`, and the degree `n` component
   maps to `h x`. Define the new map on a finite expansion `∑ xₙ` by `∑ πₙ (f xₙ)`.
   Uniqueness of expansions makes it `R`-linear. It preserves degree and lifts `h`.
   Since `1` and all base scalars have degree zero and are fixed by `f`, it preserves
   the unit and the base algebra map.
3. For `x ∈ 𝒞 n` and `y ∈ 𝒞 m`, take the degree `n + m` part of `f x * f y`.
   A pair of degrees `i + j = n + m` other than `(n,m)` has both `i ≠ n` and `j ≠ m`,
   by cancellation in `ℤ`. Both factors of that term belong to `J`, so the term is zero.
   Thus only `πₙ (f x) * πₘ (f y)` remains. Distributing finite homogeneous expansions
   proves multiplicativity for arbitrary elements, giving the required algebra lift. -/
theorem exists_graded_squareZero_lift
    {R C : Type u} {D : Type v} [CommRing R] [CommRing C] [CommRing D]
    [Algebra R C] [Algebra R D]
    (𝒞 : ℤ → Submodule R C) [GradedAlgebra 𝒞]
    (𝒟 : ℤ → Submodule R D) [GradedAlgebra 𝒟]
    [AlgebraicGeometry.Smooth
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R C)))]
    [Algebra.FinitePresentation R C]
    (J : Ideal D) (hJ : J.IsHomogeneous 𝒟)
    (hJ_sq : ∀ x ∈ J, ∀ y ∈ J, x * y = 0)
    (h : C →ₐ[R] D ⧸ J)
    (hh : ∀ (n : ℤ) (x : C), x ∈ 𝒞 n →
      h x ∈ (𝒟 n).map (Ideal.Quotient.mkₐ R J).toLinearMap) :
    ∃ h' : C →ₐ[R] D,
      (∀ (n : ℤ) (x : C), x ∈ 𝒞 n → h' x ∈ 𝒟 n) ∧
      (Ideal.Quotient.mkₐ R J).comp h' = h := by
  sorry

end GradedAlgebra
