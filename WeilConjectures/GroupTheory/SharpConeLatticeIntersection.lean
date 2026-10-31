/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# A sharp fs monoid is the lattice part of its rational cone

Source: ILO, Exposé VIII 3.1.17, printed p. 101, and Remark 3.1.29, printed p. 103;
the elementary lattice-cone expansion recorded in the DAG
(blueprint: lem-trf-sharp-cone-lattice-intersection).

The multiplicative type tag lets the additive monoid use the existing fs predicate.
Its group completion is written additively. Rationalization uses `ℚ ⊗[ℤ] G`, as in
the dependency's characteristic-rank definition, canonically identified with `G ⊗[ℤ] ℚ`
by tensor symmetry. The parameter `C` is fixed to the canonical hull by `hC`.
Mathlib's `PointedCone` means a cone containing zero; the no-line condition is stated
separately below, rather than inferred from this terminology.
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace AlgebraicGeometry

/-- A sharp finitely generated integral saturated monoid has finite free group completion,
an injective rationalization, a finitely generated rational cone containing no line and
spanning its rationalization by differences, and is precisely its cone's lattice part.
Source: ILO VIII 3.1.17 and Remark 3.1.29, printed pp. 101 and 103; the expanded
lattice-cone statement and elementary proof in the DAG
(blueprint: lem-trf-sharp-cone-lattice-intersection).

Proof:
1. Integrality identifies the monoid with its canonical image in its group completion
   (`def-trf-fs-log-blowup`). Finite monoid generators generate the group. If `n g = 0`
   with `n > 0`, saturation places both `g` and `-g` in the monoid, so sharpness gives
   `g = 0`. Thus the completion is finitely generated and torsion-free.
2. Apply `Module.basisOfFiniteTypeTorsionFree'`
   (`lem-trf-fg-torsionfree-group-free`) to obtain a basis indexed by `Fin r`.
3. Extend every integral basis coordinate to a rational tensor coordinate. These
   coordinates show that `1 ⊗ g = 0` implies `g = 0`, and that the tensors of the basis
   span the rationalization, including rank zero.
4. Express every monoid element in the finite monoid generators. Substitution into
   nonnegative rational combinations identifies their finite cone hull with `C`.
   Every group element is a difference of monoid elements; expressing rational tensor
   coordinates and separating positive and negative coefficients shows every tensor
   is a difference of two elements of `C`, including the empty generating family.
5. If `1 ⊗ g` belongs to `C`, clear all denominators in a finite nonnegative rational
   expression to obtain `N g` in the monoid, with `N > 0`, using tensor injectivity.
   Saturation (`def-trf-fs-log-blowup`) puts `g` in the monoid. The reverse inclusion
   follows from the hull definition. Empty sums use denominator product one.
6. If `x` and `-x` lie in `C`, clear both sets of denominators to get monoid elements
   `a,b` with tensors `N x,-N x`. Injectivity and integrality give `a+b=0`.
   Sharpness gives `a=0`; since `N` is nonzero in `ℚ`, `x=0`. Zero belongs to the
   cone by the empty sum. For the zero monoid, the completion and rationalization
   are zero, and the cone is `{0}`. -/
theorem sharp_fs_monoid_cone_lattice_intersection
    (P : Type u) [AddCommMonoid P]
    (hfs : IsFineSaturatedMonoid (Multiplicative P))
    (hsharp : ∀ p : P, IsAddUnit p → p = 0)
    (C : PointedCone ℚ
      (TensorProduct ℤ ℚ (Additive (Algebra.GrothendieckGroup (Multiplicative P)))))
    (hC : C = PointedCone.hull ℚ (Set.range (fun p : P ↦
      (1 : ℚ) ⊗ₜ[ℤ] Additive.ofMul (Algebra.GrothendieckGroup.of (Multiplicative.ofAdd p))))) :
    (∃ r : ℕ, Nonempty
      (Module.Basis (Fin r) ℤ (Additive (Algebra.GrothendieckGroup (Multiplicative P))))) ∧
    Function.Injective (fun g : Additive (Algebra.GrothendieckGroup (Multiplicative P)) ↦
      (1 : ℚ) ⊗ₜ[ℤ] g) ∧
    (∃ (m : ℕ) (v : Fin m → Additive (Algebra.GrothendieckGroup (Multiplicative P))),
      C = PointedCone.hull ℚ (Set.range (fun j : Fin m ↦ (1 : ℚ) ⊗ₜ[ℤ] v j))) ∧
    (∀ x : TensorProduct ℤ ℚ (Additive (Algebra.GrothendieckGroup (Multiplicative P))),
      x ∈ C → -x ∈ C → x = 0) ∧
    (∀ x : TensorProduct ℤ ℚ (Additive (Algebra.GrothendieckGroup (Multiplicative P))),
      ∃ a ∈ C, ∃ b ∈ C, x = a - b) ∧
    (∀ g : Additive (Algebra.GrothendieckGroup (Multiplicative P)),
      (1 : ℚ) ⊗ₜ[ℤ] g ∈ C ↔
        ∃ p : P, Additive.ofMul (Algebra.GrothendieckGroup.of (Multiplicative.ofAdd p)) = g) := by
  sorry

end AlgebraicGeometry
