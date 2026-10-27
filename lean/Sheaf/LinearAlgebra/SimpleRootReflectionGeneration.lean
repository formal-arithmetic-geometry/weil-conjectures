/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.BigOperators.Group.List.Defs

/-!
# Simple-root reflections generate the root reflection group

Source: Milne, *Algebraic Groups*, Appendix C.11 (first assertion), printed p.610,
and C.21--C.22, printed p.612 (blueprint: lem-sfb-simple-root-reflection-generation).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace RootPairing

/-- Each root reflection is a finite product of simple-root reflections, and the two
sets of reflections generate the same subgroup of the real general linear group.
The reflections are specified by their explicit formula as linear automorphisms.
Source: Milne, *Algebraic Groups*, Appendix C.11 (first assertion), printed p.610,
and C.21--C.22, printed p.612 (blueprint: lem-sfb-simple-root-reflection-generation).

Proof:
1. Direct substitution gives `s_{-a} = s_a`, `s_a(a) = -a`, and `s_a^2 = 1`.
   Expanding the bilinear form shows that every reflection is an isometry. Thus each
   reflection is a linear automorphism, and the root set is stable under negation.
   If the root set is empty, spanning forces the space and base to be zero and empty;
   both generated subgroups are the identity subgroup.
2. Write each root in its unique integral base coordinates. A positive root has
   nonnegative coordinates and strictly positive integral height (the sum of coordinates).
   Each root is positive or the negative of a positive root. For a positive root not in
   the base, and any base element a, some other coordinate is positive: otherwise reducedness
   makes the root a or -a, and positivity makes it a, a contradiction.
3. Expanding the positive squared norm of a positive nonsimple root b gives a base element
   a with positive coordinate and positive B(b,a). The integer m = 2 B(b,a) / B(a,a) is
   positive. The root c = s_a(b) has the same coordinates away from a, one of which is
   positive by step 2. Sign coherence makes all its coordinates nonnegative, so c is
   positive and its height is strictly smaller than the height of b.
4. The isometry and involution identities imply s_a s_b s_a = s_{s_a(b)} as linear maps:
   B(s_a(x),b) = B(x,s_a(b)) and B(s_a(b),s_a(b)) = B(b,b). Thus s_b = s_a s_c s_a.
5. Strong induction on positive height now writes every positive root reflection as a
   word in base reflections: a base root gives a one-letter word; otherwise use steps 3
   and 4 and prepend and append s_a to the shorter-height word. At height one the
   nonnegative integral coordinate vector is a single base vector. Negative roots reduce
   to positive roots using s_{-b} = s_b.
6. The inclusion of the base in the roots gives one subgroup inclusion; the finite words
   of step 5 give the other. Products are taken in the general linear group, so these
   are equalities of linear automorphisms. The empty list has product the identity.
-/
theorem simple_root_reflection_generation
    (V : Type u) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hBsymm : B.IsSymm)
    (hBpos : ∀ x : V, x ≠ 0 → 0 < B x x)
    (R : Set V) (hRfinite : R.Finite) (hRzero : (0 : V) ∉ R)
    (hRspan : Submodule.span ℝ R = ⊤)
    (hRline : ∀ a ∈ R,
      R ∩ {x : V | ∃ t : ℝ, t • a = x} = {a, -a})
    (hRreflect : ∀ a ∈ R,
      Set.BijOn (fun x : V ↦ x - (2 * B x a * (B a a)⁻¹) • a) R R)
    (hRint : ∀ a ∈ R, ∀ b ∈ R, ∃ n : ℤ, 2 * B b a * (B a a)⁻¹ = (n : ℝ))
    (D : Set V) (hDR : D ⊆ R)
    (e : Module.Basis D ℝ V) (he : ∀ a : D, e a = (a : V))
    (hDcoords : ∀ b ∈ R, ∃ n : D → ℤ,
      (∀ a : D, (n a : ℝ) = e.repr b a) ∧
      ((∀ a : D, 0 ≤ n a) ∨ (∀ a : D, n a ≤ 0))) :
    (∀ b ∈ R, ∃ w : List (V ≃ₗ[ℝ] V),
      (∀ g ∈ w, ∃ a ∈ D, ∀ x : V,
        g x = x - (2 * B x a * (B a a)⁻¹) • a) ∧
      (∀ x : V, w.prod x = x - (2 * B x b * (B b b)⁻¹) • b)) ∧
    Subgroup.closure {g : V ≃ₗ[ℝ] V | ∃ b ∈ R, ∀ x : V,
      g x = x - (2 * B x b * (B b b)⁻¹) • b} =
    Subgroup.closure {g : V ≃ₗ[ℝ] V | ∃ a ∈ D, ∀ x : V,
      g x = x - (2 * B x a * (B a a)⁻¹) • a} := by
  sorry

end RootPairing
