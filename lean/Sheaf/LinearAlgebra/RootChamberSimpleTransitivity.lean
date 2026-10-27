/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.LinearAlgebra.RealRootChambers
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Simple-root cones and simple transitivity on chambers

Source: Milne, *Algebraic Groups*, Appendix C.9--C.10, pp.609--610,
and C.19--C.22, pp.611--612 (blueprint: lem-sfb-root-chamber-simple-transitivity).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace RootPairing

/-- Bases correspond equivariantly to chambers, and the reflection group acts simply
transitively on chambers, including the empty root system.
Source: Milne C.9--C.10 and C.21--C.22, via C.19--C.20
(blueprint: lem-sfb-root-chamber-simple-transitivity).

Proof:
1. Substitution shows that reflections are involutions preserving the form. Hence the group
   permutes roots and hyperplanes, is orthogonal, and acts faithfully on the finite spanning
   root set, so it is finite. If the root set is empty, spanning gives V = 0 and all claims.
2. For a regular t, put P_t = {a in R | B t a > 0}. The signed inequalities defined by P_t
   form a convex nonempty set. Signs are constant on connected subsets of the hyperplane
   complement, so this sign cell is exactly the connected component of t.
3. Let S_t be the roots in P_t not expressible as a sum of two roots in P_t. Induct on the
   finite set of positive values B t a: every decomposable root splits into two roots with
   smaller positive values. Thus S_t generates every positive root integrally and spans V.
4. Distinct a,b in S_t have B a b <= 0. Otherwise reducedness makes them nonproportional,
   and the positive integers m = 2 B a b / B b b and n = 2 B a b / B a a satisfy mn < 4
   by positive definiteness. One equals 1, so a-b is a root by reflection and negation.
   Its sign at t makes one of a,b decomposable, a contradiction.
5. Split a real linear relation on S_t into disjoint strictly positive parts u=v. Their
   mutual pairing is nonpositive, so positive definiteness gives u=v=0. Pairing with t
   forces both supports empty. Hence S_t is a basis, and its positive roots are P_t.
6. For any base D, the pairing-coordinate map is bijective, so there is a vector with all
   simple pairings 1. Same-sign integral expansions identify its sign cell with C_D and
   establish the positive-root formula. Conversely step 5 supplies a base for each chamber.
   If two bases define this cell, expanding each in the other gives nonnegative integral
   coordinate vectors. A unit vector cannot split nontrivially into such nonzero vectors;
   hence the bases coincide. This gives the bijection.
7. A simple reflection s_a preserves the positive roots other than a: only the a-coordinate
   changes, and reducedness ensures some other coordinate of such a root is positive.
   All group elements transport bases, and orthogonality gives w C_D = C_(w D).
8. To transport chambers choose h in C_D, y in C', and maximize B (w y) h over the finite
   orbit. Any negative simple pairing would be increased by that simple reflection.
   Regularity rules out zero pairings, so w y lies in C_D and w C' = C_D.
9. For freeness use lem-sfb-simple-root-reflection-generation to write a chamber stabilizer
   as a shortest word in simple reflections. The positive-root formula makes it preserve P.
10. If this word is u s_a and nonempty, then u a = -w a is negative. Apply
    lem-sfb-root-sign-word-deletion to u and a, using step 7: deleting one factor of u
    shortens u s_a by two, a contradiction (the empty u case is also excluded by that
    lemma). Thus the stabilizer is trivial. Apply this to w2 inverse times w1 for
    uniqueness between any two chambers, and combine with steps 6--8 and the rank-zero case.
-/
theorem realRoot_chamber_simple_transitivity
    (V : Type u) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hBsymm : B.IsSymm)
    (hBpos : ∀ x : V, x ≠ 0 → 0 < B x x)
    (R : Set V) (hRfinite : R.Finite) (hRzero : (0 : V) ∉ R)
    (hRspan : Submodule.span ℝ R = ⊤)
    (hRline : ∀ a ∈ R, R ∩ (Submodule.span ℝ {a} : Set V) = {a, -a})
    (hRreflect : ∀ a ∈ R, Set.BijOn (realRootPreReflection B a) R R)
    (hRintegral : ∀ a ∈ R, ∀ b ∈ R, ∃ z : ℤ, 2 * B b a * (B a a)⁻¹ = (z : ℝ)) :
    Set.BijOn (realRootCone B) {D | IsRealRootBase R D} {C | IsRealRootChamber B R C} ∧
    (∀ D : Set V, IsRealRootBase R D → ∀ x ∈ realRootCone B D,
      realPositiveRoots R D = {b | b ∈ R ∧ 0 < B x b}) ∧
    (∀ C C' : Set V, IsRealRootChamber B R C → IsRealRootChamber B R C' →
      ∃! w : realRootReflectionGroup B R, (w : V ≃ₗ[ℝ] V) '' C = C') ∧
    (∀ (w : realRootReflectionGroup B R) (D : Set V), IsRealRootBase R D →
      IsRealRootBase R ((w : V ≃ₗ[ℝ] V) '' D) ∧
      (w : V ≃ₗ[ℝ] V) '' realRootCone B D =
        realRootCone B ((w : V ≃ₗ[ℝ] V) '' D)) ∧
    (R = ∅ → (∀ x : V, x = 0) ∧ IsRealRootBase R ∅ ∧
      realRootCone B ∅ = Set.univ ∧ (Set.univ : Set V) = {0} ∧
      realRootReflectionGroup B R = ⊥) := by
  sorry

end RootPairing
