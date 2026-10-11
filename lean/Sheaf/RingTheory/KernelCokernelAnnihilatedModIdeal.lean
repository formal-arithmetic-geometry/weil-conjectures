/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ExactSequence

/-!
# Scalar quasi-inverses and reduction modulo an ideal

Source: Stacks Project, Cohomology of Schemes, Remark 0888, the commutative algebra
argument and its limit argument
(blueprint: lem-weil-pbc-kernel-cokernel-annihilated-mod-ideal).
-/

universe u v v' w w' z z'

open CategoryTheory CategoryTheory.Limits

open scoped ZeroObject

namespace LinearMap

/-- Source: Stacks Project, Remark 0888, the exact-sequence hypothesis
(blueprint: lem-weil-pbc-kernel-cokernel-annihilated-mod-ideal).

The kernel/cokernel formulation is equivalent to the exact-sequence formulation.
Proof: the inclusion of the kernel, `u`, and the projection to `N / range u` give the
canonical exact sequence (def-weil-pbc-exact-sequence). Conversely, exactness identifies
`T` with `ker u` and `Q` with `N / range u` by linear isomorphisms, which preserve
annihilation by every scalar. Thus the two annihilator conditions are equivalent. -/
theorem ker_coker_annihilated_iff_exists_exact_sequence
    {A : Type u} [CommRing A]
    {M N : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (K : Ideal A) (t : ℕ) (u : M →ₗ[A] N) :
    (K ^ t ≤ Module.annihilator A (ker u) ∧
      K ^ t ≤ Module.annihilator A (N ⧸ range u)) ↔
    ∃ (T Q : ModuleCat.{v} A) (i : T ⟶ ModuleCat.of A M)
      (p : ModuleCat.of A N ⟶ Q),
      (ComposableArrows.mk₅ (0 : (0 : ModuleCat.{v} A) ⟶ T) i
        (ModuleCat.ofHom u) p (0 : Q ⟶ (0 : ModuleCat.{v} A))).Exact ∧
      K ^ t ≤ Module.annihilator A T ∧ K ^ t ≤ Module.annihilator A Q := by
  sorry

/-- Source: Stacks Project, Remark 0888, the maps "fg", reduction modulo `J`, and
compatibility and annihilation used in the limit argument
(blueprint: lem-weil-pbc-kernel-cokernel-annihilated-mod-ideal).

Proof, following the eight elementary steps of the node:
1. The exact-sequence convention is given by def-weil-pbc-exact-sequence, and its
   equivalence with the hypothesis is the preceding statement.
2. Since `f` kills the class of `y` in the cokernel, `f • y` lies in the range of `u`.
3. Two lifts differ by an element of `ker u`, killed by `g`, so `g • x` is independent
   of the lift.
4. Sums and scalar multiples of lifts lift the corresponding sums and scalar multiples;
   independence therefore makes the resulting map `h` linear.
5. Choose `f • m` as the lift of `u m` to obtain `h.comp u = (f*g) • id`.
   Applying `u` to `g • x` gives the other composite.
6. In a commuting square, `a x` lifts `f • b y`; the lifting formula for `h'` then
   gives `a.comp h = h'.comp b`.
7. For any map `v` admitting the stated two scalar composites, each `f*g` kills its
   kernel and its cokernel. Finite sums of these products generate `K^(2*t)`, so that
   ideal kills both modules.
8. Linearity makes `u` and `h` preserve the submodules `J • ⊤`. Their induced maps
   on the quotients retain both scalar composites; step 7 proves clause (c).
The cokernel is the quotient by the range; the reduced map `M/JM → N/JN` is the
induced map `Submodule.mapQ` on the quotients by `J • ⊤`. Naturality is quantified
over every map with the lifting formula, hence over the canonical map of clause (a),
without choosing new definitions. -/
theorem ker_coker_annihilated_mod_ideal
    {A : Type u} [CommRing A]
    {M : Type v} {N : Type v'}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (K : Ideal A) (t : ℕ) (ht : 1 ≤ t) (u : M →ₗ[A] N)
    (hker : K ^ t ≤ Module.annihilator A (ker u))
    (hcoker : K ^ t ≤ Module.annihilator A (N ⧸ range u)) :
    (∀ (f g : A), f ∈ K ^ t → g ∈ K ^ t →
      (∀ y : N, ∃ x : M, u x = f • y) ∧
      (∀ (y : N) (x x' : M), u x = f • y → u x' = f • y → g • x = g • x') ∧
      ∃ h : N →ₗ[A] M,
        (∀ (y : N) (x : M), u x = f • y → h y = g • x) ∧
        h.comp u = (f * g) • LinearMap.id ∧
        u.comp h = (f * g) • LinearMap.id ∧
        ∀ (M' : Type w) (N' : Type w') [AddCommGroup M'] [Module A M']
          [AddCommGroup N'] [Module A N'] (u' : M' →ₗ[A] N'),
          K ^ t ≤ Module.annihilator A (ker u') →
          K ^ t ≤ Module.annihilator A (N' ⧸ range u') →
          ∀ (a : M →ₗ[A] M') (b : N →ₗ[A] N') (h' : N' →ₗ[A] M'),
            u'.comp a = b.comp u →
            (∀ (y : N') (x : M'), u' x = f • y → h' y = g • x) →
            a.comp h = h'.comp b) ∧
    (∀ J : Ideal A,
      let ū := (J • ⊤ : Submodule A M).mapQ (J • ⊤ : Submodule A N) u
        (Submodule.smul_top_le_comap_smul_top J u)
      K ^ (2 * t) ≤ Module.annihilator A (ker ū) ∧
      K ^ (2 * t) ≤ Module.annihilator A ((N ⧸ (J • ⊤ : Submodule A N)) ⧸ range ū)) ∧
    (∀ (P : Type z) (R : Type z') [AddCommGroup P] [Module A P] [AddCommGroup R] [Module A R]
      (v : P →ₗ[A] R),
      (∀ (f g : A), f ∈ K ^ t → g ∈ K ^ t →
        ∃ k : R →ₗ[A] P,
          k.comp v = (f * g) • LinearMap.id ∧ v.comp k = (f * g) • LinearMap.id) →
      K ^ (2 * t) ≤ Module.annihilator A (ker v) ∧
      K ^ (2 * t) ≤ Module.annihilator A (R ⧸ range v)) := by
  sorry

end LinearMap
