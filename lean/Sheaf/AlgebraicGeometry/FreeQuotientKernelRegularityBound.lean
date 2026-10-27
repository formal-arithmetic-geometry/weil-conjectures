module

public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Polynomial.Eval.Defs
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.Cohomology.Projective
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact

/-!
# Uniform regularity of kernels of coherent free-sheaf quotients

Source: Stacks Project, Varieties, Tag 08AG, lemma-bound-quotients-free;
Tag 08A3, definition-regularity
(blueprint: lem-sfb-free-quotient-kernel-regularity-bound).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProjectiveSpace

/-- The kernels of coherent quotients of a rank-`r` free sheaf with fixed Euler polynomial
have a regularity bound depending only on the dimension, rank and polynomial, uniformly
in the field. On projective space over a field, coherent means quasi-coherent of finite
type, rendered by the recorded `Scheme.Modules.IsQuasiCoherentFiniteType`.

Source: Stacks Project, Varieties, Tag 08AG, lemma-bound-quotients-free;
regularity is Tag 08A3 (blueprint: lem-sfb-free-quotient-kernel-regularity-bound).

Proof:
1. Induct on `n`, simultaneously for every rank, polynomial and field. For `n = 0`
   the vanishing range is empty. For positive `n`, apply induction to the difference
   polynomial `P(t) - P(t-1)` and put `b = max(1, m')` for its bound `m'`.
2. Pass to an infinite extension of the field. Projective-space base change
   (lemma-nagata-projective-space-base-change-proper and -pullback), flat coherent
   base change (lem-sc-flat-base-change-coherent), dimension invariance
   (lem-pc-finrank-field-base-change), and projective finiteness and vanishing
   (lem-pc-projective-space-coherent-finiteness and -cohomology-bound) preserve the
   polynomial and allow vanishing to descend.
3. Choose a common regular hyperplane for the quotient, kernel, free sheaf and
   structure sheaf (lem-sfb-coherent-regular-hyperplane-restriction). The stalkwise
   nonzerodivisor calculation gives a short exact restricted quotient sequence.
4. Its quotient has difference Euler polynomial by the hyperplane sequence. Induction
   makes the restricted kernel `m'`-regular. The regularity consequences
   (lem-sfb-m-regular-coherent-sheaf-consequences) give higher-cohomology vanishing
   on the hyperplane for all twists at least `b`.
5. The hyperplane long exact sequence makes the maps in degrees at least two
   injective for twists at least `b`. Serre vanishing
   (lem-pc-projective-space-serre-vanishing) then forces these groups to be zero.
6. Write `h_t` for the finite dimension of the first cohomology of the kernel at
   twist `t`. The same sequence gives surjections from twist `d-1` to `d` for `d ≥ b`.
7. An injective such map with `d > b` makes restriction of kernel sections at `d`
   surjective. Restriction of linear forms is surjective by the structure-sheaf
   sequence and lem-pc-projective-space-twist-cohomology. Hyperplane multiplication
   surjectivity lifts products of sections, so restriction at `d+1` is surjective.
   Thus injectivity propagates; eventual Serre vanishing forces a plateau to be zero.
8. While nonzero, the dimensions strictly decrease, so first cohomology vanishes
   at every twist at least `b + h_b`.
9. Twisting the quotient sequence and applying lem-pc-euler-additive and the twist
   cohomology calculation gives chi(K(b)) = r * binomial(n+b,n) - P(b).
   Higher cohomology above degree one is zero, and sections inject into the free
   sheaf's sections, so `0 ≤ h_b ≤ P(b)`. Put `N = max(0, ceil(P(b)))`.
10. Take `a = b + N + n + 1`. The first-cohomology bound applies at `a-1`; the
    higher-degree bound applies at `a-j` for `2 ≤ j ≤ n`. The choice is independent
    of the quotient and field, and descends by step 2. Impossible polynomials give
    a vacuous assertion. -/
theorem exists_freeQuotient_kernel_regularity_bound (n r : ℕ) (hr : 1 ≤ r)
    (P : Polynomial ℚ) :
    ∃ a : ℤ, ∀ (k : Type u) [Field k]
      (K F : (ℙ(ULift.{u} (Fin (n + 1)); Spec (CommRingCat.of k))).Modules)
      (i : K ⟶ SheafOfModules.free
        (R := (ℙ(ULift.{u} (Fin (n + 1)); Spec (CommRingCat.of k))).ringCatSheaf)
        (ULift.{u} (Fin r)))
      (q : SheafOfModules.free
        (R := (ℙ(ULift.{u} (Fin (n + 1)); Spec (CommRingCat.of k))).ringCatSheaf)
        (ULift.{u} (Fin r)) ⟶ F)
      (w : i ≫ q = 0),
      (CategoryTheory.ShortComplex.mk i q w).ShortExact →
      Scheme.Modules.IsQuasiCoherentFiniteType K →
      Scheme.Modules.IsQuasiCoherentFiniteType F →
      (∀ d : ℤ, ((F ⊗ twist (ULift.{u} (Fin (n + 1))) (Spec (CommRingCat.of k)) d).eulerChar
        k : ℚ) = P.eval (d : ℚ)) →
      ∀ j : ℕ, 1 ≤ j → j ≤ n →
        Subsingleton ((K ⊗ twist (ULift.{u} (Fin (n + 1)))
          (Spec (CommRingCat.of k)) (a - (j : ℤ))).H j) := by
  sorry

end AlgebraicGeometry.ProjectiveSpace
