module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.Separable

import Mathlib.FieldTheory.FinTrdeg
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.MvPowerSeries.Expand

/-!
# Perfect core of a finitely generated extension of a perfect field

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose IV, 3.2.1 and
Proposition 3.2.3(ii),(iii), printed pp. 55--56
(blueprint: lem-sfb-finitely-generated-residue-perfect-core).

Membership in the intersection of the images of all iterated Frobenius maps is
expressed pointwise by the existence of a `p ^ n`-th root for every natural `n`.
-/

@[expose] public section

universe u v

/-- Every element of the perfect core of a finitely generated field extension of a
perfect field of characteristic `p` is separable algebraic over the base field.
`IsSeparable k x` includes algebraicity, since a transcendental element has zero
minimal polynomial, which is not separable.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose IV, 3.2.1 and
Proposition 3.2.3(ii),(iii), printed pp. 55--56
(blueprint: lem-sfb-finitely-generated-residue-perfect-core).

Proof plan:
1. Write `L = k(a_1, ..., a_m)`. Choose a finite transcendence basis using
   `lem-weil-pbc-finitely-generated-field-finite-transcendence-basis` and put
   `F = k(t_1, ..., t_r)`. The generators `a_j` are algebraic over `F`, so
   `lem-weil-pbc-algebraic-generators-finite-extension` makes `L/F` finite.
   This includes the empty basis and the empty list of generators.
2. For a characteristic-`p` field `H`, shift a Laurent series into `H[[t]]`.
   Apply `lem-weil-pbc-power-series-frobenius-coefficientwise` and cancel
   the shift to obtain that the coefficient `b_i` moves to exponent `p*i`
   and becomes `b_i ^ p`. Iteration gives exponent `p^n*i` and coefficient
   `b_i ^ (p^n)`, with the zeroth iteration equal to the identity.
3. An element of the perfect core of `H((t))` has support divisible by every
   `p^n`. A nonzero integer cannot be divisible by these unbounded powers,
   so the series is constant. The constant coefficients of its roots show
   that this constant belongs to the perfect core of `H`. Conversely roots
   in `H` give constant roots in `H((t))`. Zero is included.
4. Embed `F` in the iterated Laurent field `k((T_1))...((T_r))`; Laurent
   coefficient comparison makes the polynomial map injective, and fractions
   extend it to `F`. The fields exist by `lem-weil-pbc-laurent-series-field`,
   and the presentation of `F` is `def-weil-pbc-transcendence-basis`.
   Successive applications of step 3 show that its perfect core is that of
   `k`, hence `k` itself by repeated surjectivity of the base Frobenius.
   Roots in `F` map to roots in the Laurent field; conversely roots of base
   elements already lie in `k`. Thus the perfect core of `F` is `k`, also
   when `r = 0` and the embedding is the identity.
5. Apply `lem-per-finite-extension-perfect-core` to `L/F`: each element of
   the perfect core of `L` is algebraic over the perfect core of `F`, hence
   over `k`. Separability of `L/F` is unnecessary.
6. Let `P` be the monic irreducible minimal polynomial of such an element.
   If its derivative vanishes, all nonzero exponents are divisible by `p`.
   Taking `p`-th roots of coefficients in `k` gives `P = Q^p` with positive
   degree `Q`, contradicting irreducibility. Its nonzero derivative has
   smaller degree, so it is coprime to `P`. This is separability by
   `def-weil-pbc-separable-algebraic-extension`, also for zero and for an
   algebraic extension `L/k`. -/
theorem isSeparable_of_fg_of_forall_exists_pow_eq
    {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    (p : ℕ) [Fact p.Prime] [CharP k p] [CharP L p]
    (hperfect : Function.Surjective (fun a : k ↦ a ^ p))
    (hfg : (⊤ : IntermediateField k L).FG)
    (x : L) (hx : ∀ n : ℕ, ∃ y : L, y ^ (p ^ n) = x) :
    IsSeparable k x := by
  sorry
