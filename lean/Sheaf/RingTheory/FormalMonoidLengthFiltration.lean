module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Length
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Order.PiLex
public import Mathlib.LinearAlgebra.Quotient.Basic
import Sheaf.RingTheory.MonoidCompletionCoefficients

/-!
# Monomial filtration of a truncated monoid completion

Source: ILO, Travaux de Gabber, VI 1.6(i)--(ii), printed p. 70, formal monoid
models; the monomial-filtration refinement is agent-supplied. Length additivity
is Stacks Project, Tag 00IV (blueprint: lem-trf-formal-monoid-length-filtration).
-/

@[expose] public section

universe u v w

open scoped DirectSum

namespace AddMonoidAlgebra

/-- The extended nth ideal power in the completed monoid algebra.
Source: ILO VI 1.6(i)--(ii), printed p. 70, agent-supplied filtration refinement
(blueprint: lem-trf-formal-monoid-length-filtration). -/
noncomputable abbrev monoidFiltrationPower {A : Type u} [CommRing A]
    {P : Type v} [AddCommMonoid P] (b : Ideal (AddMonoidAlgebra A P)) (n : ℕ) :
    Ideal (AdicCompletion b (AddMonoidAlgebra A P)) :=
  Ideal.map (algebraMap (AddMonoidAlgebra A P)
    (AdicCompletion b (AddMonoidAlgebra A P))) (b ^ n)

/-- The truncated completion `B / b^n B`, with its canonical scalar actions.
Source: ILO VI 1.6(i)--(ii), printed p. 70, agent-supplied filtration refinement
(blueprint: lem-trf-formal-monoid-length-filtration). -/
abbrev monoidFiltrationQuotient {A : Type u} [CommRing A]
    {P : Type v} [AddCommMonoid P] (b : Ideal (AddMonoidAlgebra A P)) (n : ℕ) :=
  AdicCompletion b (AddMonoidAlgebra A P) ⧸ monoidFiltrationPower b n

open Classical in
/-- Ordered coefficient tails give the monomial filtration and its length formula.

Source: ILO VI 1.6(i)--(ii), printed p. 70, agent-supplied refinement; Stacks
Tag 00IV (blueprint: lem-trf-formal-monoid-length-filtration).

Indices start at zero: `F 0` is the paper's `F₁`, and `F (Fin.last N)` is
`F_{N+1}`. The coefficient identification is normalized on every polynomial
representative. The constant map is characterized modulo every power by the
completion projections, so it is the canonical constant coefficient, not an
unspecified algebra map. Each factor equivalence is `A`-linear and intertwines
all `B`-scalars with their constant coefficients: exactly a `B`-module
isomorphism for the stated action. The additive-subgroup stability equivalence
says precisely that the two submodule lattices coincide.

Proof plan:
1. Apply `lem-trf-monoid-completion-coefficients` to obtain the attained maximal
   decomposition lengths, finite sublevel sets, coefficient completion and its
   finite-level coefficient identification. Every class has a polynomial lift
   supported on the finite sublevel set.
2. Positivity implies that a sum of two exponents is zero only if both are zero.
   Thus constant coefficient is multiplicative, and constants give its section.
   The weighted lexicographic order is total and adding a nonzero exponent
   strictly increases it. List the finite sublevel set in this order.
3. For a tail starting at `t j`, lift all earlier coefficients as zero. In a
   convolution coefficient at or below `t j`, a nonzero second exponent would
   strictly increase the first exponent. Therefore earlier coefficients remain
   zero and the coefficient at `t j` is multiplied by the constant coefficient.
   This proves stability of the tails and the asserted scalar action.
4. Coefficient at `t j` is surjective, with kernel the next tail. Its inverse on
   the factor sends a residue `a` to the monomial `a z^(t j)`. This is independent
   of the lift by the coefficient ideal criterion. The first isomorphism theorem
   gives the displayed equivalence. Stability under all constants is equivalent
   to stability under all `B`-scalars, since constants split the constant map.
5. `lem-trf-maximal-adic-graded-length-bridge` gives finite length of `A/m^k`.
   Apply `lem-weil-pbc-length-additive-short-exact` (Mathlib's
   `Module.length_eq_add_of_exact`) successively to the tail inclusions,
   starting at the zero tail. This proves finite length and the sum formula.
-/
theorem formalMonoid_length_filtration
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (P : Type v) [AddCommMonoid P] [AddMonoid.FG P]
    (G : Type w) [AddCommGroup G] (ι : P →+ G) (hι : Function.Injective ι)
    (wgt : G →+ ℤ) (hpos : ∀ p : P, p ≠ 0 → 0 < wgt (ι p))
    (r : ℕ) (coordinates : G ≃+ (Fin r → ℤ))
    (b : Ideal (AddMonoidAlgebra A P))
    (hb : b = Ideal.map (algebraMap A (AddMonoidAlgebra A P))
        (IsLocalRing.maximalIdeal A) ⊔
      Ideal.span {x | ∃ p : P, p ≠ 0 ∧ x = single p (1 : A)}) :
    ∃ ν : P → ℕ,
      ν 0 = 0 ∧
      (∀ p : P, IsGreatest {q : ℕ | ∃ f : Fin q → P,
        (∀ i : Fin q, f i ≠ 0) ∧ (∑ i, f i) = p} (ν p)) ∧
      (∀ k : ℕ, 1 ≤ k →
        Module.length A (A ⧸ (IsLocalRing.maximalIdeal A) ^ k) < ⊤) ∧
      ∃ c : AdicCompletion b (AddMonoidAlgebra A P) →ₐ[A] A,
        (∀ (k : ℕ) (x : AdicCompletion b (AddMonoidAlgebra A P))
            (f : AddMonoidAlgebra A P),
          AdicCompletion.evalₐ b k x = Ideal.Quotient.mk (b ^ k) f →
          Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ k) (c x) =
            Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ k) (f.coeff 0)) ∧
        ∀ n : ℕ, 1 ≤ n →
          Set.Finite {p : P | ν p < n} ∧
          ∃ e : monoidFiltrationQuotient b n ≃ₗ[A]
              ⨁ p : {p : P // ν p < n},
                A ⧸ (IsLocalRing.maximalIdeal A) ^ (n - ν p.1),
            (∀ (f : AddMonoidAlgebra A P) (p : {p : P // ν p < n}),
              e (Ideal.Quotient.mk (monoidFiltrationPower b n)
                (AdicCompletion.of b (AddMonoidAlgebra A P) f)) p =
                Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ (n - ν p.1)) (f.coeff p.1)) ∧
            (∀ (N : ℕ) (t : Fin N ≃ {p : P // ν p < n}),
              (∀ i j : Fin N, i < j →
                wgt (ι (t i).1) < wgt (ι (t j).1) ∨
                  (wgt (ι (t i).1) = wgt (ι (t j).1) ∧
                    Pi.Lex (· < ·) (· < ·)
                      (coordinates (ι (t i).1)) (coordinates (ι (t j).1)))) →
              ∃ F : Fin (N + 1) → Submodule
                  (AdicCompletion b (AddMonoidAlgebra A P)) (monoidFiltrationQuotient b n),
                (∀ (j : Fin (N + 1)) (x : monoidFiltrationQuotient b n),
                  x ∈ F j ↔ ∀ i : Fin N, i.val < j.val → e x (t i) = 0) ∧
                F 0 = ⊤ ∧ F (Fin.last N) = ⊥ ∧
                (∀ j : Fin N, F j.succ ≤ F j.castSucc) ∧
                ∀ j : Fin N,
                  ∃ φ : ((F j.castSucc) ⧸
                      (F j.succ).comap (F j.castSucc).subtype) ≃ₗ[A]
                      (A ⧸ (IsLocalRing.maximalIdeal A) ^ (n - ν (t j).1)),
                    (∀ x : F j.castSucc,
                      φ (Submodule.Quotient.mk x) = e x.1 (t j)) ∧
                    (∀ (a : AdicCompletion b (AddMonoidAlgebra A P))
                        (x : (F j.castSucc) ⧸ (F j.succ).comap (F j.castSucc).subtype),
                      φ (a • x) = c a • φ x) ∧
                    (∀ T : AddSubgroup
                        (A ⧸ (IsLocalRing.maximalIdeal A) ^ (n - ν (t j).1)),
                      (∀ (a : AdicCompletion b (AddMonoidAlgebra A P))
                        (x : A ⧸ (IsLocalRing.maximalIdeal A) ^ (n - ν (t j).1)),
                        x ∈ T → c a • x ∈ T) ↔
                      (∀ (a : A)
                        (x : A ⧸ (IsLocalRing.maximalIdeal A) ^ (n - ν (t j).1)),
                        x ∈ T → a • x ∈ T))) ∧
            Module.length (AdicCompletion b (AddMonoidAlgebra A P))
              (monoidFiltrationQuotient b n) < ⊤ ∧
            Module.length (AdicCompletion b (AddMonoidAlgebra A P))
                (monoidFiltrationQuotient b n) =
              ∑ᶠ p : {p : P // ν p < n},
                Module.length A (A ⧸ (IsLocalRing.maximalIdeal A) ^ (n - ν p.1)) := by
  sorry

end AddMonoidAlgebra
