/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.RingTheory.MonoidCompletionCoefficients
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Coefficient control and monomial survival in completed monoid hypersurfaces

Source: agent-formulated refinement of Illusie–Laszlo–Orgogozo, Travaux de Gabber,
Exposé VI 1.6(i)--(ii), printed p. 70 (model notation, not a theorem asserted there);
Stacks Project, Tags 00FN and 0316 for Noetherianity
(blueprint: lem-trf-complete-model-coefficient-nonvanishing).
-/

@[expose] public section

universe u v

namespace AddMonoidAlgebra

open Classical in
/-- Coefficients in a completed positive monoid algebra over a complete local domain,
and survival of every monomial modulo a series with nonzero nonunit constant term.

Source: agent-formulated refinement of ILO, Exposé VI 1.6(i)--(ii), printed p. 70,
and Stacks Project, Tags 00FN and 0316
(blueprint: lem-trf-complete-model-coefficient-nonvanishing).

The ring and algebra structures on `T → A` are quantified with their formulas, as in
`monoidCompletion_coefficients`; explicit structure arguments avoid the pointwise
multiplication instance on the function type. The ideal `J` is fixed by its displayed
identity, and every monomial is the image under the canonical completion map.

Proof plan (the node's six steps):
1. Choose finitely many nonzero generators of `T`, allowing an empty list. Mapping
   polynomial variables to their monomials surjects onto `A[T]`. Apply
   `lem-weil-pbc-finite-type-algebra-noetherian` and then
   `lem-weil-pbc-adic-completion-noetherian` to obtain Noetherianity of the completion.
2. Apply `lem-trf-monoid-completion-coefficients` to the inclusion `T → H` and `W`.
   This gives all coefficient families, componentwise addition, finite convolution,
   and the coefficient formula for `a z^t`. The coefficient `1 ≠ 0` at `t` proves
   every monomial is nonzero.
3. For a fixed exponent `t`, use strong induction on weights `n < W(t)`. At an
   exponent of weight `n`, every convolution term other than the constant term of
   `θ` involves a coefficient of `b` at strictly smaller weight, so is zero by
   induction. Thus `0 = r b_s`, and the domain hypothesis and `r ≠ 0` give `b_s = 0`.
   Weight zero starts the induction because all nonzero exponents have positive weight.
4. At `t` the same convolution leaves only `r b_t`; all other terms have second
   exponent of weight below `W(t)` and vanish by step 3.
5. The quotient is Noetherian by `lem-weil-pbc-surjective-image-noetherian`.
   If `z^t = θ b`, its coefficients vanish below `W(t)` and equal `1` at `t`.
   Steps 3--4 yield `1 = r b_t`, contradicting `r` in the proper maximal ideal.
6. For `T = {0}`, the generator list is empty, the completion is `A`, and `θ = r`.
   There are no lower weights; step 4 is ordinary multiplication and step 5 says
   `1` survives in `A/(r)`. Thus neither this case nor exponent zero is excluded.
-/
theorem completeModel_coefficient_nonvanishing
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (H : Type v) [AddCommGroup H] (T : AddSubmonoid H) [AddMonoid.FG T]
    (W : H →+ ℤ) (hpos : ∀ t : T, t ≠ 0 → 0 < W (t : H))
    (hfree : ∃ d : ℕ, Nonempty (H ≃+ (Fin d → ℤ))) :
    ∃ (J : Ideal (AddMonoidAlgebra A T)),
      J = Ideal.map (algebraMap A (AddMonoidAlgebra A T))
            (IsLocalRing.maximalIdeal A) ⊔
          Ideal.span {x | ∃ t : T, t ≠ 0 ∧ x = AddMonoidAlgebra.single t (1 : A)} ∧
      IsNoetherianRing (AdicCompletion J (AddMonoidAlgebra A T)) ∧
      ∃ (ring : CommRing (T → A))
        (alg : @Algebra A (T → A) _ ring.toSemiring)
        (c : @AlgEquiv A (AdicCompletion J (AddMonoidAlgebra A T)) (T → A)
          _ _ ring.toSemiring _ alg),
        (∀ (a b : T → A) (t : T),
          (@Add.add (T → A) ring.toAdd a b) t = a t + b t) ∧
        (∀ (a b : T → A) (t : T),
          (@Mul.mul (T → A) ring.toMul a b) t =
            ∑ᶠ q : {q : T × T // q.1 + q.2 = t}, a q.1.1 * b q.1.2) ∧
        (∀ t : T, Set.Finite {q : T × T | q.1 + q.2 = t}) ∧
        (∀ (a : A) (t s : T),
          c (AdicCompletion.of J (AddMonoidAlgebra A T)
            (AddMonoidAlgebra.single t a)) s = if s = t then a else 0) ∧
        (∀ t : T, AdicCompletion.of J (AddMonoidAlgebra A T)
          (AddMonoidAlgebra.single t (1 : A)) ≠ 0) ∧
        (∀ (r : A), r ∈ IsLocalRing.maximalIdeal A → r ≠ 0 →
          ∀ θ : AdicCompletion J (AddMonoidAlgebra A T), c θ 0 = r →
            IsNoetherianRing
              (AdicCompletion J (AddMonoidAlgebra A T) ⧸ Ideal.span {θ}) ∧
            (∀ t : T,
              Ideal.Quotient.mk (Ideal.span {θ})
                (AdicCompletion.of J (AddMonoidAlgebra A T)
                  (AddMonoidAlgebra.single t (1 : A))) ≠ 0) ∧
            (∀ (t : T) (b : AdicCompletion J (AddMonoidAlgebra A T)),
              (∀ s : T, W (s : H) < W (t : H) → c (θ * b) s = 0) →
                (∀ s : T, W (s : H) < W (t : H) → c b s = 0) ∧
                  c (θ * b) t = r * c b t)) := by
  sorry

end AddMonoidAlgebra
