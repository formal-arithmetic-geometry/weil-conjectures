/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q119
-/
module

public import Sheaf.RingTheory.CompleteToricModel
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.RingTheory.CohenRing
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Basic
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.RegularLocalLocalization
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import WeilConjectures.RingTheory.LocalizationOfRegularRing
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.LocalCompletionQuotient
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Cohen parameters after completed monoid substitution

Source: ILO, Travaux de Gabber, VI 1.6(ii), printed p. 70, and the auxiliary
Laurent-stratum verification in the DAG
(blueprint: lem-trf-cohen-monoid-substitution-parameter).

The helpers name the actual localizations, quotients, completions and canonical
maps in the statement. Their data are explicit; only the main assertion is postponed.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

namespace CohenMonoidSubstitution

variable {V : Type u} [CommRing V] {K : Type v} [AddCommGroup K] {n : ℕ}

/-- The localization `E_*` of `E = V[K][t]` at the chosen prime.
Source: ILO VI 1.6(ii), auxiliary stratum calculation
(blueprint: lem-trf-cohen-monoid-substitution-parameter). -/
abbrev Local (P : Ideal (ToricMonoid.PolynomialRing V K n)) [P.IsPrime] :=
  Localization.AtPrime P

/-- The maximal-ideal completion `D` of `E_*`.
Source: ILO VI 1.6(ii), auxiliary stratum calculation
(blueprint: lem-trf-cohen-monoid-substitution-parameter). -/
abbrev Complete (P : Ideal (ToricMonoid.PolynomialRing V K n)) [P.IsPrime] :=
  AdicCompletion (IsLocalRing.maximalIdeal (Local P)) (Local P)

/-- The old parameter ideal `(t)` in the localized ring.
Source: ILO VI 1.6(ii), auxiliary stratum calculation
(blueprint: lem-trf-cohen-monoid-substitution-parameter). -/
noncomputable def localParameters
    (P : Ideal (ToricMonoid.PolynomialRing V K n)) [P.IsPrime] : Ideal (Local P) :=
  (Ideal.span (Set.range (MvPolynomial.X : Fin n → ToricMonoid.PolynomialRing V K n))).map
    (algebraMap (ToricMonoid.PolynomialRing V K n) (Local P))

/-- The quotient `E' = E_* /(t)`.
Source: ILO VI 1.6(ii), auxiliary stratum calculation
(blueprint: lem-trf-cohen-monoid-substitution-parameter). -/
abbrev Stratum (P : Ideal (ToricMonoid.PolynomialRing V K n)) [P.IsPrime] :=
  Local P ⧸ localParameters P

/-- The old parameter ideal extended to `D`.
Source: ILO VI 1.6(ii), auxiliary stratum calculation
(blueprint: lem-trf-cohen-monoid-substitution-parameter). -/
noncomputable def completeParameters
    (P : Ideal (ToricMonoid.PolynomialRing V K n)) [P.IsPrime] : Ideal (Complete P) :=
  (localParameters P).map (algebraMap (Local P) (Complete P))

/-- The canonical map `E → E_* → D`.
Source: ILO VI 1.6(ii), auxiliary stratum calculation
(blueprint: lem-trf-cohen-monoid-substitution-parameter). -/
noncomputable def polynomialMap
    (P : Ideal (ToricMonoid.PolynomialRing V K n)) [P.IsPrime] :
    ToricMonoid.PolynomialRing V K n →+* Complete P :=
  (algebraMap (Local P) (Complete P)).comp
    (algebraMap (ToricMonoid.PolynomialRing V K n) (Local P))

/-- The prescribed coefficient map `V → D`.
Source: ILO VI 1.6(ii), auxiliary substitution calculation
(blueprint: lem-trf-cohen-monoid-substitution-parameter). -/
noncomputable def coefficientMap
    (P : Ideal (ToricMonoid.PolynomialRing V K n)) [P.IsPrime] : V →+* Complete P :=
  (polynomialMap P).comp (algebraMap V (ToricMonoid.PolynomialRing V K n))

/-- The image of a Laurent monomial `[k]` in `D`.
Source: ILO VI 1.6(ii), auxiliary substitution calculation
(blueprint: lem-trf-cohen-monoid-substitution-parameter). -/
noncomputable def latticeMonomial
    (P : Ideal (ToricMonoid.PolynomialRing V K n)) [P.IsPrime] (k : K) : Complete P :=
  polynomialMap P (MvPolynomial.C (AddMonoidAlgebra.single k (1 : V)))

/-- The image of an old variable `t_i` in `D`.
Source: ILO VI 1.6(ii), auxiliary substitution calculation
(blueprint: lem-trf-cohen-monoid-substitution-parameter). -/
noncomputable def oldParameter
    (P : Ideal (ToricMonoid.PolynomialRing V K n)) [P.IsPrime] (i : Fin n) : Complete P :=
  polynomialMap P (MvPolynomial.X i)

open Classical in
/-- Substitution preserves the nonzero Cohen parameter class after the old parameters
are set to zero.

Source: ILO VI 1.6(ii), printed p. 70; the strengthened Laurent-stratum verification
is the agent-origin argument of the node
(blueprint: lem-trf-cohen-monoid-substitution-parameter).

`I` and `J` are named by equalities, so they are exactly the displayed completion
ideals. The local and regular structures are conclusions, not added hypotheses.
The equation on `e` specifies the canonical completion-of-quotient comparison.
All completions carry their inverse-limit topologies, written as infima of the
induced discrete-quotient topologies. The augmentation is fixed on every monomial
with every coefficient, and therefore fixes `D` and kills nonzero monomials.

Proof:
1. Choose a finite basis of `K` and identify `V[K]` with a Laurent polynomial ring.
   By lem-weil-pbc-power-series-field-cohen-regular-complete with zero variables,
   Cohen rings and fields are regular local. Apply lem-weil-pbc-regular-local-localization,
   lem-trf-polynomial-ring-regular-base and lem-weil-pbc-localization-of-regular-ring
   to obtain regularity of the Laurent polynomial rings and their prime localizations.
2. Evaluating the old variables at zero gives `E' ≃ V[K]_q`; reducing modulo `p`
   gives `E'/p ≃ k[K]_(q/p)`. Hence both rings are regular local. The element `p`
   is nonzero: a denominator killing it would have all coefficients zero in the
   Cohen domain. It lies in the maximal ideal because `p ∈ P`.
3. Apply lem-weil-pbc-regular-local-quotient-independent-generators to `(p)` in `E'`.
   If `p` lay in the square of the maximal ideal, all independent generating
   cotangent classes would vanish. The generating set would be empty, contradicting
   `p ≠ 0`. Thus its cotangent class is nonzero.
4. By lem-weil-pbc-local-completion-quotient, `D/(t)D ≃ completion(E')`, with the
   displayed compatibility on `E_*`. Lem-weil-pbc-local-completion-local-ring
   identifies completed maximal ideals. Lem-weil-pbc-module-completion-complete at
   level two preserves the nonzero cotangent class and gives completeness of `D`.
5. Send `c[s]t^a` to `c[δ(s)][β(s)]t^a` on finite monoid polynomials.
   The completion ideal maps into the target completion ideal, since `p,t_i ∈ m_D`
   and `β(s) ≠ 0` for nonzero `s`. Compatible maps on all finite adic quotients
   give the continuous ring map `ψ`. Sharpness makes constant coefficient an
   augmentation; completeness of `D` extends it to the continuous map `ε`.
6. Expand `θ-p` as a finite sum of nonzero monomial multiples and old variable
   multiples. Applying `εψ` kills the former and gives `εψθ = p + Σ t_i a_i`.
   This proves the congruence and maximal-ideal membership. Its image under `e`
   is `p`, outside the completed maximal ideal squared by step 4, so `εψθ` cannot
   belong to `m_D²`. This also covers `n=0`, trivial monoids, and `θ=p-t_1`.
-/
theorem cohen_monoid_substitution_parameter
    (p : ℕ) (hV : IsCohenRing p V)
    [Module.Free ℤ K] [Module.Finite ℤ K]
    (S : Type w) [AddCommMonoid S] (T : Type z) [AddCommMonoid T]
    (hS : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative S))
    (hT : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative T))
    (hsharpS : ∀ s : S, IsUnit (Multiplicative.ofAdd s) → s = 0)
    (hsharpT : ∀ t : T, IsUnit (Multiplicative.ofAdd t) → t = 0)
    (f : S →+ K × T) (hβ : ∀ s : S, s ≠ 0 → (f s).2 ≠ 0)
    (P : Ideal (ToricMonoid.PolynomialRing V K n)) [P.IsPrime]
    (hp : (p : ToricMonoid.PolynomialRing V K n) ∈ P)
    (ht : ∀ i : Fin n, (MvPolynomial.X i : ToricMonoid.PolynomialRing V K n) ∈ P)
    (I : Ideal (ToricMonoid.PolynomialRing V S n))
    (hI : I = Ideal.span {(p : ToricMonoid.PolynomialRing V S n)} ⊔
      ToricMonoid.chartIdeal V S n) :
    ∃ (_ : IsLocalRing (Complete P)) (_ : IsRegularLocalRing (Stratum P)),
      IsRegularLocalRing (Stratum P ⧸ Ideal.span {(p : Stratum P)}) ∧
      (p : Stratum P) ≠ 0 ∧
      (p : Stratum P) ∈ IsLocalRing.maximalIdeal (Stratum P) ∧
      (p : Stratum P) ∉ IsLocalRing.maximalIdeal (Stratum P) ^ 2 ∧
      ∃ (_ : IsLocalRing
        (AdicCompletion (IsLocalRing.maximalIdeal (Stratum P)) (Stratum P)))
        (e : (Complete P ⧸ completeParameters P) ≃+*
          AdicCompletion (IsLocalRing.maximalIdeal (Stratum P)) (Stratum P)),
        (∀ a : Local P,
          e (Ideal.Quotient.mk (completeParameters P) (algebraMap (Local P) (Complete P) a)) =
            algebraMap (Stratum P)
              (AdicCompletion (IsLocalRing.maximalIdeal (Stratum P)) (Stratum P))
              (Ideal.Quotient.mk (localParameters P) a)) ∧
        (p : AdicCompletion (IsLocalRing.maximalIdeal (Stratum P)) (Stratum P)) ∈
          IsLocalRing.maximalIdeal
            (AdicCompletion (IsLocalRing.maximalIdeal (Stratum P)) (Stratum P)) ∧
        (p : AdicCompletion (IsLocalRing.maximalIdeal (Stratum P)) (Stratum P)) ∉
          IsLocalRing.maximalIdeal
            (AdicCompletion (IsLocalRing.maximalIdeal (Stratum P)) (Stratum P)) ^ 2 ∧
        ∀ (J : Ideal (AddMonoidAlgebra (Complete P) T)),
          J = (IsLocalRing.maximalIdeal (Complete P)).map
              (algebraMap (Complete P) (AddMonoidAlgebra (Complete P) T)) ⊔
            Ideal.span {b | ∃ t : T, t ≠ 0 ∧ b = AddMonoidAlgebra.single t (1 : Complete P)} →
          ∃ ψ : AdicCompletion I (ToricMonoid.PolynomialRing V S n) →+*
              AdicCompletion J (AddMonoidAlgebra (Complete P) T),
            @Continuous _ _
              (⨅ l : ℕ, TopologicalSpace.induced (AdicCompletion.evalₐ I l) ⊥)
              (⨅ l : ℕ, TopologicalSpace.induced (AdicCompletion.evalₐ J l) ⊥) ψ ∧
            (∀ (s : S) (c : V),
              ψ (AdicCompletion.of I (ToricMonoid.PolynomialRing V S n)
                (MvPolynomial.C (AddMonoidAlgebra.single s c))) =
              AdicCompletion.of J (AddMonoidAlgebra (Complete P) T)
                (AddMonoidAlgebra.single (f s).2
                  (coefficientMap P c * latticeMonomial P (f s).1))) ∧
            (∀ i : Fin n,
              ψ (AdicCompletion.of I (ToricMonoid.PolynomialRing V S n) (MvPolynomial.X i)) =
              algebraMap (Complete P) (AdicCompletion J (AddMonoidAlgebra (Complete P) T))
                (oldParameter P i)) ∧
            ∃ ε : AdicCompletion J (AddMonoidAlgebra (Complete P) T) →+* Complete P,
              @Continuous _ _
                (⨅ l : ℕ, TopologicalSpace.induced (AdicCompletion.evalₐ J l) ⊥)
                (IsLocalRing.maximalIdeal (Complete P)).adicTopology ε ∧
              (∀ (t : T) (d : Complete P),
                ε (AdicCompletion.of J (AddMonoidAlgebra (Complete P) T)
                  (AddMonoidAlgebra.single t d)) = if t = 0 then d else 0) ∧
              ∀ θ : AdicCompletion I (ToricMonoid.PolynomialRing V S n),
                θ - (p : AdicCompletion I (ToricMonoid.PolynomialRing V S n)) ∈
                  (ToricMonoid.chartIdeal V S n).map
                    (algebraMap (ToricMonoid.PolynomialRing V S n)
                      (AdicCompletion I (ToricMonoid.PolynomialRing V S n))) →
                ε (ψ θ) - (p : Complete P) ∈ completeParameters P ∧
                ε (ψ θ) ∈ IsLocalRing.maximalIdeal (Complete P) ∧
                ε (ψ θ) ∉ IsLocalRing.maximalIdeal (Complete P) ^ 2 ∧
                Ideal.Quotient.mk (completeParameters P) (ε (ψ θ)) =
                  (p : Complete P ⧸ completeParameters P) ∧
                e (Ideal.Quotient.mk (completeParameters P) (ε (ψ θ))) =
                  (p : AdicCompletion (IsLocalRing.maximalIdeal (Stratum P)) (Stratum P)) := by
  sorry

end CohenMonoidSubstitution
