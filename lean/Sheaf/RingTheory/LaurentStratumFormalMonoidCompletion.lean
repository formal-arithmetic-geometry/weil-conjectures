/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.RingTheory.CohenRing
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.LocalizationOfRegularRing
import WeilConjectures.RingTheory.CompletionRegularLocal
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Sheaf.TraceFormula.SharpFsOrthantEmbedding
import Sheaf.NumberTheory.Padics.AdicInverseLimitIso

/-! # Completion over a Laurent coefficient stratum

Source: ILO, Travaux de Gabber, VI 1.6, printed p. 70; the agent-supplied
Laurent coefficient comparison and augmentation calculation attached to that model
(blueprint: lem-trf-laurent-stratum-formal-monoid-completion).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace AddMonoidAlgebra.LaurentStratum

/-- The literal Laurent group ring with `n` polynomial variables, `L[K][t]`.
Source: the coefficient-stratum construction attached to ILO VI 1.6, p. 70
(blueprint: lem-trf-laurent-stratum-formal-monoid-completion). -/
abbrev CoefficientRing (L : Type u) [CommRing L] (K : Type v) [AddCommGroup K] (n : ℕ) :=
  MvPolynomial (Fin n) (AddMonoidAlgebra L K)

/-- The coefficient localization `E_* = E_p`, using Mathlib's localization.
Source: ILO VI 1.6, p. 70, coefficient-stratum construction
(blueprint: lem-trf-laurent-stratum-formal-monoid-completion). -/
abbrev LocalCoefficients {L : Type u} [CommRing L] {K : Type v} [AddCommGroup K]
    {n : ℕ} (p : Ideal (CoefficientRing L K n)) [p.IsPrime] := Localization.AtPrime p

/-- The maximal-ideal completion `D` of the literal coefficient localization.
Source: ILO VI 1.6, p. 70, coefficient-stratum construction; Stacks Tag 00M9
(blueprint: lem-trf-laurent-stratum-formal-monoid-completion). -/
abbrev CompletedCoefficients {L : Type u} [CommRing L] {K : Type v} [AddCommGroup K]
    {n : ℕ} (p : Ideal (CoefficientRing L K n)) [p.IsPrime] :=
  AdicCompletion (IsLocalRing.maximalIdeal (LocalCoefficients p)) (LocalCoefficients p)

/-- Completion at the Laurent coefficient stratum, with all comparison maps normalized.
The maps `q` and `s` point out of the middle quotient; thus the displayed first
isomorphism of the node is `q.symm`. The variables `r`, `b`, and `a` are fixed by
explicit equalities, not arbitrary additional choices. All completions are Mathlib's
compatible-family construction. The topologies are the adic topologies of the extended
ideals. The last inverse formula specifies the coefficient inclusion into `H/J`.

Source: ILO, Travaux de Gabber, VI 1.6, printed p. 70; agent-supplied refinement
(blueprint: lem-trf-laurent-stratum-formal-monoid-completion).

Proof plan:
1. The zero-variable case of `lem-weil-pbc-power-series-field-cohen-regular-complete`
   makes `L` regular local. Use `lem-weil-pbc-regular-local-localization` and identify
   its group ring, after a basis of `K`, with a polynomial ring localized at the
   product of the Laurent variables. `lem-trf-polynomial-ring-regular-base` and
   `lem-weil-pbc-localization-of-regular-ring` make `E` regular Noetherian, hence
   `E_p` regular local. Empty Laurent variable lists localize at 1.
2. `lem-weil-pbc-completion-regular-local`, `lem-weil-pbc-adic-completion-noetherian`,
   `lem-weil-pbc-local-completion-local-ring`, and
   `lem-weil-pbc-adic-completion-mod-ideal` give the asserted properties of `D`.
   Reduction sends `e/s` to its fraction in `Frac(E/p)`, identifying the residue
   field and proving nonzeroness.
3. `lem-trf-sharp-fs-orthant-embedding` embeds `T` in a finite orthant. Coordinate
   sum is a strictly positive weight. Nonzero members of a finite generating list
   generate the monomial ideal; `lem-weil-pbc-finite-type-algebra-noetherian` and
   `lem-weil-pbc-localization-noetherian` make all rings and defining ideals
   Noetherian and finitely generated.
4. Sharpness makes constant coefficient a ring map. The kernel of `U -> E/p`
   is `r`, so `r` is prime. Coefficient denominators outside `p` are invertible
   in `Z`; extend to `f : E_p[T] -> Z`. Its defining ideal extends to `m_Z`.
5. In `B/b^j`, a denominator is `c+h`, with `c` a unit and `h^j=0`. Its inverse
   is `c⁻¹ * sum (i=0,...,j-1) (-c⁻¹*h)^i`. The fraction equality criterion in
   `def-weil-pbc-localization-at-prime` makes this well-defined. It inverts `q`,
   and the quotient maps commute with reduction since they extend the same map.
6. `lem-trf-positive-monoid-adic-filtration` identifies the finite coefficient
   quotients as sums of `A/m^(j-ν(v))`. The map `A -> D` identifies each summand
   by `lem-weil-pbc-adic-completion-mod-power`. Hence `s` is a ring isomorphism;
   every level is induced by the same coefficient map, so reductions commute.
7. Apply `lem-trf-adic-inverse-limit-iso` to `s ∘ q.symm`. This gives `e` and its
   projection equations, coefficient and monomial normalization. Projection kernels
   are extended ideal powers by `lem-weil-pbc-adic-completion-mod-power`, proving
   continuity of both directions for the displayed adic topologies.
8. `lem-trf-formal-monoid-residue-domain`, with the embedding and weight of step 3,
   gives the constant coefficient map and its monomial kernel. It induces `g`,
   whose inverse is coefficient inclusion. For the zero monoid the generator list
   is empty and `H=D`. The same constructions allow `K=0` and `n=0`.
-/
theorem completion
    (L : Type u) [CommRing L] [IsLocalRing L]
    (hL : IsField L ∨ ∃ p₀ : ℕ, IsCohenRing p₀ L)
    (K : Type v) [AddCommGroup K] [Module.Free ℤ K] [Module.Finite ℤ K]
    (T : Type w) [AddCommMonoid T]
    (hfs : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative T))
    (hsharp : ∀ t : T, IsUnit (Multiplicative.ofAdd t) → t = 0)
    (n : ℕ) (p : Ideal (CoefficientRing L K n)) [p.IsPrime]
    (hp : Ideal.map (algebraMap L (CoefficientRing L K n)) (IsLocalRing.maximalIdeal L) ⊔
      Ideal.span (Set.range (MvPolynomial.X : Fin n → CoefficientRing L K n)) ≤ p)
    (r : Ideal (AddMonoidAlgebra (CoefficientRing L K n) T))
    (hr : r = Ideal.map (algebraMap (CoefficientRing L K n)
        (AddMonoidAlgebra (CoefficientRing L K n) T)) p ⊔
      Ideal.span {z | ∃ t : T, t ≠ 0 ∧ z = single t (1 : CoefficientRing L K n)}) :
    ∃ _ : IsRegularLocalRing (CompletedCoefficients p),
      Nontrivial (CompletedCoefficients p) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (CompletedCoefficients p))
        (CompletedCoefficients p) ∧
      (∃ k : (CompletedCoefficients p ⧸ IsLocalRing.maximalIdeal (CompletedCoefficients p))
          ≃+* FractionRing (CoefficientRing L K n ⧸ p),
        ∀ e₀ : CoefficientRing L K n,
          k (Ideal.Quotient.mk _ (algebraMap (LocalCoefficients p) (CompletedCoefficients p)
            (algebraMap (CoefficientRing L K n) (LocalCoefficients p) e₀))) =
          algebraMap (CoefficientRing L K n ⧸ p) (FractionRing (CoefficientRing L K n ⧸ p))
            (Ideal.Quotient.mk p e₀)) ∧
      ∃ _ : r.IsPrime,
      ∀ (b : Ideal (AddMonoidAlgebra (LocalCoefficients p) T)),
        b = Ideal.map (algebraMap (LocalCoefficients p)
            (AddMonoidAlgebra (LocalCoefficients p) T))
            (IsLocalRing.maximalIdeal (LocalCoefficients p)) ⊔
          Ideal.span {z | ∃ t : T, t ≠ 0 ∧ z = single t (1 : LocalCoefficients p)} →
      ∀ (a : Ideal (AddMonoidAlgebra (CompletedCoefficients p) T)),
        a = Ideal.map (algebraMap (CompletedCoefficients p)
            (AddMonoidAlgebra (CompletedCoefficients p) T))
            (IsLocalRing.maximalIdeal (CompletedCoefficients p)) ⊔
          Ideal.span {z | ∃ t : T, t ≠ 0 ∧ z = single t (1 : CompletedCoefficients p)} →
      ∃ f : AddMonoidAlgebra (LocalCoefficients p) T →+* Localization.AtPrime r,
        (∀ (t : T) (e₀ : CoefficientRing L K n),
          f (single t (algebraMap (CoefficientRing L K n) (LocalCoefficients p) e₀)) =
          algebraMap (AddMonoidAlgebra (CoefficientRing L K n) T) (Localization.AtPrime r)
            (single t e₀)) ∧
      ∃ (q : ∀ j : ℕ, 0 < j →
          (AddMonoidAlgebra (LocalCoefficients p) T ⧸ b ^ j) ≃+*
          (Localization.AtPrime r ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime r) ^ j))
        (s : ∀ j : ℕ, 0 < j →
          (AddMonoidAlgebra (LocalCoefficients p) T ⧸ b ^ j) ≃+*
          (AddMonoidAlgebra (CompletedCoefficients p) T ⧸ a ^ j)),
        (∀ (j : ℕ) (hj : 0 < j) (x : AddMonoidAlgebra (LocalCoefficients p) T),
          q j hj (Ideal.Quotient.mk (b ^ j) x) = Ideal.Quotient.mk _ (f x)) ∧
        (∀ (j : ℕ) (hj : 0 < j) (x : AddMonoidAlgebra (LocalCoefficients p) T),
          s j hj (Ideal.Quotient.mk (b ^ j) x) = Ideal.Quotient.mk (a ^ j)
            (mapRingHom T (algebraMap (LocalCoefficients p) (CompletedCoefficients p)) x)) ∧
        (∀ (i j : ℕ) (hij : i ≤ j) (hi : 0 < i) (hj : 0 < j)
            (x : AddMonoidAlgebra (LocalCoefficients p) T ⧸ b ^ j),
          Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal (Localization.AtPrime r)) hij
            (q j hj x) = q i hi (Ideal.Quotient.factorPow b hij x)) ∧
        (∀ (i j : ℕ) (hij : i ≤ j) (hi : 0 < i) (hj : 0 < j)
            (x : AddMonoidAlgebra (LocalCoefficients p) T ⧸ b ^ j),
          Ideal.Quotient.factorPow a hij (s j hj x) =
            s i hi (Ideal.Quotient.factorPow b hij x)) ∧
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime r))
          (Localization.AtPrime r) ≃+*
          AdicCompletion a (AddMonoidAlgebra (CompletedCoefficients p) T),
        (∀ (j : ℕ) (hj : 0 < j)
            (x : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime r))
              (Localization.AtPrime r)),
          AdicCompletion.evalₐ a j (e x) =
          s j hj ((q j hj).symm (AdicCompletion.evalₐ
            (IsLocalRing.maximalIdeal (Localization.AtPrime r)) j x))) ∧
        @Continuous _ _
          (Ideal.map (algebraMap (Localization.AtPrime r)
            (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime r))
              (Localization.AtPrime r)))
            (IsLocalRing.maximalIdeal (Localization.AtPrime r))).adicTopology
          (Ideal.map (algebraMap (AddMonoidAlgebra (CompletedCoefficients p) T)
            (AdicCompletion a (AddMonoidAlgebra (CompletedCoefficients p) T))) a).adicTopology e ∧
        @Continuous _ _
          (Ideal.map (algebraMap (AddMonoidAlgebra (CompletedCoefficients p) T)
            (AdicCompletion a (AddMonoidAlgebra (CompletedCoefficients p) T))) a).adicTopology
          (Ideal.map (algebraMap (Localization.AtPrime r)
            (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime r))
              (Localization.AtPrime r)))
            (IsLocalRing.maximalIdeal (Localization.AtPrime r))).adicTopology e.symm ∧
        (∀ (t : T) (e₀ : CoefficientRing L K n),
          e (AdicCompletion.of (IsLocalRing.maximalIdeal (Localization.AtPrime r))
            (Localization.AtPrime r)
            (algebraMap (AddMonoidAlgebra (CoefficientRing L K n) T) (Localization.AtPrime r)
              (single t e₀))) =
          AdicCompletion.of a (AddMonoidAlgebra (CompletedCoefficients p) T)
            (single t (algebraMap (LocalCoefficients p) (CompletedCoefficients p)
              (algebraMap (CoefficientRing L K n) (LocalCoefficients p) e₀)))) ∧
      ∃ ε : AdicCompletion a (AddMonoidAlgebra (CompletedCoefficients p) T) →+*
          CompletedCoefficients p,
        (∀ (t : T) (d : CompletedCoefficients p),
          ε (AdicCompletion.of a (AddMonoidAlgebra (CompletedCoefficients p) T) (single t d)) =
            @ite (CompletedCoefficients p) (t = 0) (Classical.propDecidable (t = 0)) d 0) ∧
      ∃ g : (AdicCompletion a (AddMonoidAlgebra (CompletedCoefficients p) T) ⧸
          Ideal.span {z | ∃ t : T, t ≠ 0 ∧
            z = AdicCompletion.of a (AddMonoidAlgebra (CompletedCoefficients p) T) (single t 1)})
          ≃+* CompletedCoefficients p,
        (∀ x : AdicCompletion a (AddMonoidAlgebra (CompletedCoefficients p) T),
          g (Ideal.Quotient.mk _ x) = ε x) ∧
        ∀ d : CompletedCoefficients p,
          g.symm d = Ideal.Quotient.mk _
            (AdicCompletion.of a (AddMonoidAlgebra (CompletedCoefficients p) T) (single 0 d)) := by
  sorry

end AddMonoidAlgebra.LaurentStratum
