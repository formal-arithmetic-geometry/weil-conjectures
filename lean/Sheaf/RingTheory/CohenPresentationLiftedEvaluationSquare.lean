/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.RingTheory.CohenRing
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Sheaf.AlgebraicGeometry.IsRegularScheme
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.FieldCohenPowerSeriesFormallySmooth
import WeilConjectures.RingTheory.FormallySmoothAdicLiftIntoComplete
import WeilConjectures.RingTheory.PowerSeriesAdicEvaluation

/-!
# Lifting a fixed Cohen presentation and adjoining kernel variables

Source: Stacks Project, dpa.tex, Tag 09PZ (lemma-ci-well-defined), first and third
proof paragraphs (blueprint: lem-trf-cohen-presentation-lifted-evaluation-square).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace MvPowerSeries

/-- A fixed field/Cohen presentation lifts through a complete local surjection and
extends by evaluation on any finite tuple of kernel generators.

Source: Stacks Project, dpa.tex, Tag 09PZ (lemma-ci-well-defined), first and third
proof paragraphs (blueprint: lem-trf-cohen-presentation-lifted-evaluation-square).
The two variable blocks are indexed by `Fin n ⊕ Fin s`. The coefficient equation for
`e` specifies exactly the regrouping into the iterated power-series ring. The formula
using `truncTotal N` is the sum over all monomials of total y-degree less than `N`.

Proof:
1. Regroup the coefficient family indexed by pairs of multiindices. Addition and
   multiplication agree coefficientwise, the latter by the same finite convolution
   sum (def-weil-pbc-multivariate-power-series). This gives `e`, including empty blocks.
   The constant-y coefficient projection has the constant-series inclusion as a section.
2. Apply lem-weil-pbc-power-series-field-cohen-regular-complete with n and n+s variables.
   Transfer along regrouping to obtain regular locality, completeness and the maximal
   ideal formulas. The projection sends coefficient and x generators into the target
   maximal ideal and y generators to zero, so is local.
3. Write J = ker r. Every element of J is a nonunit, so lies in the maximal ideal of R.
   If z belongs to every J + m_R^N, its image lies in every m_A^N and is zero by
   separatedness of A (def-weil-pbc-adically-complete-ring). Thus J is closed, and
   surjectivity identifies R/J with A.
4. Use lem-weil-pbc-field-cohen-power-series-formally-smooth over the integers, then
   lem-weil-pbc-fs-adic-lift-into-complete with source T₀, target R, I = m_R, J = ker r
   and both exponents one. Locality of c₀ and surjectivity of r give the required
   containment in the image of m_R: any lift of a nonunit is a nonunit. This gives
   the local lift f with r f = c₀.
5. Each b_j is in J, hence in m_R. Apply lem-weil-pbc-power-series-adic-evaluation
   with coefficient map f, ideal m_R and variables b to obtain h, its restrictions,
   and the displayed congruences. The maximal-ideal generators show h is local.
6. Apply r to these congruences. All positive-degree terms vanish, because r(b_j)=0;
   the constant term is c₀ of the constant-y coefficient. The error lies in m_A^N
   for every positive N, so separatedness gives the commuting square. For s=0,
   h is f and the projection is the identity; for n=0 the coefficient ring is Λ.
No surjectivity of h is asserted. -/
theorem cohen_presentation_lifted_evaluation_square
    {A : Type u} {R : Type v} {Λ : Type w}
    [CommRing A] [CommRing R] [CommRing Λ]
    [IsNoetherianRing A] [IsNoetherianRing R] [IsLocalRing A] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (r : R →+* A) [IsLocalHom r] (hr : Function.Surjective r)
    (p : ℕ) [CharP (IsLocalRing.ResidueField A) p]
    (hΛ : (p = 0 ∧ IsField Λ ∧ CharZero Λ) ∨ (0 < p ∧ IsCohenRing p Λ))
    (n : ℕ) (c₀ : MvPowerSeries (Fin n) Λ →+* A) [IsLocalHom c₀]
    (hc₀ : Function.Surjective c₀) (s : ℕ) (b : Fin s → R)
    (hb : Ideal.span (Set.range b) = RingHom.ker r) :
    ∃ (_ : IsLocalRing Λ)
      (_ : IsRegularLocalRing (MvPowerSeries (Fin n) Λ))
      (_ : IsRegularLocalRing (MvPowerSeries (Fin s) (MvPowerSeries (Fin n) Λ))),
      (∃ e : MvPowerSeries (Fin n ⊕ Fin s) Λ ≃+*
          MvPowerSeries (Fin s) (MvPowerSeries (Fin n) Λ),
        ∀ (G : MvPowerSeries (Fin n ⊕ Fin s) Λ)
          (α : Fin n →₀ ℕ) (ν : Fin s →₀ ℕ),
          coeff α (coeff ν (e G)) = coeff (Finsupp.sumElim α ν) G) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) Λ))
        (MvPowerSeries (Fin n) Λ) ∧
      IsAdicComplete
        (IsLocalRing.maximalIdeal (MvPowerSeries (Fin s) (MvPowerSeries (Fin n) Λ)))
        (MvPowerSeries (Fin s) (MvPowerSeries (Fin n) Λ)) ∧
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) Λ) =
        (IsLocalRing.maximalIdeal Λ).map C ⊔
          Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) Λ)) ∧
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin s) (MvPowerSeries (Fin n) Λ)) =
        (IsLocalRing.maximalIdeal Λ).map
            ((C : MvPowerSeries (Fin n) Λ →+*
              MvPowerSeries (Fin s) (MvPowerSeries (Fin n) Λ)).comp C) ⊔
          Ideal.span
            (Set.range (fun i : Fin n ↦
              (C (X i : MvPowerSeries (Fin n) Λ) :
                MvPowerSeries (Fin s) (MvPowerSeries (Fin n) Λ))) ∪
             Set.range (X : Fin s → MvPowerSeries (Fin s) (MvPowerSeries (Fin n) Λ))) ∧
      Function.Surjective
        (constantCoeff : MvPowerSeries (Fin s) (MvPowerSeries (Fin n) Λ) →+*
          MvPowerSeries (Fin n) Λ) ∧
      IsLocalHom
        (constantCoeff : MvPowerSeries (Fin s) (MvPowerSeries (Fin n) Λ) →+*
          MvPowerSeries (Fin n) Λ) ∧
      ∃ (f : MvPowerSeries (Fin n) Λ →+* R)
        (h : MvPowerSeries (Fin s) (MvPowerSeries (Fin n) Λ) →+* R),
        IsLocalHom f ∧ IsLocalHom h ∧ r.comp f = c₀ ∧ h.comp C = f ∧
        (∀ j : Fin s, h (X j) = b j) ∧ r.comp h = c₀.comp constantCoeff ∧
        ∀ (F : MvPowerSeries (Fin s) (MvPowerSeries (Fin n) Λ)) (N : ℕ),
          1 ≤ N →
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N) (h F) =
              Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N)
                (MvPolynomial.eval₂ f b (F.truncTotal N)) := by
  sorry

end MvPowerSeries
