/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Fin.Tuple.Basic
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.CompletionRegularLocal
import WeilConjectures.RingTheory.CompletionDimension
import Sheaf.RingTheory.RegularCompleteCoefficientCoordinates
import WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete

/-! # Completions of parameter charts with prescribed coefficients

Source: Stacks Project, Algebra, Tag 0C0S (2) and its proof; the explicit parameter-chart
calculation in the accepted DAG proof.
(blueprint: lem-trf-parameter-chart-completion-substitution).

The pivot is `none` precisely for the empty chart. Coordinates retain their original
labels: the pivot, the ratio coordinates, and the coordinates outside the center.
All auxiliary definitions are the explicit rings and maps of this single statement.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace IsLocalRing

variable {R : Type u} [CommRing R] {n r : ℕ}

/-- The concatenated parameter list `(u,t)` in the polynomial ring.
Source: Tag 0C0S, parameter-chart calculation
(blueprint: lem-trf-parameter-chart-completion-substitution). -/
noncomputable def parameterChartBaseParameter (u : Fin n → R) :
    Fin (n + r) → MvPolynomial (Fin r) R :=
  Fin.append (fun i ↦ MvPolynomial.C (u i)) MvPolynomial.X

/-- Original labels embedded in one larger finite type; the final label is unused.
Source: Tag 0C0S, parameter-chart calculation
(blueprint: lem-trf-parameter-chart-completion-substitution). -/
noncomputable def parameterChartCenter (J : Finset (Fin (n + r))) : Finset (Fin (n + r + 1)) :=
  J.image Fin.castSucc

/-- A pivot in the larger label type; the unused last label handles the empty center.
Source: Tag 0C0S, parameter-chart calculation
(blueprint: lem-trf-parameter-chart-completion-substitution). -/
noncomputable def parameterChartPivot (a : Option (Fin (n + r))) : Fin (n + r + 1) :=
  a.elim (Fin.last (n + r)) Fin.castSucc

/-- The displayed quotient chart, with an unused final zero parameter.
That parameter never belongs to the center, so it creates no relation or ratio variable.
Source: Tag 0C0S, parameter-chart calculation
(blueprint: lem-trf-parameter-chart-completion-substitution). -/
noncomputable abbrev ParameterChartRing (u : Fin n → R) (J : Finset (Fin (n + r)))
    (a : Option (Fin (n + r))) :=
  MvPolynomial ((parameterChartCenter J).erase (parameterChartPivot a))
      (MvPolynomial (Fin r) R) ⧸
    (Ideal.span (Set.range (fun i : (parameterChartCenter J).erase (parameterChartPivot a) ↦
      MvPolynomial.C (Fin.snoc (α := fun _ : Fin (n + r + 1) ↦ MvPolynomial (Fin r) R)
        (parameterChartBaseParameter (r := r) u) 0 i.1) -
      MvPolynomial.C (Fin.snoc (α := fun _ : Fin (n + r + 1) ↦ MvPolynomial (Fin r) R)
        (parameterChartBaseParameter (r := r) u) 0 (parameterChartPivot a)) * MvPolynomial.X i)) :
      Ideal (MvPolynomial ((parameterChartCenter J).erase (parameterChartPivot a))
        (MvPolynomial (Fin r) R)))

/-- The polynomial-ring structural map to its quotient chart.
Source: Tag 0C0S, parameter-chart calculation
(blueprint: lem-trf-parameter-chart-completion-substitution). -/
noncomputable def parameterChartPolynomialMap (u : Fin n → R) (J : Finset (Fin (n + r)))
    (a : Option (Fin (n + r))) : MvPolynomial (Fin r) R →+* ParameterChartRing u J a :=
  (Ideal.Quotient.mk _).comp MvPolynomial.C

/-- The labelled coordinate list: ratios on `J` minus the pivot, original parameters elsewhere.
Source: Tag 0C0S, parameter-chart calculation
(blueprint: lem-trf-parameter-chart-completion-substitution). -/
noncomputable def parameterChartCoordinate (u : Fin n → R) (J : Finset (Fin (n + r)))
    (a : Option (Fin (n + r))) (i : Fin (n + r)) : ParameterChartRing u J a :=
  if h : i.castSucc ∈ (parameterChartCenter J).erase (parameterChartPivot a) then
    Ideal.Quotient.mk _ (MvPolynomial.X
      (⟨i.castSucc, h⟩ : (parameterChartCenter J).erase (parameterChartPivot a)))
  else parameterChartPolynomialMap u J a (parameterChartBaseParameter u i)

/-- The coordinate origin ideal of the chart.
Source: Tag 0C0S, parameter-chart calculation
(blueprint: lem-trf-parameter-chart-completion-substitution). -/
noncomputable def parameterChartOrigin (u : Fin n → R) (J : Finset (Fin (n + r)))
    (a : Option (Fin (n + r))) : Ideal (ParameterChartRing u J a) :=
  Ideal.span (Set.range (parameterChartCoordinate u J a))

/-- The localization at the chart origin; primality is supplied by the theorem.
Source: Tag 0C0S, parameter-chart calculation
(blueprint: lem-trf-parameter-chart-completion-substitution). -/
abbrev ParameterChartLocalRing (u : Fin n → R) (J : Finset (Fin (n + r)))
    (a : Option (Fin (n + r))) [(parameterChartOrigin u J a).IsPrime] :=
  Localization.AtPrime (parameterChartOrigin u J a)

/-- The local structural ring map from the original ring to the chart localization.
Source: Tag 0C0S, parameter-chart calculation
(blueprint: lem-trf-parameter-chart-completion-substitution). -/
noncomputable def parameterChartStructuralMap (u : Fin n → R) (J : Finset (Fin (n + r)))
    (a : Option (Fin (n + r))) [(parameterChartOrigin u J a).IsPrime] :
    R →+* ParameterChartLocalRing u J a :=
  (algebraMap (ParameterChartRing u J a) (ParameterChartLocalRing u J a)).comp
    ((parameterChartPolynomialMap u J a).comp MvPolynomial.C)

/-- The maximal-ideal completion of the localized chart.
Source: Tag 0C0S, parameter-chart calculation
(blueprint: lem-trf-parameter-chart-completion-substitution). -/
abbrev ParameterChartCompletion (u : Fin n → R) (J : Finset (Fin (n + r)))
    (a : Option (Fin (n + r))) [(parameterChartOrigin u J a).IsPrime] :=
  AdicCompletion (maximalIdeal (ParameterChartLocalRing u J a)) (ParameterChartLocalRing u J a)

/-- The completed maximal ideal, written as an extended ideal without an extra instance.
Source: Tag 0C0S, parameter-chart calculation
(blueprint: lem-trf-parameter-chart-completion-substitution). -/
noncomputable def parameterChartCompletedIdeal (u : Fin n → R) (J : Finset (Fin (n + r)))
    (a : Option (Fin (n + r))) [(parameterChartOrigin u J a).IsPrime] :
    Ideal (ParameterChartCompletion u J a) :=
  (maximalIdeal (ParameterChartLocalRing u J a)).map
    (algebraMap (ParameterChartLocalRing u J a) (ParameterChartCompletion u J a))

/-- The image of any original polynomial-chart element in the completed localized chart.
Source: Tag 0C0S, parameter-chart calculation
(blueprint: lem-trf-parameter-chart-completion-substitution). -/
noncomputable def parameterChartIntoCompletion (u : Fin n → R) (J : Finset (Fin (n + r)))
    (a : Option (Fin (n + r))) [(parameterChartOrigin u J a).IsPrime] :
    ParameterChartRing u J a →+* ParameterChartCompletion u J a :=
  (algebraMap (ParameterChartLocalRing u J a) (ParameterChartCompletion u J a)).comp
    (algebraMap (ParameterChartRing u J a) (ParameterChartLocalRing u J a))

/-- The substitution on original parameters: `e Y_i` on ratio labels and `W_i` elsewhere.
Source: Tag 0C0S, parameter-chart calculation
(blueprint: lem-trf-parameter-chart-completion-substitution). -/
noncomputable def parameterChartSubstitutionVariable (F : Type u) [CommRing F]
    (J : Finset (Fin (n + r))) (a : Option (Fin (n + r))) (i : Fin (n + r)) :
    MvPowerSeries (Fin (n + r)) F :=
  if i ∈ J ∧ some i ≠ a then MvPowerSeries.X (a.getD i) * MvPowerSeries.X i
  else MvPowerSeries.X i

/-- Completed parameter charts preserve the specified coefficient section.
Source: Stacks Project, Algebra, Tag 0C0S (2), with the explicit chart calculation
(blueprint: lem-trf-parameter-chart-completion-substitution).

Proof (the accepted seven-step DAG proof):
1. Reduction modulo the original maximal ideal and evaluation at all polynomial and
ratio variables gives C/q = F. Killing the displayed coordinates also kills every v_i
by v_i = v_a y_i. Localization has the same residue field
(def-weil-pbc-mv-polynomial-ring, def-weil-pbc-localization-at-prime).
2. R[t] is Noetherian regular by lem-weil-pbc-regular-local-localization and
lem-trf-polynomial-ring-regular-base. By lem-sf-noetherian-polynomial-dimension its
dimension is n+r. A length-n prime chain in R extends by the polynomial variables;
localization at the origin preserves this strict chain, so its dimension is n+r.
The generating list is therefore a regular system of parameters
(def-weil-pbc-krull-dimension-ring, def-weil-pbc-regular-system-of-parameters).
3. Localizing the base first gives the identical chart localization: both maps invert
exactly elements with nonzero residue. Apply lem-trf-parameter-blowup-algebra-regular
and lem-trf-parameter-blowup-coordinate-quotients with all coordinate equations;
the dimension is 1+(|J|-1)+(n+r-|J|)=n+r. The empty chart is step 2.
4. Apply lem-weil-pbc-adic-completion-noetherian,
lem-weil-pbc-local-completion-local-ring, lem-weil-pbc-adic-completion-mod-ideal,
lem-weil-pbc-completion-regular-local and lem-weil-pbc-completion-dimension to R and B.
Their completions are regular, of the same dimensions, and have the same residue fields.
5. Construct the completed structural map componentwise on all ideal-power quotients.
The quotient-kernel equality of lem-weil-pbc-adic-completion-mod-power proves
continuity. At level one the residue map is the identity, so its composite with c
is the prescribed coefficient section (def-weil-pbc-adic-completion).
6. Apply lem-trf-regular-complete-coefficient-coordinates to each completion, using c
and its transported section. The parameter lists generate their maximal ideals.
Uniqueness is lem-weil-pbc-power-series-universal-property-complete.
7. On coefficients the composite fixes F. The chart relations give v_a = e,
v_i = e Y_i on ratio labels and v_l = Z_l outside J, including the adjoined t_j.
By lem-weil-pbc-power-series-variables-complete the target series ring is complete;
lem-weil-pbc-power-series-universal-property-complete extends these formulas to
all series, equivalently the displayed congruences for every total-degree truncation.
The empty lists and singleton center require no alteration of the argument.
-/
theorem existsUnique_parameterChartCompletion_coordinates
    [IsRegularLocalRing R] (u : Fin n → R)
    (hu : IsRegularSystemOfParameters (List.ofFn u))
    (c : ResidueField R →+* AdicCompletion (maximalIdeal R) R)
    (hc : ∀ b : ResidueField R, AdicCompletion.evalOneₐ (maximalIdeal R) (c b) = b)
    (J : Finset (Fin (n + r))) (a : Option (Fin (n + r)))
    (ha : (J = ∅ ∧ a = none) ∨ ∃ j ∈ J, a = some j) :
    (parameterChartOrigin u J a).IsMaximal ∧
    ∀ [(parameterChartOrigin u J a).IsPrime],
      IsNoetherianRing (ParameterChartLocalRing u J a) ∧
      IsRegularLocalRing (ParameterChartLocalRing u J a) ∧
      ringKrullDim (ParameterChartLocalRing u J a) = ((n + r : ℕ) : WithBot ℕ∞) ∧
      IsLocalHom (parameterChartStructuralMap u J a) ∧
      ∃ (εC : (ParameterChartRing u J a ⧸ parameterChartOrigin u J a) ≃+* ResidueField R)
        (εB : ResidueField (ParameterChartLocalRing u J a) ≃+* ResidueField R),
        (∀ b : R, εC (Ideal.Quotient.mk _
          (parameterChartPolynomialMap u J a (MvPolynomial.C b))) = residue R b) ∧
        (∀ x : ParameterChartRing u J a,
          εB (residue (ParameterChartLocalRing u J a)
            (algebraMap _ (ParameterChartLocalRing u J a) x)) = εC (Ideal.Quotient.mk _ x)) ∧
        ∃ (g : AdicCompletion (maximalIdeal R) R →+* ParameterChartCompletion u J a),
          (∀ (k : ℕ) (x : AdicCompletion (maximalIdeal R) R) (b : R),
            AdicCompletion.evalₐ (maximalIdeal R) k x =
              Ideal.Quotient.mk (maximalIdeal R ^ k) b →
            AdicCompletion.evalₐ (maximalIdeal (ParameterChartLocalRing u J a)) k (g x) =
              Ideal.Quotient.mk (maximalIdeal (ParameterChartLocalRing u J a) ^ k)
                (parameterChartStructuralMap u J a b)) ∧
          (∀ b : ResidueField R,
            εB (AdicCompletion.evalOneₐ (maximalIdeal (ParameterChartLocalRing u J a))
              (g (c b))) = b) ∧
          ∃ (ψ : MvPowerSeries (Fin n) (ResidueField R) ≃+*
              AdicCompletion (maximalIdeal R) R),
            (∀ b : ResidueField R, ψ (MvPowerSeries.C b) = c b) ∧
            (∀ i : Fin n, ψ (MvPowerSeries.X i) =
              algebraMap R (AdicCompletion (maximalIdeal R) R) (u i)) ∧
            (∀ k : ℕ, Ideal.comap ψ.toRingHom
              (((maximalIdeal R).map
                (algebraMap R (AdicCompletion (maximalIdeal R) R))) ^ k) =
              Ideal.span (Set.range (MvPowerSeries.X : Fin n →
                MvPowerSeries (Fin n) (ResidueField R))) ^ k) ∧
            ∃ Θ : MvPowerSeries (Fin (n + r)) (ResidueField R) ≃+*
                ParameterChartCompletion u J a,
              (∀ Θ' : MvPowerSeries (Fin (n + r)) (ResidueField R) ≃+*
                  ParameterChartCompletion u J a,
                ((∀ b : ResidueField R, Θ' (MvPowerSeries.C b) = g (c b)) ∧
                (∀ i : Fin (n + r), Θ' (MvPowerSeries.X i) =
                  parameterChartIntoCompletion u J a (parameterChartCoordinate u J a i)) ∧
                (∀ k : ℕ, Ideal.comap Θ'.toRingHom (parameterChartCompletedIdeal u J a ^ k) =
                  Ideal.span (Set.range (MvPowerSeries.X : Fin (n + r) →
                    MvPowerSeries (Fin (n + r)) (ResidueField R))) ^ k)) ↔ Θ' = Θ) ∧
              (∀ i : Fin (n + r),
                Θ.symm (parameterChartIntoCompletion u J a
                  (parameterChartPolynomialMap u J a (parameterChartBaseParameter u i))) =
                    parameterChartSubstitutionVariable (ResidueField R) J a i) ∧
              (∀ (z : MvPowerSeries (Fin n) (ResidueField R)) (k : ℕ),
                Θ.symm (g (ψ z)) -
                  MvPolynomial.eval₂ MvPowerSeries.C
                    (fun i : Fin n ↦
                      parameterChartSubstitutionVariable (ResidueField R) J a (i.castAdd r))
                    (MvPowerSeries.truncTotal k z) ∈
                  Ideal.span (Set.range (MvPowerSeries.X : Fin (n + r) →
                    MvPowerSeries (Fin (n + r)) (ResidueField R))) ^ k) := by
  sorry

end IsLocalRing
