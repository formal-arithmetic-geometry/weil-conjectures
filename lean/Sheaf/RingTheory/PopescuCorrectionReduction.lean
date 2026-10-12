/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Smooth.StandardSmooth

/-! # The explicit corrected polynomial quotient and its reduction -/

@[expose] public section

universe u w d

namespace Algebra

variable (R : Type u) [CommRing R] (A : Type w) [CommRing A] [Algebra R A]
variable (I : Ideal R) (n m : ℕ) (N : Fin m → ℕ)
variable (g : Fin m → MvPolynomial (Fin n) A) (ε : (i : Fin m) → Fin (N i) → I)

/-- Variables of the corrected presentation. The `ULift` sets the carrier universe
without changing the finite set of variables. -/
abbrev PopescuCorrectionVariables := Fin n ⊕ ULift.{d} (Σ i : Fin m, Fin (N i))

/-- The equation `gᵢ - ∑ εᵢⱼ δᵢⱼ`, with genuine polynomial data. -/
noncomputable def popescuCorrectionRelation (i : Fin m) :
    MvPolynomial (PopescuCorrectionVariables.{d} n m N) A :=
  MvPolynomial.rename Sum.inl (g i) -
    ∑ j, MvPolynomial.C (algebraMap R A (ε i j)) *
      MvPolynomial.X (Sum.inr (ULift.up ⟨i, j⟩))

/-- The finitely generated ideal of the corrected equations. -/
noncomputable def popescuCorrectionIdeal :
    Ideal (MvPolynomial (PopescuCorrectionVariables.{d} n m N) A) :=
  Ideal.span (Set.range (popescuCorrectionRelation.{u, w, d} R A I n m N g ε))

/-- The corrected quotient, constructed independently of any existence theorem. -/
abbrev PopescuCorrectionQuotient :=
  MvPolynomial (PopescuCorrectionVariables.{d} n m N) A ⧸
    popescuCorrectionIdeal.{u, w, d} R A I n m N g ε

/-- Reduction of the explicit corrected quotient identifies it with a polynomial
extension of the quotient by the uncorrected reduced equations.

Source: Stacks Project, Tag 07CK (lemma-lift-once), the equality `A'/IA' = Bbar[δᵢⱼ]`.

Proof: Reduce coefficients and variables modulo `I`. Each coefficient `εᵢⱼ` vanishes,
so the corrected relations become just the renamed reduced `gᵢ`. The universal
properties of polynomial rings and ideal quotients give mutually inverse maps between
the reduced corrected quotient and the polynomial ring in the correction variables
over the quotient by the reduced `gᵢ`: send old variables to the constant polynomials
of their classes, correction variables to the new polynomial variables, and coefficients
to their quotient classes. The reverse map sends coefficient classes and old variables
to their images in the reduced corrected quotient, and each new variable to the class
of its correction variable. Membership of every `εᵢⱼ` in `I` makes both maps respect
the relations. They are inverse on coefficients and every variable, hence everywhere
by polynomial and quotient extensionality. The maps commute with `R/I`, as can be
checked on lifts from `R`. `ULift` merely relabels the correction variables. This also
handles empty sets and the zero algebra; no assumption on `I²` or smoothness is used.
(blueprint: lem-weil-pbc-popescu-correction-reduction-equiv) -/
theorem nonempty_popescuCorrectionQuotient_reduction_equiv :
    Nonempty
      ((PopescuCorrectionQuotient.{u, w, d} R A I n m N g ε ⧸
        I.map (algebraMap R (PopescuCorrectionQuotient.{u, w, d} R A I n m N g ε))) ≃ₐ[R ⧸ I]
        MvPolynomial (ULift.{d} (Σ i : Fin m, Fin (N i)))
          (MvPolynomial (Fin n) (A ⧸ I.map (algebraMap R A)) ⧸
            Ideal.span (Set.range fun i ↦
              MvPolynomial.map (Ideal.Quotient.mk (I.map (algebraMap R A))) (g i)))) := by
  sorry

end Algebra
