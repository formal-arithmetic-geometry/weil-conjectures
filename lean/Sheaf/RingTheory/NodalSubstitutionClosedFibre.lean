/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv
import WeilConjectures.RingTheory.PowerSeriesCompleteOverCompleteBase
import WeilConjectures.RingTheory.CompleteLocalQuotient
import WeilConjectures.RingTheory.PowerSeriesAdicEvaluation
import WeilConjectures.RingTheory.MvPowerSeriesQuotientKernel
import WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete

/-! # Nodal substitution and the chosen closed fibre

Source: Stacks Project, curves.tex, Tag 0CBX,
lemma-formal-local-structure-nodal-family, third paragraph.
(blueprint: lem-trf-nodal-substitution-closed-fibre)

The concrete abbreviations name the hypersurface and the two ideals used in the statement.
The chosen fibre equivalence is a ring equivalence with its scalar compatibility written
on representatives from A; this expresses exactly that it is a k-algebra equivalence.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace MvPowerSeries.NodalSubstitution

/-- The equation ideal `(xy-h)` in the ambient two-variable power series ring.
Source: Stacks Project, Tag 0CBX, third paragraph.
(blueprint: lem-trf-nodal-substitution-closed-fibre) -/
abbrev relationIdeal (A : Type u) [CommRing A] (h : A) :
    Ideal (MvPowerSeries (Fin 2) A) :=
  Ideal.span {(X 0 : MvPowerSeries (Fin 2) A) * X 1 - C h}

/-- The actual quotient `A[[x,y]]/(xy-h)`.
Source: Stacks Project, Tag 0CBX, third paragraph.
(blueprint: lem-trf-nodal-substitution-closed-fibre) -/
abbrev Model (A : Type u) [CommRing A] (h : A) : Type u :=
  MvPowerSeries (Fin 2) A ⧸ relationIdeal A h

/-- The ideal `m A[[x,y]] + (x,y)`.
Source: Stacks Project, Tag 0CBX, third paragraph.
(blueprint: lem-trf-nodal-substitution-closed-fibre) -/
abbrev ambientIdeal (A : Type u) [CommRing A] [IsLocalRing A] :
    Ideal (MvPowerSeries (Fin 2) A) :=
  (IsLocalRing.maximalIdeal A).map (C : A →+* MvPowerSeries (Fin 2) A) ⊔
    Ideal.span (Set.range (X : Fin 2 → MvPowerSeries (Fin 2) A))

/-- The image of the ambient maximal ideal in the hypersurface quotient.
Source: Stacks Project, Tag 0CBX, third paragraph.
(blueprint: lem-trf-nodal-substitution-closed-fibre) -/
abbrev modelIdeal (A : Type u) [CommRing A] [IsLocalRing A] (h : A) :
    Ideal (Model A h) :=
  (ambientIdeal A).map (Ideal.Quotient.mk (relationIdeal A h))

/-- Adic substitution descends to the nodal equation and agrees with the chosen closed
fibre equivalence, with the asserted maximal ideals and residue fields.
Source: Stacks Project, curves.tex, Tag 0CBX,
lemma-formal-local-structure-nodal-family, third paragraph.
(blueprint: lem-trf-nodal-substitution-closed-fibre)

Proof:
1. Power-series-noetherian and power-series-local-ring make R Noetherian and local.
Every series is its constant plus xG+yH, so its maximal ideal is `ambientIdeal A`.
Power-series-complete-over-complete-base gives completeness for this ideal.
2. Since h is in m, xy-h is in this maximal ideal. Complete-local-quotient gives
Noetherianity, locality, the image maximal ideal, and completeness of C.
3. Power-series-adic-evaluation applied to u,v gives E and its truncation formula.
The equation uv=alpha(h) kills xy-h, so E descends to the A-algebra map phi.
Its inverse image of n contains the maximal ideal of C and is proper, hence equals it;
therefore phi is local.
4. Coefficient reduction R -> k[[x,y]] is surjective by coefficientwise lifting.
The finitely generated ideal m has extended ideal as kernel by
lem-sbc-mv-power-series-quotient-kernel. The inverse image of (xy) is
mR+(xy-h), giving rho and its formula on every power series representative.
5. Complete-local-quotient makes B/mB complete for its maximal ideal. The two maps
from R to B/mB, induced by phi and by theta after coefficient reduction, have the
same constants and variables. Power-series-universal-property-complete makes them
equal. Descending proves phibar=theta composed with rho, hence bijectivity.
6. Power-series-local-ring and quotient-local-structure identify the maximal ideal
of k[[x,y]]/(xy) with (x,y). Theta carries it to n/mB, so
n=mB+(u,v)=a_C B. Constant coefficient modulo m identifies C/a_C with k;
theta followed by quotienting by the variables identifies B/n with k.
The displayed scalar equations specify the residue identifications over A.
-/
theorem closed_fibre
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (θ : (MvPowerSeries (Fin 2) (A ⧸ IsLocalRing.maximalIdeal A) ⧸
      Ideal.span {(X 0 : MvPowerSeries (Fin 2) (A ⧸ IsLocalRing.maximalIdeal A)) * X 1})
      ≃+* (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)))
    (hθ : ∀ a : A,
      θ (Ideal.Quotient.mk _ (C (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a))) =
        Ideal.Quotient.mk _ (algebraMap A B a))
    (h : A) (hh : h ∈ IsLocalRing.maximalIdeal A)
    (u v : B) (hu : u ∈ IsLocalRing.maximalIdeal B)
    (hv : v ∈ IsLocalRing.maximalIdeal B) (huv : u * v = algebraMap A B h)
    (hvars : ∀ i : Fin 2,
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) (![u, v] i) =
        θ (Ideal.Quotient.mk _ (X i))) :
    (IsNoetherianRing (MvPowerSeries (Fin 2) A) ∧
      IsLocalRing (MvPowerSeries (Fin 2) A) ∧
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) A) = ambientIdeal A ∧
      IsAdicComplete (ambientIdeal A) (MvPowerSeries (Fin 2) A)) ∧
    IsNoetherianRing (Model A h) ∧
    ∃ localC : IsLocalRing (Model A h),
      @IsLocalRing.maximalIdeal (Model A h) _ localC = modelIdeal A h ∧
      IsAdicComplete (modelIdeal A h) (Model A h) ∧
      ∃ φ : Model A h →ₐ[A] B,
        IsLocalHom φ ∧
        (∀ i : Fin 2, φ (Ideal.Quotient.mk _ (X i)) = ![u, v] i) ∧
        (∀ (F : MvPowerSeries (Fin 2) A) (N : ℕ),
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal B ^ N)
              (φ (Ideal.Quotient.mk _ F)) =
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal B ^ N)
              (MvPolynomial.eval₂ (algebraMap A B) ![u, v] (F.truncTotal N))) ∧
        ∃ ρ : (Model A h ⧸
            (IsLocalRing.maximalIdeal A).map (algebraMap A (Model A h))) ≃+*
            (MvPowerSeries (Fin 2) (A ⧸ IsLocalRing.maximalIdeal A) ⧸
              Ideal.span
                {(X 0 : MvPowerSeries (Fin 2) (A ⧸ IsLocalRing.maximalIdeal A)) * X 1}),
          (∀ F : MvPowerSeries (Fin 2) A,
            ρ (Ideal.Quotient.mk _ (Ideal.Quotient.mk (relationIdeal A h) F)) =
              Ideal.Quotient.mk _ (MvPowerSeries.map
                (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) F)) ∧
          ∃ φbar : (Model A h ⧸
              (IsLocalRing.maximalIdeal A).map (algebraMap A (Model A h))) →+*
              (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)),
            (∀ c : Model A h, φbar (Ideal.Quotient.mk _ c) =
              Ideal.Quotient.mk _ (φ c)) ∧
            φbar = θ.toRingHom.comp ρ.toRingHom ∧
            Function.Bijective φbar ∧
            IsLocalRing.maximalIdeal B = (modelIdeal A h).map φ ∧
            IsLocalRing.maximalIdeal B =
              (IsLocalRing.maximalIdeal A).map (algebraMap A B) ⊔ Ideal.span {u, v} ∧
            ∃ (eC : (Model A h ⧸ modelIdeal A h) ≃+* (A ⧸ IsLocalRing.maximalIdeal A))
              (eB : (B ⧸ IsLocalRing.maximalIdeal B) ≃+* (A ⧸ IsLocalRing.maximalIdeal A)),
              (∀ a : A, eC (Ideal.Quotient.mk _ (algebraMap A (Model A h) a)) =
                Ideal.Quotient.mk _ a) ∧
              (∀ a : A, eB (Ideal.Quotient.mk _ (algebraMap A B a)) =
                Ideal.Quotient.mk _ a) := by
  sorry

end MvPowerSeries.NodalSubstitution
