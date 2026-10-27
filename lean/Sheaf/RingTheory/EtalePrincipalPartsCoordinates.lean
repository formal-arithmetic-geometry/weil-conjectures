/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.RingTheory.DiagonalJets
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Basis.Defs
import Sheaf.RingTheory.FormallyEtaleAssociatedGraded
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Unramified.Basic

/-! # Relative principal parts in étale polynomial coordinates

Source: Stacks Project, Algebra, Tags 0H93, 0H90, 0H8Z; the polynomial diagonal
calculation and the coefficientwise formal-translation comparison in the DAG proof
(blueprint: lem-per-etale-relative-principal-parts-coordinates).

The equivalences below are pinned down on the coordinate generators, and the
base-change equivalence on pure tensors. Taylor expansion is the inverse applied
to the second-factor map. Its translation identity is stated coefficientwise in
all degrees in the series variables and in degrees at most the jet order in the
polynomial variables. Thus it specifies exactly the class modulo the variable
ideal power, without choosing representatives of a quotient.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v w x
open scoped TensorProduct

namespace DiagonalJets

/-- The explicit truncated polynomial algebra in coordinate differences.
Source: Stacks Tag 0H93, polynomial case
(blueprint: lem-per-etale-relative-principal-parts-coordinates). -/
abbrev coordinateRing (R : Type v) [CommRing R] (n t : ℕ) :=
  MvPolynomial (Fin n) R ⧸ MvPolynomial.idealOfVars (Fin n) R ^ (t + 1)

/-- The coordinate polynomial quotient projection. Source: Stacks Tag 0H93
(blueprint: lem-per-etale-relative-principal-parts-coordinates). -/
def coordinateMk (R : Type v) [CommRing R] (n t : ℕ) :
    MvPolynomial (Fin n) R →ₐ[R] coordinateRing R n t :=
  Ideal.Quotient.mkₐ R (MvPolynomial.idealOfVars (Fin n) R ^ (t + 1))

/-- The projection from the tensor square to the recorded principal-parts algebra.
Source: Stacks Tag 0H90
(blueprint: lem-per-etale-relative-principal-parts-coordinates). -/
def principalMk (R₀ : Type u) (R : Type v) [CommRing R₀] [CommRing R] [Algebra R₀ R]
    (t : ℕ) : R ⊗[R₀] R →ₐ[R] principalParts R₀ R t :=
  Ideal.Quotient.mkₐ R (KaehlerDifferential.ideal R₀ R ^ (t + 1))

/-- The second-factor universal jet, with its actual base-algebra structure.
Source: Stacks Tag 0H90
(blueprint: lem-per-etale-relative-principal-parts-coordinates). -/
def rightJet (R₀ : Type u) (R : Type v) [CommRing R₀] [CommRing R] [Algebra R₀ R]
    (t : ℕ) : R →ₐ[R₀] principalParts R₀ R t :=
  (Ideal.Quotient.mkₐ R₀ (KaehlerDifferential.ideal R₀ R ^ (t + 1))).comp
    Algebra.TensorProduct.includeRight

/-- Taylor expansion in a specified principal-parts coordinate equivalence.
Source: Stacks Tags 0H93 and 0H90
(blueprint: lem-per-etale-relative-principal-parts-coordinates). -/
def coordinateTaylor (R₀ : Type u) (R : Type v) [CommRing R₀] [CommRing R] [Algebra R₀ R]
    (n t : ℕ) (e : coordinateRing R n t ≃ₐ[R] principalParts R₀ R t) :
    R →ₐ[R₀] coordinateRing R n t :=
  (e.symm.toAlgHom.restrictScalars R₀).comp (rightJet R₀ R t)

/-- Coordinate truncation is the quotient map between successive ideal powers.
Source: Stacks Tag 0H93, canonical quotient maps
(blueprint: lem-per-etale-relative-principal-parts-coordinates). -/
def coordinateTruncate (R : Type v) [CommRing R] (n : ℕ) {s t : ℕ} (h : s ≤ t) :
    coordinateRing R n t →+* coordinateRing R n s :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- Principal-parts truncation is the quotient map on the actual tensor square.
Source: Stacks Tags 0H93 and 0H90
(blueprint: lem-per-etale-relative-principal-parts-coordinates). -/
def principalTruncate (R₀ : Type u) (R : Type v)
    [CommRing R₀] [CommRing R] [Algebra R₀ R] {s t : ℕ} (h : s ≤ t) :
    principalParts R₀ R t →+* principalParts R₀ R s :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- Étale coordinates identify relative principal parts with truncated polynomials,
compatibly with truncation, every coefficient change, and formal translation.
The base-changed ring is written `R₀' ⊗[R₀] R`, the canonical tensor commutation
of the statement's `R ⊗[R₀] R₀'`, to use its standard left `R₀'`-algebra structure.
Low-degree coefficients of every representative specify the translation class;
higher-degree terms are exactly the ideal being quotiented out.

Source: Stacks Tags 0H93, 0H90 and 0H8Z and the explicit coefficient calculation
(blueprint: lem-per-etale-relative-principal-parts-coordinates).

Proof: (1) The polynomial and tensor universal properties identify `R ⊗ S` with
`R[X]`. Substitution `Y = X - z`, with inverse `X = Y + z`, identifies the
augmentation ideal with the variable ideal. Its power discards exactly monomials
of degree at least `t+1`, giving the indicated monomial basis.
(2) The map `R ⊗ S → R ⊗ R` is the base change of `S → R`, hence étale by
lem-weil-pbc-etale-ring-base-change. (3) Multiplication on the tensor square is
surjective, and its composite with `R ⊗ S` is the polynomial augmentation.
Apply lem-sfb-augmented-etale-associated-graded at exponent `t+1`. Composing
with (1) gives the unique coordinate equivalence with the stated generator formula.
(4) Apply its inverse to `1 ⊗ h`. The coordinate formula gives `T(z)=z+Y`;
augmentation gives the constant coefficient. Truncations agree on coefficients
and generators, hence on the polynomial quotients and on `T`.
(5) After any base change, tensor balancing identifies the new coordinate algebra
with the base change of `S → R`, again étale. Apply (1)--(3) to it.
(6) The canonical principal-parts base-change map sends `a ⊗ [r ⊗ h]` to
`[(a ⊗ r) ⊗ (1 ⊗ h)]`. In both coordinate bases it fixes every monomial and
maps its coefficient by tensor base change. It is therefore an isomorphism,
without flatness. Applying it to the second factor identifies the Taylor maps.
(7) Define formal translation by its coefficient at `Z^α Y^β`, namely the
coefficient at `α+β` multiplied by the product of binomial coefficients.
There are finitely many `β` of degree at most `t`. This translation is continuous:
terms of `Z`-degree at least `q+t` give coefficients of degree at least `q`.
(8) Convolution and the integral binomial identity show multiplicativity; all
sums for each coefficient are finite, and no factorial is inverted.
(9) The étale hypothesis gives vanishing differentials by
lem-weil-pbc-etale-ring-map-iff-etale-affine. By
lem-weil-pbc-formally-unramified-ring-iff-kahler-zero, square-zero lifts are
unique. Apply this successively to the powers of `(Y)` to get nilpotent uniqueness.
(10) Coefficientwise application of `τ` to `T` and formal translation of `τ`
are maps of `S`-algebras, where `z` acts as `Z+Y`. They agree modulo `(Y)` and
therefore agree by (9), giving every displayed coefficient identity. For `t=0`
it is already equality modulo `(Y)`; for `n=0` the variable sets are empty.
Every construction and argument allows zero rings. -/
theorem etale_relative_principalParts_coordinates
    (R₀ : Type u) (R : Type v) [CommRing R₀] [CommRing R] [Algebra R₀ R]
    (n : ℕ) (φ : MvPolynomial (Fin n) R₀ →ₐ[R₀] R) (hφ : φ.toRingHom.Etale) :
    ∃ e : ∀ t : ℕ, coordinateRing R n t ≃ₐ[R] principalParts R₀ R t,
      (∀ (t : ℕ) (j : Fin n),
        e t (coordinateMk R n t (MvPolynomial.X j)) =
          principalMk R₀ R t
            ((1 : R) ⊗ₜ[R₀] φ (MvPolynomial.X j) -
              φ (MvPolynomial.X j) ⊗ₜ[R₀] (1 : R))) ∧
      (∀ (t : ℕ) (j : Fin n),
        coordinateTaylor R₀ R n t (e t) (φ (MvPolynomial.X j)) =
          coordinateMk R n t
            (MvPolynomial.C (φ (MvPolynomial.X j)) + MvPolynomial.X j)) ∧
      (∀ (t : ℕ) (h : R) (p : MvPolynomial (Fin n) R),
        coordinateMk R n t p = coordinateTaylor R₀ R n t (e t) h →
          MvPolynomial.constantCoeff p = h) ∧
      (∀ (s t : ℕ) (hst : s ≤ t) (q : coordinateRing R n t),
        principalTruncate R₀ R hst (e t q) = e s (coordinateTruncate R n hst q)) ∧
      (∀ (s t : ℕ) (hst : s ≤ t) (h : R),
        coordinateTruncate R n hst (coordinateTaylor R₀ R n t (e t) h) =
          coordinateTaylor R₀ R n s (e s) h) ∧
      (∀ t : ℕ, ∃ b : Module.Basis {β : Fin n →₀ ℕ // β.sum (fun _ k ↦ k) ≤ t}
          R (principalParts R₀ R t),
        ∀ β, b β = e t (coordinateMk R n t (MvPolynomial.monomial β.val 1))) ∧
      (∀ (R₀' : Type w) [CommRing R₀'] [Algebra R₀ R₀'],
        ∃ (e' : ∀ t : ℕ, coordinateRing (R₀' ⊗[R₀] R) n t ≃ₐ[R₀' ⊗[R₀] R]
            principalParts R₀' (R₀' ⊗[R₀] R) t)
          (θ : ∀ t : ℕ, (R₀' ⊗[R₀] principalParts R₀ R t) ≃ₐ[R₀']
            principalParts R₀' (R₀' ⊗[R₀] R) t),
          (∀ (t : ℕ) (j : Fin n),
            e' t (coordinateMk (R₀' ⊗[R₀] R) n t (MvPolynomial.X j)) =
              principalMk R₀' (R₀' ⊗[R₀] R) t
                ((1 : R₀' ⊗[R₀] R) ⊗ₜ[R₀'] ((1 : R₀') ⊗ₜ[R₀] φ (MvPolynomial.X j)) -
                  ((1 : R₀') ⊗ₜ[R₀] φ (MvPolynomial.X j)) ⊗ₜ[R₀']
                    (1 : R₀' ⊗[R₀] R))) ∧
          (∀ (t : ℕ) (a : R₀') (r h : R),
            θ t (a ⊗ₜ[R₀] principalMk R₀ R t (r ⊗ₜ[R₀] h)) =
              principalMk R₀' (R₀' ⊗[R₀] R) t
                ((a ⊗ₜ[R₀] r) ⊗ₜ[R₀'] ((1 : R₀') ⊗ₜ[R₀] h))) ∧
          (∀ (t : ℕ) (a : R₀') (p : MvPolynomial (Fin n) R),
            θ t (a ⊗ₜ[R₀] e t (coordinateMk R n t p)) =
              e' t (coordinateMk (R₀' ⊗[R₀] R) n t
                (MvPolynomial.C (a ⊗ₜ[R₀] (1 : R)) *
                  MvPolynomial.map Algebra.TensorProduct.includeRight.toRingHom p))) ∧
          (∀ (t : ℕ) (a : R₀') (h : R) (p : MvPolynomial (Fin n) R),
            coordinateMk R n t p = coordinateTaylor R₀ R n t (e t) h →
              coordinateTaylor R₀' (R₀' ⊗[R₀] R) n t (e' t) (a ⊗ₜ[R₀] h) =
                coordinateMk (R₀' ⊗[R₀] R) n t
                  (MvPolynomial.C (a ⊗ₜ[R₀] (1 : R)) *
                    MvPolynomial.map Algebra.TensorProduct.includeRight.toRingHom p))) ∧
      (∀ (C : Type x) [CommRing C] [Algebra R₀ C]
          (τ : R →ₐ[R₀] MvPowerSeries (Fin n) C),
        (∀ j : Fin n, τ (φ (MvPolynomial.X j)) = MvPowerSeries.X j) →
          ∀ (t : ℕ) (h : R) (p : MvPolynomial (Fin n) R),
            coordinateMk R n t p = coordinateTaylor R₀ R n t (e t) h →
              ∀ (α β : Fin n →₀ ℕ), β.sum (fun _ k ↦ k) ≤ t →
                MvPowerSeries.coeff α (τ (MvPolynomial.coeff β p)) =
                  (∏ j : Fin n, Nat.choose (α j + β j) (β j)) •
                    MvPowerSeries.coeff (α + β) (τ h)) := by
  sorry

end DiagonalJets
