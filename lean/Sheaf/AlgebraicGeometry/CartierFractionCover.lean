/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q92
-/
module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Sheaf.RingTheory.HeightOneFractionOrder
public import Sheaf.RingTheory.StrictHenselizationPresentationIn

/-! # Cartier fraction covers and strict-local Weil coefficients

Source: Stacks Project, Divisors, Tags 02OX, 0BE2, 0BE3, 0BE8 and 0EBM;
Algebra, Tag 04GW (blueprint: def-per-cartier-fraction-cover).

A cover by actual local fractions is a presentation of a Cartier divisor.
No quotient representative is chosen and no connectedness assumption is imposed.
The cycle and height-one fraction orders are the existing library constructions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- Local fraction equations on an open cover, with regular unit ratios on overlaps.
The cover is indexed by the points it covers, so an empty scheme has an empty presentation.
Source: Stacks, Divisors, Tag 02OX (blueprint: def-per-cartier-fraction-cover). -/
structure CartierFractionCover (Y : Scheme.{u}) where
  opens : Y → Y.Opens
  mem : ∀ x : Y, x ∈ opens x
  numerator : ∀ x : Y, Y.presheaf.obj (op (opens x))
  denominator : ∀ x : Y, Y.presheaf.obj (op (opens x))
  numerator_regular : ∀ (x z : Y) (hz : z ∈ opens x),
    Y.presheaf.germ (opens x) z hz (numerator x) ∈ nonZeroDivisors (Y.presheaf.stalk z)
  denominator_regular : ∀ (x z : Y) (hz : z ∈ opens x),
    Y.presheaf.germ (opens x) z hz (denominator x) ∈ nonZeroDivisors (Y.presheaf.stalk z)
  overlap_unit : ∀ (x t z : Y) (hx : z ∈ opens x) (ht : z ∈ opens t),
    ∃ e : (Y.presheaf.stalk z)ˣ,
      Y.presheaf.germ (opens x) z hx (numerator x) *
          Y.presheaf.germ (opens t) z ht (denominator t) =
        e.val * Y.presheaf.germ (opens t) z ht (numerator t) *
          Y.presheaf.germ (opens x) z hx (denominator x)

/-- Equality of the Weil coefficients with the normalized orders of every local equation.
On a normal Noetherian scheme the tested local rings are DVRs; their length orders
are finite on the regular numerators and denominators.
Source: Stacks, Tags 02RJ and 0BE3 (blueprint: def-per-cartier-fraction-cover). -/
def CartierFractionCover.HasCoefficients {Y : Scheme.{u}} (C : CartierFractionCover Y)
    (W : Y → ℤ) : Prop :=
  ∀ (x z : Y) (hz : z ∈ C.opens x), ringKrullDim (Y.presheaf.stalk z) = 1 →
    ((Ring.ord (Y.presheaf.stalk z)
      (Y.presheaf.germ (C.opens x) z hz (C.numerator x))).toNat : ℤ) -
      ((Ring.ord (Y.presheaf.stalk z)
        (Y.presheaf.germ (C.opens x) z hz (C.denominator x))).toNat : ℤ) = W z

/-- An effective presentation uses regular equations, with denominator one.
Existence of this presentation is effectivity of the represented Cartier divisor.
Source: Stacks, Tag 01WQ (blueprint: def-per-cartier-fraction-cover). -/
def CartierFractionCover.IsEffective {Y : Scheme.{u}} (C : CartierFractionCover Y) : Prop :=
  ∀ x : Y, C.denominator x = 1

/-- The support is the locus where a local fraction is not a regular unit.
Source: Stacks, Tag 02OX (blueprint: def-per-cartier-fraction-cover). -/
def CartierFractionCover.support {Y : Scheme.{u}} (C : CartierFractionCover Y) : Set Y :=
  {x | ¬ ∃ e : (Y.presheaf.stalk x)ˣ,
    Y.presheaf.germ (C.opens x) x (C.mem x) (C.numerator x) =
      e.val * Y.presheaf.germ (C.opens x) x (C.mem x) (C.denominator x)}

/-- A fixed multiple of a Weil cycle is Cartier when it has local fraction equations.
Source: Stacks, Tags 0BE3 and 0BE8 (blueprint: def-per-cartier-fraction-cover). -/
def IsCartierWeilMultiple (Y : Scheme.{u}) (E : AlgebraicCycle Y ℤ) (a : ℤ) : Prop :=
  ∃ C : CartierFractionCover Y, C.HasCoefficients (fun z ↦ a * E z)

/-- Pullback coefficients on codimension-one points, extended by zero elsewhere.
The theorem using this function proves that these coefficients are locally finite.
Source: Stacks, Tag 0BE3; ind-etale valuation comparison
(blueprint: def-per-cartier-fraction-cover). -/
def etaleWeilCoefficient {V Y : Scheme.{u}} (f : V ⟶ Y)
    (E : AlgebraicCycle Y ℤ) (z : V) : ℤ :=
  if ringKrullDim (V.presheaf.stalk z) = 1 then E (f z) else 0

/-- The coefficient at a height-one prime of an algebra over the stalk at y.
Contraction and the actual stalk-to-scheme map identify the generic point downstairs.
This definition allows the algebra to lie in a larger universe than the scheme.
Source: Stacks, Tags 04GW and 0BE3 (blueprint: def-per-cartier-fraction-cover). -/
def localWeilCoefficient {Y : Scheme.{u}} (E : AlgebraicCycle Y ℤ) (y : Y)
    {H : Type v} [CommRing H] (φ : Y.presheaf.stalk y →+* H)
    (q : Ring.WeilHeightOnePrime H) : ℤ :=
  E (Y.fromSpecStalk y (PrimeSpectrum.comap φ q.val))

/-- Strict-local principality of a fixed multiple, for every residue separable closure
and every universal pointed-etale presentation. Normal-domain and Noetherian
properties are included as witnesses, so the normalized fraction-order API applies
without any conditional or potentially vacuous normality hypothesis.
Source: Stacks, Tags 04GW, 0BE3 and 0EBM
(blueprint: def-per-cartier-fraction-cover). -/
def IsStrictLocallyPrincipalWeilMultiple (Y : Scheme.{u})
    (E : AlgebraicCycle Y ℤ) (a : ℤ) : Prop :=
  ∀ (y : Y) (K H : Type (max u v)) [Field K]
    [Algebra (IsLocalRing.ResidueField (Y.presheaf.stalk y)) K]
    [IsSepClosure (IsLocalRing.ResidueField (Y.presheaf.stalk y)) K]
    [Algebra (Y.presheaf.stalk y) K]
    [IsScalarTower (Y.presheaf.stalk y)
      (IsLocalRing.ResidueField (Y.presheaf.stalk y)) K]
    [CommRing H] [Algebra (Y.presheaf.stalk y) H],
    Algebra.StrictHenselizationPresentationIn.{u, v} (Y.presheaf.stalk y) K H →
    ∃ (hD : IsDomain H) (hN : IsNoetherianRing H) (hI : IsIntegrallyClosed H)
      (c : (FractionRing H)ˣ), ∀ q : Ring.WeilHeightOnePrime H,
        @Ring.weilFractionOrder H _ hD hN hI q c.val =
          a * localWeilCoefficient E y (algebraMap (Y.presheaf.stalk y) H) q

end AlgebraicGeometry.Scheme
