/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.RingTheory.StrictHenselizationPresentationIn
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import WeilConjectures.RingTheory.PolynomialOriginRegularLocal
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import WeilConjectures.RingTheory.StrictHenselizationRegular
import WeilConjectures.RingTheory.StrictHenselizationDimension

/-!
# Coordinate dimensions in polynomial strict local rings

Source: Stacks Project, Algebra, Tags 00ON, 00OP, 00OQ, and More on Algebra,
Tags 06LN, 06LK (blueprint: lem-trf-polynomial-strict-local-coordinate-dimension).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace MvPolynomial

/-- The prime local rings of a polynomial algebra and a coordinate quotient, and their
strict henselizations for the same residue separable closure, are regular local rings.
Their dimensions differ by the number of removed coordinates.

Here `L` names the selected-coordinate ideal. The equation `hq` is the quotient-prime
correspondence: it says precisely that `q` contains `L` and `q' = q / L`. The equation
`hΩ` identifies the two residue embeddings through the canonical quotient-induced map.
Regular local rings include both localness and Noetherianity in Mathlib.

Source: Stacks Project, Algebra, Tags 00ON, 00OP, 00OQ, and More on Algebra,
Tags 06LN, 06LK (blueprint: lem-trf-polynomial-strict-local-coordinate-dimension).

Proof:
1. Group monomials into selected and remaining variables, writing P = A[T_j] with
   A = k[T_i : i in K]. Evaluation at zero in the selected variables has kernel L,
   so P/L is the polynomial algebra in the remaining variables. The origin ideal m
   of A is maximal because A/m = k. Its contraction from q is m.
2. Polynomial regularity (lem-weil-pbc-polynomial-ring-field-regular-ring) makes the
   prime localizations of P and P/L regular local. The origin calculation
   (lem-weil-pbc-polynomial-ring-origin-regular-local) gives dim A_m = K.card.
3. The coefficient inclusion A to P is flat by lem-nagata-polynomial-projection-flat
   and lem-weil-pbc-flat-ring-map-iff-flat-affine.
4. The local fibre P_q/mP_q identifies with (P/L)_(q/L): send f/s to its quotient
   fraction. A denominator outside q stays outside q/L; every fraction lifts.
   Changing lifts adds elements of L, which vanish, and multiplying by an allowed
   denominator preserves the fraction relation. These mutually inverse maps also
   identify the residue fields.
5. The flat height formula (lem-weil-pbc-flat-height-formula) gives
   dim P_q = dim A_m + dim (P/L)_(q/L). Substitute K.card and commute the summands.
6. Apply lem-sc-strict-henselization-regular and lem-sc-strict-henselization-dimension
   to the two local rings with the common residue separable closure. This gives
   regularity and the two dimension invariances. Substitute in step 5 for the last
   equality. No maximality of q is used; empty and full K are included.
-/
theorem polynomial_strictLocal_coordinate_dimension
    (k : Type u) [Field k] (E : Type v) [Finite E] (K : Finset E)
    (L : Ideal (MvPolynomial E k))
    (_hL : L = Ideal.span (Set.range (fun i : K ↦ (X i.1 : MvPolynomial E k))))
    (q : Ideal (MvPolynomial E k)) [q.IsPrime]
    (q' : Ideal (MvPolynomial E k ⧸ L)) [q'.IsPrime]
    (hq : q = q'.comap (Ideal.Quotient.mk L))
    (Ω R R' : Type (max u v w)) [Field Ω]
    [Algebra q.ResidueField Ω] [IsSepClosure q.ResidueField Ω]
    [Algebra q'.ResidueField Ω] [IsSepClosure q'.ResidueField Ω]
    (_hΩ : algebraMap q.ResidueField Ω =
      (algebraMap q'.ResidueField Ω).comp
        (Ideal.ResidueField.map q q' (Ideal.Quotient.mk L) hq))
    [Algebra (Localization.AtPrime q) Ω]
    [IsScalarTower (Localization.AtPrime q) q.ResidueField Ω]
    [Algebra (Localization.AtPrime q') Ω]
    [IsScalarTower (Localization.AtPrime q') q'.ResidueField Ω]
    [CommRing R] [Algebra (Localization.AtPrime q) R]
    [CommRing R'] [Algebra (Localization.AtPrime q') R']
    (_hR : Algebra.StrictHenselizationPresentationIn.{max u v, w}
      (Localization.AtPrime q) Ω R)
    (_hR' : Algebra.StrictHenselizationPresentationIn.{max u v, w}
      (Localization.AtPrime q') Ω R') :
    IsRegularLocalRing (Localization.AtPrime q) ∧
      IsRegularLocalRing (Localization.AtPrime q') ∧
      IsRegularLocalRing R ∧ IsRegularLocalRing R' ∧
      ringKrullDim (Localization.AtPrime q) =
        ringKrullDim (Localization.AtPrime q') + (K.card : WithBot ℕ∞) ∧
      ringKrullDim R = ringKrullDim (Localization.AtPrime q) ∧
      ringKrullDim R' = ringKrullDim (Localization.AtPrime q') ∧
      ringKrullDim R = ringKrullDim R' + (K.card : WithBot ℕ∞) := by
  sorry

end MvPolynomial
