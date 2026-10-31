/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.HilbertSamuelPresentation
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateFlag
public import WeilConjectures.AlgebraicGeometry.MarkedIdealInvariantData
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.Field.ULift

/-! # Logarithmic differential and factorial coefficient ideals

Source: BMT, arXiv:0905.3580, sections 5.1 and 5.4; ILO VIII 2.3.13
(blueprint: def-trf-logarithmic-coefficient-ideal).
All ideals are actual constructions. Integer derivations on rational algebras are precisely
rational derivations: the Leibniz rule kills inverses of nonzero integers. This avoids choosing
algebra instances on the rings of sections, including the zero ring of an empty open.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.MarkedIdeal
open HilbertSamuel

/-- The logarithmic differential ideal from its affine ideals. On a smooth rational scheme
these affine ideals commute with localization, so `ofIdeals` returns exactly that family,
without any choice of coordinates or generators. The single step is the existing
`logDerivative` of def-trf-marked-ideal-invariant-data, iterated `j` times. Source: BMT 5.4
(blueprint: def-trf-logarithmic-coefficient-ideal). -/
def logDifferential {N : Scheme.{u}} (E : List N.IdealSheafData)
    (I : N.IdealSheafData) (j : ℕ) : N.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals
    (fun U ↦ (logDerivative (E.map (fun D ↦ D.ideal U)))^[j] (I.ideal U))

/-- The displayed factorial-weighted coefficient ideal on the specified hypersurface.
Every exponent uses natural division, with positive denominator for each index in the sum.
Source: BMT 5.4, weighted sums and restriction to maximal contact
(blueprint: def-trf-logarithmic-coefficient-ideal). -/
def logarithmicCoefficientIdeal {N H : Scheme.{u}} (E : List N.IdealSheafData)
    (I : N.IdealSheafData) (i : H ⟶ N) (d : ℕ) : H.IdealSheafData :=
  ∑ j ∈ Finset.range d, ((logDifferential E I j).comap i) ^ (d.factorial / (d - j))

/-- The hypotheses of a logarithmic coefficient restriction. The two coordinate-flag
conditions say that the ordered boundary is SNC and transverse to N and H respectively.
The open in `maxOrder` is an arbitrary neighbourhood of cosupport, not a global order bound.
The equation and order-one condition specify the actual hypersurface cut out by h.
Source: BMT 5.1 and 5.4; the chosen-section formulation in ILO VIII 2.3.13's local input
(blueprint: def-trf-logarithmic-coefficient-ideal). -/
structure LogCoefficientData {S : Embedded (ULift.{u} ℚ)} (M : Marked S) where
  finite : QuasiCompact S.p
  supportFinite : QuasiCompact (M.j ≫ S.p)
  boundary : HasEtaleCoordinateFlag S.p M.j.ker M.j.ker S.boundary
  maxOrder : ∃ U : M.N.Opens,
    {x | (M.marking : ℕ∞) ≤ order M.ideal x} ⊆ (U : Set M.N) ∧
      ∀ x ∈ U, order M.ideal x ≤ (M.marking : ℕ∞)
  H : Scheme.{u}
  i : H ⟶ M.N
  closed : IsClosedImmersion i
  smooth : Smooth ((i ≫ M.j) ≫ S.p)
  h : Γ(M.N, ⊤)
  equation : i.ker = Scheme.IdealSheafData.ofIdealTop (Ideal.span {h})
  contact : Scheme.IdealSheafData.ofIdealTop (Ideal.span {h}) ≤
    logDifferential (S.boundary.map (fun D ↦ D.comap M.j)) M.ideal (M.marking - 1)
  orderOne : ∀ x : H,
    order (Scheme.IdealSheafData.ofIdealTop (Ideal.span {h})) (i x) = 1
  transverse : HasEtaleCoordinateFlag S.p (i ≫ M.j).ker (i ≫ M.j).ker S.boundary

/-- A marked realization of the actual coefficient ideal, allowing only transport along an
isomorphism over the specified hypersurface. Coherence and positive mark are supplied by
`Marked`, never assumed of an arbitrary substitute ideal. Source: BMT 5.4
(blueprint: def-trf-logarithmic-coefficient-ideal). -/
def IsLogCoefficient {S : Embedded (ULift.{u} ℚ)} {M : Marked S}
    (D : LogCoefficientData M) (Q : Marked S) : Prop :=
  ∃ e : Q.N ≅ D.H, Q.j = e.hom ≫ D.i ≫ M.j ∧
    Q.ideal = (logarithmicCoefficientIdeal (S.boundary.map (fun B ↦ B.comap M.j))
      M.ideal D.i M.marking).comap e.hom ∧ Q.marking = M.marking.factorial

end AlgebraicGeometry.MarkedIdeal
