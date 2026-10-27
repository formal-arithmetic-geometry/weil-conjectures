/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FreeLogChartCoordinates
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters

/-!
# Free chart presentation and strict-local parameters

Source: ILO VI 1.2, 1.6--1.7 (blueprint: lem-trf-free-log-chart-strict-parameters).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- The free chart calculation is carried out over a single strict-local ring.
Source: ILO VI 1.2, 1.6--1.7, printed pp. 69--70; steps 2--4 of
lem-trf-free-log-chart-ordinary-parameters.
(blueprint: lem-trf-free-log-chart-strict-parameters).

Proof: the ordinary local ring is Noetherian by affine localization. Identify the
geometric strict-local ring with its algebraic strict henselization, using the
canonical comparison and its base-map equation. It is local and Noetherian, and
the local structural map reflects units. Thus exactly the ordinary nonunit indices J
are nonunits in the strict ring A. Let K be the complementary indices. A chart
monomial is a unit exactly when its J exponents vanish. The chart pushout is
N^J times A^units: send [(a_J,a_K),v] to (a_J,t_K^a_K v), and send (a_J,v)
back to [(a_J,0),v]. The pushout relation proves that these are inverse. Modding out
units yields E, with precisely the asserted value on every monomial. The structural
image of a nonunit contains a positive J exponent and is therefore in the span of
the t_j; each t_j is the image of a nonunit. This proves the ideal equation.
The group completion of N^J is Z^J, so its rational rank is |J|. Log regularity
now says A/I is regular and dim A = dim(A/I) + |J|. Choose a minimal generating
list of its maximal ideal with dim(A/I) entries and lift it to m_A. Together with
the ordered given t_j the lifts generate m_A: lift the quotient expression and
then express the remainder using I. This list has dim A entries, proving the
regular-parameter assertion. When J is empty the same argument lifts the full
quotient parameter list; dimension zero allows the empty list. -/
theorem freeLogChart_strict_parameters
    (W : Scheme.{u}) [IsAffine W] [IsLocallyNoetherian W]
    (N : EtaleLogStructure W) (hfs : N.IsFineSaturated)
    (hlog : FineSaturatedLogScheme.IsLogRegular ⟨W, inferInstance, N, hfs⟩)
    (r : ℕ) (β : Multiplicative (ULift.{u} (Fin r) → ℕ) →*
      N.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 W))))
    (hβ : N.IsChart (Scheme.Etale.mk (𝟙 W)) β)
    (w : W) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ W) (ht : (Scheme.SpecToEquivOfField Ω W t).1 = w) :
      (∃ E : N.characteristic t ≃*
          Multiplicative ({i : ULift.{u} (Fin r) //
            ¬ IsUnit (FreeLogChart.ordinaryCoordinate N β w i)} → ℕ),
        ∀ a : Multiplicative (ULift.{u} (Fin r) → ℕ),
          E (Associates.mk (N.toEtalePrelogStructure.germ t
            (Scheme.Etale.mk (𝟙 W)) (CategoryTheory.Over.homMk t (by simp)) (β a))) =
            Multiplicative.ofAdd (fun j ↦ a.toAdd j.val)) ∧
      (N.nonunitIdeal t).map (strictLocalRingStrictHenselizationIso W t).hom.hom =
        Ideal.span {a | ∃ i : ULift.{u} (Fin r),
          ¬ IsUnit (FreeLogChart.ordinaryCoordinate N β w i) ∧
            a = FreeLogChart.strictCoordinate N β t i} ∧
      (∃ (_ : IsLocalRing (Scheme.strictHenselizationRing t))
          (_ : IsNoetherianRing (Scheme.strictHenselizationRing t)),
        (∃ b : List (Scheme.strictHenselizationRing t),
          IsLocalRing.IsRegularSystemOfParameters
            (((FreeLogChart.nonunitIndices N β w).map
              (FreeLogChart.strictCoordinate N β t)) ++ b))) := by sorry

end AlgebraicGeometry
