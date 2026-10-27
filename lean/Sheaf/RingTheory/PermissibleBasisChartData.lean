module

public import Sheaf.RingTheory.LocalStandardBasisInvariants
public import Sheaf.AlgebraicGeometry.PermissibleCoordinateChart
public import WeilConjectures.Blowup.Affine.ChartAlgebra
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Coordinates for the single-index permissible standard-basis correction

Source: Hironaka (1970), (13.1), p.168, and (19.1)–(20.3), pp.176–177.
(blueprint: def-trf-permissible-basis-chart-data).

All chart rings are existing constructions. Maps are specified on coefficients
and every variable, which determines them uniquely. Division is specified in
the ambient localization before localizing the chart, retaining its meaning even
when the exceptional equation becomes a zero divisor on the quotient ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

namespace Hironaka

open AlgebraicGeometry AlgebraicGeometry.AffineBlowup AlgebraicGeometry.NodalLocal

variable {T : Type u} [CommRing T] {r s : ℕ}

/-- The existing coordinate quotient with pivot zero and all `x` coordinates in the centre.
Source: Hironaka (1970), (13.1), p.168.
(blueprint: def-trf-permissible-basis-chart-data). -/
abbrev ParameterChart (x : Fin (r + 1) → T) :=
  PermissibleCoordinateChart.Chart x Finset.univ 0

/-- The ratio labels in the existing quotient presentation.
Source: Hironaka (1970), (13.1), p.168.
(blueprint: def-trf-permissible-basis-chart-data). -/
abbrev RatioLabel (r : ℕ) := ↥((Finset.univ : Finset (Fin (r + 1))).erase 0)

/-- The map from the presented chart into `T[1/x₀]`, fixed on all generators.
Source: Hironaka (1970), (13.1), p.168.
(blueprint: def-trf-permissible-basis-chart-data). -/
def IsAmbientChartMap (x : Fin (r + 1) → T)
    (ι : ParameterChart x →+* Localization.Away (x 0)) : Prop :=
  (∀ h : T, ι (algebraMap T (ParameterChart x) h) = algebraMap T _ h) ∧
    ∀ i : RatioLabel r,
      ι (PermissibleCoordinateChart.ratio x Finset.univ 0 i) =
        chartFraction (x 0) 1 (x i)

/-- The quotient chart map, fixed by the quotient on coefficients and ratio fractions.
Source: Hironaka (1970), (19.1)–(19.2), p.176.
(blueprint: def-trf-permissible-basis-chart-data). -/
def IsQuotientChartMap (x : Fin (r + 1) → T) (b : Ideal T)
    (ρ : ParameterChart x →+*
      chartRing ((Ideal.span (Set.range x)).map (Ideal.Quotient.mk b))
        (Ideal.Quotient.mk b (x 0))) : Prop :=
  (∀ h : T, ρ (algebraMap T (ParameterChart x) h) =
    algebraMap (T ⧸ b) _ (Ideal.Quotient.mk b h)) ∧
    ∀ i : RatioLabel r,
      (ρ (PermissibleCoordinateChart.ratio x Finset.univ 0 i) :
        Localization.Away (Ideal.Quotient.mk b (x 0))) =
          chartFraction (Ideal.Quotient.mk b (x 0)) 1 (Ideal.Quotient.mk b (x i))

/-- Reduction of the polynomial presentation modulo the original maximal ideal.
The surviving variables retain their nonzero labels.
Source: Hironaka (1970), (13.1), p.168.
(blueprint: def-trf-permissible-basis-chart-data). -/
def residuePolynomialMap [IsLocalRing T] (r : ℕ) :
    MvPolynomial (RatioLabel r) T →+*
      MvPolynomial {i : Fin (r + 1) // i ≠ 0} (IsLocalRing.ResidueField T) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (IsLocalRing.residue T))
    (fun i ↦ MvPolynomial.X ⟨i.val, Finset.ne_of_mem_erase i.property⟩)

/-- The localized order space `U_d`; no rationality or separability of the prime is assumed.
Source: Hironaka (1970), §13, p.168, and Lemma 20.
(blueprint: def-trf-permissible-basis-chart-data). -/
def InOrderSpace {k : Type u} [Field k] (r : ℕ)
    (p : PrimeSpectrum (MvPolynomial {i : Fin (r + 1) // i ≠ 0} k))
    (d : ℕ) (φ : MvPolynomial (Fin (r + 1)) k) : Prop :=
  φ.IsHomogeneous d ∧
    algebraMap _ (Localization.AtPrime p.asIdeal) (MvPolynomial.dehomogenizeX k 0 φ) ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) ^ d

/-- A fraction in the ambient chart, followed by localization at its prime.
This avoids choosing a coefficient field or dividing inside the quotient `R`.
Source: Hironaka (1970), (19.1)–(19.2), p.176.
(blueprint: def-trf-permissible-basis-chart-data). -/
def IsDividedElement (x : Fin (r + 1) → T)
    (ι : ParameterChart x →+* Localization.Away (x 0))
    (p' : PrimeSpectrum (ParameterChart x)) (e : ℕ) (f : T)
    (g : Localization.AtPrime p'.asIdeal) : Prop :=
  ∃ h : ParameterChart x, ι h = chartFraction (x 0) e f ∧
    algebraMap (ParameterChart x) (Localization.AtPrime p'.asIdeal) h = g

/-- The coordinate map into the tangent ring, pinned on coefficients and parameters.
The membership witnesses simply express that parameters lie in the maximal ideal.
Source: Hironaka (1970), (13.1), p.168.
(blueprint: def-trf-permissible-basis-chart-data). -/
def IsParameterGradedMap [IsLocalRing T] (x : Fin (r + 1) → T) (y : Fin s → T)
    (χ : MvPolynomial (Fin (r + 1) ⊕ Fin s) (IsLocalRing.ResidueField T) →+*
      Ideal.associatedGraded (IsLocalRing.maximalIdeal T)) : Prop :=
  (∀ c, χ (MvPolynomial.C c) = algebraMap (T ⧸ IsLocalRing.maximalIdeal T) _ c) ∧
    (∀ i, ∃ hi : x i ∈ IsLocalRing.maximalIdeal T ^ 1,
      χ (MvPolynomial.X (Sum.inl i)) = initialForm T 1 ⟨x i, hi⟩) ∧
    (∀ j, ∃ hj : y j ∈ IsLocalRing.maximalIdeal T ^ 1,
      χ (MvPolynomial.X (Sum.inr j)) = initialForm T 1 ⟨y j, hj⟩)

/-- The ambient chart localized at the inverse image of the chosen point.
Source: Hironaka (1970), (19.2), p.176.
(blueprint: def-trf-permissible-basis-chart-data). -/
abbrev LocalChart {D C : Type u} [CommRing D] [CommRing C]
    (ρ : D →+* C) (z : PrimeSpectrum C) :=
  Localization.AtPrime (PrimeSpectrum.comap ρ z).asIdeal

/-- The kernel of the actual localized quotient chart map.
Source: Hironaka (1970), (19.2), p.176.
(blueprint: def-trf-permissible-basis-chart-data). -/
def transformIdeal {D C : Type u} [CommRing D] [CommRing C]
    (ρ : D →+* C) (z : PrimeSpectrum C) : Ideal (LocalChart ρ z) :=
  RingHom.ker (Localization.localRingHom (PrimeSpectrum.comap ρ z).asIdeal
    z.asIdeal ρ rfl)

/-- The original ring maps to the localized parameter chart through the quotient.
Source: Hironaka (1970), (19.2), p.176.
(blueprint: def-trf-permissible-basis-chart-data). -/
def originalToLocal (x : Fin (r + 1) → T) (p' : PrimeSpectrum (ParameterChart x)) :
    T →+* Localization.AtPrime p'.asIdeal :=
  (algebraMap (ParameterChart x) (Localization.AtPrime p'.asIdeal)).comp
    (algebraMap T (ParameterChart x))

/-- The exceptional and transverse ideal `(x₀,y)` in the localized ambient chart.
Source: Hironaka (1970), Lemma 20, pp.176–177.
(blueprint: def-trf-permissible-basis-chart-data). -/
def exceptionalIdeal (x : Fin (r + 1) → T) (y : Fin s → T)
    (p' : PrimeSpectrum (ParameterChart x)) : Ideal (Localization.AtPrime p'.asIdeal) :=
  (Ideal.span ({x 0} ∪ Set.range y)).map (originalToLocal x p')

/-- The ideal generated by a strict prefix; it is zero for the first index.
Source: Hironaka (1970), Lemma 20, pp.176–177.
(blueprint: def-trf-permissible-basis-chart-data). -/
def prefixIdeal {V : Type u} [CommRing V] {m : ℕ} (g : Fin m → V) (a : Fin m) : Ideal V :=
  Ideal.span {h | ∃ j, j < a ∧ h = g j}

/-- The triangular change of one generator, with empty sum at the first index.
Source: Hironaka (1970), Lemma 20, pp.176–177.
(blueprint: def-trf-permissible-basis-chart-data). -/
def correctedGenerator {V : Type u} [CommRing V] {m : ℕ}
    (f : Fin m → V) (a : Fin m) (c : Fin m → V) : V :=
  f a - ∑ j ∈ Finset.univ.filter (fun j ↦ j < a), c j * f j

end Hironaka
