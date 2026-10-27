module

public import Sheaf.RingTheory.SupportedHomogeneousDivision
public import Mathlib.RingTheory.MvPowerSeries.Rename

/-! # Initial exponents of formal ideals

Source: Bierstone--Milman 1997, §3, Theorem 3.17 and Corollaries 3.19--3.20
(blueprint: def-trf-formal-initial-diagram).
No leading exponent is assigned to the zero series.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u

namespace MonomialDiagram

/-- Being the first nonzero exponent in total-degree lexicographic order.
Source: BM 1997, §3 (blueprint: def-trf-formal-initial-diagram). -/
def IsFirstExponent {d : ℕ} {L : Type u} [CommRing L]
    (F : MvPowerSeries (Fin d) L) (α : Fin d →₀ ℕ) : Prop :=
  MvPowerSeries.coeff α F ≠ 0 ∧ ∀ β : Fin d →₀ ℕ,
    Finsupp.DegLex (· < ·) (· < ·) β α → MvPowerSeries.coeff β F = 0

/-- The diagram of initial exponents, excluding zero series by a nonzero coefficient.
Source: BM 1997, §3 (blueprint: def-trf-formal-initial-diagram). -/
def initialDiagram {d : ℕ} {L : Type u} [CommRing L]
    (K : Ideal (MvPowerSeries (Fin d) L)) : Set (Fin d →₀ ℕ) :=
  {α | ∃ F ∈ K, IsFirstExponent F α}

/-- Cumulative count of complementary monomials. The counted set is finite, even for
an arbitrary diagram: it is contained in a finite total-degree ball.
Source: BM 1997, Corollary 3.20 (blueprint: def-trf-formal-initial-diagram). -/
def hilbertCount {d : ℕ} (D : Set (Fin d →₀ ℕ)) (n : ℕ) : ℕ :=
  {α : Fin d →₀ ℕ | α ∉ D ∧ α.degree ≤ n}.ncard

/-- The actual truncated quotient by the ideal and the indicated power of the variables.
Source: BM 1997, Corollary 3.20 (blueprint: def-trf-formal-initial-diagram). -/
abbrev truncation {d : ℕ} {L : Type u} [CommRing L]
    (K : Ideal (MvPowerSeries (Fin d) L)) (n : ℕ) :=
  MvPowerSeries (Fin d) L ⧸
    (K ⊔ (Ideal.span (Set.range (MvPowerSeries.X (σ := Fin d) (R := L)))) ^ (n + 1))

/-- Extension of a diagram by free final coordinates.
Source: BMT §6.5 (blueprint: def-trf-formal-initial-diagram). -/
def freeExtension {d : ℕ} (D : Set (Fin d →₀ ℕ)) (r : ℕ) :
    Set (Fin (d + r) →₀ ℕ) :=
  {α | ∃ β ∈ D, ∀ i : Fin d, β i ≤ α (Fin.castAdd r i)}

end MonomialDiagram
