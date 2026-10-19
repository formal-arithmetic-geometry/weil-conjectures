module

public import Mathlib.RingTheory.MvPowerSeries.Restricted
public import Mathlib.RingTheory.MvPowerSeries.GaussNorm
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Maps.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Finite presentations by restricted power series

Source: Temkin, Stable modification of relative curves, Theorem 3.5.5, Steps 2--3,
pp. 22--23 (blueprint: def-trf-restricted-series-presentation).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v w

namespace RestrictedSeries

/-- Constants in Mathlib's restricted-series subring, at polyradius one.
Source: Temkin, Theorem 3.5.5, Step 3
(blueprint: def-trf-restricted-series-presentation). -/
noncomputable def constants (R : Type u) [NormedCommRing R] [IsUltrametricDist R] (n : ℕ) :
    R →+* (MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin n ↦ (1 : ℝ))) :=
  (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R).codRestrict _
    (MvPowerSeries.isRestricted_C _)

/-- A finite restricted-series presentation, with finitely generated relations and the
adic quotient topology. The topology on the target is the principal adic topology.
Source: Temkin, Theorem 3.5.5, Step 3
(blueprint: def-trf-restricted-series-presentation). -/
def IsTopologicallyFinitelyPresented
    (R : Type u) [NormedCommRing R] [IsUltrametricDist R]
    (A : Type v) [CommRing A] (scalar : R →+* A) (π : R) : Prop :=
  ∃ (n : ℕ)
    (f : (MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin n ↦ (1 : ℝ))) →+* A),
    Function.Surjective f ∧ (RingHom.ker f).FG ∧
    f.comp (constants R n) = scalar ∧
    @Topology.IsQuotientMap _ _ (Ideal.span {constants R n π}).adicTopology
      (Ideal.span {scalar π}).adicTopology f

/-- An affinoid presentation with its Banach quotient norm. The Gauss norm and the
restricted-series subring are Mathlib's; no coefficientwise product topology is used.
The zero quotient is permitted.
Source: Temkin, Theorem 3.5.5, Steps 2--3
(blueprint: def-trf-restricted-series-presentation). -/
def IsAffinoidQuotient
    (F : Type u) [NormedField F] [IsUltrametricDist F]
    (B : Type v) [NormedCommRing B] (scalar : F →+* B) : Prop :=
  CompleteSpace B ∧
    ∃ (n : ℕ)
      (f : (MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin n ↦ (1 : ℝ))) →+* B),
      Function.Surjective f ∧ f.comp (constants F n) = scalar ∧
      ∀ b : B, ‖b‖ = sInf {r : ℝ | ∃ s, f s = b ∧
        r = MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin n ↦ 1) s.val}

/-- The image of a ring map is bounded and generated topologically by finitely many
variables over the specified scalar ring. Approximation takes place in the image,
with the topology induced from the ambient normed ring.
Source: Temkin, Theorem 3.5.5, Step 2
(blueprint: def-trf-restricted-series-presentation). -/
def HasBoundedTopologicallyGeneratedImage
    (R : Type u) [CommRing R] (A : Type v) [CommRing A]
    (B : Type w) [NormedCommRing B] (scalar : R →+* A) (j : A →+* B) : Prop :=
  (∃ M : ℝ, ∀ a : A, ‖j a‖ ≤ M) ∧
    ∃ (n : ℕ) (x : Fin n → A), ∀ (a : A) (ε : ℝ), 0 < ε →
      ∃ p : MvPolynomial (Fin n) R,
        ‖j a - MvPolynomial.eval₂ (j.comp scalar) (fun i ↦ j (x i)) p‖ < ε

end RestrictedSeries
