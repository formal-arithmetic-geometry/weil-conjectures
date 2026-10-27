/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
import Sheaf.RingTheory.TateNormalizationLift

/-!
# Finite generation of the canonical reduction of a strict affinoid

Source: Bosch--Guentzer--Remmert, Non-Archimedean Analysis, Sections 6.3--6.4;
Fargues, Groupes analytiques rigides p-divisibles, Section 1.7.1, printed p. 18
(blueprint: lem-trf-affinoid-canonical-reduction-finite-type).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v

namespace RestrictedSeries

/-- The function `rho` in the canonical-reduction statement: supremum of the absolute
values of all continuous unital `K`-algebra characters. It uses the given Banach topology.
Source: BGR, Sections 6.3--6.4; Fargues, Section 1.7.1, printed p. 18
(blueprint: lem-trf-affinoid-canonical-reduction-finite-type). -/
noncomputable def affinoidCharacterSup
    (K : Type u) [NormedField K] (C : Type v) [NormedCommRing C] [Algebra K C]
    (c : C) : ℝ :=
  sSup {r : ℝ | ∃ χ : C →ₐ[K] K, Continuous χ ∧ r = ‖χ c‖}

/-- The canonical reduction is generated over the residue field by finitely many classes.
The conclusion is written on representatives: each spectral-unit-ball element is a
polynomial in the chosen elements, with coefficients in the valuation ring, modulo an
element of spectral value strictly below one. Lifting the finitely many coefficients of
a residue-field polynomial gives exactly this criterion for generation of
`C_{≤1}/C_{<1}` over `{a : K | ‖a‖ ≤ 1}/{a : K | ‖a‖ < 1}`.

The open-set condition gives the quotient Gauss topology, allowing every equivalent
Banach norm on `C`. It does not require the chosen norm to equal a quotient Gauss norm.

Source: BGR, Sections 6.3--6.4; Fargues, Section 1.7.1, printed p. 18
(blueprint: lem-trf-affinoid-canonical-reduction-finite-type).

Proof (the node's four steps):
1. Apply lem-trf-affinoid-spectral-banach-norm to obtain the nonarchimedean algebra
norm properties of `rho`; its unit ball is a subring and its strict unit ball an ideal.
Constants induce the residue-field action. Apply lem-trf-tate-normalization-lift to
obtain a finite injective map from a Tate algebra in `d` variables to `C`. The kernel
of the presentation is proper since `C` is nonzero. The source is reduced, since the
restricted-series ring embeds in the formal-power-series domain; this includes `d = 0`.
2. By lem-trf-affinoid-supremum-seminorm-calculus the Tate spectral function is its
Gauss norm. Its maximal-residue-field description agrees with continuous characters,
since maximal residues are finite over the algebraically closed field and their
quotient-Gauss bounds give continuity. Coefficient reduction identifies the source
reduction with the polynomial ring over the residue field: only finitely many
coefficients have norm one, and the remaining coefficients have supremum below one.
Finite coefficient convolution gives multiplicativity, and lifting finitely many
coefficients gives surjectivity.
3. Apply lem-trf-finite-affinoid-canonical-reduction to this finite normalization.
Choose spectral-unit-ball representatives of its finitely many module generators;
the images of the source variables also lie in the spectral unit ball.
4. Write any reduction class as a finite linear combination of these module generators
with polynomial coefficients in the source variables. The source-variable images and
module-generator representatives together generate the target reduction as an algebra.
Lift the finitely many residue coefficients to elements of `K` of norm at most one.
Equality of reduction classes means that the difference has spectral value below one.
No surjectivity of the reduction map or finiteness of the full integral ring is used. -/
theorem affinoid_canonical_reduction_finite_type
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K]
    (hK : ∃ a : K, a ≠ 0 ∧ ‖a‖ ≠ 1)
    (C : Type v) [NormedCommRing C] [CompleteSpace C] [Nontrivial C] [IsReduced C]
    [Algebra K C]
    (haff : ∃ (r : ℕ)
      (q : (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ))) →+* C),
      Function.Surjective q ∧ q.comp (constants K r) = algebraMap K C ∧
      ∀ U : Set C, IsOpen U ↔ ∀ s, q s ∈ U → ∃ ε : ℝ, 0 < ε ∧
        ∀ t, MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin r ↦ 1)
          (t.val - s.val) < ε → q t ∈ U) :
    ∃ (t : ℕ) (b : Fin t → C),
      (∀ i, affinoidCharacterSup K C (b i) ≤ 1) ∧
      ∀ c : C, affinoidCharacterSup K C c ≤ 1 →
        ∃ p : MvPolynomial (Fin t) K,
          (∀ ν : Fin t →₀ ℕ, ‖p.coeff ν‖ ≤ 1) ∧
          affinoidCharacterSup K C (c - MvPolynomial.eval₂ (algebraMap K C) b p) < 1 := by
  sorry

end RestrictedSeries
