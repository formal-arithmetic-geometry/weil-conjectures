/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import WeilConjectures.RingTheory.CohenRing
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.PowerSeriesFullCoordinatesCohen
import Mathlib.RingTheory.LocalRing.Module

/-! # Equivariant relative coordinate lifts through a Cohen presentation

Source: ILO, Travaux de Gabber, VIII Lemma 5.5.2, proof, printed p.128;
Stacks Project, More on Algebra, Tag 07NM (3)
(blueprint: lem-per-equivariant-relative-coordinate-lift).

All continuity assertions use the maximal-ideal-adic topology explicitly.
The source action in the final equivariance equation is Mathlib's coefficientwise
`rescale`, hence is the action scaling each source variable by its primed character.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace MvPowerSeries

/-- A second eigenparameter system lifts to relative Cohen coordinates, keeping the
common prefix literally fixed.

Source: ILO VIII Lemma 5.5.2, proof, printed p.128, and Stacks Tag 07NM (3)
(blueprint: lem-per-equivariant-relative-coordinate-lift).

Proof:
1. By lem-weil-pbc-power-series-field-cohen-regular-complete the source is complete
Noetherian regular local with maximal ideal (p,X) and dimension d+1. The two parameter
lists of A have length d and span its maximal ideal. By
lem-weil-pbc-regular-local-cotangent-dimension their cotangent classes are bases.
2. On the common prefix the two eigencharacters agree: distinct powers of zeta differ
by a unit, whereas each parameter has nonzero cotangent class. Keep those X_i fixed.
For the remaining indices write z'_i as a combination of f(X_j), lift its coefficients
using surjectivity, and thus choose a lift u_i in the variables ideal.
3. Replace u_i by |H|^{-1} times the sum of chi'_i(h)^{-1} h(u_i). The variables ideal
is stable. Equivariance of f shows the image is z'_i. Reindexing the sum proves the
primed eigenvector equation. The coefficient action is trivial, so no twisted scalar
terms occur. The common prefix already satisfies that equation by step 2.
4. The relative cotangent space I/(pI+I^2), I=(X), is k^d by linear coefficients.
It maps onto the d-dimensional cotangent space of A and hence is isomorphic to it.
Consequently the lifted classes form a basis. Together with p they span the source
cotangent space; lem-weil-pbc-nakayama-local-generators gives generators of its
maximal ideal. Their number d+1 makes them a regular system of parameters.
5. Apply lem-weil-pbc-power-series-full-coordinates-cohen to obtain the coefficient
algebra equivalence. It is continuous for maximal-ideal-adic topologies because it
is a local ring isomorphism. Truncations show it is the canonical substitution and
that it intertwines rescale by the primed characters with the original action.
For d=0 this is the coefficient identity; for l=d every variable is fixed.
-/
theorem exists_equivariant_relative_coordinate_lift
    (C : Type u) [CommRing C] [IsLocalRing C] [IsNoetherianRing C]
    (p d : ℕ) (hC : IsCohenRing p C)
    (H : Type v) [CommGroup H] [Fintype H]
    (hN : IsUnit (Fintype.card H : C))
    (ζ : Cˣ) (hζ : ζ ^ Fintype.card H = 1)
    (hsep : ∀ a : ℕ, 1 ≤ a → a < Fintype.card H → IsUnit (1 - (ζ : C) ^ a))
    (χ χ' : Fin d → H →* Cˣ)
    (hχ : ∀ (i : Fin d) (h : H), χ i h ∈ Subgroup.zpowers ζ)
    (hχ' : ∀ (i : Fin d) (h : H), χ' i h ∈ Subgroup.zpowers ζ)
    (ρ : H →* RingAut (MvPowerSeries (Fin d) C))
    (hcontinuous : ∀ h : H,
      @Continuous (MvPowerSeries (Fin d) C) (MvPowerSeries (Fin d) C)
        (IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) C)).adicTopology
        (IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) C)).adicTopology (ρ h))
    (hfixed : ∀ (h : H) (c : C), ρ h (MvPowerSeries.C c) = MvPowerSeries.C c)
    (heigen : ∀ (h : H) (i : Fin d),
      ρ h (X i) = MvPowerSeries.C (χ i h).val * X i)
    (A : Type w) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (α : H →* RingAut A)
    (f : MvPowerSeries (Fin d) C →+* A) [IsLocalHom f]
    (hfsurj : Function.Surjective f)
    (hf : ∀ (h : H) (r : MvPowerSeries (Fin d) C), f (ρ h r) = α h (f r))
    (residueIdentification : IsLocalRing.ResidueField C ≃+* IsLocalRing.ResidueField A)
    (hresidue : ∀ c : C, IsLocalRing.residue A (f (MvPowerSeries.C c)) =
      residueIdentification (IsLocalRing.residue C c))
    (hparameters : IsLocalRing.IsRegularSystemOfParameters
      (List.ofFn (fun i : Fin d ↦ f (X i))))
    (z' : Fin d → A)
    (hparameters' : IsLocalRing.IsRegularSystemOfParameters (List.ofFn z'))
    (heigen' : ∀ (h : H) (i : Fin d),
      α h (z' i) = f (MvPowerSeries.C (χ' i h).val) * z' i)
    (l : ℕ) (hl : l ≤ d)
    (hprefix : ∀ i : Fin d, i.val < l → z' i = f (X i)) :
    ∃ t' : Fin d → MvPowerSeries (Fin d) C,
      (∀ i : Fin d, t' i ∈ Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) C))) ∧
      (∀ i : Fin d, f (t' i) = z' i) ∧
      (∀ i : Fin d, i.val < l → t' i = X i) ∧
      (∀ (h : H) (i : Fin d), ρ h (t' i) = MvPowerSeries.C (χ' i h).val * t' i) ∧
      IsLocalRing.IsRegularSystemOfParameters (MvPowerSeries.C (p : C) :: List.ofFn t') ∧
      ∃ e : MvPowerSeries (Fin d) C ≃ₐ[C] MvPowerSeries (Fin d) C,
        (∀ i : Fin d, e (X i) = t' i) ∧
        (∀ F : MvPowerSeries (Fin d) C, e F = subst t' F) ∧
        @Continuous (MvPowerSeries (Fin d) C) (MvPowerSeries (Fin d) C)
          (IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) C)).adicTopology
          (IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) C)).adicTopology e ∧
        ∀ (h : H) (F : MvPowerSeries (Fin d) C),
          e (rescale (fun i : Fin d ↦ (χ' i h).val) F) = ρ h (e F) := by
  sorry

end MvPowerSeries
