/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.TowerPreservation
public import Sheaf.Paper.WitnessCompatibility
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.Paper.FiniteAmplificationProper
import Sheaf.Paper.ProperFamilyWitnessCompatibility
import Sheaf.Paper.PullbackFamilyWitnessCompatibility
import Sheaf.Paper.TowerPreservationFromAmplification

/-!
# Amplification for proper base-change squares

Source: blueprint sec-proper-base-change/sk-thm-properbasechange, order 1354;
Stacks Tags 095U, 0GL0, 09C1, 09C7 and 09C2
(blueprint: thm-weil-pbc-amplification-proper).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- AMP with the common bound `2 * e`, WIT, and TOW for a proper Cartesian square.
The same adic coefficient datum is used by all three predicates.
Source: blueprint order 1354; Stacks Tags 095U, 0GL0, 09C1, 09C7 and 09C2
(blueprint: thm-weil-pbc-amplification-proper).

Proof, following the repaired assembly without perfectness over intermediate quotients:
1. Evaluating the annihilator hypothesis on 1 gives N in I. Thus N^n kills A/I^n.
Since N is invertible at every stalk, every additive order in the finite quotient is
invertible there. The Cartesian square pasted with a geometric point of Y' identifies
its fibre for f' with the fibre for f at the composite point of Y, by a scheme isomorphism.
The induced homeomorphism preserves topological Krull dimension, so the same bound e
applies to f'. This works for empty fibres as well.
2. Apply [thm-weil-pbc-direct-image-finiteness-proper] to f and f' at every positive
quotient, with these additive-order and geometric-fibre bounds. Apply
[lem-weil-pbc-pullback-preserves-bounded-constructible] to g and g' for exactness,
bounded constructibility, and preservation of each cohomological interval. These four
conclusions assemble into AMP(square; 2e).
3. Apply [lem-weil-pbc-proper-family-witness-compatibility] separately to f and f'.
This is the proper torsion projection-formula argument, with the canonical site
comparison and retained etale origins; no quotient is assumed perfect over another.
Apply [lem-weil-pbc-pullback-family-witness-compatibility] separately to g and g'.
This uses actual etale inverse-image origins and the scalar/pullback comparison;
bounded-below full faithfulness lifts their normalizations and morphisms uniquely.
The four family conclusions assemble into WIT(square).
4. Apply [lem-weil-pbc-tower-preservation-from-amplification] to the AMP and WIT
just constructed. Its uniform input bound, quotient-linear output tower construction,
and common local models give TOW(square). Combine the three assertions.
-/
theorem amplification_of_isProper
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    {A : Type (u + 1)} [CommRing A] (d : Scheme.AdicCoefficientDatum A)
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    (hDimX : ∃ k : ℕ, topologicalKrullDim X ≤ (k : WithBot ℕ∞))
    (hDimY : ∃ k : ℕ, topologicalKrullDim Y ≤ (k : WithBot ℕ∞))
    (hDimX' : ∃ k : ℕ, topologicalKrullDim X' ≤ (k : WithBot ℕ∞))
    (hDimY' : ∃ k : ℕ, topologicalKrullDim Y' ≤ (k : WithBot ℕ∞))
    [IsProper f] [IsProper f']
    (N : ℕ) (hN : 0 < N) (hAnnihilator : ∀ a : A ⧸ d.ideal, N • a = 0)
    (hInvertX : ∀ x : X, IsUnit (N : X.presheaf.stalk x))
    (hInvertY : ∀ y : Y, IsUnit (N : Y.presheaf.stalk y))
    (hInvertX' : ∀ x : X', IsUnit (N : X'.presheaf.stalk x))
    (hInvertY' : ∀ y : Y', IsUnit (N : Y'.presheaf.stalk y))
    (e : ℕ)
    (hFib : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim ↥(pullback f y) ≤ (e : WithBot ℕ∞)) :
    Scheme.HasFiniteLevelAmplification sq d (2 * e) ∧
      WitnessCompatibility sq d ∧ Scheme.HasTowerPreservation sq d := by
  have hAmp := finiteLevelAmplification_of_isProper sq d hDimX hDimY hDimX' hDimY'
    N hN hAnnihilator hInvertX hInvertY hInvertX' hInvertY' e hFib
  have hWit : WitnessCompatibility sq d :=
    ⟨pbcFamilyWitnessCompatibility_directImage_of_isProper f d,
      pbcFamilyWitnessCompatibility_directImage_of_isProper f' d,
      pbcFamilyWitnessCompatibility_pullback g d,
      pbcFamilyWitnessCompatibility_pullback g' d⟩
  exact ⟨hAmp, hWit, towerPreservation_of_amplification_witnesses sq d (2 * e) hAmp hWit⟩

end AlgebraicGeometry.ProEtale
