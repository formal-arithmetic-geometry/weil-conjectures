/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.Paper.OrgogozoInductionData
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober
import Sheaf.AlgebraicGeometry.ExcellentBaseGenericCurvePreparation
import Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable
import Sheaf.SixFunctors.TraceFormula.FiniteEtaleMarkingSections

/-!
# Marked semistable curve after alteration over an excellent base

Source: de Jong, Families of curves and alterations (1997), Theorem 2.4 (i), (ii),
and Remark 2.5, printed pp. 602--603 (blueprint:
lem-trf-excellent-base-marked-semistable-curve).

## Main statements

* `exists_excellentBaseMarkedSemistableCurve` states the marked semistable alteration.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Orgogozo

namespace AlgebraicGeometry

/-- A proper dominant family of curves over an excellent base admits simultaneous alterations
with a marked semistable model.
Source: de Jong, Families of curves and alterations (1997), Theorem 2.4 (i), (ii), and
Remark 2.5, printed pp. 602--603 (blueprint: lem-trf-excellent-base-marked-semistable-curve).

Proof plan (the node's four steps):
1. Apply `lem-trf-excellent-base-generic-curve-preparation` to obtain alterations of source and
   base, a proper dominant family, a smooth geometrically integral generic fibre, and the
   prepared boundary.
2. Apply `lem-trf-dejong-arbitrary-base-marked-semistable` to the prepared family to obtain a
   proper flat finitely presented nodal curve, its generic-fibre properties, and a divisor
   containing the transformed boundary.
3. Apply `lem-trf-finite-etale-marking-sections` to split the proper étale divisor into finitely
   many disjoint sections; pull the exceptional closed subset back along the finite base map.
4. Compose the three commutative alteration squares. Properness and finite-over-a-dense-open
   are stable under the displayed compositions, and the fibre, nodal, generic-fibre, marking,
   and boundary assertions are inherited by finite base change.

The geometric fibres are those over the chosen algebraic closure `geometricPoint B' y` of each
residue field (def-weil-geometric-fibre).
-/
theorem exists_excellentBaseMarkedSemistableCurve
    {C B : Scheme.{u}} (f : C ⟶ B)
    [IsIntegral C] [IsIntegral B] [IsNoetherian C] [IsNoetherian B]
    (hC : IsExcellentScheme C) (hB : IsExcellentScheme B)
    [IsProper f] [IsDominant f]
    (hgeneric : ∃ η : B, IsGenericPoint η Set.univ ∧
      topologicalKrullDim (f.fiber η) = 1)
    (Z : Set C) (hZ : IsClosed Z ∧ Z ≠ Set.univ) :
    ∃ (C' B' : Scheme.{u}) (a : C' ⟶ C) (b : B' ⟶ B) (f' : C' ⟶ B'),
      a ≫ f = f' ≫ b ∧
      IsIntegral C' ∧ IsExcellentScheme C' ∧ IsNoetherian C' ∧
      IsIntegral B' ∧ IsExcellentScheme B' ∧ IsNoetherian B' ∧
      (IsProper a ∧ Surjective a ∧
        (∃ U : C.Opens, Dense (U : Set C) ∧ IsFinite (pullback.snd a U.ι))) ∧
      (IsProper b ∧ Surjective b ∧
        (∃ U : B.Opens, Dense (U : Set B) ∧ IsFinite (pullback.snd b U.ι))) ∧
      IsProper f' ∧ Flat f' ∧ LocallyOfFinitePresentation f' ∧
      QuasiCompact f' ∧ QuasiSeparated f' ∧
      (∀ y : B', IsSemistableGeometricCurve (pullback.snd f' (geometricPoint B' y))) ∧
      (∃ η' : B', IsGenericPoint η' Set.univ ∧
        Smooth (f'.fiberToSpecResidueField η') ∧
        GeometricallyIntegral (f'.fiberToSpecResidueField η')) ∧
      (∃ n : ℕ, ∃ s : Fin n → (B' ⟶ C'), ∃ T : Set B',
        (∀ i : Fin n, s i ≫ f' = 𝟙 B') ∧
        (∀ i j : Fin n, i ≠ j →
          Disjoint (Set.range (s i)) (Set.range (s j))) ∧
        (∀ i : Fin n, ∀ x : C', x ∈ Set.range (s i) →
          (f'.stalkMap x).hom.FormallySmooth) ∧
        (IsClosed T ∧ T ≠ Set.univ) ∧
        a ⁻¹' Z ⊆ (⋃ i : Fin n, Set.range (s i)) ∪ f' ⁻¹' T) := by
  sorry

end AlgebraicGeometry
