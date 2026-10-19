/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q141
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Finite locally finitely presented morphisms are of finite presentation

Source: Stacks Project, Tag 057T, proof paragraph beginning "Since π is finite";
Morphisms, Definition Tag 01TP (blueprint: lem-trf-finite-morphism-finite-presentation).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite, locally finitely presented morphism is of finite presentation and separated.
Finite presentation is spelled out as local finite presentation, quasi-compactness and
quasi-separatedness, as in Stacks Project, Definition Tag 01TP. The separatedness clause
is the additional property explicitly asserted in the proof of Tag 057T
(blueprint: lem-trf-finite-morphism-finite-presentation).

Proof: By `def-weil-finite-integral-morphism`, a finite morphism is affine.
By clause (3) of `lem-weil-pbc-affine-morphism-permanence`, an affine morphism is
quasi-compact and separated; separatedness implies quasi-separatedness. Combining
quasi-compactness and quasi-separatedness with the assumed local finite presentation
gives finite presentation by `def-sbc-locally-finite-presentation` (Stacks Tag 01TP).
This also retains the separatedness asserted in the source paragraph of Tag 057T. -/
theorem finitePresentation_of_finite_of_locallyOfFinitePresentation
    {T U : Scheme.{u}} (p : T ⟶ U) [IsFinite p] [LocallyOfFinitePresentation p] :
    LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ QuasiSeparated p ∧ IsSeparated p := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry
