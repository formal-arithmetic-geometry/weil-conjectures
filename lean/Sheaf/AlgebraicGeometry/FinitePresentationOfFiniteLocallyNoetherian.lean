/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finite morphisms over locally Noetherian schemes are of finite presentation

Source: the Weil conjectures blueprint, `sec-nagata-compactification`,
`sk-prop-nagata-sketch-zmt`, node of order 198 (blueprint: pqf-lem-finite-fp-locnoeth).
Finite presentation uses the convention of Stacks Project, Tag 01TP.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite morphism to a locally Noetherian scheme is of finite presentation.
Source: the Weil conjectures blueprint, `sec-nagata-compactification`,
`sk-prop-nagata-sketch-zmt`, node of order 198 (blueprint: pqf-lem-finite-fp-locnoeth).

Proof:
1. By `lem-weil-pbc-finite-iff-integral-lft`, the finite morphism is locally of finite type.
   It is affine by `def-weil-pbc-scheme-conventions`, hence quasi-compact and quasi-separated
   by `lem-weil-pbc-affine-morphism-permanence` (3).
2. By `pqf-lem-lft-fp-locnoeth`, locally finite type over the locally Noetherian target
   (`pqf-def-locnoeth`) implies locally of finite presentation.
3. These three properties are exactly finite presentation according to
   `def-weil-pbc-scheme-conventions` and `def-sbc-locally-finite-presentation`
   (Stacks Project, Tag 01TP). -/
theorem finitePresentation_of_finite_over_locallyNoetherian
    {S T : Scheme.{u}} (p : T ⟶ S) [IsLocallyNoetherian S] [IsFinite p] :
    LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ QuasiSeparated p := by
  sorry

end AlgebraicGeometry
