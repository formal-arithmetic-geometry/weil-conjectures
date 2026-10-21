/- Copyright (c) 2026 The SHEAF contributors. All rights reserved. -/
module

public import Sheaf.Paper.RingedRefinementConstruction
public import Sheaf.Paper.CanonicalRingedRefinementSquare
import Sheaf.SixFunctors.OpenTensorNormalization
import Sheaf.Paper.DerivedAdjunctionShift
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Paper.RingedCoefficientProjectionCocycle
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems

/-!
# Normalized clopen comparisons and coherence

(blueprint: lem-pur-ringed-refinement-clopen-laws).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization

namespace SheafOfModules.RingedRefinement

/-- Clopen component comparisons and the coherence remaining after the mate calculation.
Source: coefficient supplement Steps 3--8; Stacks 03DI, 07A7, 0E47
(blueprint: lem-pur-ringed-refinement-clopen-laws).
Proof: use normalized open base change for beta. Split the ringed module category
along the clopen section and its complementary open. Projection onto the section
is the row (identity, zero). Exact localization retains this product decomposition,
so scalar extension preserves the projection by additivity. The open comparisons
are fixed by their inverse transpose equations; restricting to the open proves their
compatibility with scalar comparison and composition. Paste these compatibilities
for the three factors of h to obtain HCompatible. Successive coefficient changes
use the balanced associator, and successive refinements select nested components;
the same rows (identity, zero, zero) give refinement composition. Mate pasting gives
spatial coefficient composition. Exact open maps act termwise on complexes; scalar
counits and geometric adjunctions have their canonical cochain shifts, proving all
shift fields. These calculations take place on the whole ringed derived category,
also on the vertical site, before evaluation or any total limit. -/
theorem ringedRefinementClopen {m : Mode} {T : Scheme.{u}} {c : Coefficients m T}
    (o : Calculus c) (p : Spatial o) (sc : ScalarComparisons o)
    (ac : ScalarComposition o) :
    ∃ e : OpenComparisons p, HCompatible sc e ∧
      ResidualLaws sc ac (canonicalRefinements e) ∧
      Nonempty (BasicShifts sc (canonicalRefinements e)) := by
  sorry

end SheafOfModules.RingedRefinement
