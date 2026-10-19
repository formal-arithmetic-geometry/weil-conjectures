/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.RingedRefinementAssembly
import Sheaf.Paper.RingedCoefficientProjectionCocycle
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Paper.DerivedAdjunctionShift
import Sheaf.SixFunctors.OpenTensorNormalization

/-! Normalized ringed refinement construction and comparison obligations. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory AlgebraicGeometry SheafOfModules.OpenTensorNormalization

namespace SheafOfModules.RingedRefinement

/-- The pre-mate geometric square and the coefficient, spatial, and elementary shift
coherences of normalized operations. This does not assert the refinement square,
input naturality, or the commuting coefficient square.
Source: Bhatt--Scholze 6.7.6--6.7.7, coefficient supplement, steps 3--10;
Stacks 0E47, 0D6D, 0D6E (blueprint: lem-pur-ringed-refinement-coherences).

Proof: restrict the inverse beta and delta comparisons to their defining open
units. Their compatibility is then the coherent scalar/pullback compositor.
The clopen decomposition is an exact product equivalence on complexes and derived
categories; scalar extension preserves its identity/zero projection. Paste this
projection equation with beta and open composition to obtain `h_compatible`.
The section/retraction compositor agrees on both coefficient sides by pullback
composition coherence. The coefficient cocycle and units are obtained from the
normalized projection cocycle, using the balanced associators fixed on pure
tensors and on K-flat representatives; transposition similarly gives the open
coefficient and unit equations. For successive refinements, the nested clopen
projections both have matrix (identity, zero, zero). Paste their normalized open
comparisons, then take mates to obtain refinement composition; selecting the whole
component gives the identity. Spatial coefficient compatibility follows by pasting
the two inverse-image/scalar squares and taking mates. Exact open operations act
termwise; scalar shifts are fixed by the universal cochain counits. The derived
adjunction shift equations give compatibility of the geometric unit and counit.
Assembly derives shifts of beta and delta from their inverse transposes, and
of h from its three factors. It then derives shifts of chi, the refinement and
both square composites. Assembly constructs the scalar shifts and their counit
compatibility from the universal property. The clopen projection shifts follow in
Assembly from its image equation and
uniqueness of the counit retraction. Only the inverse-scalar comparison shift
equation remains here. The same proofs work on the
actual vertical sites, retaining all semilinear transitions. -/
theorem normalizedRefinementCoherences {m : Mode} {T : Scheme.{u}}
    {c : Coefficients m T} (o : Calculus c) (p : Spatial o)
    (sc : ScalarComparisons o) (ac : ScalarComposition o) (e : OpenComparisons p) :
    ElementaryCoherences sc ac (canonicalRefinements e) ∧
      Nonempty (ElementaryShifts sc e) := by sorry

end SheafOfModules.RingedRefinement
