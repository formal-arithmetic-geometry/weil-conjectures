/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FormallyUnramifiedConormal
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.UniversalThickeningFlatBaseChange
import Sheaf.AlgebraicGeometry.UniversalThickeningOpenRestriction

/-!
# Vanishing of the conormal sheaf for a flat morphism with open diagonal

Source: Stacks Project, Tag 04FF, the conormal calculation.
(blueprint: lem-weil-pbc-flat-open-diagonal-conormal-zero).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The conormal sheaf of any universal first order thickening vanishes when the
morphism is flat and its diagonal is an open immersion. No finite type assumption
is needed in this calculation.
Source: Stacks Project, Tag 04FF, proof, using Tags 04F9 and 04FA.
(blueprint: lem-weil-pbc-flat-open-diagonal-conormal-zero).
Proof: write p and q for the projections from X ×[S] X. The open diagonal makes f
formally unramified, and base change makes q formally unramified. Flat base change
of a universal thickening identifies p* C_f with C_q (04F9). On the open image D
of the diagonal, q is an isomorphism. Open restriction (04FA) identifies C_q|D
with the conormal of this isomorphism. The identity thickening of D is universal:
its lift of a test map is the composite with the inverse isomorphism. Uniqueness
of universal thickenings identifies its zero ideal with the ideal of any other
choice, so C_q|D is zero. Pull back the base-change identification along the
diagonal. Pullback along an open immersion is restriction, and Δ ≫ p = id_X;
composition and identity isomorphisms for tensor pullback therefore identify C_f
with the pullback of the zero module. Pullback preserves zero objects because it
is a left adjoint, so C_f is zero. -/
theorem flat_openDiagonal_conormal_isZero {X S X' : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsOpenImmersion (pullback.diagonal f)]
    (i : X ⟶ X') (s : X' ⟶ S) (H : IsUniversalFirstOrderThickening f i s) :
    IsZero (formallyUnramifiedConormal f i s H) := by sorry

end AlgebraicGeometry
