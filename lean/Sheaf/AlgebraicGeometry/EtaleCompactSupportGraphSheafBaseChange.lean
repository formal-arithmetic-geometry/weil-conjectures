/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphProjectionTermwise

/-!
# The sheaf graph projection under base change

Source: SGA 4 XVII 6.2.11; Stacks Project Tags 03S6, 0F4L, 0E46 and 0E47.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Base change preserves the clopen-graph projection, as a transformation of sheaves.
There are no complexes, localization functors or total derived direct images in this identity.
Source: SGA 4 XVII 6.2.11; Stacks Project Tags 03S6, 0F4L, 0E46 and 0E47.
(blueprint: lem-a2-compact-support-graph-sheaf-base-change).

Proof: transpose the specified graph map back under inverse image/direct image.
The triangle identities cancel its inserted unit and counit, giving the original etale
sum base-change comparison, clopen graph projection and graph composition comparison.
Write these over the fiber products of the compactification with its etale source.
The graph is a clopen section of the second projection. Pulling the graph
and its complementary open subset through the cartesian square gives the graph and complement
for the pulled-back compactification. The graph projection is the identity on the graph
component and zero on the complement; its base change has the same two restrictions. The
sheaf axiom for this disjoint open cover equates them. The etale sum exchange is normalized
by the inverse conjugate of the inverse-image/direct-image exchange; the open-extension
exchange and the graph composition comparison are likewise normalized by their displayed
adjunctions. Horizontal and vertical mate pasting therefore identify the comparison maps
in the two rectangles with the specified sum, pullback-square and open-extension maps.
Composing the equal graph projections with those comparisons proves the displayed equation.
Empty fibers and the zero ring give the same identity and require no extra assumption. -/
theorem compactSupportGraphSheafProjection_baseChange
    (A : Type (u + 1)) [CommRing A]
    {U X X' : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    (c : Compactification f) (g : X' ⟶ X) :
    let c' := c.ofIsPullback (IsPullback.of_hasPullback g f).flip
    let E := etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance
    let H := upperStar (ModuleCat.{u + 1} A) (pullback.snd g f)
    let E' := etaleLowerShriek (ModuleCat.{u + 1} A) (pullback.fst g f) inferInstance
    let P := upperStar (ModuleCat.{u + 1} A) c.g
    let P' := upperStar (ModuleCat.{u + 1} A) c'.g
    let T := upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g g)
    let δ := compactSupportGraphSheafProjection A f c (etaleCompactificationGraphMap A f c)
    let δ' := compactSupportGraphSheafProjection A (pullback.fst g f) c'
      (etaleCompactificationGraphMap A (pullback.fst g f) c')
    letI := isIso_etaleLowerShriekBaseChangeMap A g f
    let σ := (asIso (etaleLowerShriekBaseChangeMap A g f)).symm
    Functor.whiskerRight σ.hom P' ≫ (Functor.associator H E' P').hom ≫
        Functor.whiskerLeft H δ' ≫
        openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} A)
          (c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback g f).flip).toCommSq =
      (Functor.associator E (upperStar (ModuleCat.{u + 1} A) g) P').hom ≫
        Functor.whiskerLeft E
          (squareUpperStarIso (ModuleCat.{u + 1} A)
            (IsPullback.of_hasPullback c.g g).toCommSq).hom ≫
        (Functor.associator E P T).inv ≫ Functor.whiskerRight δ T := by sorry

end AlgebraicGeometry.Etale
