/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck
public import Sheaf.CategoryTheory.RightDerivedSingleUnitHomologyComparison

/-! # The bottom Grothendieck edge and the derived unit

Source: Stacks Project, Derived Categories, Tags 015N and 015J.
(blueprint: lem-sc-grothendieck-bottom-edge-single-unit)
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The raw bottom edge, with its source identified, is homology of the derived unit.
Source: Stacks Project, Derived Categories, Tags 015N and 015J, bottom interval.
(blueprint: lem-sc-grothendieck-bottom-edge-single-unit).

Proof: Put R = RF(X). It has no negative homology. The left exactness of F implies
that the degree-zero homology of the unit F(X)[0] to R is invertible. Specifically,
under singleFunctorCompHomologyFunctorIso and the single-object derived homology
comparison, this map is toRightDerivedZero, by
rightDerivedPlusSingleUnitHomology_comp_comparison. Its inverse is exactly the
rightDerivedZeroIsoSelf factor in grothendieckBottomEdgeSourceIso.
Since F(X)[0] has no positive homology, the unit factors uniquely through truncation
below 1 of R. Since R has no negative homology, this truncation lies in degree zero,
and its further truncation at degrees at least zero is isomorphic to itself.
The canonical eTruncLTCompETruncGEIso identifies this bottom interval with H^0(R)[0].
The degree-zero homology equality just established therefore identifies the inverse
source isomorphism followed by the interval inclusion with the derived unit.
Expand grothendieckSpectralObjectHIso at q = 0: the zero shifts of the single functor,
RG, and homology cancel by their shift-zero coherence identities. Naturality of the
single-object derived homology comparison for G moves the inverse H^0 identification
through R^nG. Thus applying RG and H^n to the interval inclusion gives the displayed
map, with the inverse single-object comparison for G as its only source factor.
This uses neither an injective resolution comparison nor composite acyclicity.
For n = 0 the same interval inclusion applies; for zero objects or zero functors both
sides are zero. No assumption that G is left exact is used.
-/
theorem grothendieckBottomEdge_singleUnit
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] (X : A) (n : ℕ) :
    (F.grothendieckBottomEdgeSourceIso G n).inv.app X ≫
        (F.grothendieckBottomEdge G n).app X =
      (G.homologyRightDerivedFunctorPlusObjSingleFunctorIso (F.obj X) n).inv ≫
        (DerivedCategory.Plus.homologyFunctor C n).map
          (G.rightDerivedFunctorPlus.map (F.rightDerivedPlusSingleUnit X)) := by sorry

end CategoryTheory
