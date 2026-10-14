/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.CategoryTheory.Abelian.DerivedBottomComparison
import Sheaf.CategoryTheory.RightDerivedSingleUnitHomologyComparison

/-! # Canonical-cycle normalization of the specified bottom comparison

Source: Stacks Project, Tags 05TC, 08D4 and 0AVW.
(blueprint: new-lem-pc-derived-bottom-unit-normalization-formula).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uC vC uD vD wC wD
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
/-- The normalization calculation for the specified double-truncation comparison,
using only the canonical cycle kernel and homology quotient.

Source: Stacks Project, Tag 05TC (2), and the degree-zero comparison used in
Tags 08D4 and 0AVW.
(blueprint: new-lem-pc-derived-bottom-unit-normalization-formula).

Proof: Model the lower truncation by the smart truncation of K. Its term in
bottom degree is the quotient of K's term by boundaries, and the kernel of
its outgoing differential is H^n(K). The upper truncation of this lower
truncation is therefore the single object H^n(K) in degree n. Under this
identification, the map from cycles of K is its homology quotient. Apply S
and use naturality of the actual derived unit for the smart truncation and
for the inclusion of the double truncation. In the explicit comparison,
the inverse of the upper-truncation map cancels this inclusion; the
double-truncation map identifies its cycle class with H^n(K). Shift the
single object to degree zero. Compatibility of the single-object comparison
with the derived unit identifies the resulting map with toRightDerivedZero.
The final rightDerivedZeroIsoSelf is its inverse, so their composite is the
identity. The homology shift and single shift identifications on the two
sides are the same and cancel. Finally use bounded-below/unbounded derived
compatibility, which intertwines the actual units, and the inverse homology
of the lower-truncation projection. This gives S applied to the canonical
cycle quotient and localization/homology comparison, as displayed. This
calculation fixes the comparison by its explicit construction and makes no
claim about an arbitrary witness of a Nonempty isomorphism statement. -/
theorem normalized_bottom_unit_formula
    {C : Type uC} [Category.{vC} C] [Abelian C]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    [HasDerivedCategory.{wC} C]
    {D : Type uD} [Category.{vD} D] [Abelian D]
    [HasDerivedCategory.{wD} D]
    (S : C ⥤ D) [S.Additive] [PreservesFiniteLimits S] (n : ℤ)
    (K : CochainComplex C ℤ) :
    ((((S.mapHomologicalComplex (.up ℤ)).obj K).sc n).liftCycles
        (S.map (K.sc n).iCycles) (by
          change S.map (K.sc n).iCycles ≫ S.map (K.sc n).g = 0
          rw [← S.map_comp, (K.sc n).iCycles_g, S.map_zero])) ≫
      (((S.mapHomologicalComplex (.up ℤ)).obj K).sc n).homologyπ ≫
          ((DerivedCategory.homologyFunctorFactors D n).app
            ((S.mapHomologicalComplex (.up ℤ)).obj K)).inv ≫
          (DerivedCategory.homologyFunctor D n).map
            (S.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj K)) ≫
          (DerivedCategory.homologyFunctor D n).map
            (S.rightDerivedFunctor.map
              ((DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj K))) ≫
          (S.rightDerivedFunctorTruncatedBottomIso n).hom.app
            (DerivedCategory.Q.obj K) =
        S.map ((K.sc n).homologyπ ≫
          ((DerivedCategory.homologyFunctorFactors C n).app K).inv) := by sorry
end CategoryTheory.Functor
