/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.RestrictedDerivedEvaluationPullback

/-! # Pullback of the represented identity section

Source: Stacks Project, Tag 03Q8 and Cohomology on Sites, Tag 0BKV.
(blueprint: lem-sbc-restricted-comparison-generator-pullback).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale.RawRestrictedComparison

/-- Pullback transports the represented identity generator in zeroth derived sections.
This has no degree p, target coefficient sheaf, or raw derived-Hom class.
Source: Stacks Project, Tag 03Q8; Cohomology on Sites, Tag 0BKV.
(blueprint: lem-sbc-restricted-comparison-generator-pullback).

Proof: Write A = the sheafification of the free abelian presheaf represented by U,
G = h^* A and G' = h'^* A. Cancel the zeroIso at the source of transportZero
against its inverse. The remaining input is generator h U, namely the identity
section of A at U, mapped by the unit for h, then by sectionsIso inverse.
Write q = U times_S a, r = pr_Y and r' = pr_Y'. The pullback projection equations
give r' followed by a equals q followed by r. Expanding the restricted coefficient
map with the inverse-image composition comparisons identifies the two restrictions
of A along these equal morphisms. Naturality of the inverse-image adjunction unit,
and its composition formula, show that pulling the unit for h across q and applying
the comparison for a followed by h gives exactly the unit for h'. The terminal
object comparisons in globalSectionsUpperStarMap and sectionsIso agree: both send
the identity etale object of V' to the base change of U. Thus the resulting section
is generator h' U. Postcompose with zeroIso inverse for G' to obtain the stated
identity. This uses no higher derived morphism and no invertibility of the section
pullback. Identity maps, degree-zero sections, and empty schemes obey the same unit
and terminal-object equations. -/
theorem restrictedComparison_generator_pullback {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (U : S.Etale) :
    transportZero a h h' w
      ((upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U))
      ((upperStar AddCommGrpCat.{v + 1} h').obj (freeSheaf S U))
      ((upperStarComp AddCommGrpCat.{v + 1} a h h' w.symm).inv.app (freeSheaf S U)) U
      ((zeroIso ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)
        ((upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U))).inv (generator h U)) =
    (zeroIso ((MorphismProperty.Over.pullback @Etale ⊤ h').obj U)
      ((upperStar AddCommGrpCat.{v + 1} h').obj (freeSheaf S U))).inv (generator h' U) := by
  sorry

end AlgebraicGeometry.Etale.RawRestrictedComparison
