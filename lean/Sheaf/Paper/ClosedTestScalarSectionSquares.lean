/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.ClosedTestScalarModelDiagrams

/-! # Scalar squares for actual sections, derived restriction and direct-image evaluation
Source: Stacks Tags 07A6, 070Y and 0D6F
(blueprint: lem-sfb-closed-test-scalar-section-squares). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ClosedTestScalarModelCoherence
open ClosedTestKInjectiveSectionModels
open ClosedTestDerivedExchangeModel (restrict restrictPush scalarUnit adj pullComp)
variable {Λ S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj S] [IsCommMonObj S]
  (c : Λ ⟶ S) [IsMonHom c]


/-- The three section squares, with the universal comparisons in their forward direction.
Source: Stacks sites-cohomology.tex Tags 07A6, 0D6F and 0FPI; derived.tex Tag 070Y
(blueprint: lem-sfb-closed-test-scalar-section-squares).
Proof: the coefficient square commutes by naturality of pullback from the point.
The internal/section equivalence preserves restriction, sections and the adjunction.
On underlying sections, restriction preserves the actual unit section and presheaf
restriction, so the first equation holds sectionwise. Apply rightDerivedPullback
composition to this ordinary equation, using its universal computation-unit
normalization, to get the second equation. For the third, the two composites are
induced by the literal identity (b_* F)(W) = F(b^*W). Their computation-unit
normalizations agree on every complex, so uniqueness of the total right derived
functor identifies them. No scalar comparison is inverted. -/
theorem closed_test_scalar_section_squares :
(∀ {X Y : Scheme.{u}} (b : X ⟶ Y) (W : Y.ProEt) (W' : X.ProEt)
      (t : W' ⟶ testFibre b W)
      (F : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj S Y)),
    (sectionArrow S b W W' t).app F ≫
        (evaluation Λ W').map ((CondensedRing.comapUpperStarIso c b).hom.app F) =
      (sectionArrow Λ b W W' t).app ((restriction c Y).obj F)) ∧
  (∀ {X Y : Scheme.{u}} (b : X ⟶ Y) (W : Y.ProEt) (W' : X.ProEt)
      (t : W' ⟶ testFibre b W)
      (N : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj S Y))),
    (derivedSectionArrow S b W W' t).app N ≫
        (gamma c W').app ((CondensedRing.upperStar S b).mapDerivedCategory.obj N) ≫
        (evaluation Λ W').rightDerivedFunctor.map
          ((CondensedRing.derivedComapUpperStarIso c b).hom.app N) =
      (gamma c W).app N ≫
        (derivedSectionArrow Λ b W W' t).app ((restrict c Y).obj N)) ∧
  (∀ {X Y : Scheme.{u}} (b : X ⟶ Y) (W : Y.ProEt)
      (N : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X))),
    (derivedPushEvaluation S b W).hom.app N ≫ (gamma c (testFibre b W)).app N =
      (gamma c W).app ((CondensedRing.moduleObjectDerivedPushforward S b).obj N) ≫
        (evaluation Λ W).rightDerivedFunctor.map ((restrictPush c b).app N) ≫
        (derivedPushEvaluation Λ b W).hom.app ((restrict c X).obj N)) := by sorry

end AlgebraicGeometry.ProEtale.ClosedTestScalarModelCoherence
