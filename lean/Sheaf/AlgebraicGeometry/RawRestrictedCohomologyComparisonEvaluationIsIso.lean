/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap

/-! # Evaluation part of the raw restricted comparison

(blueprint: lem-sbc-raw-restricted-cohomology-comparison-evaluation-is-iso).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The evaluation at the represented identity is invertible before the explicit
shift identification.  This is the derived Yoneda and sections calculation.
Source: Stacks Project, Tag 03Q8 and Cohomology on Sites, Tags 072W, 0BKV and 0D6F.
(blueprint: lem-sbc-raw-restricted-cohomology-comparison-evaluation-is-iso).

Proof: choose a bounded-below injective resolution of `F`.  Restriction to the
etale pullback preserves injectives by exact extension by zero.  The derived
localization bijection identifies morphisms from the free represented sheaf
with homotopy classes of maps into that resolution, while the sheafification,
free-abelian Yoneda and sections adjunction identifies those classes with
cohomology classes of the restricted sections complex.  Evaluation at the
represented identity is exactly this identification, including degree zero and
the empty pullback.
-/
theorem isIso_rawRestrictedCohomologyComparisonEvaluation {S Y : Scheme.{v}}
    (h : Y ⟶ S) (p : ℕ) (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (U : S.Etale) :
    IsIso (let W := (MorphismProperty.Over.pullback @Etale ⊤ h).obj U
      let A := (upperStar AddCommGrpCat.{v + 1} h).obj
        (RawRestrictedComparison.freeSheaf S U)
      let x := (RawRestrictedComparison.zeroIso W A).inv
        (RawRestrictedComparison.generator h U)
      let T := RawRestrictedComparison.sectionsFunctor W ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0
      RawRestrictedComparison.Evaluation.evaluate T x :
        AddCommGrpCat.of
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
                ((upperStar AddCommGrpCat.{v + 1} h).obj
                  (RawRestrictedComparison.freeSheaf S U)) ⟶
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(p : ℤ)⟧) ⟶
          (RawRestrictedComparison.sectionsFunctor
            ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U) ⋙
            DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).obj
            (((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(p : ℤ)⟧)) := by
  sorry

end AlgebraicGeometry.Etale
