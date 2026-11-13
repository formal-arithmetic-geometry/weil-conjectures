/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonEvaluationIsIso

/-! # Natural abelian higher-image comparison

Source: Stacks Project, Tag 03Q8.
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Etale

attribute [local instance] RawRestrictedComparison.etaleComposition
  RawRestrictedComparison.etaleIdentities RawRestrictedComparison.etalePullbacks
  RawRestrictedComparison.etaleBaseChange RawRestrictedComparison.sheafifyInstance
  RawRestrictedComparison.weakSheafifyInstance

/-- Evaluation of raw derived Hom is naturally isomorphic, in the coefficient
sheaf, to cohomology restricted to an etale pullback. No qcqs or continuity
hypothesis is used (Stacks, Tags 03Q8, 072W and 0BKV). -/
theorem nonempty_abelianHigherDirectImage_evaluationFunctorIso
    {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℕ) (U : X.Etale) :
    Nonempty
      ((DerivedCategory.Plus.singleFunctor
          (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        shiftFunctor _ (q : ℤ) ⋙ preadditiveYoneda ⋙
        (Functor.whiskeringLeft _ _ _).obj
          (uliftYoneda.{u + 1} ⋙
            (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
            presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
            upperStar AddCommGrpCat.{u + 1} h ⋙
            DerivedCategory.Plus.singleFunctor _ 0).op) ⋙ (evaluation _ _).obj (Opposite.op U) ≅
      upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom h) ⋙
        DerivedCategory.singleFunctor
          (Sheaf (pullback U.hom h).smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        cohomology AddCommGrpCat.{u + 1} (pullback U.hom h) (q : ℤ))  := by
  let W := (MorphismProperty.Over.pullback @Etale ⊤ h).obj U
  let A := (upperStar AddCommGrpCat.{u + 1} h).obj
    (RawRestrictedComparison.freeSheaf X U)
  let x := (RawRestrictedComparison.zeroIso W A).inv
    (RawRestrictedComparison.generator h U)
  let T := RawRestrictedComparison.sectionsFunctor W ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0
  let S := DerivedCategory.Plus.singleFunctor
    (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0
  let E := S ⋙ shiftFunctor _ (q : ℤ)
  let P := S ⋙ shiftFunctor _ (q : ℤ) ⋙ preadditiveYoneda ⋙
    (Functor.whiskeringLeft _ _ _).obj
      (uliftYoneda.{u + 1} ⋙
        (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
        presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        upperStar AddCommGrpCat.{u + 1} h ⋙
        DerivedCategory.Plus.singleFunctor _ 0).op
  let e : P ⋙ (evaluation _ _).obj (Opposite.op U) ≅ E ⋙ T :=
    NatIso.ofComponents (fun F ↦ by
      have hi := isIso_rawRestrictedCohomologyComparisonEvaluation h q F U
      exact @asIso _ _ _ _ (RawRestrictedComparison.Evaluation.evaluate T x) hi) (by
        intro F F' f
        ext z
        change T.map (z ≫ E.map f) x = T.map (E.map f) (T.map z x)
        rw [T.map_comp]
        rfl)
  let L := upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom h)
  let R := (Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctor
  let H₀ := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0
  let Hq := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)
  let D := RawRestrictedComparison.sectionsFunctor W
  let τ : shiftFunctor _ (q : ℤ) ⋙ D ⋙ H₀ ≅ D ⋙ Hq :=
    Functor.isoWhiskerRight (D.commShiftIso (q : ℤ)) H₀ ≪≫
      Functor.isoWhiskerLeft D (H₀.shiftIso (q : ℤ) 0 (q : ℤ) (add_zero _))
  let δ : S ⋙ D ≅ L ⋙ DerivedCategory.singleFunctor _ 0 ⋙ R :=
    (Functor.associator S DerivedCategory.Plus.ι (L.mapDerivedCategory ⋙ R)).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.Plus.singleFunctorιIso _ 0)
        (L.mapDerivedCategory ⋙ R) ≪≫
      (Functor.associator (DerivedCategory.singleFunctor _ 0) L.mapDerivedCategory R).symm ≪≫
      Functor.isoWhiskerRight (L.mapDerivedCategorySingleFunctor 0) R ≪≫
      Functor.associator L (DerivedCategory.singleFunctor _ 0) R
  exact ⟨e ≪≫ Functor.isoWhiskerLeft S τ ≪≫ Functor.isoWhiskerRight δ Hq⟩

end AlgebraicGeometry.Etale
