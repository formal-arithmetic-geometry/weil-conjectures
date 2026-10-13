/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.AlgebraicGeometry.RestrictedDerivedSectionZeroComparison

/-! # Unshifted single comparison before restricted section homology

Source: Stacks Project, Tags 07A6 and 0D6F.
(blueprint: lem-sbc-restricted-derived-sections-single).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale.RawRestrictedComparison

/-- On unshifted singles, the restriction and single comparisons give the explicit
complex pullback and coefficient map, before applying any homology functor.
Source: Stacks Project, Tags 07A6, 0D6F and 03Q8.
(blueprint: lem-sbc-restricted-derived-sections-single).

Proof: Expand the transformation as the derived unit and Leray, followed by the
restriction-composition isomorphism. Move the source single comparison past the
unit and Leray using naturality. On the actual single complex, factorization of
exact inverse image through Q identifies the resulting map with the derived
unit and Leray followed by mapDerivedCategoryFactors. The restriction comparison
on the single is Q of mapCochainComplexSingleFunctor followed by the single of
upperStarComp(q,r) inverse and upperStarComp(r',a). Its naturality for the arbitrary
coefficient map supplies the last factor r'^* phi. Compose and cancel the single
comparison inverses. No coefficient is assumed invertible; the zero sheaf and
empty scheme give the same identities. No shift or homology comparison is used. -/
theorem restrictedDerivedSections_single {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : (upperStar AddCommGrpCat.{v + 1} a).obj F ⟶ F') (U : S.Etale) :
    let q := rawAffineRestrictedMap a h h' w U
    let r := Limits.pullback.snd U.hom h
    let r' := Limits.pullback.snd U.hom h'
    let R := (upperStar AddCommGrpCat.{v + 1} r).obj F
    let τ := Functor.whiskerLeft
      (DerivedCategory.Plus.ι ⋙
        D(upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h)))
      (derivedSectionPullback (rawAffineRestrictedMap a h h' w U)) ≫
    Functor.whiskerRight
      (Functor.whiskerLeft DerivedCategory.Plus.ι
        (derivedRestrictionIso a h h' w U).hom)
      (rightDerivedGlobalSections AddCommGrpCat.{v + 1} (Limits.pullback U.hom h'))
    τ.app ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      (sectionsFunctor ((MorphismProperty.Over.pullback @Etale ⊤ h').obj U)).map
        (((upperStar AddCommGrpCat.{v + 1} a).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
          (DerivedCategory.Plus.singleFunctor _ 0).map φ) ≫
      (Evaluation.singleIso (upperStar AddCommGrpCat.{v + 1} r')
        (Sheaf.Γ (Limits.pullback U.hom h').smallEtaleTopology AddCommGrpCat.{v + 1}) F').hom =
    (Evaluation.singleIso (upperStar AddCommGrpCat.{v + 1} r)
      (Sheaf.Γ (Limits.pullback U.hom h).smallEtaleTopology AddCommGrpCat.{v + 1}) F).hom ≫
      (derivedSectionPullback q).app
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj R)) ≫
      (rightDerivedGlobalSections AddCommGrpCat.{v + 1} (Limits.pullback U.hom h')).map
        ((upperStar AddCommGrpCat.{v + 1} q).mapDerivedCategoryFactors.hom.app
            ((CochainComplex.singleFunctor _ 0).obj R) ≫
          DerivedCategory.Q.map
            (((upperStar AddCommGrpCat.{v + 1} q).mapCochainComplexSingleFunctor 0).hom.app R ≫
              (CochainComplex.singleFunctor _ 0).map
                (rawAffineRestrictedCoefficient a h h' w F F' φ U))) := by sorry

end AlgebraicGeometry.Etale.RawRestrictedComparison
