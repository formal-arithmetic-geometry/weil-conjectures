/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceComparison
import WeilConjectures.AlgebraicGeometry.StrictLocalComplexSectionsMate

/-! # The derived mate on a neighbourhood germ

## References

* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The germ leg and derived mate agree with restriction of stage hypercohomology.
This identity stops before replacing derived restriction by termwise restriction:
that replacement is the separate theorem `injectiveSections_strictLocal_comparison`. -/
theorem strictLocalInjectiveSourceIso_derivedRestriction {X S : Scheme.{v}}
    (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) (Q : StrictLocalNeighbourhoodGeometry f s)
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
    ∀ i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
        ((strictLocalCohomologySourceLegs s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n).app (op i)) ≫
        ((Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictLocalizationToBase s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictLocalizationToBase s)).toCommSq).hom))
                |>.app K))) ≫
        (strictLocalBaseChangeTargetIso f s K n).hom =
            (strictLocalInjectiveSourceIso f s K n J q i).hom ≫
              representativeSectionsComparison
                ((strictLocalNeighbourhoodProjection f s).app i) q n ≫
      (Etale.cohomology AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodDiagram f s).obj i) n).map
        ((Etale.mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
          (Q.legs.app i)).unit.app
            ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app
        i)).mapDerivedCategory.obj
              K.obj)) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
        ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{v + 1} (Q.legs.app i)).hom.app
            ((Etale.upperStar AddCommGrpCat.{v + 1} (Q.legs.app i)).mapDerivedCategory.obj
              ((Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f
        s).app i)).mapDerivedCategory.obj
                K.obj))) ≫
      (Etale.cohomology AddCommGrpCat.{v + 1} (pullback f (Scheme.strictLocalizationToBase
        s)) n).map
        ((Functor.mapDerivedCategoryNatIso
          (Etale.upperStarComp AddCommGrpCat.{v + 1} (Q.legs.app i)
        ((strictLocalNeighbourhoodProjection f s).app i) (pullback.fst f
        (Scheme.strictLocalizationToBase s))
            (Q.over i).symm) ≪≫
          (Functor.mapDerivedCategoryCompIso
            (Etale.upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app i))
            (Etale.upperStar AddCommGrpCat.{v + 1} (Q.legs.app i))).symm).inv.app K.obj) := by
  intro i
  let M : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ :=
    ((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj
  let F := lowerStar AddCommGrpCat.{v + 1} f
  let L : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ :=
    (F.mapHomologicalComplex (.up ℤ)).obj M
  have : F.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f)
  have (k : ℤ) : Injective (L.X k) :=
    F.injective_obj ((InjectiveObject.ι _).obj (J.obj.X k))
  have : L.IsKInjective := by
    obtain ⟨b, hb⟩ := J.property
    let : J.obj.IsStrictlyGE b := hb
    have : L.IsStrictlyGE b := by dsimp [L, M]; infer_instance
    exact CochainComplex.isKInjective_of_injective L b
  let r := sourceInjectiveDirectImageIso f K J q
  rw [sourceLocalizedSectionsIso_germ s _ L r n i]
  simp only [Category.assoc]
  have hm := strictLocalComplexSectionRestriction_mate f s K n Q J q i
  erw [hm]
  have h := (injectiveSections_strictLocal_comparison f s K n Q J q).2.2 i
  rw [h]
  delta sourceLocalizedSectionsIso strictLocalInjectiveSourceIso
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rfl

end AlgebraicGeometry.Etale
