/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictLocalLocalizedHomGerm
import WeilConjectures.AlgebraicGeometry.StrictLocalDerivedMateSectionsFactorization

/-! # The derived mate on the complex of neighbourhood sections

## References

* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

-- Comparing the composed section functors across localization requires extra defeq work.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The derived mate, on restricted sections of the direct-image representative,
is the canonical comparison of termwise restriction to fibre hypercohomology.
This statement starts with cohomology of the complex of sections on S: it contains
neither localized Hom classes nor their canonical germ map. -/
theorem strictLocalComplexSectionRestriction_mate {X S : Scheme.{v}}
    (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) (Q : StrictLocalNeighbourhoodGeometry f s)
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
    ∀ i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
    let M := ((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj
    let L := ((lowerStar AddCommGrpCat.{v + 1} f).mapHomologicalComplex (.up ℤ)).obj M
    strictLocalComplexSectionRestriction s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) L
      (sourceInjectiveDirectImageIso f K J q) n i ≫
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
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n).map
      ((NatIso.mapHomologicalComplex (sourceStageSectionsIso f s i) (.up ℤ)).hom.app M) ≫
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} n).inv.app _ ≫
    termwiseSectionsRestriction (Q.legs.app i)
      ((strictLocalNeighbourhoodProjection f s).app i)
      (pullback.fst f (Scheme.strictLocalizationToBase s)) (Q.over i).symm M n ≫
    representativeSectionsComparison
      (pullback.fst f (Scheme.strictLocalizationToBase s)) q n := by
  intro i
  dsimp only
  rw [strictLocalComplexSectionRestriction_derivedMate f s K n J q i]
  let M := ((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj
  let a := (NatIso.mapHomologicalComplex (sourceStageSectionsIso f s i)
    (.up ℤ)).hom.app M
  let b := (NatTrans.mapHomologicalComplex (sectionsPullbackNat (Q.legs.app i))
      (.up ℤ)).app
      (((upperStar AddCommGrpCat.{v + 1}
        ((strictLocalNeighbourhoodProjection f s).app i)).mapHomologicalComplex
          (.up ℤ)).obj M) ≫
    ((Sheaf.Γ (pullback f (Scheme.strictLocalizationToBase s)).smallEtaleTopology
      AddCommGrpCat.{v + 1}).mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (Q.legs.app i)
            ((strictLocalNeighbourhoodProjection f s).app i)
            (pullback.fst f (Scheme.strictLocalizationToBase s)) (Q.over i).symm)
          (.up ℤ)).inv.app M)
  have hb : (NatTrans.mapHomologicalComplex (strictLocalUnderivedMateSections f s i)
      (.up ℤ)).app M = a ≫ b := by
    rw [strictLocalUnderivedMateSections_eq f s Q i]
    ext k
    simp [a, b]
  rw [hb, Functor.map_comp, Category.assoc]
  have hn :=
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} n).inv.naturality b
  change _ ≫ _ = _ ≫ _ at hn
  dsimp only [Functor.comp_map] at hn
  simpa only [a, b, M, termwiseSectionsRestriction, Category.assoc] using!
    congrArg (fun t ↦
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n).map a ≫
        t ≫ representativeSectionsComparison
          (pullback.fst f (Scheme.strictLocalizationToBase s)) q n) hn

end AlgebraicGeometry.Etale
