/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.MateProjectionData
public import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalInjectiveSourceComparison
public import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry.NeighbourhoodGeometry
import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalComplexSectionsMate
import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalLocalizedHomGerm

/-! # Computing source derived sections on an injective representative

Source: Stacks Project, Tags 03Q8 and 03Q9, final injective-complex paragraph.
-/

/- This original-model counterpart follows the proved calculation in
WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceRestriction.
The spectrum and structure morphism are those of the small coordinate-ring colimit. -/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The canonical cycle comparison identifies the strict-local derived mate with
restriction along the fixed geometric cone leg.
Source: Stacks Project, Tag 03Q9, final injective-complex paragraph; Tag 03Q8. -/
theorem smallModel_strictLocalInjectiveSourceIso_restriction {X S : Scheme.{v}}
    (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) (Q : StrictLocalNeighbourhoodGeometry f s)
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
    ∀ i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
        ((smallModel_strictLocalCohomologySourceLegs s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n).app (op i)) ≫
        ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom))
                |>.app K))) =
            (smallModel_strictLocalInjectiveSourceIso f s K n J q i).hom ≫
              termwiseSectionsRestriction (Q.smallModelLegs.app i)
                ((strictLocalNeighbourhoodProjection f s).app i)
                (pullback.fst f (Scheme.strictHenselizationStructuralMap s))
                (Q.smallModelOver i).symm
                (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj) n ≫
              representativeSectionsComparison
                (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) q n ≫
              (smallModel_strictLocalBaseChangeTargetIso f s K n).inv := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
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
    intro i
    apply (cancel_mono (smallModel_strictLocalBaseChangeTargetIso f s K n).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    let r := smallModel_sourceInjectiveDirectImageIso f K J q
    rw [smallModel_sourceLocalizedSectionsIso_germ s _ L r n i]
    simp only [Category.assoc]
    erw [smallModel_strictLocalComplexSectionRestriction_mate f s K n Q J q i]
    delta smallModel_sourceLocalizedSectionsIso smallModel_strictLocalInjectiveSourceIso
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
    rfl

end AlgebraicGeometry.Etale
