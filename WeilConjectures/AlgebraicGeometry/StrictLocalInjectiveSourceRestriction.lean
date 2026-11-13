/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceComparison
import WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceDerivedRestriction

/-! # Computing source derived sections on an injective representative

## References

* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The canonical cycle comparison identifies the strict-local derived mate with
restriction along the fixed geometric cone leg. -/
theorem strictLocalInjectiveSourceIso_restriction {X S : Scheme.{v}}
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
                |>.app K))) =
            (strictLocalInjectiveSourceIso f s K n J q i).hom ≫
              termwiseSectionsRestriction (Q.legs.app i)
                ((strictLocalNeighbourhoodProjection f s).app i)
                (pullback.fst f (Scheme.strictLocalizationToBase s))
                (Q.over i).symm
                (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj) n ≫
              representativeSectionsComparison
                (pullback.fst f (Scheme.strictLocalizationToBase s)) q n ≫
              (strictLocalBaseChangeTargetIso f s K n).inv := by
  intro i
  apply (cancel_mono (strictLocalBaseChangeTargetIso f s K n).hom).1
  rw [Category.assoc]
  rw [strictLocalInjectiveSourceIso_derivedRestriction f s K n Q J q i]
  have h := (injectiveSections_strictLocal_comparison f s K n Q J q).2.2 i
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    congrArg (fun a ↦ (strictLocalInjectiveSourceIso f s K n J q i).hom ≫ a) h

end AlgebraicGeometry.Etale
