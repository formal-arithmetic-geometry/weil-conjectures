/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Sheaf.AlgebraicGeometry.LerayBounded

import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful

/-!
# Restriction and Leray for an open immersion

Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary`, node
`lem-kun-open-immersion-restriction`; Stacks Project, Tags 08BJ, 070K, 070Y and 070I
(blueprint: lem-kun-open-immersion-restriction).

The canonical unbounded Leray map is the hom component of
`rightDerivedLowerStarCompRightDerivedGlobalSectionsIso`. The final equality says that
its restriction to the bounded-below derived category is the inverse of
`rightDerivedGlobalSectionsLerayPlus`, under `rightDerivedFunctorPlusCompatibility`.
-/

@[expose] public section

universe u

open CategoryTheory

private theorem derived_plus_unit_compatibility
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (K : HomotopyCategory.Plus C) :
    DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K) ≫
        F.rightDerivedFunctorPlusCompatibility.hom.app (DerivedCategory.Plus.Qh.obj K) =
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.Plus.ι C).obj K) := by
  simpa only [Functor.rightDerivedFunctorPlusιUnit, Functor.ιRightDerivedFunctorUnit,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] using
    NatTrans.congr_app (by
      simp [Functor.rightDerivedFunctorPlusCompatibility] :
      F.rightDerivedFunctorPlusιUnit ≫ Functor.whiskerLeft DerivedCategory.Plus.Qh
        F.rightDerivedFunctorPlusCompatibility.hom = F.ιRightDerivedFunctorUnit) K

private theorem derived_comp_plus_compatibility
    {C D T : Type*} [Category C] [Category D] [Category T]
    [Abelian C] [Abelian D] [Abelian T]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory T]
    [EnoughInjectives C] [EnoughInjectives D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ T) (H : C ⥤ T)
    [F.Additive] [G.Additive] [H.Additive]
    [F.PreservesInjectiveObjects] [F.PreservesKInjectiveComplexes]
    (e : F ⋙ G ≅ H) :
    Functor.whiskerRight (Functor.rightDerivedFunctorPlusCompIso' F G e).hom
        DerivedCategory.Plus.ι ≫ H.rightDerivedFunctorPlusCompatibility.hom =
      Functor.whiskerLeft F.rightDerivedFunctorPlus G.rightDerivedFunctorPlusCompatibility.hom ≫
        Functor.whiskerRight F.rightDerivedFunctorPlusCompatibility.hom G.rightDerivedFunctor ≫
        Functor.whiskerLeft DerivedCategory.Plus.ι
          (Functor.rightDerivedFunctorCompIso' F G e).hom := by
  apply (cancel_epi (Functor.isoWhiskerRight
    (Functor.rightDerivedFunctorPlusCompIso F G) DerivedCategory.Plus.ι).hom).1
  apply Functor.rightDerived_ext
    ((F ⋙ G).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
    (F ⋙ G).rightDerivedFunctorPlusιUnit (HomotopyCategory.Plus.quasiIso C)
  ext K : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.isoWhiskerRight_hom]
  change DerivedCategory.Plus.ι.map ((F ⋙ G).rightDerivedFunctorPlusUnit.app K) ≫ _ = _
  rw [← Category.assoc, ← Functor.map_comp,
    Functor.rightDerivedFunctorPlusCompIso_fac_app]
  have hp := NatTrans.congr_app (Functor.rightDerivedFunctorPlusCompIso'_fac F G e) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hp
  rw [← Category.assoc, ← Functor.map_comp, hp, Functor.map_comp, Category.assoc,
    derived_plus_unit_compatibility H K]
  change _ = DerivedCategory.Plus.ι.map
    ((F ⋙ G).rightDerivedFunctorPlusUnit.app K) ≫ _
  rw [← Category.assoc, ← Functor.map_comp,
    Functor.rightDerivedFunctorPlusCompIso_fac_app,
    Functor.rightDerivedFunctorPlusCompUnit_app, Functor.map_comp, Category.assoc]
  have hn := G.rightDerivedFunctorPlusCompatibility.hom.naturality
    (F.rightDerivedFunctorPlusUnit.app K)
  simp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  erw [← Functor.map_comp_assoc, derived_plus_unit_compatibility F K]
  rw [reassoc_of% (derived_plus_unit_compatibility G (F.mapHomotopyCategoryPlus.obj K))]
  have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app
      ((HomotopyCategory.Plus.ι C).obj K) = 𝟙 _ := by
    simpa only [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] using
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv_hom_id_app
        ((HomotopyCategory.Plus.ι C).obj K)
  have hu : (Functor.rightDerivedFunctorCompUnit F G).app
      ((HomotopyCategory.Plus.ι C).obj K) =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj K.obj) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K.obj) := by
    simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, hi,
      Category.id_comp, Category.comp_id]
    erw [DerivedCategory.Qh.map_id, Category.id_comp]
    rfl
  erw [reassoc_of% hu.symm]
  have hf : Functor.rightDerivedFunctorCompUnit F G ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (Functor.rightDerivedFunctorCompIso' F G e).hom =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (.up ℤ))
          DerivedCategory.Qh ≫ H.rightDerivedFunctorUnit := by
    have hcomp : (F ⋙ G).rightDerivedFunctorUnit ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (Functor.rightDerivedFunctorCompIso F G).hom =
        Functor.rightDerivedFunctorCompUnit F G := by
      simp [Functor.rightDerivedFunctorCompIso]
    rw [← hcomp, Category.assoc, ← Functor.whiskerLeft_comp]
    simp only [Functor.rightDerivedFunctorCompIso', Iso.trans_hom, Iso.symm_hom,
      Iso.hom_inv_id_assoc]
    exact Functor.rightDerivedNatTrans_fac _ _ _ _
      (HomotopyCategory.quasiIso C (.up ℤ)) _
  have hf' := NatTrans.congr_app hf K.obj
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hf'
  erw [hf']
  congr 1

namespace AlgebraicGeometry.Etale

/-- The counit of inverse image followed by direct image along an open immersion is a
natural isomorphism. The canonical Leray map is invertible for every unbounded derived
abelian sheaf, and restricts to the inverse of the bounded-below Leray isomorphism.
Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary`, node
`lem-kun-open-immersion-restriction`; Stacks Project, Tags 08BJ, 070K, 070Y and 070I
(blueprint: lem-kun-open-immersion-restriction).

Proof:
1. The direct image is fully faithful by
   `lem-sc-open-immersion-pushforward-fully-faithful`, so the adjunction counit is invertible.
2. The unbounded Leray morphism is the hom component of the existing natural composition
   isomorphism `rightDerivedLowerStarCompRightDerivedGlobalSectionsIso`.
3. The bounded and unbounded composition isomorphisms are defined by uniqueness of right
   derived functors. Precompose the desired natural-transformation identity with the bounded
   composition isomorphism and apply the universal property of the derived functor of
   `lowerStar ⋙ Γ`. Its defining unit identities reduce the two composites to the same map:
   the homotopy-category image of `lowerStarCompGlobalSectionsIso.hom` followed by the
   unbounded sections unit. Naturality of the bounded/unbounded compatibility moves it past
   the bounded direct-image unit. The compatibility itself intertwines the bounded and
   unbounded units by its defining uniqueness property. This proves the identity on all
   bounded-below derived objects, including precisely the inverse of the canonical bounded
   Leray isomorphism defined in `lem-kun-leray-bdd`. -/
theorem openImmersion_restriction_leray {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    IsIso (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).counit ∧
    (∀ F : DerivedCategory (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}),
      IsIso ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        AddCommGrpCat.{u + 1} j).hom.app F)) ∧
    (∀ E : DerivedCategory.Plus (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}),
      DerivedCategory.Plus.ι.map (rightDerivedGlobalSectionsLerayPlus j E).inv ≫
          (Sheaf.Γ U.smallEtaleTopology
            AddCommGrpCat.{u + 1}).rightDerivedFunctorPlusCompatibility.hom.app E =
        (Sheaf.Γ X.smallEtaleTopology
          AddCommGrpCat.{u + 1}).rightDerivedFunctorPlusCompatibility.hom.app
              ((lowerStar AddCommGrpCat.{u + 1} j).rightDerivedFunctorPlus.obj E) ≫
          (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
            ((lowerStar AddCommGrpCat.{u + 1} j).rightDerivedFunctorPlusCompatibility.hom.app E) ≫
          (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
            AddCommGrpCat.{u + 1} j).hom.app (DerivedCategory.Plus.ι.obj E)) := by
  refine ⟨?_, (fun F ↦ inferInstance), ?_⟩
  · infer_instance
  · intro E
    have : (lowerStar AddCommGrpCat.{u + 1} j).PreservesInjectiveObjects :=
      Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
        (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j)
    exact NatTrans.congr_app
      (derived_comp_plus_compatibility (lowerStar AddCommGrpCat.{u + 1} j)
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1})
        (Sheaf.Γ U.smallEtaleTopology AddCommGrpCat.{u + 1})
        (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} j)) E

end AlgebraicGeometry.Etale
