/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ComparisonDirectImageCanonicalMate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# ProEtaleDirectImageMateCompatibility

Source: blueprint direct-image comparison, Stacks Tags 09A6 and 0B65.
(blueprint: lem-pe-direct-image-mate-compatibility).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
section

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory C'] [HasDerivedCategory D']
  [EnoughInjectives D] [EnoughInjectives D']
  {l : C ⥤ D} {r : D ⥤ C} {p : C' ⥤ D'} {t : D' ⥤ C'}
  {a : C ⥤ C'} {b : D ⥤ D'}
  [l.Additive] [r.Additive] [p.Additive] [t.Additive] [a.Additive] [b.Additive]
  [PreservesFiniteLimits l] [PreservesFiniteColimits l]
  [PreservesFiniteLimits p] [PreservesFiniteColimits p]
  [PreservesFiniteLimits a] [PreservesFiniteColimits a]
  [PreservesFiniteLimits b] [PreservesFiniteColimits b]

private theorem derived_mate_eq (e : l ⊣ r) (d : p ⊣ t) (σ : a ⋙ p ≅ l ⋙ b) :
    let θ := (Functor.mapDerivedCategoryPlusCompIso a p).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso σ ≪≫ Functor.mapDerivedCategoryPlusCompIso l b
    Functor.rightDerivedFunctorPlusBaseChange (mateEquiv e d σ.hom).natTrans =
      (mateEquiv e.derivedPlus d.derivedPlus θ.hom).natTrans := by
  dsimp only
  let θ := (Functor.mapDerivedCategoryPlusCompIso a p).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso σ ≪≫ Functor.mapDerivedCategoryPlusCompIso l b
  have hθ (N : HomotopyCategory.Plus C) :
      θ.hom.app (DerivedCategory.Plus.Qh.obj N) ≫
        D+(b).map (l.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        b.mapDerivedCategoryPlusFactorsh.hom.app (l.mapHomotopyCategoryPlus.obj N) =
      D+(p).map (a.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        p.mapDerivedCategoryPlusFactorsh.hom.app (a.mapHomotopyCategoryPlus.obj N) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus σ.hom).app N) := by
    simp only [θ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
    rw [Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh l b N]
    rw [Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh σ N]
    rw [← Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh a p N]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  apply Functor.rightDerived_ext (R+(r) ⋙ D+(a))
    (Functor.whiskerRight r.rightDerivedFunctorPlusUnit D+(a) ≫
      (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso D)
  apply NatTrans.ext
  funext M
  have hf := congr_app (Functor.rightDerivedFunctorPlusBaseChange_fac
    (mateEquiv e d σ.hom).natTrans) M
  have hm := Adjunction.derivedPlus_mateEquiv_app_fac e d σ.hom θ.hom hθ M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at hf ⊢
  rw [hf, hm]
  simp [Functor.rightDerivedFunctorPlusBaseChangeAux,
    Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app]

end

variable (Λ : Type (u + 1)) [CommRing Λ]

private theorem underived_comparison_counit {U V : Scheme.{u}} (f : U ⟶ V)
    (K : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).inv.app
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj K) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f).map
        ((lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)).app K) ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj K) =
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).map
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app K) := by
  have h := mateEquiv_counit_symm
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)) K
  have hi := iterated_mateEquiv_conjugateEquiv_symm
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) V)
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) U)
    (lowerStarCompComparisonLowerStarIso f (ModuleCat.{u + 1} Λ)).inv
  unfold lowerStarComparisonUpperStarBaseChange at h
  rw [hi] at h
  change _ = (comparisonUpperStarCompUpperStarIso
    (ModuleCat.{u + 1} Λ) f).hom.app _ ≫ _ at h
  simpa only [lowerStarComparisonUpperStarBaseChange, Category.assoc,
    Iso.inv_hom_id_app_assoc] using
    congrArg (fun t ↦ (comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} Λ) f).inv.app ((Etale.lowerStar
        (ModuleCat.{u + 1} Λ) f).obj K) ≫ t) h

private theorem underived_comparison_mate {U V : Scheme.{u}} (f : U ⟶ V) :
    lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ) =
      (mateEquiv (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).hom).natTrans := by
  apply NatTrans.ext
  funext K
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [mateEquiv_counit]
  apply (cancel_epi ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).inv.app
    ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj K))).1
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using
    underived_comparison_counit Λ f K


/-- The canonical comparison square on bounded-below derived categories:
apply the exact functors termwise, then localize the sheaf comparison and its inverse.
Source: blueprint sk-thm-pe-direct-image-comparison, proof steps 2, 3 and 6; Stacks Tag 09A6
(blueprint: sk-thm-pe-direct-image-comparison). -/
noncomputable def directImageComparisonPullbackPlusIso
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategoryPlus ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus ≅
      (Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y)
    (ProEtale.upperStar (ModuleCat.{u + 1} Λ) g)).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g) ≪≫
      Functor.mapDerivedCategoryPlusCompIso
        (Etale.upperStar (ModuleCat.{u + 1} Λ) g)
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X)

/-- The unit and counit equations for the specified derived comparison.
Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-thm-pe-direct-image-comparison/_section.md, proof steps 2, 3 and 6; Stacks Tags 09A6 and 0B65.
(blueprint: lem-pe-direct-image-mate-compatibility).

Proof: Apply Mathlib iterated_mateEquiv_conjugateEquiv_symm to the four ordinary
inverse-image/direct-
image adjunctions. It identifies the mate of the specified pullback comparison with
lowerStarComparisonUpperStarBaseChange. Apply the exact functors termwise to bounded-below
complexes and localize. The composition and natural-isomorphism factorization equations for
mapDerivedCategoryPlus show that directImageComparisonPullbackPlusIso is the localized ordinary
square. Adjunction.derivedPlus_mateEquiv_app_fac computes its derived mate after the unit of the
right-derived etale direct image. The defining factorization of
rightDerivedFunctorPlusBaseChange gives the identical formula for
comparisonDirectImageCanonicalMate. Uniqueness of transformations out of that right-derived
functor identifies these maps. Mathlib unit_mateEquiv and mateEquiv_counit then give the two
displayed equations. The equation derivedAdjunctionPlus_eq_derivedPlus identifies the recorded
adjunctions; no finiteness or qcqs condition is used in this normalization, and zero categories
satisfy the same identities. -/
theorem directImageMateCompatibility
    (Λ : Type u) [CommRing Λ] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (∀ A : DerivedCategory.Plus
          (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))),
        (comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) Y).mapDerivedCategoryPlus.map
            ((Etale.upperStarLowerStarAdjunction
              (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g).derivedAdjunctionPlus.unit.app A) ≫
          (comparisonDirectImageCanonicalMate (ULift.{u + 1, u} Λ) g).app
            ((Etale.upperStar
              (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g).mapDerivedCategoryPlus.obj A) =
        (ProEtale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g).derivedAdjunctionPlus.unit.app
            ((comparisonUpperStar
              (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) Y).mapDerivedCategoryPlus.obj A) ≫
          (ProEtale.lowerStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g).rightDerivedFunctorPlus.map
              ((directImageComparisonPullbackPlusIso (ULift.{u + 1, u} Λ) g).hom.app A)) ∧
    (∀ B : DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))),
        (ProEtale.upperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g).mapDerivedCategoryPlus.map
            ((comparisonDirectImageCanonicalMate (ULift.{u + 1, u} Λ) g).app B) ≫
          (ProEtale.upperStarLowerStarAdjunction
            (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g).derivedAdjunctionPlus.counit.app
              ((comparisonUpperStar
                (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) X).mapDerivedCategoryPlus.obj B) =
        (directImageComparisonPullbackPlusIso (ULift.{u + 1, u} Λ) g).hom.app
          ((Etale.lowerStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g).rightDerivedFunctorPlus.obj B) ≫
          (comparisonUpperStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) X).mapDerivedCategoryPlus.map
              ((Etale.upperStarLowerStarAdjunction
                (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g).derivedAdjunctionPlus.counit.app B))
    := by
  let A := ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)
  have hm : comparisonDirectImageCanonicalMate (ULift.{u + 1, u} Λ) g =
      (mateEquiv (Etale.upperStarLowerStarAdjunction A g).derivedPlus
        (upperStarLowerStarAdjunction A g).derivedPlus
        (directImageComparisonPullbackPlusIso (ULift.{u + 1, u} Λ) g).hom).natTrans := by
    unfold comparisonDirectImageCanonicalMate
    rw [underived_comparison_mate, derived_mate_eq]
    rfl
  rw [hm]
  rw [Adjunction.derivedAdjunctionPlus_eq_derivedPlus,
    Adjunction.derivedAdjunctionPlus_eq_derivedPlus]
  constructor
  · intro K
    exact unit_mateEquiv _ _ _ K
  · intro K
    exact mateEquiv_counit _ _ _ K

end AlgebraicGeometry.ProEtale
