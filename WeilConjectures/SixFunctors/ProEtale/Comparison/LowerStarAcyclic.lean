/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Injective
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs

/-!
# Acyclicity for pro-étale direct images on the affine pro-étale basis

Let `f : U ⟶ V` be a morphism of schemes. A pro-étale sheaf `G` on `U` is acyclic for the
direct image `f_*` as soon as its higher derived sections over the pro-étale `U`-schemes
`U ×_V W` vanish, for `W` running over the affine pro-étale site of `V`
(`AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_of_isZero_rightDerived`): the higher
direct images are computed by `f_*` of an injective resolution, whose complex of sections over
`W` is the complex of sections over `U ×_V W` of the resolution, and exactness of a complex of
sheaves can be tested on the presheaves underlying its restriction to the affine pro-étale site.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- Evaluation of pro-étale sheaves at an object of the pro-étale site. -/
noncomputable abbrev sectionsFunctor {X : Scheme.{u}} (Y : X.ProEt) :
    Sheaf (ProEt.topology X) A ⥤ A :=
  sheafToPresheaf (ProEt.topology X) A ⋙ (evaluation _ A).obj (op Y)

/-- A short complex of pro-étale sheaves is exact if the short complexes of sections over all
objects of the affine pro-étale site are exact. -/
lemma ShortComplex.exact_of_exact_sectionsFunctor {X : Scheme.{u}}
    (S : ShortComplex (Sheaf (ProEt.topology X) A))
    (h : ∀ W : X.AffineProEt,
      (S.map (sectionsFunctor A ((AffineProEt.toProEt X).obj W))).Exact) : S.Exact := by
  have : HasLimitsOfSize.{u, u + 1} A := hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} A
  let Φ := (AffineProEt.toProEt X).sheafPushforwardContinuous A (AffineProEt.topology X)
    (ProEt.topology X)
  have : LocallySmall.{u + 1} X.AffineProEt := ⟨fun _ _ ↦ ⟨ULift.{u + 1} _, ⟨Equiv.ulift.symm⟩⟩⟩
  have : EssentiallySmall.{u + 1} X.AffineProEt := essentiallySmall_of_small_of_locallySmall _
  have : HasSheafify (AffineProEt.topology X) A :=
    GrothendieckTopology.hasSheafify_of_essentiallySmall A _
  have : Abelian (Sheaf (AffineProEt.topology X) A) := sheafIsAbelian
  have : Φ.Additive := ⟨rfl⟩
  have : Φ.PreservesHomology := {}
  rw [← S.exact_map_iff_of_faithful Φ]
  -- the presheaves underlying the restriction to the affine site form an exact short complex
  let T := (S.map Φ).map (sheafToPresheaf (AffineProEt.topology X) A)
  have hT : T.Exact := by
    rw [ShortComplex.exact_iff_evaluation]
    exact fun W ↦ h W.unop
  -- sheafifying it gives back the restriction, sheafification being exact
  have : (presheafToSheaf (AffineProEt.topology X) A).PreservesHomology := {}
  have hT' := hT.map (presheafToSheaf (AffineProEt.topology X) A)
  refine (ShortComplex.exact_iff_of_iso ?_).1 hT'
  exact (ShortComplex.mapNatIso (S.map Φ) (sheafificationNatIso _ _)).symm

/-- A pro-étale sheaf `G` on `U` is acyclic for the direct image along `f : U ⟶ V` if its higher
derived sections over `U ×_V W` vanish for every object `W` of the affine pro-étale site of
`V`. -/
theorem rightAcyclic_lowerStar_of_isZero_rightDerived {U V : Scheme.{u}} (f : U ⟶ V)
    (G : Sheaf (ProEt.topology U) A)
    (h : ∀ (W : V.AffineProEt) (q : ℕ), IsZero (((sectionsFunctor A
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj
        ((AffineProEt.toProEt V).obj W))).rightDerived (q + 1)).obj G)) :
    (ProEtale.lowerStar A f).rightAcyclic G := by
  intro q
  let R : InjectiveResolution G := injectiveResolution G
  refine IsZero.of_iso ?_ (R.isoRightDerivedObj _ (q + 1))
  rw [HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology]
  refine ShortComplex.exact_of_exact_sectionsFunctor A _ fun W ↦ ?_
  have h' := (h W q).of_iso (R.isoRightDerivedObj _ (q + 1)).symm
  rw [HomologicalComplex.homologyFunctor_obj,
    ← HomologicalComplex.exactAt_iff_isZero_homology] at h'
  exact h'

section Acyclicity

/-- Blueprint `prop-weil-pbc-site-comparison-finite-level`: Exactness and full faithfulness at
finite level

*Acyclicity.* For every injective étale sheaf `I` the pro-étale sheaf `ν^* I` is acyclic for
`ν_*`: `R^q ν_* (ν^* I) = 0` for `q > 0`. The other two clauses of the node, exactness of `ν^*`
and invertibility of the unit `F ⟶ ν_* ν^* F`, are
`AlgebraicGeometry.ProEtale.preservesFiniteLimits_comparisonUpperStar`,
`AlgebraicGeometry.ProEtale.preservesFiniteColimits_comparisonUpperStar` and
`AlgebraicGeometry.ProEtale.isIso_comparisonAdjunction_unit`. -/
theorem rightAcyclic_comparisonUpperStar_obj_of_injective (X : Scheme.{u})
    (I : Sheaf X.smallEtaleTopology A)
    [Injective I] : ν_*(X)[A].rightAcyclic (ν^*(X)[A].obj I) :=
  sorry

/-- The global sections functor of the small pro-étale site: the sections over the terminal
object. -/
noncomputable abbrev globalSectionsFunctor (X : Scheme.{u}) :
    Sheaf (ProEt.topology X) A ⥤ A :=
  sectionsFunctor A (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X))

/-- **Derived sections over an object of the pro-étale site.** For `T` an object of the small
pro-étale site of `X`, the derived sections over `T` of a pro-étale sheaf `G` on `X` are the
derived global sections of its pullback to `T`: the pullback is the restriction to the
localization `T_proét` of `X_proét`, which is exact and preserves injectives. -/
lemma isZero_rightDerived_sectionsFunctor_of_upperStar {X : Scheme.{u}} (T : X.ProEt)
    (G : Sheaf (ProEt.topology X) A) (q : ℕ)
    (h : IsZero (((globalSectionsFunctor A T.left).rightDerived q).obj
      ((ProEtale.upperStar A T.hom).obj G))) :
    IsZero (((sectionsFunctor A T).rightDerived q).obj G) := by
  have hT : WeaklyEtale T.hom := T.prop
  let j := ProEtale.localizationRestriction A T.hom hT
  -- `T` is the image of the terminal object of `T_proét` under the localization functor
  let e : T ≅ (MorphismProperty.Over.map ⊤ hT).obj
      (MorphismProperty.Over.mk ⊤ (𝟙 T.left) (MorphismProperty.id_mem _ T.left)) :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by exact Category.id_comp _)
  have : j.Additive := { }
  let eΓ : sectionsFunctor A T ≅ j ⋙ globalSectionsFunctor A T.left :=
    NatIso.ofComponents (fun G ↦ G.obj.mapIso e.op) (fun φ ↦ (φ.hom.naturality e.inv.op).symm)
  let eR : (sectionsFunctor A T).rightDerived q ≅
      (j ⋙ globalSectionsFunctor A T.left).rightDerived q :=
    { hom := NatTrans.rightDerived eΓ.hom q
      inv := NatTrans.rightDerived eΓ.inv q
      hom_inv_id := by rw [← NatTrans.rightDerived_comp, eΓ.hom_inv_id, NatTrans.rightDerived_id]
      inv_hom_id := by rw [← NatTrans.rightDerived_comp, eΓ.inv_hom_id, NatTrans.rightDerived_id] }
  have : PreservesFiniteColimits j :=
    preservesFiniteColimits_of_natIso (ProEtale.upperStarIsoLocalizationRestriction A T.hom hT)
  have : PreservesFiniteLimits j :=
    preservesFiniteLimits_of_natIso (ProEtale.upperStarIsoLocalizationRestriction A T.hom hT)
  refine IsZero.of_iso ?_ (eR.app G ≪≫
    (Functor.rightDerivedCompIsoOfExact j (globalSectionsFunctor A T.left) q).app G)
  exact h.of_iso (((globalSectionsFunctor A T.left).rightDerived q).mapIso
    ((ProEtale.upperStarIsoLocalizationRestriction A T.hom hT).app G).symm)

/-- The comparison pullbacks commute with pullback along any morphism `g : Y ⟶ X`:
`g^* ν_X^* ≅ ν_Y^* g^*`, both being left adjoint to `ν_X_* g_* ≅ g_* ν_Y_*`. -/
noncomputable def comparisonUpperStarCompUpperStarIso {Y X : Scheme.{u}} (g : Y ⟶ X) :
    comparisonUpperStar A X ⋙ ProEtale.upperStar A g ≅
      Etale.upperStar A g ⋙ comparisonUpperStar A Y :=
  (conjugateIsoEquiv ((Etale.upperStarLowerStarAdjunction A g).comp (comparisonAdjunction A Y))
    ((comparisonAdjunction A X).comp (ProEtale.upperStarLowerStarAdjunction A g))).symm
    (lowerStarCompComparisonLowerStarIso g A).symm

/-- **Comparison of global cohomology.** The derived global sections of the comparison pullback
`ν^* M` of an étale sheaf vanish in degree `q` if those of `M` do: `RΓ(X_proét, ν^* M) ≅
RΓ(X_ét, M)`, by the invertibility of the derived unit `M ⟶ Rν_* ν^* M`. -/
lemma isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar_obj (X : Scheme.{u})
    (M : Sheaf X.smallEtaleTopology A) (q : ℕ)
    (h : IsZero (((Etale.sectionsFunctor A X).rightDerived q).obj M)) :
    IsZero (((globalSectionsFunctor A X).rightDerived q).obj
      ((comparisonUpperStar A X).obj M)) := by
  have := isIso_comparisonAdjunction_unit A X
  have : (comparisonLowerStar A X).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (comparisonAdjunction A X)
  -- the global sections of a pro-étale sheaf are the global sections of its restriction
  let eΓ : comparisonLowerStar A X ⋙ Etale.sectionsFunctor A X ≅ globalSectionsFunctor A X :=
    Iso.refl _
  let eR : (comparisonLowerStar A X ⋙ Etale.sectionsFunctor A X).rightDerived q ≅
      (globalSectionsFunctor A X).rightDerived q :=
    { hom := NatTrans.rightDerived eΓ.hom q
      inv := NatTrans.rightDerived eΓ.inv q
      hom_inv_id := by rw [← NatTrans.rightDerived_comp, eΓ.hom_inv_id, NatTrans.rightDerived_id]
      inv_hom_id := by rw [← NatTrans.rightDerived_comp, eΓ.inv_hom_id, NatTrans.rightDerived_id] }
  -- the derived unit `M ⟶ Rν_* ν^* M` is invertible
  have hu := (comparisonAdjunction A X).isIso_derivedPlus_unit_app_of_rightAcyclic
    (fun _ _ ↦ inferInstance) (fun I _ ↦ rightAcyclic_comparisonUpperStar_obj_of_injective A X I)
    ((DerivedCategory.Plus.singleFunctor _ 0).obj M)
  let e : (DerivedCategory.Plus.singleFunctor _ 0 ⋙
      (comparisonLowerStar A X ⋙ Etale.sectionsFunctor A X).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor A q).obj ((comparisonUpperStar A X).obj M) ≅
      (DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (Etale.sectionsFunctor A X).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor A q).obj M :=
    (DerivedCategory.Plus.homologyFunctor A q).mapIso
      ((Functor.rightDerivedFunctorPlusCompIso _ _).app _ ≪≫
        (Etale.sectionsFunctor A X).rightDerivedFunctorPlus.mapIso
          ((comparisonLowerStar A X).rightDerivedFunctorPlus.mapIso
            (((comparisonUpperStar A X).mapDerivedCategoryPlusSingleFunctor 0).app M).symm ≪≫
          (asIso ((comparisonAdjunction A X).derivedPlus.unit.app _)).symm))
  refine IsZero.of_iso ?_ (eR.symm.app _ ≪≫
    ((comparisonLowerStar A X ⋙ Etale.sectionsFunctor A X)
      |>.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q).symm.app _ ≪≫ e ≪≫
    ((Etale.sectionsFunctor A X).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
      q).app M)
  exact h

end Acyclicity

/-- **Acyclicity of pulled-back injectives over quasi-compact quasi-separated objects.** Let
`f : U ⟶ V` be quasi-compact and quasi-separated, `I` an injective étale sheaf on `U` and `W` an
object of the affine pro-étale site of `V`. Then the higher derived sections of `ν_U^* I` over
the quasi-compact quasi-separated pro-étale `U`-scheme `U ×_V W` vanish. -/
theorem isZero_rightDerived_sectionsFunctor_comparisonUpperStar_obj {U V : Scheme.{u}}
    (f : U ⟶ V) [QuasiCompact f] [QuasiSeparated f] (I : Sheaf U.smallEtaleTopology A)
    [Injective I] (W : V.AffineProEt) (q : ℕ) :
    IsZero (((sectionsFunctor A ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj
      ((AffineProEt.toProEt V).obj W))).rightDerived (q + 1)).obj
        ((comparisonUpperStar A U).obj I)) := by
  obtain ⟨J, _, _, ⟨pres⟩⟩ := AffineProEt.exists_relativeLimitPresentation _ W
  let c := pullbackPresentationCone f pres
  refine isZero_rightDerived_sectionsFunctor_of_upperStar A c.pt _ _ ?_
  refine IsZero.of_iso ?_ (((globalSectionsFunctor A c.pt.left).rightDerived (q + 1)).mapIso
    ((comparisonUpperStarCompUpperStarIso A c.pt.hom).app I))
  refine isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar_obj A _ _ _ ?_
  have (j : J) : CompactSpace
      ((pullbackPresentationDiagram f pres ⋙ toProEt U ⋙ ProEt.forget U).obj j).left :=
    inferInstanceAs (CompactSpace ((pullbackPresentationDiagram f pres).obj j).left)
  have (j : J) : QuasiSeparatedSpace
      ((pullbackPresentationDiagram f pres ⋙ toProEt U ⋙ ProEt.forget U).obj j).left :=
    inferInstanceAs (QuasiSeparatedSpace ((pullbackPresentationDiagram f pres).obj j).left)
  have {i j : J} (g : i ⟶ j) : IsAffineHom
      ((pullbackPresentationDiagram f pres ⋙ toProEt U ⋙ ProEt.forget U).map g).left :=
    inferInstanceAs (IsAffineHom ((pullbackPresentationDiagram f pres).map g).left)
  refine Etale.isZero_rightDerived_sectionsFunctor_upperStar_of_isLimit A I
    (pullbackPresentationDiagram f pres ⋙ toProEt U ⋙ ProEt.forget U) ((ProEt.forget U).mapCone c)
    (isLimitPullbackPresentationCone f pres) (q + 1) fun j ↦ ?_
  have : Injective ((Etale.upperStar A
      ((pullbackPresentationDiagram f pres ⋙ toProEt U ⋙ ProEt.forget U).obj j).hom).obj I) :=
    Etale.injective_upperStar_obj_of_etale' A ((pullbackPresentationDiagram f pres).obj j).hom I
  exact Functor.isZero_rightDerived_obj_injective_succ _ _ _

/-- For `f` quasi-compact and quasi-separated, the comparison pullback `ν_U^* I` of an injective
étale sheaf is acyclic for the pro-étale direct image `f_*`. -/
theorem rightAcyclic_lowerStar_comparisonUpperStar_obj_of_injective {U V : Scheme.{u}}
    (f : U ⟶ V) [QuasiCompact f] [QuasiSeparated f] (I : Sheaf U.smallEtaleTopology A)
    [Injective I] :
    (ProEtale.lowerStar A f).rightAcyclic ((comparisonUpperStar A U).obj I) :=
  rightAcyclic_lowerStar_of_isZero_rightDerived A f _
    (isZero_rightDerived_sectionsFunctor_comparisonUpperStar_obj A f I)

end AlgebraicGeometry.ProEtale
