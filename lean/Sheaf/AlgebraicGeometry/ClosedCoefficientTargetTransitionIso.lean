/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseChangeStalkTransition
import WeilConjectures.SixFunctors.Finite.BaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ClosedImmersion

/-! # Closed coefficient transition comparison -/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
variable (Λ : Type (u + 1)) [CommRing Λ]

private lemma mapped_unit_comp_isIso
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (F : C ⥤ E) (G : D ⥤ E)
    (c : R ⋙ F ≅ G) (K : C) [IsIso (adj.unit.app K)] :
    IsIso (F.map (adj.unit.app K) ≫ c.hom.app (L.obj K)) := by
  infer_instance

private lemma derived_counit_isIso_of_exact_fullyFaithful
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] [R.Full] [R.Faithful]
    (adj : L ⊣ R) (M : DerivedCategory.Plus D) :
    IsIso (adj.derivedPlus.counit.app M) := by
  obtain ⟨K, ⟨e⟩⟩ : ∃ K : HomotopyCategory.Plus D,
      Nonempty (DerivedCategory.Plus.Qh.obj K ≅ M) :=
    ⟨_, ⟨DerivedCategory.Plus.Qh.objObjPreimageIso M⟩⟩
  rw [← NatTrans.isIso_app_iff_of_iso _ e]
  have hK : IsIso (adj.mapHomotopyCategoryPlus.counit.app K) := by
    have : IsIso ((HomotopyCategory.Plus.ι D).map
        (adj.mapHomotopyCategoryPlus.counit.app K)) := by
      rw [Adjunction.ι_map_mapHomotopyCategoryPlus_counit_app]
      obtain ⟨N, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective K
      change IsIso ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app
        ((HomotopyCategory.quotient D _).obj N.obj))
      rw [Adjunction.mapHomotopyCategory_counit_app_quotient]
      have (n : ℤ) : IsIso (((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app
          N.obj).f n) := by
        rw [Adjunction.mapHomologicalComplex_counit_app_f]
        infer_instance
      have : IsIso ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app N.obj) :=
        HomologicalComplex.Hom.isIso_of_components _
      infer_instance
    exact isIso_of_fully_faithful (HomotopyCategory.Plus.ι D) _
  have : IsIso R.rightDerivedFunctorPlusUnit :=
    Functor.isIso_rightDerivedFunctorPlusUnit R
  have hf := adj.derivedPlus_counit_app_fac K
  have : IsIso (L.mapDerivedCategoryPlus.map (R.rightDerivedFunctorPlusUnit.app K) ≫
      adj.derivedPlus.counit.app (DerivedCategory.Plus.Qh.obj K)) := by
    rw [hf]
    infer_instance
  have : IsIso (R.rightDerivedFunctorPlusUnit.app K) :=
    NatIso.isIso_app_of_isIso R.rightDerivedFunctorPlusUnit K
  have : IsIso (L.mapDerivedCategoryPlus.map (R.rightDerivedFunctorPlusUnit.app K)) :=
    Functor.map_isIso _ _
  exact IsIso.of_isIso_comp_left
    (L.mapDerivedCategoryPlus.map (R.rightDerivedFunctorPlusUnit.app K)) _

private lemma lowerStarPlusTransition_eq_unit {Y Y' X : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ X)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    lowerStarPlusTransition Λ a h (a ≫ h) rfl K =
      R+((h)_*[ModuleCat.{u + 1} Λ]).map
          ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) a).unit.app K) ≫
        (Functor.rightDerivedFunctorPlusCompIso' ((a)_*[ModuleCat.{u + 1} Λ])
          ((h)_*[ModuleCat.{u + 1} Λ])
          (lowerStarComp (ModuleCat.{u + 1} Λ) a h)).hom.app
          (D+((a)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  have : ((a)_*[ModuleCat.{u + 1} Λ]).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a)
  let adjA := derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) a
  let adjH := derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h
  let c := Functor.rightDerivedFunctorPlusCompIso' ((a)_*[ModuleCat.{u + 1} Λ])
    ((h)_*[ModuleCat.{u + 1} Λ]) (lowerStarComp (ModuleCat.{u + 1} Λ) a h)
  rw [lowerStarPlusTransition]
  simp only [eqToIso_refl, Iso.refl_trans]
  rw [Functor.map_comp, ← Category.assoc]
  have hc := derivedPlus_unit_comp_upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a h
    (a ≫ h) rfl (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K)
  rw [← derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus] at hc
  rw [← derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus] at hc
  rw [← derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus] at hc
  change (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) (a ≫ h)).unit.app
      (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K) ≫
      R+((a ≫ h)_*[ModuleCat.{u + 1} Λ]).map
        ((upperStarPlusComp (ModuleCat.{u + 1} Λ) a h).hom.app
          (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K)) =
    adjH.unit.app (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K) ≫
      R+((h)_*[ModuleCat.{u + 1} Λ]).map
        (adjA.unit.app (D+((h)^*[ModuleCat.{u + 1} Λ]).obj
          (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K))) ≫
      c.hom.app (D+((a)^*[ModuleCat.{u + 1} Λ]).obj
        (D+((h)^*[ModuleCat.{u + 1} Λ]).obj
          (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K))) at hc
  rw [hc]
  have hn := c.hom.naturality
    (D+((a)^*[ModuleCat.{u + 1} Λ]).map (adjH.counit.app K))
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [Category.assoc]
  rw [← hn, ← Functor.map_comp_assoc]
  have hu := adjA.unit.naturality (adjH.counit.app K)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hu
  rw [← hu, Functor.map_comp, ← Category.assoc]
  rw [reassoc_of% (adjH.right_triangle_components K)]
  rfl

private lemma closed_derived_unit_single_isIso {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i]
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) i).unit.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (((i)_*[ModuleCat.{u + 1} Λ]).obj G))) := by
  let adj := derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) i
  have hε (M : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      IsIso (adj.counit.app M) := by
    dsimp only [adj]
    rw [derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus]
    exact derived_counit_isIso_of_exact_fullyFaithful
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i) M
  have : IsIso adj.counit := NatIso.isIso_of_isIso_app _
  have := adj.fullyFaithfulROfIsIsoCounit.full
  have := adj.fullyFaithfulROfIsIsoCounit.faithful
  let R := (i)_*[ModuleCat.{u + 1} Λ]
  let M := (DerivedCategory.Plus.singleFunctor _ 0).obj G
  let e : (DerivedCategory.Plus.singleFunctor _ 0).obj (R.obj G) ≅
      R.rightDerivedFunctorPlus.obj M :=
    ((R.mapDerivedCategoryPlusSingleFunctor 0).app G).symm ≪≫
      R.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.symm.app M
  exact adj.isIso_unit_app_of_iso e

private lemma lowerStarPlusTransition_isIso_of_unit {Y Y' X : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ X) (h' : Y' ⟶ X) (w : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [IsIso ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) a).unit.app K)] :
    IsIso (lowerStarPlusTransition Λ a h h' w K) := by
  subst w
  rw [lowerStarPlusTransition_eq_unit]
  have : ((a)_*[ModuleCat.{u + 1} Λ]).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a)
  exact mapped_unit_comp_isIso
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) a)
    R+((h)_*[ModuleCat.{u + 1} Λ]) R+((a ≫ h)_*[ModuleCat.{u + 1} Λ])
    (Functor.rightDerivedFunctorPlusCompIso' ((a)_*[ModuleCat.{u + 1} Λ])
      ((h)_*[ModuleCat.{u + 1} Λ]) (lowerStarComp (ModuleCat.{u + 1} Λ) a h)) K

/-- For a Cartesian square Y→T over X→S, a closed immersion i:Z→T, and the corresponding Cartesian
square YZ→Z, the canonical target transition is an isomorphism with coefficient i_*G.

Source: Stacks Project, Tag 0F07; Tags 03QP and 0959.
(blueprint: lem-sbc-closed-coefficient-target-transition-iso)

Proof: Paste the two given Cartesian squares to obtain a Cartesian square eZ,a,i,e. Its pulled-back
closed immersion a is closed. Finite base change identifies e^*i_*G with a_*eZ^*G. Exact inverse
image identifies the pullback of the single complex with the single complex of this sheaf. As in
the source comparison, exact and fully faithful closed direct image makes the derived unit
invertible on a closed pushforward single complex. Transport this property across the finite
base-change and single-complex isomorphisms. Derived composition expresses the lower-star
transition as the image of the invertible derived unit followed by the composition isomorphism.
Every remaining factor in the target transition is an inverse-image composition comparison,
equality transport, or single-complex comparison, hence invertible. Apply degree-q homology.
-/
theorem baseChangeTargetTransition_isIso_closed_coefficients
    {X S T Y Z YZ : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S}
    {e : Y ⟶ T} {h : Y ⟶ X} (sq : IsPullback e h g p)
    (i : Z ⟶ T) [IsClosedImmersion i] {eZ : YZ ⟶ Z} {hZ : YZ ⟶ X}
    (sqZ : IsPullback eZ hZ (i ≫ g) p) (a : YZ ⟶ Y)
    (wa : a ≫ e = eZ ≫ i) (wh : a ≫ h = hZ) (q : ℤ)
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (baseChangeTargetTransition Λ e h q i a eZ hZ wa wh
      (((i)_*[ModuleCat.{u + 1} Λ]).obj G)) := by
  have sqI : IsPullback eZ a i e :=
    IsPullback.of_bot (wh.symm ▸ sqZ) wa.symm sq
  have : IsClosedImmersion a := MorphismProperty.of_isPullback sqI inferInstance
  let H := (((i)_*[ModuleCat.{u + 1} Λ]).obj G)
  have hbc : IsIso (baseChangeMap (ModuleCat.{u + 1} Λ) sqI.toCommSq) :=
    isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} Λ) sqI
  let J := (((eZ)^*[ModuleCat.{u + 1} Λ]).obj G)
  let b : (((e)^*[ModuleCat.{u + 1} Λ]).obj H) ≅
      (((a)_*[ModuleCat.{u + 1} Λ]).obj J) :=
    asIso ((baseChangeMap (ModuleCat.{u + 1} Λ) sqI.toCommSq).app G)
  let K := D+((e)^*[ModuleCat.{u + 1} Λ]).obj
    ((DerivedCategory.Plus.singleFunctor _ 0).obj H)
  let d : K ≅ (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((a)_*[ModuleCat.{u + 1} Λ]).obj J) :=
    (((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app H ≪≫
      (DerivedCategory.Plus.singleFunctor _ 0).mapIso b
  have : IsIso ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) a).unit.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (((a)_*[ModuleCat.{u + 1} Λ]).obj J))) :=
    closed_derived_unit_single_isIso Λ a J
  have : IsIso ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) a).unit.app K) :=
    (NatTrans.isIso_app_iff_of_iso _ d).mpr inferInstance
  have : IsIso (lowerStarPlusTransition Λ a h hZ wh K) :=
    lowerStarPlusTransition_isIso_of_unit Λ a h hZ wh K
  dsimp only [baseChangeTargetTransition, Functor.comp_obj]
  infer_instance


end AlgebraicGeometry.Etale
