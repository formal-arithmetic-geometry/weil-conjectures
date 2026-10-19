/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.Paper.PurEtaleScalarMateProjection
public import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar
import Sheaf.Paper.EtaleScalarPullbackUnit
import Sheaf.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities

/-! # Scalar-unit normalization of the etale coefficient mate

Source: Stacks Project, Tags 07A6, 07A7 and 0D6J.
(blueprint: lem-r2-etale-scalar-mate-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem coefficient_mate_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ C} {R : C ⥤ A} {G : B ⥤ D} {S : D ⥤ B}
    {LX : C ⥤ D} {UX : D ⥤ C} {LY : A ⥤ B} {UY : B ⥤ A}
    (adjA : F ⊣ R) (adjB : G ⊣ S) (adjX : LX ⊣ UX) (adjY : LY ⊣ UY)
    (l : LY ⋙ G ≅ F ⋙ LX) (a : UY ⋙ F ≅ G ⋙ UX)
    (hu : ∀ K, F.map (adjY.unit.app K) ≫ a.hom.app (LY.obj K) ≫
      UX.map (l.hom.app K) = adjX.unit.app (F.obj K)) (K : C) :
    adjY.unit.app (R.obj K) ≫ UY.map
      ((mateEquiv adjA adjB (TwoSquare.mk _ _ _ _ l.hom)).natTrans.app K) ≫
      ((mateEquiv adjB adjA (TwoSquare.mk _ _ _ _ a.hom)).natTrans.app
        (LX.obj K)) = R.map (adjX.unit.app K) := by
  apply (adjA.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [mateEquiv_counit]
  dsimp only [TwoSquare.mk]
  rw [reassoc_of% (a.hom.naturality
    ((mateEquiv adjA adjB (TwoSquare.mk _ _ _ _ l.hom)).natTrans.app K))]
  rw [← UX.map_comp, mateEquiv_counit, UX.map_comp]
  dsimp only [TwoSquare.mk]
  rw [reassoc_of% (hu (R.obj K))]
  exact (adjX.unit.naturality ((adjA.counit).app K)).symm.trans
    (by simp)

private theorem mate_left_iso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L E : A ⥤ B} {R : B ⥤ A} {L' E' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (e : L ≅ E) (e' : L' ≅ E')
    (s : G ⋙ E' ⟶ E ⋙ H) :
    (mateEquiv (adj.ofNatIsoLeft e) (adj'.ofNatIsoLeft e')
      (TwoSquare.mk _ _ _ _ s)).natTrans =
      (mateEquiv adj adj'
        (TwoSquare.mk _ _ _ _
          (Functor.whiskerLeft G e'.hom ≫ s ≫ Functor.whiskerRight e.inv H))).natTrans := by
  ext X
  simp only [mateEquiv_apply, TwoSquare.mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Category.id_comp, Adjunction.ofNatIsoLeft_unit, Adjunction.ofNatIsoLeft_counit,
    Functor.map_comp, Functor.comp_map, Category.assoc]
  repeat first | erw [Category.id_comp] | erw [Category.comp_id]
  rfl


private theorem exact_counit
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) f).counit.app N).hom =
      (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map
          ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility.hom.app N) ≫
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).ofNatIsoLeft
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)).counit.app
            N.obj := by
  change _root_.DerivedCategory.Plus.ι.map
    ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) f).counit.app N) = _
  simp only [derivedUpperStarLowerStarAdjunctionPlus, Adjunction.derivedAdjunctionPlus,
    Adjunction.map_restrictFullyFaithful_counit_app,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_inv, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp]
  rfl

private theorem plus_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : _root_.DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    ((derivedUpperStarRestrictScalarsIso φ f).hom.app N).hom =
      (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ f)).hom.app
        N.obj := by
  have he : _root_.DerivedCategory.Plus.ι.mapIso
      (((Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryPlusCompIso
        (upperStar (ModuleCat.{u + 1} A) f)).app N) =
      ((Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryCompIso
        (upperStar (ModuleCat.{u + 1} A) f)).app N.obj :=
    Iso.ext (Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app _ _ N)
  have hi := congrArg Iso.inv he
  simp only [Functor.mapIso_inv, Iso.app_inv] at hi
  simp only [derivedUpperStarRestrictScalarsIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom]
  change _root_.DerivedCategory.Plus.ι.map _ ≫ _root_.DerivedCategory.Plus.ι.map _ ≫
    _root_.DerivedCategory.Plus.ι.map _ = _
  simp only [hi, Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app]
  rfl
private theorem ambient_mate_exact
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarRestrictionDirectImageMap φ f =
      (mateEquiv
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).ofNatIsoLeft
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f))
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).ofNatIsoLeft
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f))
        (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso
          (upperStarRestrictScalarsIsoSheaf φ f)).hom)).natTrans := by
  symm
  exact mate_left_iso _ _ _ _ _

private theorem ambient_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map
        ((scalarRestrictionDirectImageMap φ f).app N) ≫
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)).counit.app
          ((Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj N) =
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ f)).hom.app
        (R(lowerStar (ModuleCat.{u + 1} B) f).obj N) ≫
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map
        (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).ofNatIsoLeft
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f)).counit.app N) := by
  rw [ambient_mate_exact]
  exact mateEquiv_counit _ _ _ _
private theorem bounded_comparison
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (scalarRestrictionDirectImageMap φ f).app N.obj =
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
          ((lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctorPlusCompatibility.inv.app N) ≫
        ((rightDerivedLowerStarRestrictScalars φ f).app N).hom ≫
          (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility.hom.app
            ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj N) := by
  let FA := upperStar (ModuleCat.{u + 1} A) f
  let FB := upperStar (ModuleCat.{u + 1} B) f
  let UX := Sheaf.restrictScalars X.smallEtaleTopology φ
  let UY := Sheaf.restrictScalars Y.smallEtaleTopology φ
  let eB := (lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctorPlusCompatibility.app N
  let eA := (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility.app
    (UX.mapDerivedCategoryPlus.obj N)
  let a := Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ f)
  let adjA := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
  have hp := (derivedRestrictScalars_adjunction_identities φ f).2 N
  simp only [derivedBaseChangeSourceRestrictScalarsIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Category.assoc] at hp
  have hp' := congrArg (fun q ↦ FA.mapDerivedCategoryPlus.map
    ((derivedLowerStarRestrictScalarsIso φ f).hom.app N) ≫ q) hp
  dsimp only [FA] at hp'
  simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp] at hp'
  have hp'' := congrArg (fun q ↦ _root_.DerivedCategory.Plus.ι.map q) hp'
  simp only [Functor.map_comp] at hp''
  change ((derivedUpperStarRestrictScalarsIso φ f).hom.app
      ((lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctorPlus.obj N)).hom ≫
    UX.mapDerivedCategory.map
      ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} B) f).counit.app N).hom =
    FA.mapDerivedCategory.map ((derivedLowerStarRestrictScalarsIso φ f).hom.app N).hom ≫
      ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) f).counit.app
        (UX.mapDerivedCategoryPlus.obj N)).hom at hp''
  erw [plus_square] at hp''
  apply (adjA.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  erw [ambient_counit]
  change _ = FA.mapDerivedCategory.map (UY.mapDerivedCategory.map eB.inv) ≫
    FA.mapDerivedCategory.map _ ≫ FA.mapDerivedCategory.map eA.hom ≫ adjA.counit.app _
  erw [← exact_counit A f (UX.mapDerivedCategoryPlus.obj N)]
  erw [← hp'']
  erw [reassoc_of% (a.hom.naturality eB.inv)]
  erw [← UX.mapDerivedCategory.map_comp]
  erw [exact_counit B f N]
  dsimp only [eB]
  simp only [Iso.app_inv, ← CategoryTheory.Functor.map_comp_assoc,
    Iso.inv_hom_id_app]
  exact (congrArg (fun q ↦ a.hom.app
      (R(lowerStar (ModuleCat.{u + 1} B) f).obj N.obj) ≫ UX.mapDerivedCategory.map q)
    ((congrArg (fun q ↦ q ≫
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f)).counit.app N.obj)
      (FB.mapDerivedCategory.map_id _)).trans (Category.id_comp _))).symm

/-- The canonical coefficient mate respects scalar units, and the ambient restriction
mate is invertible on bounded-below inputs. This is a normalization assertion for
arbitrary scheme morphisms, with no properness or projection-formula assumption.
Source: Stacks Tags 07A6, 07A7 and 0D6J
(blueprint: lem-r2-etale-scalar-mate-normalization).
Proof: first express the exact inverse-image/restriction square as the derived
square of the ordinary adjunction conjugate. Derivation preserves its mate, and
restriction along the full inclusions of D+ identifies its geometric units and
counits with the bounded-below derived adjunction. The universal right-derived
unit equation then identifies its restriction with
rightDerivedLowerStarRestrictScalars. That comparison is invertible, since
restriction sends injective B-sheaves to direct-image-acyclic A-sheaves. This proves
the first assertion. Apply scalarPullbackUnit for the independent scalar-unit
normalization of scalarPullbackIso on the ambient derived categories. Transpose
under the A-geometric adjunction: the mate counit identity, naturality of the
restriction/pullback square and the scalar-unit equation show
unit_Y followed by restriction of scalarMate followed by the restriction/direct-image
mate equals direct image of unit_X. Naturality of the scalar and geometric units
extends this to every arrow eta, using its scalar-adjoint transpose. Substitute the
bounded comparison from the first step and its exact-versus-derived inclusion
isomorphisms to obtain precisely the displayed second equation. -/
theorem scalarMatePlusNormalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (∀ N : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)),
      IsIso ((scalarRestrictionDirectImageMap φ f).app N.obj)) ∧
    (∀ (K : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (M : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
      (η : K ⟶ (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj M),
      (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)).unit.app
          (R(lowerStar (ModuleCat.{u + 1} A) f).obj K.obj) ≫
        (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
          ((scalarMate φ f).app K.obj ≫
            R(lowerStar (ModuleCat.{u + 1} B) f).map
              (((Adjunction.ofIsRightAdjoint
                (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).homEquiv
                  K.obj M.obj).symm η.hom)) =
        (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility.inv.app K ≫
          (((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus.map η ≫
            (asIso (rightDerivedLowerStarRestrictScalars φ f)).inv.app M).hom) ≫
          (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
            ((lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctorPlusCompatibility.hom.app
              M)) := by
  constructor
  · intro N
    rw [bounded_comparison]
    infer_instance
  · intro K M η
    let UX := Sheaf.derivedRestrictScalars X.smallEtaleTopology φ
    let UY := Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ
    let RA := lowerStar (ModuleCat.{u + 1} A) f
    let RB := lowerStar (ModuleCat.{u + 1} B) f
    let adjX := Adjunction.ofIsRightAdjoint UX
    let adjY := Adjunction.ofIsRightAdjoint UY
    let c := (adjX.homEquiv K.obj M.obj).symm η.hom
    have hunit := coefficient_mate_unit
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
      adjX adjY (scalarPullbackIso φ f) (scalarRestrictionPullbackIso φ f)
      (scalarPullbackUnit φ f) K.obj
    change adjY.unit.app (RA.rightDerivedFunctor.obj K.obj) ≫
      UY.map ((scalarMate φ f).app K.obj) ≫
        (scalarRestrictionDirectImageMap φ f).app (UX.leftAdjoint.obj K.obj) =
      RA.rightDerivedFunctor.map (adjX.unit.app K.obj) at hunit
    have hη : adjX.unit.app K.obj ≫ UX.map c = η.hom := by
      exact (adjX.homEquiv_unit _ _ c).symm.trans (Equiv.apply_symm_apply _ _)
    have hmap : adjY.unit.app (RA.rightDerivedFunctor.obj K.obj) ≫
        UY.map ((scalarMate φ f).app K.obj ≫ RB.rightDerivedFunctor.map c) ≫
          (scalarRestrictionDirectImageMap φ f).app M.obj =
        RA.rightDerivedFunctor.map η.hom := by
      rw [CategoryTheory.Functor.map_comp, Category.assoc]
      erw [(scalarRestrictionDirectImageMap φ f).naturality c]
      change _ ≫ _ ≫ _ ≫ RA.rightDerivedFunctor.map (UX.map c) = _
      have hh := congrArg (fun q ↦ q ≫ RA.rightDerivedFunctor.map (UX.map c)) hunit
      have he := (RA.rightDerivedFunctor.map_comp _ _).symm.trans
        (congrArg RA.rightDerivedFunctor.map hη)
      exact (by simpa only [Category.assoc] using hh.trans he)
    have hδ : IsIso ((scalarRestrictionDirectImageMap φ f).app M.obj) := by
      rw [bounded_comparison]
      infer_instance
    apply (cancel_mono ((scalarRestrictionDirectImageMap φ f).app M.obj)).1
    rw [Category.assoc]
    erw [hmap, bounded_comparison]
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
      Iso.hom_inv_id_app]
    erw [UY.map_id, Category.id_comp]
    change RA.rightDerivedFunctor.map η.hom = _
    simp only [ObjectProperty.FullSubcategory.comp_hom, asIso_inv,
      Category.assoc]
    have hc := congrArg (fun q ↦ q.hom)
      ((asIso (rightDerivedLowerStarRestrictScalars φ f)).inv_hom_id_app M)
    change ((inv (rightDerivedLowerStarRestrictScalars φ f)).app M).hom ≫
      ((rightDerivedLowerStarRestrictScalars φ f).app M).hom = 𝟙 _ at hc
    erw [reassoc_of% hc]
    have hn := RA.rightDerivedFunctorPlusCompatibility.hom.naturality η
    change (RA.rightDerivedFunctorPlus.map η).hom ≫
      RA.rightDerivedFunctorPlusCompatibility.hom.app _ =
      RA.rightDerivedFunctorPlusCompatibility.hom.app K ≫
        RA.rightDerivedFunctor.map η.hom at hn
    rw [hn, Iso.inv_hom_id_app_assoc]

end AlgebraicGeometry.Etale
