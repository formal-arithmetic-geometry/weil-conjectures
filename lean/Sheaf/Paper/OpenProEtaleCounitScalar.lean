module

public import Sheaf.AlgebraicGeometry.UnboundedOpenCounitSiteTransport
public import Sheaf.Paper.EtaleProEtaleCoefficientCompatibility
public import Sheaf.Paper.EtaleProEtaleScalarMate
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
import Sheaf.Paper.EtaleProEtaleScalarPullbackCube
import all Sheaf.Paper.EtaleOpenCounitFlatModels
import all Sheaf.Paper.EtaleOpenScalarExchange
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# The actual pro-etale open counit under scalar extension

Source: main-20261015 blueprint, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-exceptional.proof.md, Locality paragraph, retained Step 12
(blueprint: lem-sp-open-proetale-counit-scalar).

The compact-support arrow is the recorded arrow transported to fixed-module coordinates.
Only the canonical derived direct-image identity removes its identity proper factor.
The restriction comparison is the canonical scalar/pullback comparison in open coordinates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale
open CoefficientCompatibility

/-- Remove the identity proper factor using the canonical derived direct-image identity.
Source: blueprint Locality, identity-factor compactification
(blueprint: lem-sp-open-proetale-counit-scalar). -/
def openCounitSupportIdentity (R : Type (u + 1)) [CommRing R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R)
        (Compactification.ofIsOpenImmersion j) ≅
      (openImmersionLowerShriek
        (ModuleCat.{u + 1} R) j).mapDerivedCategory :=
  Functor.isoWhiskerLeft _ (rightDerivedLowerStarId (ModuleCat.{u + 1} R) X) ≪≫
    Functor.rightUnitor _

/-- The named compact-support coefficient arrow in exact open-extension coordinates.
This uses the genuine transported recorded arrow, not a new tensor comparison.
Source: blueprint Locality, definition of b_j
(blueprint: lem-sp-open-proetale-counit-scalar). -/
def openCounitScalarMap {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙
        liftedScalarExtension φ X ⟶
      liftedScalarExtension φ U ⋙
        (openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).mapDerivedCategory :=
  Functor.whiskerRight (openCounitSupportIdentity (ULift.{u + 1, u} A) j).inv _ ≫
    proEtaleCoefficientMap φ (Compactification.ofIsOpenImmersion j) ≫
      Functor.whiskerLeft _ (openCounitSupportIdentity (ULift.{u + 1, u} B) j).hom

/-- Exact restriction identified with the canonical derived geometric inverse image.
Source: blueprint Locality, canonical restriction coordinates
(blueprint: lem-sp-open-proetale-counit-scalar). -/
def openCounitRestrictionModel (R : Type (u + 1)) [CommRing R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (upperStar (ModuleCat.{u + 1} R) j).leftDerivedFunctor ≅
      (openImmersionRestriction
        (ModuleCat.{u + 1} R) j).mapDerivedCategory :=
  leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} R) j ≪≫
    Functor.mapDerivedCategoryNatIso
      (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} R) j)

/-- The canonical a_j, inverse to lambda_j, in exact open-restriction coordinates.
The middle isomorphism is fixed by the constant-ring maps and K-flat balancing.
Source: blueprint Locality, scalar/restriction comparison
(blueprint: lem-sp-open-proetale-counit-scalar). -/
def openCounitRestrictionScalarIso {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (openImmersionRestriction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙
        liftedScalarExtension φ U ≅
      liftedScalarExtension φ X ⋙
        (openImmersionRestriction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).mapDerivedCategory :=
  Functor.isoWhiskerRight (openCounitRestrictionModel (ULift.{u + 1, u} A) j).symm _ ≪≫
    (scalarPullbackProEtaleIso (uliftRingHom φ) j).symm ≪≫
      Functor.isoWhiskerLeft _ (openCounitRestrictionModel (ULift.{u + 1, u} B) j)

-- Keep localization constructions abstract during proof elaboration.
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor Functor.leftAdjoint Functor.rightAdjoint

private theorem supportIdentity_hom (R : Type (u + 1)) [CommRing R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} R))) :
    (openCounitSupportIdentity R j).hom.app L =
      (rightDerivedLowerStarId (ModuleCat.{u + 1} R) X).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.obj L) := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

private theorem supportIdentity_inv (R : Type (u + 1)) [CommRing R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} R))) :
    (openCounitSupportIdentity R j).inv.app L =
      (rightDerivedLowerStarId (ModuleCat.{u + 1} R) X).inv.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.obj L) := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

private theorem exceptional_etaleProperty
    (R : Type (u + 1)) [CommRing R] [Finite R] (X : Scheme.{u})
    (K : Etale.DerivedCategoryModule R X) (hK : exceptionalTransportEtaleObjects R X K) :
    AdjunctionTransfer.etaleProperty R X K := by
  obtain ⟨a, b, hab, ht⟩ := hK.2
  exact ⟨hK.1, a, b,
    Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp ht⟩

private theorem square_change
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    (P : C ⥤ D) (Q Q' : D ⥤ F) (S S' : C ⥤ E) (T : E ⥤ F)
    [P.Additive] [Q.Additive] [Q'.Additive] [S.Additive] [S'.Additive] [T.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits Q'] [PreservesFiniteColimits Q']
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits S'] [PreservesFiniteColimits S']
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (e : Q' ≅ Q) (h : P ⋙ Q ≅ S ⋙ T) (f : S ≅ S') :
    (Functor.mapDerivedCategorySquareIso
      (Functor.isoWhiskerLeft P e ≪≫ h ≪≫ Functor.isoWhiskerRight f T)).hom =
    Functor.whiskerLeft P.mapDerivedCategory (Functor.mapDerivedCategoryNatIso e).hom ≫
      (Functor.mapDerivedCategorySquareIso h).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategoryNatIso f).hom T.mapDerivedCategory := by
  ext K
  have he := NatTrans.congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft P e) K
  have hf := NatTrans.congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight f T) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at he hf
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.mapDerivedCategoryNatIso_trans, Category.assoc]
  rw [hf]
  have he' := congrArg (fun z ↦
    (Functor.mapDerivedCategoryCompIso P Q').inv.app K ≫ z ≫
      (Functor.mapDerivedCategoryCompIso P Q).inv.app K) he
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] at he'
  dsimp only [Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [reassoc_of% he']
  simp only [Iso.inv_hom_id_app_assoc]

private def etaleRestrictionModel (R : Type (u + 1)) [CommRing R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.upperStar (ModuleCat.{u + 1} R) j).leftDerivedFunctor ≅
      (Etale.openImmersionRestriction (ModuleCat.{u + 1} R) j).mapDerivedCategory :=
  Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} R) j ≪≫
    Functor.mapDerivedCategoryNatIso
      (Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} R) j)

private theorem restrictionComparison_model (R : Type (u + 1)) [CommRing R] [Finite R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    unboundedOpenRestrictionComparison R j =
      Functor.isoWhiskerRight (etaleRestrictionModel R j).symm
        (comparisonUpperStar (ModuleCat.{u + 1} R) U).mapDerivedCategory ≪≫
      (directImageComparisonAmbientPullbackIso R j).symm ≪≫
      Functor.isoWhiskerLeft
        (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory
        (openCounitRestrictionModel R j) := by
  have hs : supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} R) j =
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} R) j).symm := by
    rfl
  have h := square_change
    (comparisonUpperStar (ModuleCat.{u + 1} R) X)
    (upperStar (ModuleCat.{u + 1} R) j)
    (openImmersionRestriction (ModuleCat.{u + 1} R) j)
    (Etale.upperStar (ModuleCat.{u + 1} R) j)
    (Etale.openImmersionRestriction (ModuleCat.{u + 1} R) j)
    (comparisonUpperStar (ModuleCat.{u + 1} R) U)
    (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} R) j).symm
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} R) j)
    (Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} R) j)
  have hr : (openComparisonRestrictionIso R j).symm =
      Functor.isoWhiskerLeft
        (comparisonUpperStar (ModuleCat.{u + 1} R) X)
        (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} R) j).symm ≪≫
      comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} R) j ≪≫
      Functor.isoWhiskerRight
        (Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} R) j)
        (comparisonUpperStar (ModuleCat.{u + 1} R) U) := by
    apply Iso.ext
    apply NatTrans.ext
    funext K
    simp only [openComparisonRestrictionIso, hs, Iso.trans_inv, Iso.trans_hom,
      Iso.symm_hom, Iso.symm_inv, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, NatTrans.comp_app]
    rfl
  rw [← hr] at h
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom,
    Iso.symm_hom, Functor.mapDerivedCategoryNatIso_symm, Category.assoc] at h
  apply Iso.ext_inv
  change (Functor.mapDerivedCategorySquareIso (openComparisonRestrictionIso R j)).inv = _
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_inv,
    Iso.symm_inv, Category.assoc]
  rw [h]
  ext K
  simp only [openCounitRestrictionModel, etaleRestrictionModel,
    directImageComparisonAmbientPullbackIso, Iso.trans_inv, Iso.trans_hom,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]

private def etaleRestrictionScalarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        Etale.scalarExtension φ U ≅
      Etale.scalarExtension φ X ⋙
        (Etale.openImmersionRestriction (ModuleCat.{u + 1} B) j).mapDerivedCategory :=
  Functor.isoWhiskerRight (etaleRestrictionModel A j).symm _ ≪≫
    (Etale.scalarPullbackIso φ j).symm ≪≫
      Functor.isoWhiskerLeft _ (etaleRestrictionModel B j)

private theorem invert_comparison_square
    {C : Type*} [Category C] {A B D E F G : C}
    (a : A ≅ B) (b : B ≅ D) (c : D ⟶ G) (f : A ⟶ E)
    (d : E ≅ F) (e : F ≅ G)
    (h : a.hom ≫ b.hom ≫ c = f ≫ d.hom ≫ e.hom) :
    b.inv ≫ a.inv ≫ f = c ≫ e.inv ≫ d.inv := by
  have hh := congrArg (fun z ↦ b.inv ≫ a.inv ≫ z ≫ e.inv ≫ d.inv) h
  simpa only [Category.assoc, a.inv_hom_id_assoc, b.inv_hom_id_assoc,
    e.hom_inv_id_assoc, d.hom_inv_id, Category.comp_id] using hh.symm

private theorem restrictionScalarSquare
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) X) :
    (liftedScalarExtension φ U).map
        ((unboundedOpenRestrictionComparison (ULift.{u + 1, u} A) j).hom.app K) ≫
      (openCounitRestrictionScalarIso φ j).hom.app
        ((comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.obj K) ≫
      (openImmersionRestriction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).mapDerivedCategory.map
          ((pbcComparisonReduction X (uliftRingHom φ)).hom.app K) =
    (pbcComparisonReduction U (uliftRingHom φ)).hom.app
        ((Etale.openImmersionRestriction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory.obj K) ≫
      (comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) U).mapDerivedCategory.map
          ((etaleRestrictionScalarIso (uliftRingHom φ) j).hom.app K) ≫
      (unboundedOpenRestrictionComparison (ULift.{u + 1, u} B) j).hom.app
        ((Etale.scalarExtension (uliftRingHom φ) X).obj K) := by
  let CA := (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory
  let CB := (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) U).mapDerivedCategory
  let TP := liftedScalarExtension φ U
  let dA := directImageComparisonAmbientPullbackIso (ULift.{u + 1, u} A) j
  let dB := directImageComparisonAmbientPullbackIso (ULift.{u + 1, u} B) j
  let lp := scalarPullbackProEtaleIso (uliftRingHom φ) j
  let le := Etale.scalarPullbackIso (uliftRingHom φ) j
  have hc := etaleProEtale_scalar_pullback_cube (uliftRingHom φ) j K
  have h := invert_comparison_square (lp.app (CA.obj K))
    (TP.mapIso (dA.app K))
    ((pbcComparisonReduction U (uliftRingHom φ)).hom.app
      ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).leftDerivedFunctor.obj K))
    ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).leftDerivedFunctor.map
      ((pbcComparisonReduction X (uliftRingHom φ)).hom.app K))
    (dB.app ((Etale.scalarExtension (uliftRingHom φ) X).obj K))
    (CB.mapIso (le.app K)) hc
  dsimp only [TP, CA, CB, dA, dB, lp, le, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.app_hom, Iso.app_inv] at h
  rw [restrictionComparison_model, restrictionComparison_model]
  simp only [openCounitRestrictionScalarIso, etaleRestrictionScalarIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  have hp := Iso.map_hom_inv_id
    ((openCounitRestrictionModel (ULift.{u + 1, u} A) j).app (CA.obj K)) TP
  have he := Iso.map_hom_inv_id
    ((etaleRestrictionModel (ULift.{u + 1, u} B) j).app
      ((Etale.scalarExtension (uliftRingHom φ) X).obj K)) CB
  dsimp only [TP, CA, CB, Iso.app_hom, Iso.app_inv] at hp he
  rw [reassoc_of% hp, reassoc_of% he]
  erw [← (openCounitRestrictionModel (ULift.{u + 1, u} B) j).hom.naturality]
  rw [reassoc_of% h]
  erw [(pbcComparisonReduction U (uliftRingHom φ)).hom.naturality_assoc]
  rfl

private theorem etaleOpenScalarIso_hom
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : Etale.DerivedCategoryModule A U) :
    (Etale.openScalarExtension φ j).hom.app K =
      (Etale.properOpenCoefficientOpenIso φ j K).hom := by
  have hi : Etale.properOpenCoefficientOpenInverse φ j K =
      (Etale.openScalarExtension φ j).inv.app K := by
    unfold Etale.properOpenCoefficientOpenInverse
    apply ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} B) j).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    exact (Etale.scalarOpen_unit φ j K).symm
  have hei : Etale.properOpenCoefficientOpenIso φ j K =
      (Etale.openScalarExtension φ j).app K := by
    apply Iso.ext_inv
    exact hi
  exact (congrArg Iso.hom hei).symm

private theorem derivedCounit_change
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).obj X)]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution C]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (J : C ⥤ D) (U V : D ⥤ C)
    [J.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (E : U ≅ V) (a : J ⊣ U) (b : J ⊣ V)
    (h : ∀ M, J.map (E.hom.app M) ≫ b.counit.app M = a.counit.app M)
    (K : _root_.DerivedCategory D) :
    J.mapDerivedCategory.map ((Functor.mapDerivedCategoryNatIso E).hom.app K) ≫
      b.mapDerivedCategoryAdjunction.counit.app K =
      a.mapDerivedCategoryAdjunction.counit.app K := by
  let t := Functor.whiskerRight (Functor.mapDerivedCategoryNatIso E).hom
    J.mapDerivedCategory ≫ b.mapDerivedCategoryAdjunction.counit
  have ht : t = a.mapDerivedCategoryAdjunction.counit := by
    apply Localization.natTrans_ext _root_.DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        D (.up ℤ))
    intro H
    dsimp only [t, NatTrans.comp_app, Functor.whiskerRight_app]
    rw [Adjunction.mapDerivedCategoryAdjunction_counit_app_Qh_obj,
      Adjunction.mapDerivedCategoryAdjunction_counit_app_Qh_obj]
    change J.mapDerivedCategory.map _ ≫ J.mapDerivedCategory.map _ ≫ _ ≫ _ = _
    rw [← J.mapDerivedCategory.map_comp_assoc,
      Functor.mapDerivedCategoryNatIso_fach]
    rw [J.mapDerivedCategory.map_comp]
    simp only [Category.assoc]
    erw [J.mapDerivedCategoryFactorsh.hom.naturality_assoc]
    dsimp only [Functor.comp_map]
    rw [← _root_.DerivedCategory.Qh.map_comp]
    congr 2
    apply congrArg
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
    rw [Adjunction.mapHomotopyCategory_counit_app_quotient,
      Adjunction.mapHomotopyCategory_counit_app_quotient]
    change (HomotopyCategory.quotient
      D (.up ℤ)).map _ ≫
        (HomotopyCategory.quotient
          D (.up ℤ)).map _ = _
    dsimp only [HomotopyCategory.quotient_obj_as]
    erw [← Functor.map_comp]
    congr 1
    ext n
    simp only [Adjunction.mapHomologicalComplex_counit_app_f]
    exact h (P.X n)
  exact NatTrans.congr_app ht K

private theorem etaleCounitRestriction (R : Type (u + 1)) [CommRing R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : Etale.DerivedCategoryModule R X) :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.map
      ((Functor.mapDerivedCategoryNatIso
        (Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} R) j)).hom.app K) ≫
      (unboundedOpenEtaleAdjunction R j).counit.app K =
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} R) j).counit.app K := by
  exact derivedCounit_change
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j)
    (Etale.upperStar (ModuleCat.{u + 1} R) j)
    (Etale.openImmersionRestriction (ModuleCat.{u + 1} R) j)
    (Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} R) j)
    (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j)
    (Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R) j)
    (fun M ↦ rfl) K

private theorem etaleScalarCounitUpper
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : Etale.DerivedCategoryModule A X) :
    (Etale.openScalarExtension φ j).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K) ≫
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((Etale.properOpenCoefficientPullbackIso φ j).inv.app K) ≫
      (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} B) j).counit.app ((Etale.scalarExtension φ X).obj K) =
      (Etale.scalarExtension φ X).map
        ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).counit.app K) := by
  have h := (Etale.etaleOpenTensorComparisons φ j).counit K
  rw [Etale.openScalarRestriction_eq] at h
  exact h

private theorem counitEquation_change
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (J : C ⥤ D) (U U0 : D ⥤ C) (J' : E ⥤ F) (V V0 : F ⥤ E)
    (T : C ⥤ E) (S : D ⥤ F)
    (e : U0 ≅ U) (f : V0 ≅ V)
    (b : J ⋙ S ⟶ T ⋙ J') (a0 : U0 ⋙ T ⟶ S ⋙ V0)
    (v : U ⋙ J ⟶ 𝟭 D) (v0 : U0 ⋙ J ⟶ 𝟭 D)
    (w : V ⋙ J' ⟶ 𝟭 F) (w0 : V0 ⋙ J' ⟶ 𝟭 F)
    (K : D)
    (hv : J.map (e.hom.app K) ≫ v.app K = v0.app K)
    (hw : J'.map (f.hom.app (S.obj K)) ≫ w.app (S.obj K) = w0.app (S.obj K))
    (h : b.app (U0.obj K) ≫ J'.map (a0.app K) ≫ w0.app (S.obj K) =
      S.map (v0.app K)) :
    b.app (U.obj K) ≫
      J'.map (T.map (e.inv.app K) ≫ a0.app K ≫ f.hom.app (S.obj K)) ≫
      w.app (S.obj K) = S.map (v.app K) := by
  have hb := b.naturality (e.inv.app K)
  dsimp only [Functor.comp_map] at hb
  simp only [Functor.map_comp, Category.assoc]
  rw [hw, ← reassoc_of% hb, h]
  rw [← S.map_comp]
  congr 1
  rw [← hv, ← J.map_comp_assoc, Iso.inv_hom_id_app, J.map_id, Category.id_comp]

private theorem etaleRestrictionScalarIso_exact
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    etaleRestrictionScalarIso φ j =
      Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryNatIso
          (Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j)).symm
        (Etale.scalarExtension φ U) ≪≫
      (Etale.properOpenCoefficientPullbackIso φ j).symm ≪≫
      Functor.isoWhiskerLeft (Etale.scalarExtension φ X)
        (Functor.mapDerivedCategoryNatIso
          (Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) j)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simp only [etaleRestrictionScalarIso, etaleRestrictionModel,
    Etale.properOpenCoefficientPullbackIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc]

private theorem etaleScalarCounitRestriction
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : Etale.DerivedCategoryModule A X) :
    (Etale.properOpenCoefficientOpenIso φ j
        ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K)).hom ≫
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((etaleRestrictionScalarIso φ j).hom.app K) ≫
      (unboundedOpenEtaleAdjunction B j).counit.app ((Etale.scalarExtension φ X).obj K) =
      (Etale.scalarExtension φ X).map ((unboundedOpenEtaleAdjunction A j).counit.app K) := by
  have h := counitEquation_change
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory
    (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).mapDerivedCategory
    (Etale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory
    (Etale.openImmersionRestriction (ModuleCat.{u + 1} B) j).mapDerivedCategory
    (Etale.upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory
    (Etale.scalarExtension φ U) (Etale.scalarExtension φ X)
    (Functor.mapDerivedCategoryNatIso
      (Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j))
    (Functor.mapDerivedCategoryNatIso
      (Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) j))
    (Etale.openScalarExtension φ j).hom (Etale.properOpenCoefficientPullbackIso φ j).inv
    (unboundedOpenEtaleAdjunction A j).counit
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).counit
    (unboundedOpenEtaleAdjunction B j).counit
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} B) j).counit K
    (etaleCounitRestriction A j K)
    (etaleCounitRestriction B j ((Etale.scalarExtension φ X).obj K))
    (etaleScalarCounitUpper φ j K)
  simpa only [etaleOpenScalarIso_hom, etaleRestrictionScalarIso_exact,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app] using h

private theorem counitSquare_paste
    {EA EX EB EY PA PX PB PY : Type*}
    [Category EA] [Category EX] [Category EB] [Category EY]
    [Category PA] [Category PX] [Category PB] [Category PY]
    (JA : EA ⥤ EX) (UA : EX ⥤ EA) (JB : EB ⥤ EY) (UB : EY ⥤ EB)
    (JP : PA ⥤ PX) (UP : PX ⥤ PA) (JQ : PB ⥤ PY) (UQ : PY ⥤ PB)
    (CA : EA ⥤ PA) (CX : EX ⥤ PX) (CB : EB ⥤ PB) (CY : EY ⥤ PY)
    (TE : EA ⥤ EB) (TX : EX ⥤ EY) (TP : PA ⥤ PB) (TQ : PX ⥤ PY)
    (eA : JA ⋙ CX ≅ CA ⋙ JP) (eB : JB ⋙ CY ≅ CB ⋙ JQ)
    (rA : UA ⋙ CA ≅ CX ⋙ UP) (rB : UB ⋙ CB ≅ CY ⋙ UQ)
    (dU : CA ⋙ TP ≅ TE ⋙ CB) (dX : CX ⋙ TQ ≅ TX ⋙ CY)
    (vA : UA ⋙ JA ⟶ 𝟭 EX) (vB : UB ⋙ JB ⟶ 𝟭 EY)
    (vP : UP ⋙ JP ⟶ 𝟭 PX) (vQ : UQ ⋙ JQ ⟶ 𝟭 PY)
    (b : JP ⋙ TQ ⟶ TP ⋙ JQ) (a : UP ⋙ TP ⟶ TQ ⋙ UQ)
    (K : EX) (beta : TX.obj (JA.obj (UA.obj K)) ⟶ JB.obj (TE.obj (UA.obj K)))
    (alpha : TE.obj (UA.obj K) ⟶ UB.obj (TX.obj K))
    (hA : eA.hom.app (UA.obj K) ≫ JP.map (rA.hom.app K) ≫ vP.app (CX.obj K) =
      CX.map (vA.app K))
    (hB : eB.hom.app (UB.obj (TX.obj K)) ≫ JQ.map (rB.hom.app (TX.obj K)) ≫
      vQ.app (CY.obj (TX.obj K)) = CY.map (vB.app (TX.obj K)))
    (hb : TQ.map (eA.hom.app (UA.obj K)) ≫ b.app (CA.obj (UA.obj K)) ≫
        JQ.map (dU.hom.app (UA.obj K)) =
      dX.hom.app (JA.obj (UA.obj K)) ≫ CY.map beta ≫
        eB.hom.app (TE.obj (UA.obj K)))
    (ha : TP.map (rA.hom.app K) ≫ a.app (CX.obj K) ≫ UQ.map (dX.hom.app K) =
      dU.hom.app (UA.obj K) ≫ CB.map alpha ≫ rB.hom.app (TX.obj K))
    (he : beta ≫ JB.map alpha ≫ vB.app (TX.obj K) = TX.map (vA.app K)) :
    b.app (UP.obj (CX.obj K)) ≫ JQ.map (a.app (CX.obj K)) ≫
      vQ.app (TQ.obj (CX.obj K)) = TQ.map (vP.app (CX.obj K)) := by
  apply (cancel_epi (TQ.map (eA.hom.app (UA.obj K) ≫ JP.map (rA.hom.app K)))).1
  apply (cancel_mono (dX.hom.app K)).1
  have hn := b.naturality (rA.hom.app K)
  dsimp only [Functor.comp_map] at hn
  have hv := vQ.naturality (dX.hom.app K)
  dsimp only [Functor.comp_map, Functor.id_map] at hv
  have hnB := eB.hom.naturality alpha
  dsimp only [Functor.comp_map] at hnB
  have hd := dX.hom.naturality (vA.app K)
  dsimp only [Functor.comp_map] at hd
  dsimp only [Functor.comp_obj, Functor.id_obj] at hn hv hnB hd
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, ← hv]
  rw [← JQ.map_comp_assoc, ← JQ.map_comp_assoc, Category.assoc, ha]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hb, ← reassoc_of% hnB, hB]
  rw [← CY.map_comp_assoc, ← CY.map_comp, Category.assoc, he]
  rw [← hd, ← TQ.map_comp_assoc, ← TQ.map_comp_assoc, Category.assoc, hA]

private theorem counitEquation_of_iso
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (J : C ⥤ D) (U : D ⥤ C) (J' : E ⥤ F) (U' : F ⥤ E)
    (T : C ⥤ E) (S : D ⥤ F)
    (b : J ⋙ S ⟶ T ⋙ J') (a : U ⋙ T ⟶ S ⋙ U')
    (v : U ⋙ J ⟶ 𝟭 D) (v' : U' ⋙ J' ⟶ 𝟭 F)
    {K M : D} (t : K ≅ M)
    (h : b.app (U.obj K) ≫ J'.map (a.app K) ≫ v'.app (S.obj K) = S.map (v.app K)) :
    b.app (U.obj M) ≫ J'.map (a.app M) ≫ v'.app (S.obj M) = S.map (v.app M) := by
  apply (cancel_epi (S.map (J.map (U.map t.hom)))).1
  have hb := b.naturality (U.map t.hom)
  have ha := a.naturality t.hom
  have hv := v'.naturality (S.map t.hom)
  have hw := v.naturality t.hom
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj]
    at hb ha hv hw
  rw [reassoc_of% hb, ← J'.map_comp_assoc, ha]
  simp only [Functor.map_comp, Category.assoc]
  rw [hv, reassoc_of% h, ← S.map_comp, ← S.map_comp, hw]

private theorem mate_of_counitEquation
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {J : C ⥤ D} {U : D ⥤ C} {J' : E ⥤ F} {U' : F ⥤ E}
    (adj : J ⊣ U) (adj' : J' ⊣ U') (T : C ⥤ E) (S : D ⥤ F)
    (a : U ⋙ T ⟶ S ⋙ U') (M : D)
    (e : S.obj (J.obj (U.obj M)) ≅ J'.obj (T.obj (U.obj M)))
    (h : e.hom ≫ J'.map (a.app M) ≫ adj'.counit.app (S.obj M) =
      S.map (adj.counit.app M)) :
    adj'.homEquiv _ _ (e.inv ≫ S.map (adj.counit.app M)) = a.app M := by
  apply (adj'.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  have h' := congrArg (fun z ↦ e.inv ≫ z) h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Functor.id_obj] using h'.symm

private theorem plusNatIso_inv
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) (K : _root_.DerivedCategory.Plus C) :
    _root_.DerivedCategory.Plus.ι.map
      ((Functor.mapDerivedCategoryPlusNatIso e).inv.app K) =
        (Functor.mapDerivedCategoryNatIso e).inv.app K.obj := by
  have h : _root_.DerivedCategory.Plus.ι.mapIso
      ((Functor.mapDerivedCategoryPlusNatIso e).app K) =
        (Functor.mapDerivedCategoryNatIso e).app K.obj := by
    apply Iso.ext
    exact Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app e K
  exact congrArg Iso.inv h

private theorem plusCompIso_inv
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : _root_.DerivedCategory.Plus C) :
    _root_.DerivedCategory.Plus.ι.map
      ((Functor.mapDerivedCategoryPlusCompIso F G).inv.app K) =
        (Functor.mapDerivedCategoryCompIso F G).inv.app K.obj := by
  have h : _root_.DerivedCategory.Plus.ι.mapIso
      ((Functor.mapDerivedCategoryPlusCompIso F G).app K) =
        (Functor.mapDerivedCategoryCompIso F G).app K.obj := by
    apply Iso.ext
    exact Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app F G K
  exact congrArg Iso.inv h

private theorem exactPlusCompatibility_hom
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F]
    [Limits.PreservesFiniteColimits F] (K : _root_.DerivedCategory.Plus C) :
    F.mapDerivedCategoryPlusCompatibility.hom.app K =
      𝟙 (F.mapDerivedCategory.obj K.obj) := rfl

private theorem exactPlusCompatibility_inv
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F]
    [Limits.PreservesFiniteColimits F] (K : _root_.DerivedCategory.Plus C) :
    F.mapDerivedCategoryPlusCompatibility.inv.app K =
      𝟙 (F.mapDerivedCategory.obj K.obj) := rfl

private theorem compactComparison_generic
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory F]
    [EnoughInjectives B] [EnoughInjectives E]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions E]
    (J : A ⥤ B) (S : A ⥤ D) (T : B ⥤ E) (J' : D ⥤ E) (Z : C ⥤ F)
    (R : B ⥤ C) (Q : E ⥤ F)
    [J.Additive] [S.Additive] [T.Additive] [J'.Additive] [Z.Additive]
    [R.Additive] [Q.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
    [PreservesFiniteLimits Z] [PreservesFiniteColimits Z]
    (e : J ⋙ T ≅ S ⋙ J')
    (d : R.rightDerivedFunctorPlus ⋙ Z.mapDerivedCategoryPlus ≅
      T.mapDerivedCategoryPlus ⋙ Q.rightDerivedFunctorPlus)
    (K : _root_.DerivedCategory.Plus A) :
    let ep := (Functor.mapDerivedCategoryPlusCompIso J T).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso e ≪≫ Functor.mapDerivedCategoryPlusCompIso S J'
    let cp := Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft J.mapDerivedCategoryPlus d ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ep Q.rightDerivedFunctorPlus ≪≫
      Functor.associator _ _ _
    let jq := Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft J'.mapDerivedCategoryPlus Q.rightDerivedFunctorPlusCompatibility ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight J'.mapDerivedCategoryPlusCompatibility Q.rightDerivedFunctor ≪≫
      Functor.associator _ _ _
    let jr := Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft J.mapDerivedCategoryPlus R.rightDerivedFunctorPlusCompatibility ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight J.mapDerivedCategoryPlusCompatibility R.rightDerivedFunctor ≪≫
      Functor.associator _ _ _
    let di := Functor.isoWhiskerRight R.rightDerivedFunctorPlusCompatibility.symm
        Z.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft R.rightDerivedFunctorPlus Z.mapDerivedCategoryPlusCompatibility.symm ≪≫
      Functor.isoWhiskerRight d _root_.DerivedCategory.Plus.ι ≪≫
      Functor.isoWhiskerLeft T.mapDerivedCategoryPlus Q.rightDerivedFunctorPlusCompatibility ≪≫
      Functor.isoWhiskerRight T.mapDerivedCategoryPlusCompatibility Q.rightDerivedFunctor
    let canonical := (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight S.mapDerivedCategoryPlusCompatibility.symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft S.mapDerivedCategoryPlus jq.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight cp.symm _root_.DerivedCategory.Plus.ι ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (J.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus)
        Z.mapDerivedCategoryPlusCompatibility ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight jr Z.mapDerivedCategory ≪≫
      Functor.associator _ _ _
    let fixed := Functor.isoWhiskerLeft _root_.DerivedCategory.Plus.ι
        ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (Functor.mapDerivedCategorySquareIso e.symm)
            Q.rightDerivedFunctor ≪≫
          Functor.associator _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight J.mapDerivedCategoryPlusCompatibility.symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft J.mapDerivedCategoryPlus di.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight J.mapDerivedCategoryPlusCompatibility
        (R.rightDerivedFunctor ⋙ Z.mapDerivedCategory) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _root_.DerivedCategory.Plus.ι (Functor.associator _ _ _).symm
    canonical.hom.app K = fixed.hom.app K := by
  dsimp only
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.map_comp, Functor.comp_map, Category.assoc]
  dsimp only [Functor.comp_obj, Functor.mapDerivedCategoryPlus, ObjectProperty.lift]
  simp only [exactPlusCompatibility_hom, exactPlusCompatibility_inv,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  erw [← Q.rightDerivedFunctorPlusCompatibility.inv.naturality_assoc]
  dsimp only [Functor.comp_map]
  erw [← Q.rightDerivedFunctorPlusCompatibility.inv.naturality_assoc]
  dsimp only [Functor.comp_map]
  erw [← Q.rightDerivedFunctorPlusCompatibility.inv.naturality_assoc]
  simp only [Functor.comp_map]
  erw [plusCompIso_inv S J' K, plusNatIso_inv e K,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app J T K]
  simp only [Functor.mapDerivedCategoryNatIso_symm]
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

private theorem compactComparison_eq_fixed
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {U X : Scheme.{u}} {f : U ⟶ X} (c : Compactification f)
    (K : _root_.DerivedCategory.Plus
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (compactSupportSiteComparison R c).hom.app K =
      (fixedCompactSupportComparisonIso R c).hom.app K := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  exact compactComparison_generic
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i)
    (comparisonUpperStar (ModuleCat.{u + 1} R) U)
    (comparisonUpperStar (ModuleCat.{u + 1} R) c.Z)
    (openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i)
    (comparisonUpperStar (ModuleCat.{u + 1} R) X)
    (Etale.lowerStar (ModuleCat.{u + 1} R) c.g)
    (lowerStar (ModuleCat.{u + 1} R) c.g)
    (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} R) c.i)
    (@asIso _ _ _ _ (fixedComparisonDirectImageMatePlus R c.g)
      (isIso_fixedComparisonDirectImageMatePlus R c.g)) K

private theorem iso_inverse_of_coordinate
    {C : Type*} [Category C] {A B D E : C}
    (i : A ≅ B) (s : A ≅ D) (t : D ≅ E) (e : E ≅ B)
    (h : i.inv ≫ s.hom ≫ t.hom = e.inv) :
    s.inv = t.hom ≫ e.hom ≫ i.inv := by
  apply (cancel_epi s.hom).1
  rw [s.hom_inv_id]
  have hh := congrArg (fun z ↦ i.hom ≫ z ≫ e.hom ≫ i.inv) h
  simpa only [Category.assoc, i.hom_inv_id_assoc, e.inv_hom_id_assoc,
    Category.id_comp, Category.comp_id, i.hom_inv_id] using hh.symm

private theorem compactOpenComparison_inv
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : _root_.DerivedCategory.Plus
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (compactSupportSiteComparison R (Compactification.ofIsOpenImmersion j)).inv.app K =
      (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.map
        ((Etale.rightDerivedLowerStarIdIso R X).hom.app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.obj
            K.obj)) ≫
      (unboundedOpenExtensionComparison R j).hom.app K.obj ≫
      (rightDerivedLowerStarId (ModuleCat.{u + 1} R) X).inv.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} R) U).mapDerivedCategory.obj K.obj)) := by
  have h := (unboundedOpenCounitSiteTransport R j).2.2.2 K
  rw [← compactComparison_eq_fixed] at h
  exact iso_inverse_of_coordinate
    ((rightDerivedLowerStarId (ModuleCat.{u + 1} R) X).app _)
    ((compactSupportSiteComparison R (Compactification.ofIsOpenImmersion j)).app K)
    ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.mapIso
      ((Etale.rightDerivedLowerStarIdIso R X).app _))
    ((unboundedOpenExtensionComparison R j).app K.obj) h

private theorem etaleOpenCoefficient_identity
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : Etale.DerivedCategoryModule A U) :
    Etale.OpenCounitFlatModels.coefficientMap φ j K =
      (Etale.properOpenCoefficientOpenIso φ j K).hom := by
  exact (Etale.OpenCounitFlatModels.coefficientMap_eq φ j K).trans
    (etaleOpenScalarIso_hom φ j K)


/-- The specified left scalar map commutes with the etale/pro-etale identifications.
The right side uses the etale summandwise open tensor map, not an arbitrary isomorphism.
Source: blueprint Locality, coefficient/site square
(blueprint: lem-sp-open-proetale-counit-scalar).

Proof: specialize lem-sp-et-proet-coefficient-compatibility to the compactification
j followed by the identity. Substitute the open identity comparisons and use the last
clause of lem-sp-unbounded-open-counit-site-transport to identify the fixed comparison
with e. Cancel the proper identity factors. The normalized etale open map is the
summandwise tensor map by the sum-normalization clause of the coefficient-compatibility
lemma. Its refinement square gives the same equation for every common refinement.
No inverse of a counit is taken. -/
theorem openProEtaleCounitScalar_site
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ell p : ℕ) [Fact ell.Prime] (_hp : 0 < p) (_hEll : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (n : ℕ) (_hA : (ell ^ n : A) = 0) (_hB : (ell ^ n : B) = 0)
    (φ : A →+* B) {U X : Scheme.{u}}
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (.of k))]
    (L : _root_.DerivedCategory
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (_hL : AdjunctionTransfer.etaleProperty (ULift.{u + 1, u} A) U L) :
    (liftedScalarExtension φ X).map
        ((unboundedOpenExtensionComparison (ULift.{u + 1, u} A) j).hom.app L) ≫
      (openCounitScalarMap φ j).app
        ((comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U).mapDerivedCategory.obj L) ≫
      (openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).mapDerivedCategory.map
          ((pbcComparisonReduction U (uliftRingHom φ)).hom.app L) =
    (pbcComparisonReduction X (uliftRingHom φ)).hom.app
        ((Etale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory.obj L) ≫
      (comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X).mapDerivedCategory.map
          (Etale.properOpenCoefficientOpenIso (uliftRingHom φ) j L).hom ≫
      (unboundedOpenExtensionComparison (ULift.{u + 1, u} B) j).hom.app
        ((Etale.scalarExtension (uliftRingHom φ) U).obj L) := by
  have hA : ∃ m : ℕ, ∀ x : A, (ell ^ m) • x = 0 := by
    refine ⟨n, fun x ↦ ?_⟩
    simp only [nsmul_eq_mul, Nat.cast_pow, _hA, zero_mul]
  have hB : ∃ m : ℕ, ∀ x : B, (ell ^ m) • x = 0 := by
    refine ⟨n, fun x ↦ ?_⟩
    simp only [nsmul_eq_mul, Nat.cast_pow, _hB, zero_mul]
  let LA := (AdjunctionTransfer.etaleToPlus (ULift.{u + 1, u} A) U).obj ⟨L, _hL⟩
  obtain ⟨hLB, _, _, hs⟩ := etaleProEtaleCoefficientCompatibility
    ell p _hp _hEll k hA hB φ j (Compactification.ofIsOpenImmersion j) LA _hL
  erw [compactOpenComparison_inv (ULift.{u + 1, u} A) j LA,
    compactOpenComparison_inv (ULift.{u + 1, u} B) j
      ⟨(Etale.scalarExtension (uliftRingHom φ) U).obj LA.obj, hLB⟩] at hs
  dsimp only [LA, AdjunctionTransfer.etaleToPlus, ObjectProperty.ιOfLE] at hs
  dsimp only [rightDerivedLowerShriekOfCompactification,
    Etale.rightDerivedLowerShriekOfCompactification, Compactification.ofIsOpenImmersion,
    Functor.comp_obj, Functor.comp_map, Functor.id_obj] at hs
  have h := congrArg (fun z ↦
    (liftedScalarExtension φ X).map
      ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.map
          ((Etale.rightDerivedLowerStarIdIso (ULift.{u + 1, u} A) X).inv.app
            ((Etale.openImmersionLowerShriek
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory.obj L))) ≫
      z ≫ (rightDerivedLowerStarId (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X).hom.app
        ((openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).mapDerivedCategory.obj
            ((comparisonUpperStar
              (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) U).mapDerivedCategory.obj
                ((Etale.scalarExtension (uliftRingHom φ) U).obj L)))) hs
  simp only [Functor.map_comp, Category.assoc] at h
  erw [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at h
  erw [(pbcComparisonReduction X (uliftRingHom φ)).hom.naturality_assoc] at h
  dsimp only [Functor.comp_map, Functor.id_obj] at h
  have he := etaleOpenCoefficient_identity (uliftRingHom φ) j L
  unfold Etale.OpenCounitFlatModels.coefficientMap at he
  erw [((rightDerivedLowerStarId
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X).hom).naturality] at h
  simp only [Iso.inv_hom_id_app] at h
  simp only [← Functor.map_comp_assoc] at h
  erw [he] at h
  dsimp only [Functor.id_map, Functor.id_obj] at h
  erw [Category.comp_id] at h
  simpa only [liftedScalarExtension, Etale.scalarExtension, Functor.comp_obj,
    Compactification.ofIsOpenImmersion, openCounitScalarMap, NatTrans.comp_app,
    Functor.whiskerLeft_app,
    Functor.whiskerRight_app, supportIdentity_hom, supportIdentity_inv,
    Functor.map_comp, Functor.id_map, Category.comp_id, Category.assoc] using h


/-- The scalar-counit equation and its right-mate formulation for the actual evaluation
adjunction. The isomorphism e has hom exactly the specified compact-support arrow b_j.
All objects and equalities are in the ambient categories; their full finite-Tor
subcategories retain the same morphisms and counit.

Source: blueprint Locality, retained Step 12, middle paragraph
(blueprint: lem-sp-open-proetale-counit-scalar).

Proof:
1. Apply lem-sp-etale-open-counit-flat-models for the finite-Tor domains and an
   etale origin. The balancing comparison counit and its open-unit normalization
   give the specified etale scalar-counit equation. Apply the unbounded transport
   theorem to identify the actual
   evaluation adjunctions through the specified e_R and r_R.
2. Specialize lem-sp-et-proet-coefficient-compatibility to the identity proper factor.
   Its square compares the named b_j, including the recorded intrinsic arrow.
   Specialize lem-sfb-etale-proetale-scalar-pullback-cube to j and invert its
   pullback comparisons; this identifies the named a_j, with no coefficient flatness.
3. Precompose the desired equation at C_X K by
   T_X(J_A(r_A(K)) composed with e_A(U_A K)) and postcompose by delta_X(K).
   Naturality of b, the two squares in step 2, and naturality of the B-counit
   turn the left side into comparison of the etale scalar-counit composite,
   followed by delta_X(J_A U_A K). The A-counit transport and naturality of delta
   turn the right side into comparison of T_X(v_A), followed by that same delta.
   The etale equation equates them. Cancel both invertible boundary maps.
   Naturality along the etale-origin isomorphism proves the equation at M.
4. The refinement equality of lem-sp-et-proet-coefficient-compatibility identifies
   every common-refinement version of b_j with this one. The transpose of the right
   mate of b_j inverse is b_j inverse followed by T_X(v_A). The equation just proved
   identifies it with J_B(a_j) followed by v_B. Injectivity of the actual adjunction
   Hom bijection gives the mate equality. Empty sums, zero complexes, identity opens
   and empty opens are included throughout; flat inputs do not require a flat ring map. -/
theorem openProEtaleCounitScalar
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ell p : ℕ) [Fact ell.Prime] (_hp : 0 < p) (_hEll : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (n : ℕ) (_hA : (ell ^ n : A) = 0) (_hB : (ell ^ n : B) = 0)
    (φ : A →+* B) {U X : Scheme.{u}}
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (.of k))]
    (M : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (_hBounded : _root_.DerivedCategory.TStructure.t.bounded M)
    (_hConstructible : ∀ q : ℤ, IsConstructibleProEtaleFixedModuleSheaf X
      (ULift.{u + 1, u} A) ((_root_.DerivedCategory.homologyFunctor _ q).obj M))
    (_hTor : ∃ a b : ℤ, HasFixedCoefficientProEtaleTorAmplitude X
      (ULift.{u + 1, u} A) M a b) :
    ∃ e : (liftedScalarExtension φ X).obj
          ((openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory.obj
              ((openImmersionRestriction
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory.obj M)) ≅
        (openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).mapDerivedCategory.obj
          ((liftedScalarExtension φ U).obj
            ((openImmersionRestriction
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory.obj M)),
      e.hom = (openCounitScalarMap φ j).app
        ((openImmersionRestriction
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory.obj M) ∧
      (e.hom ≫
        (openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).mapDerivedCategory.map
            ((openCounitRestrictionScalarIso φ j).hom.app M) ≫
        (unboundedOpenProEtaleAdjunction (ULift.{u + 1, u} B) j).counit.app
          ((liftedScalarExtension φ X).obj M) =
        (liftedScalarExtension φ X).map
          ((unboundedOpenProEtaleAdjunction (ULift.{u + 1, u} A) j).counit.app M)) ∧
      (unboundedOpenProEtaleAdjunction (ULift.{u + 1, u} B) j).homEquiv _ _
        (e.inv ≫ (liftedScalarExtension φ X).map
          ((unboundedOpenProEtaleAdjunction (ULift.{u + 1, u} A) j).counit.app M)) =
        (openCounitRestrictionScalarIso φ j).hom.app M := by
  let RA := ULift.{u + 1, u} A
  let RB := ULift.{u + 1, u} B
  let JA := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} RA) j).mapDerivedCategory
  let UA := (Etale.openImmersionRestriction (ModuleCat.{u + 1} RA) j).mapDerivedCategory
  let JB := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} RB) j).mapDerivedCategory
  let UB := (Etale.openImmersionRestriction (ModuleCat.{u + 1} RB) j).mapDerivedCategory
  let JP := (openImmersionLowerShriek (ModuleCat.{u + 1} RA) j).mapDerivedCategory
  let UP := (openImmersionRestriction (ModuleCat.{u + 1} RA) j).mapDerivedCategory
  let JQ := (openImmersionLowerShriek (ModuleCat.{u + 1} RB) j).mapDerivedCategory
  let UQ := (openImmersionRestriction (ModuleCat.{u + 1} RB) j).mapDerivedCategory
  let CA := (comparisonUpperStar (ModuleCat.{u + 1} RA) U).mapDerivedCategory
  let CX := (comparisonUpperStar (ModuleCat.{u + 1} RA) X).mapDerivedCategory
  let CB := (comparisonUpperStar (ModuleCat.{u + 1} RB) U).mapDerivedCategory
  let CY := (comparisonUpperStar (ModuleCat.{u + 1} RB) X).mapDerivedCategory
  let TE := Etale.scalarExtension (uliftRingHom φ) U
  let TX := Etale.scalarExtension (uliftRingHom φ) X
  let TP := liftedScalarExtension φ U
  let TQ := liftedScalarExtension φ X
  let b := openCounitScalarMap φ j
  let a := (openCounitRestrictionScalarIso φ j).hom
  let vA := (unboundedOpenEtaleAdjunction RA j).counit
  let vB := (unboundedOpenEtaleAdjunction RB j).counit
  let vP := (unboundedOpenProEtaleAdjunction RA j).counit
  let vQ := (unboundedOpenProEtaleAdjunction RB j).counit
  have hA : ∃ m : ℕ, ∀ x : RA, (ell ^ m) • x = 0 := by
    refine ⟨n, fun x ↦ ?_⟩
    rw [nsmul_eq_mul]
    apply ULift.ext
    change ((ell ^ n : ℕ) : A) * x.down = 0
    rw [Nat.cast_pow, _hA, zero_mul]
  have hB : ∃ m : ℕ, ∀ x : RB, (ell ^ m) • x = 0 := by
    refine ⟨n, fun x ↦ ?_⟩
    rw [nsmul_eq_mul]
    apply ULift.ext
    change ((ell ^ n : ℕ) : B) * x.down = 0
    rw [Nat.cast_pow, _hB, zero_mul]
  have hD := (Etale.OpenCounitFlatModels.etaleOpenCounitFlatModels
    ell p _hp _hEll k j hA hB (uliftRingHom φ)).1
  unfold Etale.OpenCounitFlatModels.openDomains at hD
  obtain ⟨K, hK, ⟨t⟩⟩ := (hD.2.2.2.2 X (by simp)).1 M
    ⟨_hBounded, _hConstructible, _hTor⟩
  have hL : AdjunctionTransfer.etaleProperty RA U (UA.obj K) := by
    have h := exceptional_etaleProperty RA U _ (hD.1 K hK)
    let e := (Functor.mapDerivedCategoryNatIso
      (Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} RA) j)).app K
    refine ⟨?_, (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e h.2⟩
    obtain ⟨hc, a, b, hab, hv⟩ := h.1
    refine ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 ?_,
      a, b, hab, fun q hq ↦ (hv q hq).of_iso
        ((_root_.DerivedCategory.homologyFunctor _ q).mapIso e).symm⟩
    have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc q)
    exact Scheme.IsConstructibleSheaf.of_iso
      ((_root_.DerivedCategory.homologyFunctor _ q).mapIso e)
  have hs := openProEtaleCounitScalar_site ell p _hp _hEll k n _hA _hB φ j
    (UA.obj K) hL
  have hi : IsIso (b.app (CA.obj (UA.obj K))) := by
    have : IsIso
        (TQ.map ((unboundedOpenExtensionComparison RA j).hom.app (UA.obj K)) ≫
          b.app (CA.obj (UA.obj K)) ≫
            JQ.map ((pbcComparisonReduction U (uliftRingHom φ)).hom.app (UA.obj K))) := by
      rw [hs]
      infer_instance
    have := IsIso.of_isIso_comp_left
      (TQ.map ((unboundedOpenExtensionComparison RA j).hom.app (UA.obj K)))
      (b.app (CA.obj (UA.obj K)) ≫
        JQ.map ((pbcComparisonReduction U (uliftRingHom φ)).hom.app (UA.obj K)))
    exact IsIso.of_isIso_comp_right
      (b.app (CA.obj (UA.obj K)))
      (JQ.map ((pbcComparisonReduction U (uliftRingHom φ)).hom.app (UA.obj K)))
  have h : b.app (UP.obj (CX.obj K)) ≫ JQ.map (a.app (CX.obj K)) ≫
      vQ.app (TQ.obj (CX.obj K)) = TQ.map (vP.app (CX.obj K)) := by
    exact counitSquare_paste JA UA JB UB JP UP JQ UQ CA CX CB CY TE TX TP TQ
      (unboundedOpenExtensionComparison RA j) (unboundedOpenExtensionComparison RB j)
      (unboundedOpenRestrictionComparison RA j) (unboundedOpenRestrictionComparison RB j)
      (pbcComparisonReduction U (uliftRingHom φ))
      (pbcComparisonReduction X (uliftRingHom φ)) vA vB vP vQ b a K
      (Etale.properOpenCoefficientOpenIso (uliftRingHom φ) j (UA.obj K)).hom
      ((etaleRestrictionScalarIso (uliftRingHom φ) j).hom.app K)
      ((unboundedOpenCounitSiteTransport RA j).2.1 K)
      ((unboundedOpenCounitSiteTransport RB j).2.1 (TX.obj K)) hs
      (restrictionScalarSquare φ j K) (etaleScalarCounitRestriction (uliftRingHom φ) j K)
  have hm : b.app (UP.obj M) ≫ JQ.map (a.app M) ≫ vQ.app (TQ.obj M) =
      TQ.map (vP.app M) :=
    counitEquation_of_iso JP UP JQ UQ TP TQ b a vP vQ t h
  let r := (unboundedOpenRestrictionComparison RA j).app K ≪≫ UP.mapIso t
  have hn := b.naturality r.hom
  dsimp only [Functor.comp_map] at hn
  have : IsIso (TQ.map (JP.map r.hom) ≫ b.app (UP.obj M)) := by
    rw [hn]
    change IsIso (b.app (CA.obj (UA.obj K)) ≫ (JQ.mapIso (TP.mapIso r)).hom)
    infer_instance
  have : IsIso (b.app (UP.obj M)) := IsIso.of_isIso_comp_left
    (TQ.map (JP.map r.hom)) (b.app (UP.obj M))
  refine ⟨asIso (b.app (UP.obj M)), rfl, hm, ?_⟩
  exact mate_of_counitEquation (unboundedOpenProEtaleAdjunction RA j)
    (unboundedOpenProEtaleAdjunction RB j) TP TQ a M _ hm


/-- The actual open adjunction, including its counit and transpose, is the transport
through the specified open site comparison. Its identity-proper-factor normalization
is the fixed compact-support comparison. As the subcategories are full, these Hom
identities identify their adjunction and actual counit after restriction to Dctf.
Source: blueprint Locality, transport of the ordinary open sum adjunction
(blueprint: lem-sp-open-proetale-counit-scalar).

Proof: apply lem-sp-unbounded-open-counit-site-transport in coefficient R. Its counit
identity is the first clause, its Hom identity is the second. The last clause of that
lemma identifies the comparison with def-sp-fixed-compact-support-comparison after
removing the identity proper factor. The finite-Tor equivalences of
 det-sp-et-proet-adjunction-transfer and the etale origins furnished by
lem-sp-etale-open-counit-flat-models restrict these actual Hom bijections to Dctf.
Essential surjectivity covers every pro-etale object; the identity transpose recovers
its actual evaluation counit. This applies separately over A and over B. -/
theorem openProEtaleCounitScalar_transport
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : _root_.DerivedCategory.Plus
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)))
    (_hF : AdjunctionTransfer.etaleProperty R U F.obj)
    (H : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))
    (_hH : AdjunctionTransfer.etaleProperty R X H) :
    ((unboundedOpenExtensionComparison R j).hom.app
        ((Etale.openImmersionRestriction (ModuleCat.{u + 1} R) j).mapDerivedCategory.obj H) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.map
        ((unboundedOpenRestrictionComparison R j).hom.app H) ≫
      (unboundedOpenProEtaleAdjunction R j).counit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.obj H) =
      (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.map
        ((unboundedOpenEtaleAdjunction R j).counit.app H)) ∧
    (∀ (f : (Etale.openImmersionLowerShriek
      (ModuleCat.{u + 1} R) j).mapDerivedCategory.obj F.obj ⟶ H),
      (unboundedOpenProEtaleAdjunction R j).homEquiv _ _
        ((unboundedOpenExtensionComparison R j).inv.app F.obj ≫
          (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.map f) =
      (comparisonUpperStar (ModuleCat.{u + 1} R) U).mapDerivedCategory.map
        ((unboundedOpenEtaleAdjunction R j).homEquiv F.obj H f) ≫
          (unboundedOpenRestrictionComparison R j).hom.app H) ∧
    ((rightDerivedLowerStarId (ModuleCat.{u + 1} R) X).inv.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} R) U).mapDerivedCategory.obj F.obj)) ≫
      (fixedCompactSupportComparisonIso R (Compactification.ofIsOpenImmersion j)).hom.app F ≫
      (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.map
        ((Etale.rightDerivedLowerStarIdIso R X).hom.app
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} R) j).mapDerivedCategory.obj F.obj)) =
      (unboundedOpenExtensionComparison R j).inv.app F.obj) := by
  exact ⟨(unboundedOpenCounitSiteTransport R j).2.1 H,
    (unboundedOpenCounitSiteTransport R j).2.2.1 F.obj H,
    (unboundedOpenCounitSiteTransport R j).2.2.2 F⟩

end AlgebraicGeometry.ProEtale
