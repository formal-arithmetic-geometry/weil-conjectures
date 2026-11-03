/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedMorphismSheafComparison
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCompactScalarSquare
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.RecordedOpenScalarNormalization
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.RecordedRestrictionNormalization
public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonNormalization
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor

/-! # Finite coefficient site transport for the intrinsic compact-support comparison

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-reduction,
`sk-lem-sp-reduction-exceptional.proof.md`, Charts
(blueprint: lem-sp-finite-ctf-site-coefficient-square).

The ambient functors and the coefficient arrow are the recorded intrinsic
`scalarExtensionFunctor`, `reductionCompactSupport`, and `reductionDirectImageComparison`.
Etale presentations use the existing ULift coefficient and sfIntrinsicDerivedEquivalence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

/-- The finite site presentation used by this statement, built from the live comparison
functor and the canonical intrinsic realization.
Source: Stacks 099R and 00YV
(blueprint: lem-sp-finite-ctf-site-coefficient-square). -/
def finiteCtfSite (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).mapDerivedCategory ⋙
    (sfIntrinsicDerivedEquivalence T A).functor

/-- Identity-on-sections identification of the two ordinary direct images.
Source: Stacks 03D1, adjunction triangle identity
(blueprint: lem-sp-finite-ctf-site-coefficient-square). -/
def finiteCtfDirectImageIso (A : Type u) [CommRing A]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    directImageConstantPush A p ≅ proEtaleConstantDerivedDirectImage p A :=
  Functor.rightDerivedFunctorNatIso
    (SheafOfModules.pushforwardCongr
      (congrArg (fun g : proEtaleConstantRing Y A ⟶
          (proEtaleSheafDirectImage p CommRingCat.{u + 1}).obj
            (proEtaleConstantRing Z A) ↦
        (sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map g)
        ((proEtaleSheafAdjunction p CommRingCat.{u + 1}).homEquiv _ _
          |>.apply_symm_apply (proEtaleCoefficientDirectImageMap p A))))

-- Import the proved elementary helper by its private numerical name, as in
-- the library's other `import all` users; no source declaration is copied.

/-- Sectionwise identity between realization and coefficient restriction.
The data come from the existing unique linear lift of the identity of abelian sheaves.
Source: Stacks 00YV and 03DA, `realization_restrict_existsUnique`
(blueprint: lem-sp-finite-ctf-site-coefficient-square). -/
@[no_expose] def finiteCtfRealizationRestriction {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T : Scheme.{u}) :
    (sfIntrinsicModuleEquivalence T B).functor ⋙
      proEtaleCoefficientRestrictScalars T φ ≅
      Sheaf.restrictScalars.{u + 1, u, u + 1} (ProEt.topology T)
        (RingHom.ulift.{u + 1, u + 1, u, u} φ) ⋙
          (sfIntrinsicModuleEquivalence T A).functor := by
  let φ' : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B :=
    RingHom.ulift.{u + 1, u + 1, u, u} φ
  let δ := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom φ'))
  refine (finiteCtfRestrictionData (ProEt.topology T) _ _
    (ProEtale.finiteCoefficientIntrinsicScalarMap T A)
    (ProEtale.finiteCoefficientIntrinsicScalarMap T B) φ' δ ?_).exists.choose
  exact (congrArg (fun q ↦ Functor.whiskerRight q
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
      (toSheafify_naturality (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).map (CommRingCat.ofHom φ')))).symm

/-- Exact descent of the sectionwise restriction identity in intrinsic coordinates.
Source: Stacks 03D2 and 06YY
(blueprint: lem-sp-finite-ctf-site-coefficient-square). -/
def finiteCtfSiteRestrictionIso {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T : Scheme.{u}) :
    finiteCtfSite B T ⋙ scalarRestriction φ T ≅
      Sheaf.derivedRestrictScalars.{u} T.smallEtaleTopology
        (RingHom.ulift.{u + 1, u + 1, u, u} φ) ⋙ finiteCtfSite A T :=
  by
  let CA := (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).mapDerivedCategory
  let CB := (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T).mapDerivedCategory
  let EA := (sfIntrinsicDerivedEquivalence T A).functor
  let EB := (sfIntrinsicDerivedEquivalence T B).functor
  let Up := @Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T)
    (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance
    (RingHom.ulift.{u + 1, u + 1, u, u} φ)
  let Ue := Sheaf.derivedRestrictScalars.{u} T.smallEtaleTopology
    (RingHom.ulift.{u + 1, u + 1, u, u} φ)
  let eR : (sfIntrinsicModuleEquivalence T B).functor ⋙
      proEtaleCoefficientRestrictScalars T φ ≅
      Sheaf.restrictScalars.{u + 1, u, u + 1} (ProEt.topology T)
        (RingHom.ulift.{u + 1, u + 1, u, u} φ) ⋙
          (sfIntrinsicModuleEquivalence T A).functor :=
    finiteCtfRealizationRestriction φ T
  let e : EB ⋙ scalarRestriction φ T ≅ Up ⋙ EA :=
    (Functor.mapDerivedCategoryCompIso (sfIntrinsicModuleEquivalence T B).functor
      (proEtaleCoefficientRestrictScalars T φ)).symm ≪≫
      Functor.mapDerivedCategoryNatIso eR ≪≫
      Functor.mapDerivedCategoryCompIso
        (Sheaf.restrictScalars.{u + 1, u, u + 1} (ProEt.topology T)
          (RingHom.ulift.{u + 1, u + 1, u, u} φ))
        (sfIntrinsicModuleEquivalence T A).functor
  exact Functor.associator CB EB (scalarRestriction φ T) ≪≫
    Functor.isoWhiskerLeft CB e ≪≫
    (Functor.associator CB Up EA).symm ≪≫
    Functor.isoWhiskerRight
      (comparisonRestrictScalarsIso T (ULift.{u + 1, u} A)
        (RingHom.ulift.{u + 1, u + 1, u, u} φ)).symm EA ≪≫
    Functor.associator Ue CA EA

/-- The coefficient/site tensor map, defined as the mate of exact restriction.
Source: Stacks 07A4, 0G7E; the scalar specialization of the canonical ringed-topos
comparison (blueprint: lem-sp-finite-ctf-site-coefficient-square). -/
def finiteCtfSiteScalarMap {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T : Scheme.{u}) :
    finiteCtfSite A T ⋙ scalarExtensionFunctor φ T ⟶
      Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) T ⋙
        finiteCtfSite B T :=
  ((mateEquiv
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars.{u} T.smallEtaleTopology
        (RingHom.ulift.{u + 1, u + 1, u, u} φ)))
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) φ))).symm
      (TwoSquare.mk _ _ _ _ (finiteCtfSiteRestrictionIso φ T).inv)).natTrans

private theorem finiteCtfMateOfEquivalences
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (e : C ≌ E) (e' : D ≌ F)
    (β : R₁ ⋙ e.functor ≅ e'.functor ⋙ R₂) :
    IsIso (((mateEquiv a₁ a₂).symm β.hom).natTrans) := by
  let α := (mateEquiv a₁ a₂).symm β.hom
  have hm : mateEquiv a₁ a₂ α = β.hom := Equiv.apply_symm_apply _ _
  have h := iterated_mateEquiv_conjugateEquiv a₁ a₂ e.toAdjunction e'.toAdjunction α
  rw [hm] at h
  have hi : IsIso ((mateEquiv e'.toAdjunction e.toAdjunction β.hom).natTrans) := by
    dsimp only [mateEquiv, Equiv.coe_fn_mk]
    infer_instance
  have : IsIso (conjugateEquiv (a₁.comp e'.toAdjunction)
      (e.toAdjunction.comp a₂) α.natTrans) := h ▸ hi
  exact conjugateEquiv_of_iso (a₁.comp e'.toAdjunction)
    (e.toAdjunction.comp a₂) α.natTrans

private theorem finiteCtfRestrictionSheafNormalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u}) :
    comparisonRestrictScalarsSheafIso T A φ =
      (CoefficientScalarRepresentatives.comparisonRestriction T φ).symm := by
  let a₁ := (Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology φ).comp
    (comparisonAdjunction (ModuleCat.{u + 1} A) T)
  let a₂ := (comparisonAdjunction (ModuleCat.{u + 1} B) T).comp
    (Sheaf.restrictCoextendScalarsAdj (ProEt.topology T) φ)
  have he (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) :
      (a₁.leftAdjointUniq a₂).hom.app M = comparisonRestrictScalarsMap T A φ M := by
    apply (a₁.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    change a₂.unit.app M =
      (Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology φ).homEquiv _ _
        ((comparisonAdjunction (ModuleCat.{u + 1} A) T).homEquiv _ _
          (comparisonRestrictScalarsMap T A φ M))
    rw [comparisonRestrictScalarsMap, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    dsimp only [a₂]
    rw [Adjunction.comp_unit_app]
    exact (Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology φ).unit.naturality
      ((comparisonAdjunction (ModuleCat.{u + 1} B) T).unit.app M)
  apply Iso.ext
  apply NatTrans.ext
  funext M
  change comparisonRestrictScalarsMap T A φ M = (a₂.leftAdjointUniq a₁).inv.app M
  rw [Adjunction.leftAdjointUniq_inv_app, he]

private theorem finiteCtfRestrictionNormalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u}) :
    comparisonRestrictScalarsIso T A φ =
      (CoefficientScalarRepresentatives.derivedComparisonRestriction T φ).symm := by
  unfold comparisonRestrictScalarsIso
    CoefficientScalarRepresentatives.derivedComparisonRestriction
    Functor.mapDerivedCategorySquareIso
  rw [finiteCtfRestrictionSheafNormalization]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Functor.mapDerivedCategoryNatIso_symm, Iso.symm_inv, Category.assoc]

private theorem finiteCtfMatePastingIsIso
    {C D E F G H : Type*}
    [Category C] [Category D] [Category E] [Category F] [Category G] [Category H]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    {L₃ : G ⥤ H} {R₃ : H ⥤ G}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    {F₁ : C ⥤ E} {G₁ : D ⥤ F} {F₂ : E ⥤ G} {G₂ : F ⥤ H}
    (τ₁ : R₁ ⋙ F₁ ⟶ G₁ ⋙ R₂) (τ₂ : R₂ ⋙ F₂ ⟶ G₂ ⋙ R₃)
    [IsIso (((mateEquiv a₁ a₂).symm τ₁).natTrans)]
    [IsIso (((mateEquiv a₂ a₃).symm τ₂).natTrans)] :
    IsIso (((mateEquiv a₁ a₃).symm
      (TwoSquare.vComp τ₁ τ₂)).natTrans) := by
  let α₁ := (mateEquiv a₁ a₂).symm τ₁
  let α₂ := (mateEquiv a₂ a₃).symm τ₂
  have h := mateEquiv_vcomp a₁ a₂ a₃ α₁ α₂
  simp only [α₁, α₂, Equiv.apply_symm_apply] at h
  rw [← h, Equiv.symm_apply_apply]
  dsimp only [TwoSquare.hComp]
  infer_instance

/-- The canonical scalar specialization of the recorded tensor comparison is invertible.
Source: Stacks 07A4 and 0G7E; def-sp-coefficient-scalar-representatives,
`CoefficientScalarRepresentatives.comparisonMap_isIso`
(blueprint: lem-sp-finite-ctf-site-coefficient-square).
Proof: the inverse restriction square defining finiteCtfSiteRestrictionIso is the
vertical pasting of two squares. The first is the exact restriction/site comparison
with ULift coefficients; by uniqueness of the left adjoint of the two composite
restriction/comparison right adjoints it equals the inverse of
CoefficientScalarRepresentatives.derivedComparisonRestriction, so its inverse mate
is the proved scalar/site comparison comparisonMap, invertible on K-flat
representatives (Stacks 07A4). The second is the intrinsic realization restriction
square; both horizontal sides are equivalences, so by the iterated mate/conjugate
identity its inverse mate is invertible. The mate of a vertical pasting is the
horizontal composite of the two mates, hence invertible. This map is
finiteCtfSiteScalarMap by definition. No flatness of B is used. -/
theorem finiteCtfSiteScalarMap_isIso {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T : Scheme.{u}) :
    IsIso (finiteCtfSiteScalarMap φ T) := by
  let ψ := RingHom.ulift.{u + 1, u + 1, u, u} φ
  let a₁ := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars.{u} T.smallEtaleTopology ψ)
  let a₂ := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars.{u} (ProEt.topology T) ψ)
  let a₃ := proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) φ)
  let e : (sfIntrinsicDerivedEquivalence T B).functor ⋙ scalarRestriction φ T ≅
      Sheaf.derivedRestrictScalars.{u} (ProEt.topology T) ψ ⋙
        (sfIntrinsicDerivedEquivalence T A).functor :=
    (Functor.mapDerivedCategoryCompIso (sfIntrinsicModuleEquivalence T B).functor
      (proEtaleCoefficientRestrictScalars T φ)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (finiteCtfRealizationRestriction φ T) ≪≫
      Functor.mapDerivedCategoryCompIso
        (Sheaf.restrictScalars.{u + 1, u, u + 1} (ProEt.topology T) ψ)
        (sfIntrinsicModuleEquivalence T A).functor
  let τ₁ := (comparisonRestrictScalarsIso T (ULift.{u + 1, u} A) ψ).hom
  let τ₂ := e.inv
  have : IsIso (((mateEquiv a₁ a₂).symm τ₁).natTrans) := by
    dsimp only [τ₁]
    rw [finiteCtfRestrictionNormalization]
    exact CoefficientScalarRepresentatives.comparisonMap_isIso T ψ
  have : IsIso (((mateEquiv a₂ a₃).symm τ₂).natTrans) :=
    finiteCtfMateOfEquivalences a₂ a₃ (sfIntrinsicDerivedEquivalence T A)
      (sfIntrinsicDerivedEquivalence T B) e.symm
  have h := finiteCtfMatePastingIsIso a₁ a₂ a₃ τ₁ τ₂
  have he : (finiteCtfSiteRestrictionIso φ T).inv =
      (TwoSquare.vComp τ₁ τ₂).natTrans := by
    apply NatTrans.ext
    funext L
    simp [finiteCtfSiteRestrictionIso, TwoSquare.vComp, τ₁, τ₂, e, ψ]
  unfold finiteCtfSiteScalarMap
  rw [he]
  exact h

/-- The canonical tensor comparison in intrinsic finite-site coordinates.
Its map is the explicit restriction mate, not a chosen natural isomorphism.
Source: Stacks 07A4 (blueprint: lem-sp-finite-ctf-site-coefficient-square). -/
def finiteCtfSiteScalarIso {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T : Scheme.{u}) :
    finiteCtfSite A T ⋙ scalarExtensionFunctor φ T ≅
      Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) T ⋙
        finiteCtfSite B T :=
  haveI := finiteCtfSiteScalarMap_isIso φ T
  asIso (finiteCtfSiteScalarMap φ T)

private theorem finiteCtfRealizationRestriction_eq
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    finiteCtfRealizationRestriction φ T = sfRealizationRestriction T φ := by
  rfl

private theorem finiteCtfDirectImagePresentation_eq
    (A : Type u) [CommRing A] [Finite A] {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    Functor.isoWhiskerLeft (sfIntrinsicDerivedEquivalence Z A).functor
        (finiteCtfDirectImageIso A p) ≪≫ sfIntrinsicDerivedDirectImageComparison p A =
      CoefficientCompatibility.directImagePresentation A p := by
  unfold CoefficientCompatibility.directImagePresentation
  rw [finiteCtfDirectImageNormalization]
  rfl

private theorem finiteCtfScalarPresentation_mate
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    ((mateEquiv
      (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars.{u} (ProEt.topology T)
          (RingHom.ulift.{u + 1, u + 1, u, u} φ)))
      (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) φ))).symm
      (Functor.mapDerivedCategorySquareIso (sfRealizationRestriction T φ)).inv).natTrans =
        (CoefficientCompatibility.scalarPresentation φ T).hom := by
  let a := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars.{u} (ProEt.topology T) (RingHom.ulift.{u + 1, u + 1, u, u} φ))
  let b := proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) φ)
  let e := Functor.mapDerivedCategorySquareIso (sfRealizationRestriction T φ)
  ext M
  apply (b.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit]
  have h := unit_mateEquiv_symm a b e.inv M
  have hn := finiteCtfScalarPresentationUnit
    (sfIntrinsicDerivedEquivalence T A) (sfIntrinsicDerivedEquivalence T B) a b e M
  exact h.symm.trans hn

private theorem finiteCtfSiteScalarMap_normalization
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    finiteCtfSiteScalarMap φ T =
      Functor.whiskerLeft
          (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).mapDerivedCategory
          (CoefficientCompatibility.scalarPresentation φ T).hom ≫
        Functor.whiskerRight
          (CoefficientScalarRepresentatives.comparisonIso T
            (RingHom.ulift.{u + 1, u + 1, u, u} φ)).hom
          (sfIntrinsicDerivedEquivalence T B).functor := by
  let a₁ := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars.{u} T.smallEtaleTopology (RingHom.ulift.{u + 1, u + 1, u, u} φ))
  let a₂ := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars.{u} (ProEt.topology T) (RingHom.ulift.{u + 1, u + 1, u, u} φ))
  let a₃ := proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) φ)
  let τ₁ := (comparisonRestrictScalarsIso T (ULift.{u + 1, u} A)
    (RingHom.ulift.{u + 1, u + 1, u, u} φ)).hom
  let τ₂ := (Functor.mapDerivedCategorySquareIso (sfRealizationRestriction T φ)).inv
  have he : (finiteCtfSiteRestrictionIso φ T).inv =
      (TwoSquare.vComp τ₁ τ₂).natTrans := by
    ext L
    simp [finiteCtfSiteRestrictionIso, TwoSquare.vComp, τ₁, τ₂,
      finiteCtfRealizationRestriction_eq]
    rfl
  unfold finiteCtfSiteScalarMap
  rw [he]
  have h := mateEquiv_vcomp a₁ a₂ a₃
    ((mateEquiv a₁ a₂).symm τ₁) ((mateEquiv a₂ a₃).symm τ₂)
  simp only [Equiv.apply_symm_apply] at h
  change ((mateEquiv a₁ a₃).symm (TwoSquare.vComp τ₁ τ₂)).natTrans = _
  have hm := congrArg (mateEquiv a₁ a₃).symm h
  simp only [Equiv.symm_apply_apply] at hm
  rw [← hm]
  dsimp only [TwoSquare.hComp]
  rw [show ((mateEquiv a₂ a₃).symm τ₂).natTrans =
    (CoefficientCompatibility.scalarPresentation φ T).hom from
      finiteCtfScalarPresentation_mate φ T]
  dsimp only [τ₁]
  rw [finiteCtfRestrictionNormalization]
  ext M
  (simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, CoefficientScalarRepresentatives.comparisonIso, asIso_hom,
    CoefficientScalarRepresentatives.comparisonMap, Iso.symm_hom]; rfl)

private theorem finiteCtfSiteScalarIso_normalization
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u})
    (L : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) T) :
    (finiteCtfSiteScalarIso φ T).hom.app L =
      (CoefficientCompatibility.scalarPresentation φ T).hom.app
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
            T).mapDerivedCategory.obj L) ≫
        (sfIntrinsicDerivedEquivalence T B).functor.map
          ((CoefficientScalarRepresentatives.comparisonIso T
            (RingHom.ulift.{u + 1, u + 1, u, u} φ)).hom.app L) := by
  simp only [finiteCtfSiteScalarIso, asIso_hom, finiteCtfSiteScalarMap_normalization,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]

/-- The compact-support presentation, formed from the live intrinsic extension-by-zero,
its normalized direct-image comparison, and the fixed proper/open comparison.
Source: Stacks 00YV, 03D1 and 07A5
(blueprint: lem-sp-finite-ctf-site-coefficient-square). -/
def finiteCtfCompactSupportFixedIso (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) :
    (sfIntrinsicDerivedEquivalence X A).functor ⋙ reductionCompactSupport A j p ≅
      (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        j).mapDerivedCategory ⋙
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor ⋙
          (sfIntrinsicDerivedEquivalence Y A).functor :=
  Functor.isoWhiskerLeft (sfIntrinsicDerivedEquivalence X A).functor
      (Functor.isoWhiskerLeft (sfIntrinsicExtensionByZero j A).mapDerivedCategory
        (finiteCtfDirectImageIso A p)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          ((sfIntrinsicModuleEquivalence X A).funInvIdAssoc
            (ProEtale.openImmersionLowerShriek
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
                (sfIntrinsicModuleEquivalence Z A).functor)) ≪≫
        Functor.mapDerivedCategoryCompIso _ _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        j).mapDerivedCategory (sfIntrinsicDerivedDirectImageComparison p A)

private theorem finiteCtfCompactSupportFixedIso_normalization
    (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p] :
    finiteCtfCompactSupportFixedIso A j p =
      CoefficientCompatibility.supportPresentation A
        (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p)) := by
  unfold CoefficientCompatibility.supportPresentation
  rw [← finiteCtfDirectImagePresentation_eq]
  ext L
  simp only [finiteCtfCompactSupportFixedIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  rw [← reassoc_of% (finiteCtfDirectImageIso A p).hom.naturality]
  rfl

/-- The counit-normalized proper mate followed by exact open comparison,
transported through the canonical intrinsic realization.
Source: Stacks 09A6 and 09AF
(blueprint: lem-sp-finite-ctf-site-coefficient-square). -/
def finiteCtfSiteCompactSupportIso (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y)
    [IsProper p] :
    DerivedCategory.Plus.ι ⋙ finiteCtfSite A X ⋙ reductionCompactSupport A j p ≅
      DerivedCategory.Plus.ι ⋙
        Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p)) ⋙
            finiteCtfSite A Y := by
  let c : Compactification (j ≫ p) :=
    ⟨Z, p, j, rfl, inferInstance, inferInstance⟩
  exact
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (finiteCtfCompactSupportFixedIso A j p) ≪≫
        (Functor.associator _ _ _).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (fixedCompactSupportComparisonIso (ULift.{u + 1, u} A) c) _ ≪≫
    Functor.associator _ _ _

private theorem finiteCtfSiteCompactSupportIso_hom
    (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (r : Z ⟶ Y) [IsProper r]
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (finiteCtfSiteCompactSupportIso A j r).hom.app L =
      (CoefficientCompatibility.supportPresentation A
        (⟨Z, r, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ r))).hom.app
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
            X).mapDerivedCategory.obj L.obj) ≫
        (sfIntrinsicDerivedEquivalence Y A).functor.map
          ((compactSupportSiteComparison (ULift.{u + 1, u} A)
            (⟨Z, r, j, rfl, inferInstance, inferInstance⟩ :
              Compactification (j ≫ r))).hom.app L) := by
  simp only [finiteCtfSiteCompactSupportIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    finiteCtfCompactSupportFixedIso_normalization, compactSupportComparisonNormalization]
  erw [Category.id_comp]
  rfl

private theorem finiteCtfSiteCompactSupportIso_inv
    (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (r : Z ⟶ Y) [IsProper r]
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (finiteCtfSiteCompactSupportIso A j r).inv.app L =
      (sfIntrinsicDerivedEquivalence Y A).functor.map
          ((compactSupportSiteComparison (ULift.{u + 1, u} A)
            (⟨Z, r, j, rfl, inferInstance, inferInstance⟩ :
              Compactification (j ≫ r))).inv.app L) ≫
        (CoefficientCompatibility.supportPresentation A
          (⟨Z, r, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ r))).inv.app
            ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
              X).mapDerivedCategory.obj L.obj) := by
  apply (cancel_epi ((finiteCtfSiteCompactSupportIso A j r).hom.app L)).mp
  rw [Iso.hom_inv_id_app, finiteCtfSiteCompactSupportIso_hom]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [(sfIntrinsicDerivedEquivalence Y A).functor.map_id]
  simp only [Category.id_comp, Iso.hom_inv_id_app]
  rfl

private theorem finiteCtfSiteScalarIso_inv_normalization
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u})
    (L : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) T) :
    (finiteCtfSiteScalarIso φ T).inv.app L =
      (sfIntrinsicDerivedEquivalence T B).functor.map
          ((CoefficientScalarRepresentatives.comparisonIso T
            (RingHom.ulift.{u + 1, u + 1, u, u} φ)).inv.app L) ≫
        (CoefficientCompatibility.scalarPresentation φ T).inv.app
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
            T).mapDerivedCategory.obj L) := by
  apply (cancel_epi ((finiteCtfSiteScalarIso φ T).hom.app L)).mp
  rw [Iso.hom_inv_id_app, finiteCtfSiteScalarIso_normalization]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [(sfIntrinsicDerivedEquivalence T B).functor.map_id]
  simp only [Category.id_comp, Iso.hom_inv_id_app]
  rfl

/-- The five-factor finite-site coefficient computation: inverse compact-support
comparison, tensor comparison at Y, etale coefficient mate, compact-support
comparison at B, and inverse tensor comparison at X.
Source: latest blueprint Charts; Stacks 07A4, 09A6 and 09AF
(blueprint: lem-sp-finite-ctf-site-coefficient-square). -/
def finiteCtfSiteCoefficientTransport
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z Y : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] (r : Z ⟶ Y) [IsProper r]
    (L : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) X)
    (hL : _root_.DerivedCategory.TStructure.t.plus L)
    (hLB : _root_.DerivedCategory.TStructure.t.plus
      ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj L)) :
    (scalarExtensionFunctor φ Y).obj
        ((reductionCompactSupport A j r).obj ((finiteCtfSite A X).obj L)) ⟶
      (reductionCompactSupport B j r).obj
        ((scalarExtensionFunctor φ X).obj ((finiteCtfSite A X).obj L)) :=
  (scalarExtensionFunctor φ Y).map
      ((finiteCtfSiteCompactSupportIso A j r).hom.app ⟨L, hL⟩) ≫
    (finiteCtfSiteScalarIso φ Y).hom.app _ ≫
    (finiteCtfSite B Y).map
      ((Etale.compactScalarMap (RingHom.ulift.{u + 1, u + 1, u, u} φ)
        (⟨Z, r, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ r))).app L) ≫
    (finiteCtfSiteCompactSupportIso B j r).inv.app
      ⟨(Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj L, hLB⟩ ≫
    (reductionCompactSupport B j r).map ((finiteCtfSiteScalarIso φ X).inv.app L)

private theorem finiteCtfScalar_plus
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u})
    (L : Etale.DerivedCategoryModule A X)
    (hL : Etale.DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} A) X L) :
    _root_.DerivedCategory.TStructure.t.plus ((Etale.scalarExtension φ X).obj L) := by
  obtain ⟨a, b, ht⟩ := hL
  refine ⟨a, (_root_.DerivedCategory.isGE_iff _ a).mpr fun i hi ↦ ?_⟩
  apply Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    (Sheaf.restrictScalars X.smallEtaleTopology φ)
  exact ((_root_.DerivedCategory.isGE_iff _ a).mp
    (ht (Etale.scalarCoefficientSheaf φ X)).1 i hi).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ i).mapIso
        ((Etale.scalarTensorIso φ X).app L))

/-- Finite-site computation agrees with the specified intrinsic pro-etale proper/open
coefficient map, for every etale presentation and naturally in the intrinsic input.
Source: latest blueprint, part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
`sk-lem-sp-reduction-exceptional.proof.md`, Charts
(blueprint: lem-sp-finite-ctf-site-coefficient-square).

Proof: (1) The finite-ctf site equivalence, followed by sfIntrinsicDerivedEquivalence,
gives etale presentations with ULift coefficients. The common Tor interval of L,
tested on the degree-zero B-module sheaf, bounds its scalar extension L_B. Thus
both displayed lower-bound witnesses exist, without flatness or finite projective
dimension of B. Exact open extension preserves their lower bounds. Properness
makes r qcqs. (2) The proper site comparison is the counit-normalized mate and is
invertible at these bounded-below inputs; the exact open comparison is invertible.
Their existing composite is finiteCtfSiteCompactSupportIso in the reverse direction.
Its realization factors are fixed by sfIntrinsicDerivedEquivalence and the uniquely
section-normalized direct-image comparison, so they introduce no arbitrary map.
(3) Express the inverse open site and scalar-balancing maps by their open-unit
adjuncts. (4) The normalized scalar/site/pullback cube identifies those adjuncts;
injectivity of the B-linear open adjunction gives the open square. (5) The proper
scalar/site mate equation applies at j_!L and its bounded-below scalar extension.
The intrinsic proper scalar map in reductionDirectImageComparison is exactly the
B-linear transpose of extension of the A-counit. The existing realization and site
comparisons preserve that counit normalization. (6) Paste the proper and open
squares. Naturality of the proper mate and open balancing gives T_Y(c_A), then
b(C_X L), then F_B(delta_X), equal to delta_Y, C_Y(beta), then c_B. (7) Invert only
c_A and delta_X and conjugate by the given eta. This yields the five-factor formula
for the actual reductionDirectImageComparison at M. All presentations equal this
same morphism, proving independence. Naturality of the actual ambient natural
transformation gives the final equation. Proof irrelevance removes any dependence
on the two lower-bound witnesses. -/
theorem finiteCtfSiteCoefficientSquare_statement
    (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (hchar : ringChar k ≠ ell)
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (r : Z ⟶ Y) [IsProper r] [r.IsOver (Spec (.of k))] (_hf : j ≫ r = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (_hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0) (φ : A →+* B)
    (M : proEtaleDerivedCategory X A) (_hM : spFiniteConstructibleTor X A M) :
    (∀ (L : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) X)
      (_hctf : Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X L)
      (η : (finiteCtfSite A X).obj L ≅ M),
      ∃ (hL : _root_.DerivedCategory.TStructure.t.plus L)
        (hLB : _root_.DerivedCategory.TStructure.t.plus
          ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj L)),
        IsIso ((finiteCtfSiteCompactSupportIso A j r).inv.app ⟨L, hL⟩) ∧
        IsIso ((finiteCtfSiteCompactSupportIso B j r).inv.app
          ⟨(Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj L, hLB⟩) ∧
        (reductionDirectImageComparison φ j r).app M =
          (scalarExtensionFunctor φ Y).map ((reductionCompactSupport A j r).map η.inv) ≫
          finiteCtfSiteCoefficientTransport φ j r L hL hLB ≫
          (reductionCompactSupport B j r).map ((scalarExtensionFunctor φ X).map η.hom)) ∧
    ∀ (M' : proEtaleDerivedCategory X A) (_hM' : spFiniteConstructibleTor X A M')
      (g : M ⟶ M'),
      (scalarExtensionFunctor φ Y).map ((reductionCompactSupport A j r).map g) ≫
          (reductionDirectImageComparison φ j r).app M' =
        (reductionDirectImageComparison φ j r).app M ≫
          (reductionCompactSupport B j r).map ((scalarExtensionFunctor φ X).map g) := by
  sorry

end AlgebraicGeometry
