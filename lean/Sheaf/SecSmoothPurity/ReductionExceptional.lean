/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.SecSmoothPurity.ReductionDirectImage
public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.Paper.FiniteLocalizingExceptionalPreservation
public import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction
public import Sheaf.Paper.ExceptionalCoefficientComparison
public import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data

public import Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization

public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
public import Sheaf.SecSmoothPurity.DirectImageScalarExchange

public import Sheaf.Paper.PurEtaleScalarMateProjection
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.EtaleLocalNormalForm
import Sheaf.AlgebraicGeometry.EtaleSumStalks
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import Sheaf.AlgebraicGeometry.ProjectiveLineTrace
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.Paper.EtaleProEtaleAdjunctionTransfer
import Sheaf.Paper.EtaleProEtaleCoefficientCompatibility
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.Paper.MateOpenRestriction
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.UnboundedLocalizingPullback
import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.CategoryTheory.Sites.ReductionFlat
import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange


/-!
# Exceptional inverse image and coefficient extension

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
`sk-lem-sp-reduction-exceptional.md` (blueprint: det-sp-reduction-exceptional).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Use the existing small-site witness at exactly the site's object universe.
This avoids an unconstrained lift universe in scalar restriction; it imposes no
additional size hypothesis. Source: Mathlib EssentiallySmallSelf; blueprint Step 4
(blueprint: det-sp-reduction-exceptional). -/
instance reductionProEtaleSmall (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0} _

/-- The two constant-coefficient direct images have the identical sectionwise scalar
map. This is an interface equality, not a choice of direct-image comparison.
Source: blueprint Step 4, constant-ring module identification
(blueprint: det-sp-reduction-exceptional).
Proof: unfold the two sectionwise pushforwards. The scalar map in the ringed formula
is the adjoint of c_A, whereas c_A is defined as the adjoint of the constant-section
map rho_A. The adjunction triangle identity identifies these scalar maps. Extensionality
of the pushforward functors gives their equality; applying rightDerivedFunctor gives
the displayed derived equality, with the existing K-injective localization. -/
theorem reductionConstantPush_eq (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    directImageConstantPush A f = proEtaleConstantDerivedDirectImage f A := by
  have h : proEtaleRingDirectImageMap f (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A) =
        proEtaleCoefficientDirectImageMap f A := by
    change (proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app _ ≫
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          (proEtaleCoefficientDirectImageMap f A) ≫
            (proEtaleSheafAdjunction f CommRingCat.{u + 1}).counit.app _) = _
    exact (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
      |>.apply_symm_apply (proEtaleCoefficientDirectImageMap f A)
  have hF : proEtaleRingModuleDirectImage f (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A) =
        proEtaleConstantModuleDirectImage f A := by
    unfold proEtaleRingModuleDirectImage proEtaleConstantModuleDirectImage
    rw [h]
  unfold directImageConstantPush proEtaleRingDerivedDirectImage
    proEtaleConstantDerivedDirectImage
  congr 1

/-- Canonical realization of the chosen compact-support functor, obtained by cancelling
the realization equivalences at the open factor and then using the specified
K-injective direct-image comparison. Every comparison is fixed on sections.
Source: blueprint Step 4 (blueprint: det-sp-reduction-exceptional). -/
def reductionCompactSupportFixedIso (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) :
    (sfIntrinsicDerivedEquivalence X A).functor ⋙ reductionCompactSupport A j p ≅
      (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        j).mapDerivedCategory ⋙
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor ⋙
          (sfIntrinsicDerivedEquivalence Y A).functor :=
  Functor.isoWhiskerLeft (sfIntrinsicDerivedEquivalence X A).functor
      (Functor.isoWhiskerLeft (sfIntrinsicExtensionByZero j A).mapDerivedCategory
        (eqToIso (reductionConstantPush_eq A p))) ≪≫
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

/-- Exact derived descent of the section-normalized restriction square.
Source: blueprint Step 4 (blueprint: det-sp-reduction-exceptional). -/
def reductionRealizationRestrict {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T : Scheme.{u}) :
    (sfIntrinsicDerivedEquivalence T B).functor ⋙
        pbcDerivedRestrict.{u} (proEtaleConstantRingMap (T := T) φ) ≅
      Sheaf.derivedRestrictScalars.{u} (ProEt.topology T) (RingHom.ulift.{u + 1, u + 1, u, u} φ) ⋙
        (sfIntrinsicDerivedEquivalence T A).functor :=
  (Functor.mapDerivedCategoryCompIso (sfIntrinsicModuleEquivalence T B).functor
    (pbcRestrict (proEtaleConstantRingMap (T := T) φ))).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (sfRealizationRestriction T φ) ≪≫
    Functor.mapDerivedCategoryCompIso
      (Sheaf.restrictScalars (ProEt.topology T)
        (RingHom.ulift.{u + 1, u + 1, u, u} φ))
      (sfIntrinsicModuleEquivalence T A).functor

/-- The actual scalar comparison is the left mate of the exact restriction square.
Source: blueprint Step 4 (blueprint: det-sp-reduction-exceptional). -/
def reductionRealizationScalarMap {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T : Scheme.{u}) :
    (sfIntrinsicDerivedEquivalence T A).functor ⋙ scalarExtensionFunctor φ T ⟶
      pbcFixedScalarExtension.{u} (ProEt.topology T) (RingHom.ulift.{u + 1, u + 1, u, u} φ) ⋙
        (sfIntrinsicDerivedEquivalence T B).functor :=
  ((mateEquiv
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars.{u} (ProEt.topology T) (RingHom.ulift.{u + 1, u + 1, u, u} φ)))
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) φ))).symm
      (TwoSquare.mk _ _ _ _ (reductionRealizationRestrict φ T).inv)).natTrans

-- With equivalences on both sides, precomposition by the inverse mate is the
-- composite of the two adjunction Hom equivalences and the realization equivalences.
private theorem reductionInverseMate_isIso
    {C : Type*} {D : Type*} {E : Type*} {F : Type*}
    [Category* C] [Category* D] [Category* E] [Category* F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : C ≌ E) (e' : D ≌ F)
    (β : R₁ ⋙ e.functor ≅ e'.functor ⋙ R₂) :
    IsIso (((mateEquiv adj₁ adj₂).symm β.hom).natTrans) := by
  let α := ((mateEquiv adj₁ adj₂).symm β.hom).natTrans
  have h (x : C) (y : D) :
      Function.Bijective (fun k : e'.functor.obj (L₁.obj x) ⟶ e'.functor.obj y ↦
        α.app x ≫ k) := by
    let q := e'.fullyFaithfulFunctor.homEquiv.symm.trans
      ((adj₁.homEquiv x y).trans
        (e.fullyFaithfulFunctor.homEquiv.trans
          ((Iso.homCongr (Iso.refl _) (β.app y)).trans
            (adj₂.homEquiv (e.functor.obj x) (e'.functor.obj y)).symm)))
    suffices heq : (fun k : e'.functor.obj (L₁.obj x) ⟶ e'.functor.obj y ↦
        α.app x ≫ k) = q from heq.symm ▸ q.bijective
    funext k
    dsimp [q, Iso.homCongr]
    simp only [Category.id_comp]
    rw [Adjunction.homEquiv_naturality_left_symm]
    simp only [α, mateEquiv_symm_apply, Adjunction.homEquiv_unit,
      Adjunction.homEquiv_counit, Functor.FullyFaithful.homEquiv_apply,
      Functor.FullyFaithful.homEquiv_symm_apply, Functor.map_comp, Category.assoc]
    dsimp only [TwoSquare.natTrans, TwoSquare.mk,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.comp_obj, Functor.comp_map, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.leftUnitor_inv_app,
      Functor.rightUnitor_hom_app]
    simp only [Category.id_comp, Category.assoc]
    congr 1
    have hn := β.hom.naturality (e'.fullyFaithfulFunctor.preimage k)
    change e.functor.map (R₁.map _) ≫ β.hom.app y =
      β.hom.app (L₁.obj x) ≫ R₂.map (e'.functor.map _) at hn
    conv_rhs =>
      rw [← L₂.map_comp_assoc, hn, L₂.map_comp, Category.assoc,
        adj₂.counit_naturality]
    simp
  have (x : C) : IsIso (α.app x) := by
    apply isIso_of_coyoneda_map_bijective
    intro z
    let q := Iso.homCongr (Iso.refl (e'.functor.obj (L₁.obj x))) (e'.counitIso.app z)
    let q' := Iso.homCongr (Iso.refl (L₂.obj (e.functor.obj x))) (e'.counitIso.app z)
    have hq := q'.bijective.comp ((h x (e'.inverse.obj z)).comp q.symm.bijective)
    simpa [q, q', Iso.homCongr, Function.comp_def, Category.assoc] using hq
  exact NatIso.isIso_of_isIso_app α

/-- The section-normalized scalar mate is invertible without flatness of phi.
Source: blueprint Step 4 (blueprint: det-sp-reduction-exceptional).
Proof: precomposition by the inverse mate is the composite of the two adjunction
Hom equivalences and the realization Hom equivalences. Naturality identifies this
composite with the specified mate. Essential surjectivity of the target realization
extends bijectivity to every test object, so the coyoneda criterion applies. -/
theorem reductionRealizationScalarMap_isIso {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T : Scheme.{u}) :
    IsIso (reductionRealizationScalarMap φ T) := by
  exact reductionInverseMate_isIso
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars.{u} (ProEt.topology T)
        (RingHom.ulift.{u + 1, u + 1, u, u} φ)))
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) φ))
    (sfIntrinsicDerivedEquivalence T A) (sfIntrinsicDerivedEquivalence T B)
    (reductionRealizationRestrict φ T).symm

/-- The canonical scalar comparison in the original intrinsic coefficient categories.
Source: blueprint Step 4 (blueprint: det-sp-reduction-exceptional). -/
def reductionRealizationScalarIso {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T : Scheme.{u}) :=
  @asIso _ _ _ _ (reductionRealizationScalarMap φ T)
    (reductionRealizationScalarMap_isIso φ T)

/-- The recorded finite-coefficient site inverse image followed by canonical realization.
This composite uses the recorded site and scalar-extension functors.
Source: blueprint Step 4 (blueprint: det-sp-reduction-exceptional). -/
def reductionSite (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).mapDerivedCategory ⋙
    (sfIntrinsicDerivedEquivalence T A).functor

/-- Canonical commutation of site inverse image with actual intrinsic scalar extension.
Source: blueprint Step 4 (blueprint: det-sp-reduction-exceptional). -/
def reductionSiteScalarIso {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T : Scheme.{u}) :
    reductionSite A T ⋙ scalarExtensionFunctor φ T ≅
      Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) T ⋙ reductionSite B T :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (reductionRealizationScalarIso φ T) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pbcComparisonReduction.{u} T (RingHom.ulift.{u + 1, u + 1, u, u} φ)) _
      ≪≫
    Functor.associator _ _ _

/-- The compact-support comparison in the original intrinsic categories, with its
proper counit mate and the recorded realization normalization.
Source: blueprint Step 4 (blueprint: det-sp-reduction-exceptional). -/
def reductionSiteCompactSupportIso (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y)
    [IsProper p] :
    DerivedCategory.Plus.ι ⋙ reductionSite A X ⋙ reductionCompactSupport A j p ≅
      DerivedCategory.Plus.ι ⋙
        Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p)) ⋙
            reductionSite A Y :=
  Functor.isoWhiskerLeft DerivedCategory.Plus.ι
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (reductionCompactSupportFixedIso A j p) ≪≫
      (Functor.associator _ _ _).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (fixedCompactSupportComparisonIso (ULift.{u + 1, u} A)
        (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p))) _ ≪≫
    Functor.associator _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem tateScalarIso_exists
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    ∃ e : (etaleSheafExtendScalars φ T).obj (finiteEtaleTateLine T N A hA) ≅
        finiteEtaleTateLine T N B hB,
      ∀ (W : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf N).obj.obj W),
        ((etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _ e.hom).hom.app W
            (finiteEtaleTateOneGenerator A N T hA W a z) =
          finiteEtaleTateOneGenerator B N T hB W (φ a) z := by
  let J := T.smallEtaleTopology
  let P := finiteEtaleMuModulePresheaf T N
  let r := finiteEtaleTwistScalar N A hA
  let s := finiteEtaleTwistScalar N B hB
  have hs : s = φ.comp r := Subsingleton.elim _ _
  let aA := (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} r).whiskerRight
    T.Etaleᵒᵖ |>.comp (sheafificationAdjunction J (ModuleCat.{u + 1} A))
  let aB := (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} s).whiskerRight
    T.Etaleᵒᵖ |>.comp (sheafificationAdjunction J (ModuleCat.{u + 1} B))
  let aφ := etaleSheafExtendScalarsAdjunction φ T
  let β : sheafToPresheaf J (ModuleCat.{u + 1} B) ⋙
      (Functor.whiskeringRight T.Etaleᵒᵖ _ _).obj (ModuleCat.restrictScalars s) ≅
      Sheaf.restrictScalars J φ ⋙ sheafToPresheaf J (ModuleCat.{u + 1} A) ⋙
        (Functor.whiskeringRight T.Etaleᵒᵖ _ _).obj (ModuleCat.restrictScalars r) :=
    NatIso.ofComponents (fun M ↦
      Functor.isoWhiskerLeft M.obj (ModuleCat.restrictScalarsComp' r φ s hs) ≪≫
        Functor.associator M.obj (ModuleCat.restrictScalars φ)
          (ModuleCat.restrictScalars r)) (by
        intro M K f
        ext W x
        rfl)
  let ab := aB.ofNatIsoRight β
  let e := (aA.comp aφ).leftAdjointUniq ab
  have he : (aA.comp aφ).homEquiv P _ (e.hom.app P) =
      ab.unit.app P := by
    exact Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ _
  let τ : finiteEtaleTateLine T N A hA ⟶
      (Sheaf.restrictScalars J φ).obj (finiteEtaleTateLine T N B hB) :=
    aφ.homEquiv _ _ (e.hom.app P)
  refine ⟨e.app P, ?_⟩
  intro W a z
  have hh := congrArg (fun f ↦ f.app W z) he
  change τ.hom.app W
    (finiteEtaleTateOneGenerator A N T hA W 1 z) =
    finiteEtaleTateOneGenerator B N T hB W 1 z at hh
  let := AddCommGroup.zmodModule (finiteEtaleMu_annihilated T N W)
  have ha : finiteEtaleTateOneGenerator A N T hA W a z =
      a • finiteEtaleTateOneGenerator A N T hA W 1 z := by
    unfold finiteEtaleTateOneGenerator
    have hx := ModuleCat.ExtendScalars.smul_tmul r a 1 (show P.obj W from z)
    simp only [mul_one] at hx
    have hh := congrArg (fun x ↦
      ((toSheafify J (P ⋙ ModuleCat.extendScalars r)).app W) x) hx
    exact hh.symm.trans (map_smul _ _ _)
  rw [ha, map_smul]
  erw [hh]
  change φ a • finiteEtaleTateOneGenerator B N T hB W 1 z = _
  unfold finiteEtaleTateOneGenerator
  have hx := ModuleCat.ExtendScalars.smul_tmul s (φ a) 1 (show P.obj W from z)
  simp only [mul_one] at hx
  have hh := congrArg (fun x ↦
    ((toSheafify J (P ⋙ ModuleCat.extendScalars s)).app W) x) hx
  exact (map_smul _ _ _).symm.trans hh


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The scalar map on the actual ordinary Tate line, fixed on every root generator.
Source: blueprint Step 6 (blueprint: det-sp-reduction-exceptional).
Proof: the balanced tensor presentation sends a tensor z to phi(a) tensor z. Balancing
and sheafification give a linear map. These generators locally generate the sheaf, so
naturality and the generator equation determine it uniquely, including for zero rings. -/
theorem reductionEtaleTateMap_existsUnique
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    ∃! τ : finiteEtaleTateLine T N A hA ⟶
        (Sheaf.restrictScalars T.smallEtaleTopology φ).obj (finiteEtaleTateLine T N B hB),
      ∀ (W : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf N).obj.obj W),
        τ.hom.app W (finiteEtaleTateOneGenerator A N T hA W a z) =
          finiteEtaleTateOneGenerator B N T hB W (φ a) z := by
  obtain ⟨e, he⟩ := tateScalarIso_exists φ T N hA hB
  let τ := (etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _ e.hom
  refine ⟨τ, he, ?_⟩
  intro τ' hτ'
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _
    ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj
      (finiteEtaleTateLine T N B hB)).property
  ext W x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a z => exact (hτ' W a z).trans (he W a z).symm
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The canonical generator-normalized ordinary Tate scalar map.
Source: blueprint Step 6 (blueprint: det-sp-reduction-exceptional). -/
def reductionEtaleTateMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    finiteEtaleTateLine T N A hA ⟶
      (Sheaf.restrictScalars T.smallEtaleTopology φ).obj (finiteEtaleTateLine T N B hB) :=
  (reductionEtaleTateMap_existsUnique φ T N hA hB).exists.choose

/-- Transpose a degree-zero map through an adjunction to an exact derived functor.
Source: blueprint Step 6, derived scalar adjunction
(blueprint: det-sp-reduction-exceptional). -/
def reductionSingleAdjointTranspose
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
    (U : D ⥤ C) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (L : DerivedCategory C ⥤ DerivedCategory D) (a : L ⊣ U.mapDerivedCategory)
    {M : C} {Q : D} (g : M ⟶ U.obj Q) :
    L.obj ((DerivedCategory.singleFunctor C 0).obj M) ⟶
      (DerivedCategory.singleFunctor D 0).obj Q :=
  (a.homEquiv _ _).symm
    ((DerivedCategory.singleFunctor C 0).map g ≫
      (U.mapDerivedCategorySingleFunctor 0).inv.app Q)

/-- The actual derived Tate scalar map: transpose the root-normalized map under
scalar extension/restriction. Source: blueprint Step 6
(blueprint: det-sp-reduction-exceptional). -/
def reductionEtaleTateExtensionMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    (Etale.scalarExtension φ T).obj (Etale.ordinaryFiniteLine A N hA T) ⟶
      Etale.ordinaryFiniteLine B N hB T :=
  show (Etale.scalarExtension φ T).obj
      ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateLine T N A hA)) ⟶
    (DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateLine T N B hB) from
  reductionSingleAdjointTranspose (Sheaf.restrictScalars T.smallEtaleTopology φ)
    (Etale.scalarExtension φ T)
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars.{u} T.smallEtaleTopology φ))
    (reductionEtaleTateMap φ T N hA hB)

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section SingleTranspose

universe v₁ v₂ u₁ u₂ w₁ w₂
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U] (a : E ⊣ U)
omit [HasDerivedCategory C] [HasDerivedCategory D]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U] in
private theorem singleUnit (M : C) :
    (a.mapHomologicalComplex (.up ℤ)).unit.app
        ((CochainComplex.singleFunctor C 0).obj M) ≫
      (U.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).hom.app M) ≫
      (HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app (E.obj M) =
    (CochainComplex.singleFunctor C 0).map (a.unit.app M) := by
  ext i
  by_cases hi : i = 0
  · subst i
    simp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Adjunction.mapHomologicalComplex_unit_app_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self, Functor.map_comp, Category.assoc]
    rw [← U.map_comp_assoc
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (E.obj M)).inv
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (E.obj M)).hom,
      Iso.inv_hom_id, U.map_id, Category.id_comp]
    exact (a.unit.naturality_assoc
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom _).symm
  · apply (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi).eq_of_src

private theorem singleTranspose
    (L : DerivedCategory C ⥤ DerivedCategory D) (ad : L ⊣ U.mapDerivedCategory)
    (M : C) (Q : D) (g : M ⟶ U.obj Q)
    (r : L.obj ((DerivedCategory.singleFunctor C 0).obj M) ⟶
      DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor C 0).obj M)))
    (hr : ad.homEquiv _ _ r =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app
        ((CochainComplex.singleFunctor C 0).obj M)) ≫
      U.mapDerivedCategoryFactors.inv.app _)
    [IsIso r] [IsIso ((a.homEquiv M Q).symm g)] :
    IsIso ((ad.homEquiv _ _).symm
      ((DerivedCategory.singleFunctor _ 0).map g ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app Q)) := by
  let f := (a.homEquiv M Q).symm g
  let d : L.obj ((DerivedCategory.singleFunctor C 0).obj M) ⟶
      (DerivedCategory.singleFunctor D 0).obj Q :=
    r ≫ DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).hom.app M) ≫
        (DerivedCategory.singleFunctor D 0).map f
  have hd : ad.homEquiv _ _ d =
      (DerivedCategory.singleFunctor C 0).map g ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app Q := by
    dsimp only [d]
    rw [ad.homEquiv_naturality_right, hr, Functor.map_comp]
    simp only [Category.assoc]
    have hu : (DerivedCategory.singleFunctor C 0).map g =
        (DerivedCategory.singleFunctor C 0).map (a.unit.app M) ≫
          (DerivedCategory.singleFunctor C 0).map (U.map f) := by
      rw [← Functor.map_comp]
      congr 1
      exact ((a.homEquiv M Q).apply_symm_apply g).symm
    rw [hu]
    have hn := (U.mapDerivedCategorySingleFunctor 0).inv.naturality f
    dsimp only [Functor.comp_map] at hn
    rw [Category.assoc, hn]
    simp only [← Category.assoc]
    apply congrArg (· ≫ U.mapDerivedCategory.map ((DerivedCategory.singleFunctor D 0).map f))
    apply (cancel_mono ((U.mapDerivedCategorySingleFunctor 0).hom.app (E.obj M))).mp
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [← U.mapDerivedCategoryFactors.inv.naturality_assoc]
    erw [U.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app]
    erw [Category.comp_id, ← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
    exact congrArg DerivedCategory.Q.map (singleUnit E U a M)
  have hh : (ad.homEquiv _ _).symm
      ((DerivedCategory.singleFunctor C 0).map g ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app Q) = d :=
    (ad.homEquiv _ _).symm_apply_eq.mpr hd.symm
  rw [hh]
  dsimp only [d]
  infer_instance

end SingleTranspose

universe v₁ v₂ u₁ u₂

private theorem flatRepresentative_isIso
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [IsGrothendieckAbelian.{v₁} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v₁} C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{v₂} D]
    [Abelian.HasKInjectiveResolutions D]
    (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U] [E.PreservesKFlatQuasiIso]
    (a : E ⊣ U) (L : DerivedCategory C ⥤ DerivedCategory D)
    (ac : L ⊣ U.mapDerivedCategory) (P : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) :
    IsIso ((ac.homEquiv _ _).symm
      (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        U.mapDerivedCategoryFactors.inv.app _)) := by
  let ad := a.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
  let e := ac.leftAdjointUniq ad
  let HP := (HomotopyCategory.quotient _ (.up ℤ)).obj P
  let q₀ := (DerivedCategory.quotientCompQhIso C).app P
  let q₁ := (DerivedCategory.quotientCompQhIso D).app
    ((E.mapHomologicalComplex (.up ℤ)).obj P)
  let q₂ := (DerivedCategory.quotientCompQhIso C).app
    ((U.mapHomologicalComplex (.up ℤ)).obj ((E.mapHomologicalComplex (.up ℤ)).obj P))
  let ε := E.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  have : IsIso ε := E.isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
  let d : E.leftDerivedFunctor.obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P) :=
    E.leftDerivedFunctor.mapIso q₀.symm ≪≫ asIso ε ≪≫ q₁
  have hfac := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ))
    E.leftDerivedFunctorCounit U.rightDerivedFunctorUnit
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  have ht : ad.unit.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      U.mapDerivedCategory.map (E.leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      U.mapDerivedCategoryFactorsh.hom.app
        ((E.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
    simp only [ad, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Category.assoc]
    erw [← U.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
    erw [← Category.assoc, hfac]
    have hβ := NatTrans.congr_app
      U.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
      ((E.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hβ
    rw [Category.assoc]
    erw [reassoc_of% hβ]
    simp only [Iso.inv_hom_id_app]
    erw [Category.comp_id]
  have hu := U.mapDerivedCategoryFactorsh_hom_app
    ((E.mapHomologicalComplex (.up ℤ)).obj P)
  have hquot : DerivedCategory.Qh.map
      ((U.mapHomotopyCategoryFactors (.up ℤ)).inv.app
        ((E.mapHomologicalComplex (.up ℤ)).obj P)) = 𝟙 _ := by
    change DerivedCategory.Qh.map (𝟙 _) = 𝟙 _
    exact DerivedCategory.Qh.map_id _
  rw [hquot] at hu
  erw [Category.comp_id] at hu
  have hu' : U.mapDerivedCategory.map q₁.hom ≫
      U.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
      U.mapDerivedCategoryFactorsh.hom.app
        ((E.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ q₂.hom := by
    have h := congrArg (fun z ↦ z ≫ q₂.hom) hu
    change U.mapDerivedCategoryFactorsh.hom.app
      ((E.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ q₂.hom =
      (U.mapDerivedCategory.map q₁.hom ≫
        U.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          q₂.inv) ≫ q₂.hom at h
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
    exact h.symm
  have hstd : ad.unit.app (DerivedCategory.Q.obj P) ≫ U.mapDerivedCategory.map d.hom =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj P) := by
    apply (cancel_mono (U.mapDerivedCategoryFactors.hom.app
      ((E.mapHomologicalComplex (.up ℤ)).obj P))).mp
    apply (cancel_epi q₀.hom).mp
    have hn := ad.unit.naturality q₀.hom
    change q₀.hom ≫ ad.unit.app (DerivedCategory.Q.obj P) =
      ad.unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
        U.mapDerivedCategory.map (E.leftDerivedFunctor.map q₀.hom) at hn
    have hq := DerivedCategory.quotientCompQhIso_hom_naturality
      ((a.mapHomologicalComplex (.up ℤ)).unit.app P)
    have hd : E.leftDerivedFunctor.map q₀.hom ≫ d.hom = ε ≫ q₁.hom := by
      change (E.leftDerivedFunctor.mapIso q₀).hom ≫
        ((E.leftDerivedFunctor.mapIso q₀).inv ≫ ε ≫ q₁.hom) = _
      exact Iso.hom_inv_id_assoc _ _
    have hdnat : q₀.hom ≫ ad.unit.app (DerivedCategory.Q.obj P) ≫
        U.mapDerivedCategory.map d.hom =
      ad.unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
        U.mapDerivedCategory.map ε ≫ U.mapDerivedCategory.map q₁.hom := by
      calc
        _ = ad.unit.app
            (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
          U.mapDerivedCategory.map (E.leftDerivedFunctor.map q₀.hom) ≫
            U.mapDerivedCategory.map d.hom := by
          simpa only [Category.assoc] using congrArg
            (fun z ↦ z ≫ U.mapDerivedCategory.map d.hom) hn
        _ = _ := by
          rw [← U.mapDerivedCategory.map_comp, hd, Functor.map_comp]
    calc
      _ = ad.unit.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
          U.mapDerivedCategory.map ε ≫ U.mapDerivedCategory.map q₁.hom ≫
            U.mapDerivedCategoryFactors.hom.app
              ((E.mapHomologicalComplex (.up ℤ)).obj P) := by
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫
          U.mapDerivedCategoryFactors.hom.app
            ((E.mapHomologicalComplex (.up ℤ)).obj P)) hdnat
      _ = ad.unit.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
          U.mapDerivedCategory.map ε ≫
          U.mapDerivedCategoryFactorsh.hom.app
            ((E.mapHomotopyCategory (.up ℤ)).obj
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ q₂.hom := by
        exact congrArg (fun z ↦ ad.unit.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
          U.mapDerivedCategory.map ε ≫ z) hu'
      _ = DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ q₂.hom := by
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ q₂.hom) ht
      _ = q₀.hom ≫ DerivedCategory.Q.map
          ((a.mapHomologicalComplex (.up ℤ)).unit.app P) := by
        erw [Adjunction.mapHomotopyCategory_unit_app_quotient]
        exact hq
      _ = _ := by
        simp only [Category.assoc, Iso.inv_hom_id_app]
        erw [Category.comp_id]
  let t := e.hom.app (DerivedCategory.Q.obj P) ≫ d.hom
  have ht : (ac.homEquiv _ _).symm
      (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        U.mapDerivedCategoryFactors.inv.app _) = t := by
    apply (ac.homEquiv _ _).injective
    rw [show t = e.hom.app _ ≫ d.hom from rfl, ac.homEquiv_naturality_right]
    erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [Equiv.apply_symm_apply]
    exact hstd.symm
  rw [ht]
  dsimp only [t]
  infer_instance

section ScalarFlat

private theorem scalarAdditive
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    (Sheaf.composeAndSheafify J
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)).Additive :=
  (Sheaf.adjunction J
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)).left_adjoint_additive

attribute [local instance] scalarAdditive

private def scalarTensorComparison
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ) ⋙
        Sheaf.restrictScalars J φ ≅ MonoidalCategory.tensorRight
          ((presheafToSheaf J (ModuleCat.{u + 1} R)).obj
            ((Functor.const Cᵒᵖ).obj
              ((ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).obj
                (ModuleCat.of S S)))) := by
  let E : Sheaf J (ModuleCat.{u + 1} R) ⥤ Sheaf J (ModuleCat.{u + 1} S) :=
    Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  let U := Sheaf.restrictScalars J φ
  let adj : E ⊣ U :=
    Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)
  have : E.Additive := adj.left_adjoint_additive
  let B := (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).obj (ModuleCat.of S S)
  let X := (Functor.const Cᵒᵖ).obj B
  let a := presheafToSheaf J (ModuleCat.{u + 1} R)
  let a' := presheafToSheaf J (ModuleCat.{u + 1} S)
  let F := sheafToPresheaf J (ModuleCat.{u + 1} R)
  let W := (Functor.whiskeringRight Cᵒᵖ _ _).obj
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  have : J.PreservesSheafification (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ) :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)
  exact (show E ⋙ U ≅ MonoidalCategory.tensorRight (a.obj X) from
    Functor.associator F (W ⋙ a') U ≪≫
      Functor.isoWhiskerLeft F (Functor.associator W a' U) ≪≫
      Functor.isoWhiskerLeft F (Functor.isoWhiskerLeft W
        (sheafComposeNatIso J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ)
          (sheafificationAdjunction J (ModuleCat.{u + 1} S))
          (sheafificationAdjunction J (ModuleCat.{u + 1} R))).symm) ≪≫
      Functor.isoWhiskerLeft F (Functor.associator W _ a).symm ≪≫
      Functor.isoWhiskerLeft F (Functor.isoWhiskerRight
        (Functor.whiskeringRightObjCompIso _ _ ≪≫
          (Functor.whiskeringRight _ _ _).mapIso
            (ModuleCat.extendScalarsCompRestrictScalarsIso.{u + 1} φ) ≪≫
          whiskeringRightTensorRightIso _) a) ≪≫
      Functor.isoWhiskerLeft F (Sheaf.presheafToSheafCompTensorRightIso X).symm ≪≫
      (Functor.associator F a (MonoidalCategory.tensorRight (a.obj X))).symm ≪≫
      Functor.isoWhiskerRight
        (asIso (sheafificationAdjunction J (ModuleCat.{u + 1} R)).counit)
        (MonoidalCategory.tensorRight (a.obj X)) ≪≫ Functor.leftUnitor _)

private theorem scalarPreservesKFlat
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    (Sheaf.composeAndSheafify J
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)).PreservesKFlatQuasiIso := by
  classical
  let E : Sheaf J (ModuleCat.{u + 1} R) ⥤ Sheaf J (ModuleCat.{u + 1} S) :=
    Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  let U := Sheaf.restrictScalars J φ
  let adj : E ⊣ U :=
    Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)
  have : E.Additive := adj.left_adjoint_additive
  let B := (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).obj (ModuleCat.of S S)
  let X := (Functor.const Cᵒᵖ).obj B
  let a := presheafToSheaf J (ModuleCat.{u + 1} R)
  let a' := presheafToSheaf J (ModuleCat.{u + 1} S)
  let F := sheafToPresheaf J (ModuleCat.{u + 1} R)
  let W := (Functor.whiskeringRight Cᵒᵖ _ _).obj
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  have : J.PreservesSheafification (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ) :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)
  let e := scalarTensorComparison J φ
  have hU : U.Faithful := inferInstance
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf J (ModuleCat.{u + 1} R)) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfSize.{0, 0} (Sheaf J (ModuleCat.{u + 1} R)) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  have : HasCountableCoproducts (Sheaf J (ModuleCat.{u + 1} R)) :=
    ⟨fun K _ ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete K)⟩
  change E.PreservesKFlatQuasiIso
  apply CategoryTheory.Functor.PreservesKFlatQuasiIso.mk'
  intro K hK hKa
  have ht := CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa (a.obj X)
  have hEU := ht.of_iso
    ((NatIso.mapHomologicalComplex e (.up ℤ)).app K).symm
  have hUK : ((U.mapHomologicalComplex (.up ℤ)).obj
      ((E.mapHomologicalComplex (.up ℤ)).obj K)).Acyclic :=
    hEU.of_iso ((CategoryTheory.Functor.mapHomologicalComplexCompIso
      (Iso.refl (E ⋙ U)) (.up ℤ)).app K)
  intro n
  exact (ShortComplex.exact_map_iff_of_faithful _ U).1 (hUK n)

private theorem singleFlatTranspose_isIso
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [IsGrothendieckAbelian.{v₁} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v₁} C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{v₂} D]
    [Abelian.HasKInjectiveResolutions D]
    (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U] [E.PreservesKFlatQuasiIso]
    (a : E ⊣ U) (L : DerivedCategory C ⥤ DerivedCategory D)
    (ac : L ⊣ U.mapDerivedCategory) (M : C) (Q : D)
    (g : M ⟶ U.obj Q) (hM : ObjectProperty.flat M)
    [IsIso ((a.homEquiv M Q).symm g)] :
    IsIso (reductionSingleAdjointTranspose U L ac g) := by
  let P := (CochainComplex.singleFunctor C 0).obj M
  have hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P :=
    (CochainComplex.kFlat_single_obj_iff_flat M 0).2 hM
  let r := (ac.homEquiv _ _).symm
    (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      U.mapDerivedCategoryFactors.inv.app _)
  have : IsIso r := flatRepresentative_isIso E U a L ac P hP
  apply singleTranspose E U a L ac M Q g r
  exact Equiv.apply_symm_apply _ _

private theorem reductionOrdinaryTateExtension_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    IsIso ((etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _ |>.symm
      (reductionEtaleTateMap φ T N hA hB)) := by
  obtain ⟨e, he⟩ := tateScalarIso_exists φ T N hA hB
  have hτ := (reductionEtaleTateMap_existsUnique φ T N hA hB).unique he
    (reductionEtaleTateMap_existsUnique φ T N hA hB).exists.choose_spec
  have hh : (etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _ e.hom =
      reductionEtaleTateMap φ T N hA hB := hτ
  rw [← hh, Equiv.symm_apply_apply]
  infer_instance

private theorem reductionTateLine_flat
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (N : ℕ) (hA : (N : A) = 0) (hT : IsUnit (N : Γ(T, ⊤))) :
    ObjectProperty.flat (finiteEtaleTateLine T N A hA) := by
  classical
  by_cases hN : 0 < N
  · obtain ⟨r, c, p, _⟩ := etaleFiniteTwistPullback A N hN hA
    apply ObjectProperty.flat_of_tensorIso
      (Y := finiteEtaleTateSheaf A N T hA (-1))
    exact p T hT 1 (-1)
  · have hz : N = 0 := Nat.eq_zero_of_not_pos hN
    have : IsEmpty T := ⟨fun t ↦ by
      have ht := hT.map (T.Γevaluation t).hom
      simp only [hz, Nat.cast_zero, map_zero] at ht
      exact not_isUnit_zero ht⟩
    exact ObjectProperty.flat_of_isZero (Etale.isZero_sheaf_of_isEmpty _)

/-- The generator-normalized derived Tate scalar map is invertible.
Source: blueprint Step 6 (blueprint: det-sp-reduction-exceptional).
Proof: N invertible makes the Tate line locally free of rank one. Its complex in degree
zero is therefore K-flat. Derived scalar extension is ordinary tensor on that complex,
and balancing identifies it with the B-line by the preceding generator formula. Its
adjunct is precisely the displayed map through the exact-restriction single comparison.
The adjunction bijection fixes this map uniquely. No flatness of phi is used. -/
theorem reductionEtaleTateExtensionMap_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) :
    IsIso (reductionEtaleTateExtensionMap φ T N hA hB) := by
  let E := etaleSheafExtendScalars φ T
  let U := Sheaf.restrictScalars T.smallEtaleTopology φ
  let a : E ⊣ U := etaleSheafExtendScalarsAdjunction φ T
  have : E.Additive := a.left_adjoint_additive
  have : E.PreservesKFlatQuasiIso := scalarPreservesKFlat T.smallEtaleTopology φ
  have : IsIso ((a.homEquiv _ _).symm (reductionEtaleTateMap φ T N hA hB)) :=
    reductionOrdinaryTateExtension_isIso φ T N hA hB
  exact singleFlatTranspose_isIso E U a (Etale.scalarExtension φ T)
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))
    _ _ (reductionEtaleTateMap φ T N hA hB) (reductionTateLine_flat A T N hA hT)

end ScalarFlat

/-- The root-normalized derived Tate scalar isomorphism, with the actual scalar mate
as its forward map. Source: blueprint Step 6 (blueprint: det-sp-reduction-exceptional). -/
def reductionEtaleTateIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) :
    (Etale.scalarExtension φ T).obj (Etale.ordinaryFiniteLine A N hA T) ≅
      Etale.ordinaryFiniteLine B N hB T :=
  @asIso _ _ _ _ (reductionEtaleTateExtensionMap φ T N hA hB)
    (reductionEtaleTateExtensionMap_isIso φ T N hA hB hT)

/-- Commute coefficient extension with one shifted ordinary Tate line.
Source: blueprint Steps 6--7 (blueprint: det-sp-reduction-exceptional). -/
def reductionEtaleShiftedLineIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) :
    (Etale.scalarExtension φ T).obj ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) ≅
      (Etale.ordinaryFiniteLine B N hB T)⟦(2 : ℤ)⟧ :=
  letI : (Etale.scalarExtension φ T).CommShift ℤ :=
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars.{u} T.smallEtaleTopology φ)).leftAdjointCommShift ℤ
  ((Etale.scalarExtension φ T).commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso (reductionEtaleTateIso φ T N hA hB hT)

/-- Canonical reassociation at one projective-line right functor. This uses the
published scalar tensorator, inverse-image balancing and root-normalized shifted line.
Source: blueprint Step 7 (blueprint: det-sp-reduction-exceptional). -/
def reductionEtaleP1ScalarIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (S : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (hS : IsUnit (N : Γ(S, ⊤))) (K : Etale.DerivedCategoryModule A S) :
    (Etale.scalarExtension φ (ProjectiveLine S)).obj
        ((Etale.ordinaryFiniteP1Right A N hA S).obj K) ≅
      (Etale.ordinaryFiniteP1Right B N hB S).obj ((Etale.scalarExtension φ S).obj K) :=
  (Etale.ExceptionalCoefficients.tensorIso φ (ProjectiveLine S)).app
      ((Etale.ordinaryFinitePullback A (ProjectiveLine S ↘ S)).obj K,
        (Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≪≫
    (Functor.uncurry.obj (Etale.ordinaryFiniteTensor B (ProjectiveLine S))).mapIso
      (Iso.prod ((Etale.scalarPullbackIso φ (ProjectiveLine S ↘ S)).symm.app K)
        (reductionEtaleShiftedLineIso φ (ProjectiveLine S) N hA hB
          (affineTraceProjectiveInvertible N S hS)))

/-- Canonical scalar reassociation for one affine coordinate, including open pullback.
Source: blueprint Step 10 (blueprint: det-sp-reduction-exceptional). -/
def reductionEtaleLineScalarIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (S : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (hS : IsUnit (N : Γ(S, ⊤))) (K : Etale.DerivedCategoryModule A S) :
    (Etale.scalarExtension φ (AffineSpace PUnit.{u + 1} S)).obj
        ((Etale.affineTraceLineRight A N hA S).obj K) ≅
      (Etale.affineTraceLineRight B N hB S).obj ((Etale.scalarExtension φ S).obj K) :=
  (Etale.scalarPullbackIso φ (ProjectiveLine.affineChart S)).symm.app _ ≪≫
    (Etale.ordinaryFinitePullback B (ProjectiveLine.affineChart S)).mapIso
      (reductionEtaleP1ScalarIso φ S N hA hB hS K)

/-- Ordered-coordinate scalar reassociation; the zero-coordinate map is the identity.
Source: blueprint Step 10 (blueprint: det-sp-reduction-exceptional). -/
def reductionEtaleAffineScalarIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (S : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) : (K : Etale.DerivedCategoryModule A S) →
    (Etale.scalarExtension φ (affineTraceTower S d)).obj
        ((Etale.affineTraceRight A N hA S d).obj K) ≅
      (Etale.affineTraceRight B N hB S d).obj ((Etale.scalarExtension φ S).obj K) :=
  Nat.rec (motive := fun n ↦ ∀ K : Etale.DerivedCategoryModule A S,
      (Etale.scalarExtension φ (affineTraceTower S n)).obj
          ((Etale.affineTraceRight A N hA S n).obj K) ≅
        (Etale.affineTraceRight B N hB S n).obj ((Etale.scalarExtension φ S).obj K))
    (fun _K ↦ Iso.refl _) (fun n ih K ↦
      reductionEtaleLineScalarIso φ (affineTraceTower S n) N hA hB
          (affineTraceInvertible N S hS n) ((Etale.affineTraceRight A N hA S n).obj K) ≪≫
        (Etale.affineTraceLineRight B N hB (affineTraceTower S n)).mapIso (ih K)) d

/-- Canonical chart reassociation in the source's ordered affine-space model.
Source: blueprint Steps 10--11 (blueprint: det-sp-reduction-exceptional). -/
def reductionEtaleChartScalarIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U S : Scheme.{u}} (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) (e : U ⟶ affineTraceTower S d)
    (K : Etale.DerivedCategoryModule A S) :
    (Etale.scalarExtension φ U).obj
        ((Etale.ordinaryFinitePullback A e).obj
          ((Etale.affineTraceRight A N hA S d).obj K)) ≅
      (Etale.ordinaryFinitePullback B e).obj
        ((Etale.affineTraceRight B N hB S d).obj ((Etale.scalarExtension φ S).obj K)) :=
  (Etale.scalarPullbackIso φ e).symm.app _ ≪≫
    (Etale.ordinaryFinitePullback B e).mapIso
      (reductionEtaleAffineScalarIso φ S N hA hB hS d K)

/-- The ordered affine-space left functor compared with a specified compactification.
Every factor is the published proper/open composition or common-refinement comparison.
The identity step uses the two exact identity functors, so no orientation is chosen.
Source: blueprint Steps 10--11 (blueprint: det-sp-reduction-exceptional). -/
def reductionEtaleAffineLeftIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) :
    (c : Compactification (affineTraceProjection S d)) →
    Etale.affineTraceLeft A S d ≅
      Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c :=
  Nat.rec (motive := fun n ↦ ∀ c : Compactification (affineTraceProjection S n),
      Etale.affineTraceLeft A S n ≅
        Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    (fun c ↦
      (Functor.isoWhiskerRight
          (Etale.mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S) _ ≪≫
        Functor.leftUnitor _ ≪≫ Etale.rightDerivedLowerStarIdIso A S).symm ≪≫
        Etale.rightDerivedLowerShriekOfCompactificationIso A
          (Compactification.ofIsProper (𝟙 S)) c)
    (fun n ih c ↦
      let cp := HasCompactification.compactification (affineTraceProjection S n)
      let ce := c.ofComp cp
      Functor.isoWhiskerRight
          (Etale.rightDerivedLowerShriekOfCompactificationIso A
            (affineTraceLineCompactification (affineTraceTower S n)) ce.restrict) _ ≪≫
        Functor.isoWhiskerLeft _ (ih cp) ≪≫
        Etale.rightDerivedLowerShriekOfCompactificationCompIso A cp ce ≪≫
        Etale.rightDerivedLowerShriekOfCompactificationIso A (cp.comp ce) c) d

/-- The chart right adjunction is literally sum/evaluation followed by the specified
ordered affine-space adjunction. The inverse-image model comparison is the canonical
exact-to-left-derived comparison.
Source: blueprint Steps 8--11 (blueprint: det-sp-reduction-exceptional). -/
def reductionEtaleChartAdjunction (A : Type (u + 1)) [CommRing A]
    (S : Scheme.{u}) [IsNoetherian S] (N : ℕ) (hA : (N : A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A N hA t T hT)
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    {U : Scheme.{u}} (e : U ⟶ affineTraceTower S d)
    [AlgebraicGeometry.Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ⋙
        Etale.affineTraceLeft A S d ⊣
      Etale.affineTraceRight A N hA S d ⋙ Etale.ordinaryFinitePullback A e :=
  ((Etale.derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance).ofNatIsoRight
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).symm).comp
      (Etale.affineTraceAdjunction A N hA t D S hS d)

/-- Canonical chart left comparison: graph-normalized sum extension, ordered affine
composition, common refinement, then inverse source-open comparison.
Source: blueprint Step 11 (blueprint: det-sp-reduction-exceptional). -/
def reductionEtaleChartLeftIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (M : Etale.EtaleCompactSupportNormalization A)
    {X S U : Scheme.{u}} [IsNoetherian X] [IsNoetherian S] [IsNoetherian U]
    (f : X ⟶ S) (i : U ⟶ X) [IsOpenImmersion i]
    (d : ℕ) (e : U ⟶ affineTraceTower S d) [AlgebraicGeometry.Etale e] [IsSeparated e]
    (he : i ≫ f = e ≫ affineTraceProjection S d)
    (cf : Compactification f) :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ⋙
        Etale.affineTraceLeft A S d ≅
      (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) i inferInstance).mapDerivedCategory ⋙
        Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf :=
  letI := affineTraceNoetherian S d
  let cp := HasCompactification.compactification (affineTraceProjection S d)
  let cg := HasCompactification.compactification (e ≫ affineTraceProjection S d)
  Functor.isoWhiskerLeft _ (reductionEtaleAffineLeftIso A S d cp) ≪≫
    Etale.etaleAmbientLeftComparison A M e (affineTraceProjection S d) cp cg ≪≫
    (Etale.etaleAmbientLeftComparison A M i f cf (cg.copy he)).symm

/-- The chart identification is the unique counit-preserving right-adjoint comparison
for the preceding left comparison. It is therefore normalized by actual affine trace
and summation over e, with no free scalar or arbitrary right-functor isomorphism.
Source: blueprint Steps 11--12 (blueprint: det-sp-reduction-exceptional). -/
def reductionEtaleChartRightIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (M : Etale.EtaleCompactSupportNormalization A)
    {X S U : Scheme.{u}} [IsNoetherian X] [IsNoetherian S] [IsNoetherian U]
    (f : X ⟶ S) (i : U ⟶ X) [IsOpenImmersion i]
    (d : ℕ) (e : U ⟶ affineTraceTower S d) [AlgebraicGeometry.Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e]
    (he : i ≫ f = e ≫ affineTraceProjection S d) (cf : Compactification f)
    (G : Etale.DerivedCategoryModule A S ⥤ Etale.DerivedCategoryModule A X)
    (adj : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf ⊣ G)
    (N : ℕ) (hA : (N : A) = 0) (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A N hA t T hT) (hS : IsUnit (N : Γ(S, ⊤))) :
    G ⋙ Etale.ordinaryFinitePullback A i ≅
      Etale.affineTraceRight A N hA S d ⋙ Etale.ordinaryFinitePullback A e :=
  (((Etale.derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) i inferInstance).ofNatIsoRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) i).symm).comp
        adj).rightAdjointUniq
    ((reductionEtaleChartAdjunction A S N hA t D hS d e).ofNatIsoLeft
      (reductionEtaleChartLeftIso A M f i d e he cf))

/-- Canonical realization/pullback comparison, preserving the actual pullback units.
Source: blueprint Step 4 (blueprint: det-sp-reduction-exceptional). -/
def reductionRealizationPullbackIso (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (i : U ⟶ X) :
    (sfIntrinsicDerivedEquivalence X A).functor ⋙ proEtaleConstantRingDerivedPullback A i ≅
      sfFixedDerivedPullback A i ⋙ (sfIntrinsicDerivedEquivalence U A).functor :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence X A).functor
          (openSquarePullbackModel A i) ≪≫
        (sfIntrinsicModuleEquivalence X A).funInvIdAssoc
          (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i ⋙
            (sfIntrinsicModuleEquivalence U A).functor)) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Exact site/pullback comparison, followed by canonical coefficient realization.
Source: blueprint Step 4 (blueprint: det-sp-reduction-exceptional). -/
def reductionSitePullbackIso (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (i : U ⟶ X) :
    reductionSite A X ⋙ proEtaleConstantRingDerivedPullback A i ≅
      Etale.ordinaryFinitePullback (ULift.{u + 1, u} A) i ⋙ reductionSite A U :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (reductionRealizationPullbackIso A i) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sfDerivedComparisonPullbackIso A i) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).symm _

/-- The actual compact-support functor restricted to its full Dctf subcategories.
The witness only certifies membership and changes neither objects nor morphisms.
Source: blueprint, constructible adjunction convention
(blueprint: det-sp-reduction-exceptional). -/
def reductionCtfCompactSupport (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y)
    (hF : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj)) :=
  (spFiniteConstructibleTor Y A).lift
    ((spFiniteConstructibleTor X A).ι ⋙ reductionCompactSupport A j p) hF

/-- Restrict the recorded scalar extension to full Dctf subcategories.
Source: blueprint, coefficient-extension convention
(blueprint: det-sp-reduction-exceptional). -/
def reductionCtfScalar {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T : Scheme.{u})
    (hT : ∀ K : spFiniteConstructibleTorCategory T A,
      spFiniteConstructibleTor T B ((scalarExtensionFunctor φ T).obj K.obj)) :=
  (spFiniteConstructibleTor T B).lift
    ((spFiniteConstructibleTor T A).ι ⋙ scalarExtensionFunctor φ T) hT

/-- The component of a Dctf comparison in the ambient intrinsic category.
The underlying arrow changes neither coefficient functor nor object.
Source: blueprint Step 2 (blueprint: det-sp-reduction-exceptional). -/
def reductionExceptionalComponent {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (X Y : Scheme.{u})
    (hSX : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj))
    (hSY : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj))
    (GA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (GB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B)
    (c : GA ⋙ reductionCtfScalar φ X hSX ⟶ reductionCtfScalar φ Y hSY ⋙ GB)
    (K : spFiniteConstructibleTorCategory Y A) :
    (scalarExtensionFunctor φ X).obj (GA.obj K).obj ⟶
      (GB.obj ((reductionCtfScalar φ Y hSY).obj K)).obj :=
  (c.app K).hom

/-- The precise transported counit equation in intrinsic coordinates.
Factoring this proposition keeps the realization record's projections small.
Source: blueprint Step 4 (blueprint: det-sp-reduction-exceptional). -/
def reductionRealizationCounitEquation (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    (hF : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj))
    (G : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (adj : reductionCtfCompactSupport A j p hF ⊣ G)
    (origin : spFiniteConstructibleTorCategory Y A ⥤
      Etale.DerivedCategoryModule (ULift.{u + 1, u} A) Y)
    (originIso : origin ⋙ reductionSite A Y ≅ (spFiniteConstructibleTor Y A).ι)
    (right : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) Y ⥤
      Etale.DerivedCategoryModule (ULift.{u + 1, u} A) X)
    (adjunction : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p)) ⊣ right)
    (right_plus : ∀ K, DerivedCategory.TStructure.t.plus (right.obj (origin.obj K)))
    (rightIso : G ⋙ (spFiniteConstructibleTor X A).ι ≅
      origin ⋙ right ⋙ reductionSite A X) : Prop :=
  ∀ K : spFiniteConstructibleTorCategory Y A,
    (reductionCompactSupport A j p).map (rightIso.hom.app K) ≫
      (reductionSiteCompactSupportIso A j p).hom.app
        ⟨right.obj (origin.obj K), right_plus K⟩ ≫
      (reductionSite A Y).map (adjunction.counit.app (origin.obj K)) ≫
      originIso.hom.app K = (adj.counit.app K).hom

/-- A constructible exceptional adjunction realized on the ordinary etale site.
The input origin and output comparison are natural isomorphisms. The final equation
fixes the output comparison by the actual compact-support and ordinary counits.
Thus neither a free map nor an ambient pro-etale adjunction is assumed.
Source: blueprint Steps 3--4 (blueprint: det-sp-reduction-exceptional). -/
structure ReductionExceptionalRealization (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    (hF : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj))
    (G : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (adj : reductionCtfCompactSupport A j p hF ⊣ G) where
  /-- An ordinary-etale origin of every Dctf input. -/
  origin : spFiniteConstructibleTorCategory Y A ⥤
    Etale.DerivedCategoryModule (ULift.{u + 1, u} A) Y
  /-- The origin is bounded constructible of finite Tor amplitude. -/
  origin_ctf : ∀ K, Etale.DerivedCategory.boundedConstructibleFiniteTor
    (ULift.{u + 1, u} A) Y (origin.obj K)
  /-- The origin recovers exactly the original intrinsic object. -/
  originIso : origin ⋙ reductionSite A Y ≅ (spFiniteConstructibleTor Y A).ι
  /-- The ordinary right adjoint for the identical fixed compactification. -/
  right : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) Y ⥤
    Etale.DerivedCategoryModule (ULift.{u + 1, u} A) X
  /-- Its actual ordinary-etale adjunction. -/
  adjunction : Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p)) ⊣ right
  /-- Its values on the origins lie in the bounded-below comparison domain. -/
  right_plus : ∀ K, DerivedCategory.TStructure.t.plus (right.obj (origin.obj K))
  /-- The exceptional output comparison. -/
  rightIso : G ⋙ (spFiniteConstructibleTor X A).ι ≅ origin ⋙ right ⋙ reductionSite A X
  /-- The output comparison retains the actual transported counit. -/
  counit : reductionRealizationCounitEquation A j p hF G adj
    origin originIso right adjunction right_plus rightIso

/-- The intrinsic chart identification, normalized by ordinary sum/evaluation and the
specified affine-space trace. All changes of sites, scalars and inverse image are the
canonical comparisons defined above. No orientation of a Tate line is chosen.
Source: blueprint Steps 4, 11--12 (blueprint: det-sp-reduction-exceptional). -/
def reductionIntrinsicChartIso (A : Type u) [CommRing A] [Finite A]
    {X Z Y U : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian U]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    (hF : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj))
    (G : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (adj : reductionCtfCompactSupport A j p hF ⊣ G)
    (R : ReductionExceptionalRealization A j p hF G adj)
    (M : Etale.EtaleCompactSupportNormalization (ULift.{u + 1, u} A))
    (i : U ⟶ X) [IsOpenImmersion i] (d : ℕ) (e : U ⟶ affineTraceTower Y d)
    [AlgebraicGeometry.Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (he : i ≫ (j ≫ p) = e ≫ affineTraceProjection Y d)
    (N : ℕ) (hA : (N : ULift.{u + 1, u} A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport (ULift.{u + 1, u} A) N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum (ULift.{u + 1, u} A) N hA t T hT)
    (hY : IsUnit (N : Γ(Y, ⊤))) (K : spFiniteConstructibleTorCategory Y A) :
    (proEtaleConstantRingDerivedPullback A i).obj (G.obj K).obj ≅
      (reductionSite A U).obj
        ((Etale.ordinaryFinitePullback (ULift.{u + 1, u} A) e).obj
          ((Etale.affineTraceRight (ULift.{u + 1, u} A) N hA Y d).obj (R.origin.obj K))) :=
  (proEtaleConstantRingDerivedPullback A i).mapIso (R.rightIso.app K) ≪≫
    (reductionSitePullbackIso A i).app _ ≪≫
    (reductionSite A U).mapIso
      ((reductionEtaleChartRightIso (ULift.{u + 1, u} A) M (j ≫ p) i d e he
        (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p))
        R.right R.adjunction N hA t D hY).app (R.origin.obj K))

/-- The normalized chart clause, expressed in ordinary-etale coordinates and transported
through the actual finite-coefficient comparison. `o` is fixed by its origin equation;
its only role is to identify the etale origin of K_B with the scalar-extended origin.
The second equation is the commuting square for j* c and the canonical ordered Tate
reassociation. The chart identifications are the counit-preserving definitions above.
Source: blueprint Steps 4, 10--12 (blueprint: det-sp-reduction-exceptional). -/
def ReductionExceptionalChartEquation
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ℓ : ℕ) (φ : A →+* B) {X Z Y : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    (d : ℕ)
    (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj))
    (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor Y B ((reductionCompactSupport B j p).obj M.obj))
    (hSX : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj))
    (hSY : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj))
    (GA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (GB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B)
    (adjA : reductionCtfCompactSupport A j p hFA ⊣ GA)
    (adjB : reductionCtfCompactSupport B j p hFB ⊣ GB)
    (RA : ReductionExceptionalRealization A j p hFA GA adjA)
    (RB : ReductionExceptionalRealization B j p hFB GB adjB)
    (c : GA ⋙ reductionCtfScalar φ X hSX ⟶ reductionCtfScalar φ Y hSY ⋙ GB) : Prop :=
  ∃ o : RA.origin ⋙ Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) Y ≅
      reductionCtfScalar φ Y hSY ⋙ RB.origin,
    (∀ K : spFiniteConstructibleTorCategory Y A,
      (reductionSite B Y).map (o.hom.app K) ≫
          RB.originIso.hom.app ((reductionCtfScalar φ Y hSY).obj K) =
        (reductionSiteScalarIso φ Y).inv.app (RA.origin.obj K) ≫
          (scalarExtensionFunctor φ Y).map (RA.originIso.hom.app K)) ∧
    ∀ (n : ℕ) (hnA : ((ℓ ^ n : ℕ) : ULift.{u + 1, u} A) = 0)
      (hnB : ((ℓ ^ n : ℕ) : ULift.{u + 1, u} B) = 0),
    ∃ hY : IsUnit ((ℓ ^ n : ℕ) : Γ(Y, ⊤)),
    ∀ (MA : Etale.EtaleCompactSupportNormalization (ULift.{u + 1, u} A))
      (MB : Etale.EtaleCompactSupportNormalization (ULift.{u + 1, u} B))
      (tA : Etale.OrdinaryFiniteTwistTransport (ULift.{u + 1, u} A) (ℓ ^ n) hnA)
      (DA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit ((ℓ ^ n : ℕ) : Γ(T, ⊤))),
        Etale.OrdinaryFiniteP1Datum (ULift.{u + 1, u} A) (ℓ ^ n) hnA tA T hT)
      (tB : Etale.OrdinaryFiniteTwistTransport (ULift.{u + 1, u} B) (ℓ ^ n) hnB)
      (DB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit ((ℓ ^ n : ℕ) : Γ(T, ⊤))),
        Etale.OrdinaryFiniteP1Datum (ULift.{u + 1, u} B) (ℓ ^ n) hnB tB T hT)
      (_ : IsNoetherian X) (_ : IsNoetherian Y)
      (U : Scheme.{u}) [IsNoetherian U] (i : U ⟶ X) [IsOpenImmersion i]
      (e : U ⟶ affineTraceTower Y d) [AlgebraicGeometry.Etale e] [IsSeparated e]
      [LocallyOfFiniteType e] [QuasiCompact e]
      (he : i ≫ (j ≫ p) = e ≫ affineTraceProjection Y d)
      (K : spFiniteConstructibleTorCategory Y A),
      (directImageScalarPullbackIso φ i).inv.app (GA.obj K).obj ≫
          (proEtaleConstantRingDerivedPullback B i).map
            (reductionExceptionalComponent φ X Y hSX hSY GA GB c K) ≫
          (reductionIntrinsicChartIso B j p hFB GB adjB RB MB i d e he
            (ℓ ^ n) hnB tB DB hY ((reductionCtfScalar φ Y hSY).obj K)).hom =
        (scalarExtensionFunctor φ U).map
            (reductionIntrinsicChartIso A j p hFA GA adjA RA MA i d e he
              (ℓ ^ n) hnA tA DA hY K).hom ≫
          (reductionSiteScalarIso φ U).hom.app _ ≫
          (reductionSite B U).map
            (reductionEtaleChartScalarIso (RingHom.ulift.{u + 1, u + 1, u, u} φ) (ℓ ^ n) hnA hnB hY
              d e
              (RA.origin.obj K)).hom ≫
          (reductionSite B U).map
            ((Etale.affineTraceRight (ULift.{u + 1, u} B) (ℓ ^ n) hnB Y d ⋙
              Etale.ordinaryFinitePullback (ULift.{u + 1, u} B) e).map (o.hom.app K))

/-- The canonical exceptional coefficient comparison on Dctf.
Source: blueprint main-20261015, sk-lem-sp-reduction-exceptional.md
(blueprint: det-sp-reduction-exceptional).

Proof plan (the thirteen source steps, with their named dependencies):

1. Put $T_X=(-)_B$, $T_Y=(-)_B$, $F_R=Rf_{!,R}$ and $G_R=f_R^!$. By
[det-sp-scalar-extension-functor](1),(2), $T_X,T_Y$ preserve the indicated categories. By
[sk-prop-sf-rf-shriek-preservation], $F_R\dashv G_R$ is an adjunction on them. Applying
[det-sp-reduction-direct-image] to $G_AK$ gives the natural isomorphism $b(G_AK):T_YF_AG_AK\to
F_BT_XG_AK$. Thus $\tau_K=T_Y(\varepsilon_A(K))b(G_AK)^{-1}$ is a well-typed map $F_BT_XG_AK\to
T_YK$, with no flatness requirement on $B$ over $A$.

2. Under the adjunction of [sk-prop-sf-rf-shriek-preservation], define $c_K$ to be the transpose
of $\tau_K$. The inverse transpose of $h:T_XG_AK\to G_BT_YK$ is $\varepsilon_B(T_YK)F_B(h)$.
Hence its counit identity is exactly the displayed identity in the statement, and this identity
determines $c_K$ uniquely. For $u:K\to L$, naturality of $b$ [det-sp-reduction-direct-image] and
of $\varepsilon_A$ gives $T_Y(u)\tau_K=\tau_LF_BT_XG_A(u)$. Naturality of $\varepsilon_B$
identifies the left side with the inverse transpose of $G_BT_Y(u)c_K$ and the right side with
the inverse transpose of $c_LT_XG_A(u)$. Injectivity of the hom bijection proves naturality of
$c$.

3. For any scheme $T$ used below and $R=A,B$, the finite ring $R$ is discrete Noetherian: every
ascending chain of ideals stabilizes since the underlying set is finite. The scheme $T$ is
Noetherian by [lem-weil-pbc-finite-type-over-noetherian], hence qcqs. Apply
[det-pe-finite-tor-comparison-noetherian]: $\nu_T^*$ is an equivalence on the bounded
constructible finite-Tor categories, preserving and reflecting every Tor interval. Thus its
stated conclusion supplies exactly the finite-Tor equivalence needed by
[det-sp-et-proet-adjunction-transfer], for arbitrary finite rings, not just DVR quotients.
Comparison inverse image is exact and carries constant rings to constant rings by
[lem-sf-comparison-pullback-exact]; its tensor comparison is
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. These comparisons identify coefficient
extension and the pullback, Tate-tensor and shift functors on the two sites. The Tate sheaves
are locally free of rank one by [lem-asd-finite-etale-twist-line]. The ordinary compact-support
functor also restricts to these subcategories. Indeed its value $F^{\mathrm{et}}L$ on bounded
input is bounded below, since it is $Rr_*j_!L$ with $j_!$ exact. The site comparison of
[lem-sp-et-proet-coefficient-compatibility] identifies $\nu^*F^{\mathrm{et}}L$ with $F\nu^*L$,
which is in $\Dctf$ by [sk-prop-sf-rf-shriek-preservation]. Choose bounded constructible etale
origin $M$ for this object using [lem-weil-pbc-finite-ring-constructible-derived-origin]. Full
faithfulness on $D^+$ [thm-weil-pbc-site-comparison] lifts the isomorphism
$\nu^*F^{\mathrm{et}}L\simeq\nu^*M$ to $F^{\mathrm{et}}L\simeq M$. The Tor reflection already
cited then gives $F^{\mathrm{et}}L\in\Dctf$.

4. We compute the ordinary-etale chart adjunction in Steps 7–11 and then transport it. Its right
functor $H_{g,R}=e^*p_d^*(-)(d)[2d]$ restricts to the finite-Tor constructible categories: after
$\nu^*$ it is the pro-etale pullback followed by a locally trivial rank-one tensor and a shift.
Pullback preserves $\Dctf$ by [det-proper-base-change-unbounded-pullback], with the finite-ring
module-object/ordinary-module identification of [sk-prop-sf-rf-shriek-preservation]; rank-one
tensor is locally the identity, and shifts preserve boundedness and translate Tor intervals. The
equivalence of Step 3 reflects this membership. The specified site comparison
$c_{g,R}:\nu_Y^*F^{\mathrm{et}}_{g,R}\simeq F_{g,R}\nu_U^*$ is an isomorphism by
[lem-sp-et-proet-coefficient-compatibility]. Consequently [det-sp-et-proet-adjunction-transfer]
identifies the transported right adjoint with $g_R^!$, retaining the actual counit
$$\epsilon^{\mathrm{pro}}_{g,R}=\nu_Y^*(\epsilon^{\mathrm{et}}_{g,R})c_{g,R}^{-1}.$$ The first
square and its following counit clause in [lem-sp-et-proet-coefficient-compatibility] carry a
coefficient-counit identity with the ordinary-etale $\beta_g$ to that same identity with the
named pro-etale $b_g$. We use that precise assertion in Step 11, so the transported comparison
is the fixed-compactification map of the statement.

5. For $q:\mathbf P^1_S\to S$ over any base chart in our setting, choose $N=\ell^n$ annihilating
both rings and put $R_0=\mathbf Z/N$. The bases and projective lines are Noetherian and $N$ is
invertible; Noetherianity follows from [lem-weil-pbc-finite-type-over-noetherian]. By
[lem-asd-ordinary-finite-p1-adjunction], for $R=A,B$ the splitting $s_R:R_S(1)[2]\oplus
R_S\xrightarrow{\sim}Rq_*R_{\mathbf P^1_S}(1)[2]$ has components the shifted unit and the
scalar-extended Kummer class $h_R$. More precisely, the cited statement defines $h_R$ by first
taking the Kummer class over $R_0$, extending scalars to $R$ on $\mathbf P^1_S$, and then
applying inverse-image/direct-image adjunction. Write $H_0:(R_0)_{\mathbf
P^1_S}\to(R_0)_{\mathbf P^1_S}(1)[2]$ for that Kummer morphism. Then $H_R=H_0\otimes^L_{R_0}R$
has adjunct $h_R$. Derived tensor associativity gives
$(H_0\otimes^L_{R_0}A)\otimes^L_AB=H_0\otimes^L_{R_0}B$, with the canonical identifications of
both endpoints; hence $(H_A)_B=H_B$. Step 6 checks the corresponding direct-image equality with
the named coefficient map by transposition.

6. On the ordinary etale site put $b_q=\beta_q^{\mathrm{et}}$, the proper comparison explicitly
defined and asserted invertible in [lem-sp-et-proet-coefficient-compatibility], evaluated on
$A_{\mathbf P^1_S}(1)[2]$. The source twist is locally free of rank one by
[lem-asd-finite-etale-twist-line]. Thus its derived scalar extension is ordinary tensor and is
canonically $B_{\mathbf P^1_S}(1)[2]$: on an etale trivialization the map is $A\otimes_A B\to
B$, $a\otimes b\mapsto ab$, and these maps respect the transition units of $\mu_N$. On the two
components of the splitting of Step 5 the comparison sends the unit to the unit and $(h_A)_B$ to
$h_B$. For the unit this follows from the defining counit-transpose projection map: its
composite with the pullback/direct-image unit is the coefficient-extended unit, by the
adjunction triangle identity; for the second component, take the inverse transpose of
$b_q(h_A)_B$ under $q_B^*\dashv Rq_{*,B}$. The defining counit identity for $b_q$ and naturality
give $(\epsilon_{q,*,A}\,q_A^*h_A)_B=(H_A)_B=H_B$, where $\epsilon_{q,*,A}$ is the ordinary
pullback/direct-image counit, not the exceptional counit. The inverse transpose of $h_B$ is also
$H_B$ by definition; injectivity of this hom bijection gives $b_q(h_A)_B=h_B$. Thus
$b_q(s_A)_B=s_B$. By [def-amb-p1-trace], $t_{q,R}=\operatorname{pr}_2s_R^{-1}$. Multiplying the
preceding equality by inverses gives $$t_{q,B}\,b_q=(t_{q,A})_B.$$ Indeed both composites with
$(s_A)_B$ are the projection onto the second summand. This is a two-component calculation with
an invertible splitting, not an extra lemma asserting the desired exceptional comparison.

7. The actual projective-line counit is $\epsilon_{q,R,K}=(1_K\otimes t_{q,R})\pi_R^{-1}$ with
the tensor unit constraint, by [lem-asd-ordinary-finite-p1-adjunction] and [def-amb-p1-trace].
Put $L_R=R_{\mathbf P^1_S}(1)[2]$ and $F_R=Rq_{*,R}$, so $G_{q,R}K=q_R^*K\otimes_R^L L_R$. The
canonical tensor/pullback comparison is [lem-weil-pbc-ringed-topoi-derived-tensor-pullback].
Apply the square of [lem-weil-pbc-ringed-exchange-tensor-coherence] to the ringed-topos square
with scheme maps $q,q$ and coefficient change $A\to B$. After its canonical tensor and symmetry
identifications, the square says exactly $$ F_B(a_{q,K})\,b_q(G_{q,A}K)\,(\pi_A)_B
=\pi_B\,(1_{K_B}\otimes b_q(L_A)), $$ where
$a_{q,K}:(q^*K(1)[2])_B\xrightarrow{\sim}q^*(K_B)(1)[2]$. Both sides start at
$K_B\otimes_B^L(F_AL_A)_B$ and end at $F_BG_{q,B}(K_B)$. Compose with
$\epsilon_{q,B,K_B}=(1\otimes t_{q,B})\pi_B^{-1}$. The right side becomes
$1_{K_B}\otimes(t_{q,B}b_q(L_A))=1_{K_B}\otimes(t_{q,A})_B$ by Step 6; this is
$(\epsilon_{q,A,K})_B(\pi_A)_B$. Here $K$ ranges over $\Dctf(S_{\mathrm{et}},A)$, the only
inputs used in Steps 9–11: then $G_{q,A}K=q^*K\otimes^L_AL_A$ is again bounded constructible of
finite Tor amplitude (pullback, a locally free rank-one twist [lem-asd-finite-etale-twist-line]
and a shift), so $b_q(G_{q,A}K)$ is an isomorphism by
[lem-sp-et-proet-coefficient-compatibility]; $\pi_A$ is invertible because the counit of
[lem-asd-ordinary-finite-p1-adjunction] is written with $\pi^{-1}$. Since $(\pi_A)_B$ and
$b_q(G_{q,A}K)$ are isomorphisms, cancellation gives $$ (\epsilon_{q,A,K})_B\,b_q(G_{q,A}K)^{-1}
=\epsilon_{q,B,K_B}\,Rq_{*,B}(a_{q,K}). $$ Thus the actual counit at every
$K\in\Dctf(S_{\mathrm{et}},A)$ has the required coefficient identity (the uninverted form
$\epsilon_{q,B,K_B}Rq_{*,B}(a_{q,K})b_q(G_{q,A}K)=(\epsilon_{q,A,K})_B$ holds for every $K$).
This argument uses no flatness of $B$ over $A$.

8. For an open immersion $j$ or a separated finite-type etale chart map $e$, use the exact
sum-extension adjunction [lem-amb-etale-adjoint-locality]. Its derived coefficient comparison is
the summandwise tensor identification $\sigma_e$ specified by
[lem-sp-et-proet-coefficient-compatibility]. Compute its counit before passage to the derived
category. The direct-sum presheaf [def-weil-pbc-etale-sum-extension] and its geometric-fibre
description [lem-amb-etale-sum-stalks] give the evaluation map $\bigoplus_x M_x\to M$,
$(m_x)\mapsto\sum_xm_x$. On every summand the two coefficient-extended evaluations agree because
$$ (\sum_xm_x)\otimes b=\sum_x(m_x\otimes b). $$ This is equality of the sheaf maps induced from
the presheaf sums; it is not a test for equality of arbitrary derived morphisms on stalks. The
same degreewise equality on the K-flat representatives computing $\sigma_e$ gives
$$\epsilon_{e,B}\,De_{!,B}(a_e)=T(\epsilon_{e,A})\sigma_e(e_A^*-)^{-1},$$ where $a_e:T
e_A^*\simeq e_B^*T$ is the canonical pullback/tensor comparison. The open case is the same
formula with at most one lift. No flatness of $B$ over $A$ is needed.

9. Use clause (2) of the existing Mathlib leaf [lem-weil-pbc-mate-pasting] for the two
consecutive chart adjunctions $F_{i,R}\dashv G_{i,R}$, $i=1,2$, with coefficient functors
$T_0,T_1,T_2$. The square at stage $i$ is $b_i^{-1}:F_{i,B}T_{i-1}\to T_iF_{i,A}$. Its mate is
$a_i:T_{i-1}G_{i,A}\to G_{i,B}T_i$, precisely because its counit equation is the identity
checked in Steps 7 and 8. Put $$ b_{12}=F_{2,B}(b_1)b_2(F_{1,A}-),\qquad
a_{12}=G_{1,B}(a_2)a_1(G_{2,A}-). $$ Clause (2) states that $a_{12}$ is the mate of the pasted
square $b_{12}^{-1}$ for the composite adjunction of [def-weil-pbc-composite-adjunction]. Taking
its inverse transpose therefore gives
$$\epsilon_{12,B}F_{2,B}F_{1,B}(a_{12})=T_2(\epsilon_{12,A})b_{12}(G_{1,A}G_{2,A}-)^{-1}.$$ This
applies an existing general composition theorem instead of hiding a separate lemma with its own
adjunction hypotheses in the chart calculation.

10. Apply Step 9 first to the open-extension adjunction for $\mathbf A^1_S\hookrightarrow\mathbf
P^1_S$ and the projective-line adjunction from Step 7. This gives the required
coefficient-counit identity for the affine-line adjunction. By [lem-amb-affine-space-top-trace],
the $d$-coordinate adjunction is the ordered composite of these affine-line adjunctions. Its
$d=0$ case is the identity, where both comparisons are identities; if the identity holds for
$d$, apply Step 9 with one further affine-line factor to obtain it for $d+1$. Tensor
associativity and pullback monoidality of [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]
identify the resulting $a_{12}$ with $(p_d^*K(d)[2d])_B\simeq p_d^*(K_B)(d)[2d]$. The
left-functor composition isomorphism is supplied by [lem-amb-etale-compact-comparisons]. The
composition square of [lem-sp-et-proet-coefficient-compatibility] identifies $b_{12}$ with the
named compact-support coefficient map after that isomorphism; its refinement square makes this
true for the chosen compactification as well. Thus induction proves the identity with the
specified $b_{p_d}$, not just an unspecified isomorphism between its endpoints.

11. On a chart $g=fj=p_de$ the composite adjunction of Steps 8–10 has right adjoint
$H_{g,R}K=e^*p_d^*K(d)[2d]$ and composite counit, by [def-weil-pbc-composite-adjunction] and the
etale adjunction [lem-amb-etale-adjoint-locality]. After the counit-preserving left-functor
identifications below, the restriction isomorphism $j^*G_R\simeq G_{g,R}$ of
[det-sf-mate-open-restriction] identifies it with this right adjoint by the counit-preserving
uniqueness of right adjoints. Apply the coefficient identities of Steps 7–10 and the transport
of Step 4. With $a_{g,K}:(H_{g,A}K)_B\xrightarrow{\sim}H_{g,B}(K_B)$ they give precisely $$
(\epsilon_{g,A,K})_B\,b_g(H_{g,A}K)^{-1} =\epsilon_{g,B,K_B}\,Rg_{!,B}(a_{g,K}). $$ This
constructs the chart adjunction for arbitrary finite $A,B$ from existing general finite-ring
projective-line and etale adjunctions; the narrower $\mathbf Z/\ell^n$ chart lemma is not
applied to an arbitrary finite ring. The left adjoint of this composite is $Rp_{d!}\circ
De_{\Sigma!}$; by [lem-asd-etale-compact-support-normalization] the identification
$c_e:Re_!^c\simeq De_{\Sigma!}$ carries the compact-support adjunction of $e$ to
$De_{\Sigma!}\dashv e^*$ with its sum/evaluation counit, so composing with the composition map
$\alpha$ identifies the chart left adjoint with $Rg_!$, counits included. The etale
normalization square of [lem-sp-et-proet-coefficient-compatibility] says that under $c_e$ the
coefficient map $\beta_e^c$ is the summandwise tensor identification used for $e$ in Steps 8–10.
Apply the composition and refinement squares of [lem-sp-et-proet-coefficient-compatibility] to
the compactifications of $e$, $p_d$ and $g=p_de$. They identify the coefficient map used in the
composite chart counit with $b_g$ for the chosen compactification. Hence the displayed counit
identity uses exactly the map defining the transpose $c_{g,K}$.

12. The comparison $c_K$ restricts to the comparison for $g=fj$. Here is the complete
cancellation. Write $J_R=j_{!,R}$, $U_R=j_R^*$, and $v_R:J_RU_R\to1$ for the open counit, and
let $a_U:T_UU_A\simeq U_BT_X$ be the restriction/tensor identification. By
[def-weil-pbc-composite-adjunction] and [det-sf-mate-open-restriction], the counit for $g$ is
$\epsilon_{f,R}\,F_{f,R}(v_R G_{f,R})$. The canonical compact-support comparison is
$$b_g(N)=F_{f,B}(b_j(N))\,b_f(J_AN),$$ as follows by the transpose computation in Steps 8–10.
After using $a_U$ to identify $T_UU_AG_AK$ with $U_BT_XG_AK$, the inverse transpose of $U_Bc_K$
under the composite adjunction is $$\epsilon_{f,B}\,F_{f,B}(v_B G_B T_YK)\,F_{f,B}J_B(U_Bc_K)
=\epsilon_{f,B}\,F_{f,B}(c_K)\,F_{f,B}(v_B T_XG_AK),$$ by naturality of $v_B$. The defining
equation of $c_K$ turns this into $$T_Y\epsilon_{f,A}\;b_f(G_AK)^{-1}\;F_{f,B}(v_B T_XG_AK).$$
Step 8's open-counit scalar equality is an equality on the ordinary etale site; the pro-etale
open adjunction $J_R\dashv U_R$ is its transport by [det-sp-et-proet-adjunction-transfer] (Step
4 applied to $j$, all objects having etale origin by Step 3), and the first square of
[lem-sp-et-proet-coefficient-compatibility] carries the identity with $\beta_j$ to the same
identity with $b_j$. So on the pro-etale site $$v_B T_XG_AK=T_X(v_A G_AK)\,b_j(U_AG_AK)^{-1}.$$
Naturality of $b_f$ now rewrites the preceding inverse transpose as
$$T_Y\epsilon_{f,A}\;T_YF_{f,A}(v_A G_AK)\;b_f(J_AU_AG_AK)^{-1}\;F_{f,B}(b_j(U_AG_AK)^{-1})
=T_Y(\epsilon_{g,A,K})\,b_g(U_AG_AK)^{-1}.$$ This is exactly the inverse transpose defining
$c_{g,K}$; hence $j^*c_K=c_{g,K}$. Step 11 says the canonical $a_{g,K}$ has this same inverse
transpose, so uniqueness gives $j^*c_K=a_{g,K}$, the required chart identification and an
isomorphism. Here the composition square of [lem-sp-et-proet-coefficient-compatibility] for the
pair $(j,f)$, after the $\alpha_A,\alpha_B$ identifications, is exactly the displayed formula
$b_g=F_{f,B}(b_j)b_f(J_A-)$. Its refinement square identifies this formula with the comparison
for the fixed compactification of $g$, so the final inverse transpose is the named one defining
$c_{g,K}$.

13. Smooth local normal form [sbc-thm-etale-local-normal-form] gives coordinate charts after
replacing the base and source by affine neighborhoods. Compose its etale map to $\mathbf A^d_V$
with the open immersion $\mathbf A^d_V\hookrightarrow\mathbf A^d_Y$; this is an etale chart over
$Y$. Pure relative dimension fixes its dimension to $d$. The affine neighborhoods cover $X$.
They are Noetherian, as are $X,Y$ and their affine spaces, by
[lem-weil-pbc-finite-type-over-noetherian]. Open subschemes remain Noetherian by
[lem-weil-pbc-noetherian-open-subscheme-noetherian], so the chart open immersions are
quasi-compact and are of finite type by [lem-weil-pbc-qc-open-immersion-finite-type]. By
[lem-weil-pbc-qcqs-morphism-permanence](1), the etale coordinate map from an affine source to
the separated affine-space target is of finite presentation, hence finite type. It is separated:
its relative diagonal is the base change of the closed diagonal of its separated $k$-source
along $U\times_{\mathbf A^d_Y}U\to U\times_kU$, hence closed by
[lem-weil-pbc-proper-fp-permanence](b). Thus all these maps satisfy the hypotheses of the
adjunctions used above. Step 12 makes every restriction of $c_K$ an isomorphism. Clause (3) of
[det-sf-mate-open-restriction] detects isomorphisms on this open cover, and proves $c_K$ is an
isomorphism globally. Only isomorphism detection is used here; no assertion that restriction is
faithful on all derived morphisms is needed.
-/
theorem reductionExceptional_isIso
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ) [SmoothOfRelativeDimension d f]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (hf : j ≫ p = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B) :
    ∃ (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
        spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj))
      (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
        spFiniteConstructibleTor Y B ((reductionCompactSupport B j p).obj M.obj))
      (hSX : ∀ M : spFiniteConstructibleTorCategory X A,
        spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj))
      (hSY : ∀ K : spFiniteConstructibleTorCategory Y A,
        spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj)),
      ∃ (GA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
        (GB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B)
        (adjA : reductionCtfCompactSupport A j p hFA ⊣ GA)
        (adjB : reductionCtfCompactSupport B j p hFB ⊣ GB),
        ∃ (RA : ReductionExceptionalRealization A j p hFA GA adjA)
          (RB : ReductionExceptionalRealization B j p hFB GB adjB),
        ∃ hb : ∀ K : spFiniteConstructibleTorCategory Y A,
          IsIso ((reductionDirectImageComparison φ j p).app (GA.obj K).obj),
        ∃! c : GA ⋙ reductionCtfScalar φ X hSX ⟶ reductionCtfScalar φ Y hSY ⋙ GB,
          (∀ K : spFiniteConstructibleTorCategory Y A,
            (reductionCompactSupport B j p).map (c.app K).hom ≫
                (adjB.counit.app ((reductionCtfScalar φ Y hSY).obj K)).hom =
              @inv _ _ _ _ ((reductionDirectImageComparison φ j p).app (GA.obj K).obj)
                  (hb K) ≫
                (scalarExtensionFunctor φ Y).map (adjA.counit.app K).hom) ∧
          (∀ K : spFiniteConstructibleTorCategory Y A, IsIso (c.app K)) ∧
          ReductionExceptionalChartEquation ℓ φ j p d hFA hFB hSX hSY GA GB adjA adjB
            RA RB c := by
  sorry

end AlgebraicGeometry.ProEtale
