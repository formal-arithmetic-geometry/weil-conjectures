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

public import Sheaf.Paper.VectorPurityScalarSingle
public import Sheaf.Paper.PurEtaleScalarMateProjection
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.EtaleLocalNormalForm
import Sheaf.AlgebraicGeometry.EtaleSumStalks
import all Sheaf.Paper.ScalarPullbackIsoUniqueness
import all Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
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

universe u v w
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
  let J := T.smallEtaleTopology
  let P := finiteEtaleMuModulePresheaf T N
  let r := finiteEtaleTwistScalar N A hA
  let L := (Sheaf.restrictScalars J φ).obj (finiteEtaleTateLine T N B hB)
  let adj := ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} r
  let g (W : T.Etaleᵒᵖ) : P.obj W ⟶ (ModuleCat.restrictScalars r).obj (L.obj.obj W) :=
    letI := AddCommGroup.zmodModule (finiteEtaleMu_annihilated T N W)
    ModuleCat.ofHom (X := P.obj W)
      (Y := (ModuleCat.restrictScalars r).obj (L.obj.obj W))
      (({ toFun := Etale.ordinaryFiniteRootGenerator B N hB T W
          map_zero' := (Etale.ordinaryFiniteRootGenerator B N hB T W).map_zero
          map_add' := (Etale.ordinaryFiniteRootGenerator B N hB T W).map_add } :
        P.obj W →+ ((ModuleCat.restrictScalars r).obj (L.obj.obj W))).toZModLinearMap N)
  let q (W : T.Etaleᵒᵖ) : (ModuleCat.extendScalars r).obj (P.obj W) ⟶ L.obj.obj W :=
    (adj.homEquiv _ _).symm (g W)
  have hq (W : T.Etaleᵒᵖ) (z : (T.rootsOfUnitySheaf N).obj.obj W) :
      q W (@TensorProduct.tmul (ZMod N) _ _ _ _ _ (Module.compHom _ r) _ (1 : A) z) =
        Etale.ordinaryFiniteRootGenerator B N hB T W z := by
    have hh := congrArg (fun f ↦ f z) ((adj.homEquiv _ _).apply_symm_apply (g W))
    change q W (@TensorProduct.tmul (ZMod N) _ _ _ _ _
      (Module.compHom _ r) _ (1 : A) z) = (g W) z at hh
    exact hh
  have hqa (W : T.Etaleᵒᵖ) (a : A)
      (z : (T.rootsOfUnitySheaf N).obj.obj W) :
      q W (@TensorProduct.tmul (ZMod N) _ _ _ _ _ (Module.compHom _ r) _ a z) =
        finiteEtaleTateOneGenerator B N T hB W (φ a) z := by
    let _ := AddCommGroup.zmodModule (finiteEtaleMu_annihilated T N W)
    have hx : (@TensorProduct.tmul (ZMod N) _ _ _ _ _ (Module.compHom _ r) _ a z) =
        a • (@TensorProduct.tmul (ZMod N) _ _ _ _ _ (Module.compHom _ r) _ (1 : A) z :
          (ModuleCat.extendScalars r).obj (P.obj W)) := by
      simpa only [mul_one] using
        (ModuleCat.ExtendScalars.smul_tmul r a 1 (show P.obj W from z)).symm
    rw [hx, map_smul, hq]
    change φ a • (show (finiteEtaleTateLine T N B hB).obj.obj W from
      Etale.ordinaryFiniteRootGenerator B N hB T W z) = _
    change φ a • ((toSheafify J (P ⋙ ModuleCat.extendScalars
      (finiteEtaleTwistScalar N B hB))).app W
        ((@TensorProduct.tmul (ZMod N) _ _ _ _ _
          (Module.compHom _ (finiteEtaleTwistScalar N B hB)) _ (1 : B) z))) =
      (toSheafify J (P ⋙ ModuleCat.extendScalars
        (finiteEtaleTwistScalar N B hB))).app W
          ((@TensorProduct.tmul (ZMod N) _ _ _ _ _
            (Module.compHom _ (finiteEtaleTwistScalar N B hB)) _ (φ a) z))
    rw [← map_smul]
    congr 1
    simpa only [mul_one] using
      (ModuleCat.ExtendScalars.smul_tmul (finiteEtaleTwistScalar N B hB)
        (φ a) 1 (show P.obj W from z))
  let η : P ⋙ ModuleCat.extendScalars r ⟶ L.obj :=
    { app := q
      naturality := by
        intro W V f
        change (ModuleCat.extendScalars r).map (P.map f) ≫ q V = q W ≫ L.obj.map f
        apply (adj.homEquiv _ _).injective
        rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
        simp only [q, Equiv.apply_symm_apply]
        ext z
        exact congrArg (fun k ↦ k z)
          (Etale.ordinaryFiniteRootGenerator_naturality B N hB T f) }
  let τ : finiteEtaleTateLine T N A hA ⟶ L :=
    ⟨sheafifyLift J η L.property⟩
  have hτ : ∀ (W : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf N).obj.obj W),
      τ.hom.app W (finiteEtaleTateOneGenerator A N T hA W a z) =
        finiteEtaleTateOneGenerator B N T hB W (φ a) z := by
    intro W a z
    have hh := congrArg (fun f ↦ f.app W
      (@TensorProduct.tmul (ZMod N) _ _ _ _ _ (Module.compHom _ r) _ a z))
      (toSheafify_sheafifyLift J η L.property)
    exact hh.trans (hqa W a z)
  refine ⟨τ, hτ, ?_⟩
  intro τ' hτ'
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ L.property
  ext W x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a z => exact (hτ' W a z).trans (hτ W a z).symm
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The canonical generator-normalized ordinary Tate scalar map.
Source: blueprint Step 6 (blueprint: det-sp-reduction-exceptional). -/
def reductionEtaleTateMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    finiteEtaleTateLine T N A hA ⟶
      (Sheaf.restrictScalars T.smallEtaleTopology φ).obj (finiteEtaleTateLine T N B hB) :=
  (reductionEtaleTateMap_existsUnique φ T N hA hB).exists.choose

/-- The actual derived Tate scalar map: transpose the root-normalized map under
scalar extension/restriction. Source: blueprint Step 6
(blueprint: det-sp-reduction-exceptional). -/
def reductionEtaleTateExtensionMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    (Etale.scalarExtension φ T).obj (Etale.ordinaryFiniteLine A N hA T) ⟶
      Etale.ordinaryFiniteLine B N hB T :=
  WeilConjectures.PurityFiniteSetting.purityScalarSingleMap φ T
      (finiteEtaleTateLine T N A hA) ≫
    (DerivedCategory.singleFunctor _ 0).map
      (((etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _).symm
        (reductionEtaleTateMap φ T N hA hB))

section MapComparison
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C : Type v} {D : Type w} {V : Type*} {W : Type*}
  [Category.{u + 1} C] [Category.{u + 1} D] [Category V] [Category W]
  (E : C ⥤ D) (U : D ⥤ C) (L : V ⥤ W) (R : W ⥤ V)
  (i : C ⥤ V) (j : D ⥤ W) (a : E ⊣ U) (ad : L ⊣ R)
  (c : j ⋙ R ≅ U ⋙ i) (M : C) (N : D) (τ : M ⟶ U.obj N)
-- Naturality of the exact comparison and the ordinary unit identify the two transposes.
private theorem reductionFactoredTranspose :
    WeilConjectures.PurityFiniteSetting.purityAdjunctionSingleMap E U L R i j a ad c M ≫
        j.map ((a.homEquiv M N).symm τ) =
      (ad.homEquiv (i.obj M) (j.obj N)).symm (i.map τ ≫ c.inv.app N) := by
  unfold WeilConjectures.PurityFiniteSetting.purityAdjunctionSingleMap
  rw [← ad.homEquiv_naturality_right_symm]
  congr 1
  rw [Category.assoc]
  have hn := c.inv.naturality ((a.homEquiv M N).symm τ)
  dsimp only [Functor.comp_map] at hn
  erw [← hn]
  rw [← Category.assoc, ← i.map_comp]
  rw [(a.homEquiv_unit M N _).symm.trans ((a.homEquiv M N).apply_symm_apply τ)]
end MapComparison

section ReductionScalarProof
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
-- The rank-one etale trivializations imply flatness. Handle N=0 on the empty scheme.
private theorem reductionTateLineFlat
    (T : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : (N : A) = 0) (hT : IsUnit (N : Γ(T, ⊤))) :
    ObjectProperty.flat (finiteEtaleTateLine T N A hA) := by
  by_cases hN : N = 0
  · subst N
    have : Subsingleton Γ(T, ⊤) :=
      subsingleton_of_zero_eq_one ((isUnit_zero_iff).mp (by simpa using hT))
    have : IsEmpty T := Scheme.isEmpty_of_subsingleton_Γ this
    exact ObjectProperty.flat_of_isZero (Scheme.Etale.isZero_sheaf_of_isEmpty _)
  · have hstalk : ∀ x : T, IsUnit (N : T.presheaf.stalk x) := fun x ↦ by
      simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ x (by trivial)).hom
    obtain ⟨cover, hc⟩ := exists_first_twist_cover T N (Nat.pos_of_ne_zero hN) hstalk A hA
    let e := Etale.tensorInverseOfUpperStarIso (ModuleCat.{u + 1} A)
      cover.f cover.iUnion_range (finiteEtaleTateLine T N A hA) (fun i ↦ (hc i).some)
    exact ObjectProperty.flat_of_tensorIso e.rightIso

section Abstract
variable {C : Type v} {D : Type w} [Category.{u + 1} C] [Category.{u + 1} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{u + 1} C] [HasDerivedCategory.{u + 1} D]
  (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (a : E ⊣ U) {L : DerivedCategory C ⥤ DerivedCategory D}
  (ad : L ⊣ U.mapDerivedCategory) (M : C)
-- Compare the cochain unit with the degree-zero exact-restriction comparison.
private theorem reductionSingleAdjunct :
    (ad.homEquiv _ _).symm
        (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app
          ((CochainComplex.singleFunctor C 0).obj M)) ≫
            U.mapDerivedCategoryFactors.inv.app
              ((E.mapHomologicalComplex (.up ℤ)).obj
                ((CochainComplex.singleFunctor C 0).obj M))) ≫
      DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
        E (.up ℤ) 0).hom.app M) =
    (ad.homEquiv _ _).symm ((DerivedCategory.singleFunctor C 0).map
      (a.unit.app M) ≫ (U.mapDerivedCategorySingleFunctor 0).inv.app (E.obj M)) := by
  rw [← ad.homEquiv_naturality_right_symm]
  congr 1
  rw [Category.assoc]
  have hn := U.mapDerivedCategoryFactors.inv.naturality
    ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).hom.app M)
  dsimp only [Functor.comp_map] at hn
  erw [← hn]
  erw [← DerivedCategory.Q.map_comp_assoc]
  have hc : (a.mapHomologicalComplex (.up ℤ)).unit.app
      ((CochainComplex.singleFunctor C 0).obj M) ≫
        (U.mapHomologicalComplex (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).hom.app M) =
      (CochainComplex.singleFunctor C 0).map (a.unit.app M) ≫
        (HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).inv.app (E.obj M) := by
    ext n
    by_cases hn : n = 0
    · subst n
      simp only [HomologicalComplex.comp_f, Adjunction.mapHomologicalComplex_unit_app_f,
        Functor.mapHomologicalComplex_map_f]
      simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
        HomologicalComplex.single_map_f_self]
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M n hn).eq_of_src _ _
  erw [hc, DerivedCategory.Q.map_comp]
  have hs := U.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app
    (E.obj M)
  have hs' : (U.mapDerivedCategorySingleFunctor 0).inv.app (E.obj M) =
      DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).inv.app
            (E.obj M)) ≫
        U.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor D 0).obj
          (E.obj M)) := by
    exact (Iso.eq_comp_inv (U.mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor D 0).obj (E.obj M)))).mpr hs
  rw [hs']
  simp only [Category.assoc]
  rfl
end Abstract
section FlatSingle
open CategoryTheory.MonoidalCategory
variable {C : Type v} {D : Type w} [Category.{u + 1} C] [Category.{u + 1} D]
  [Abelian C] [Abelian D] [IsGrothendieckAbelian.{u + 1} C]
  [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [CategoryTheory.Abelian.HasFunctorialFlatResolution C]
  (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive] [E.PreservesKFlatQuasiIso]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (a : E ⊣ U) {L : DerivedCategory C ⥤ DerivedCategory D}
  (ad : L ⊣ U.mapDerivedCategory) (M : C)
private theorem reductionFlatSingleAdjunct_isIso (hM : ObjectProperty.flat M) :
    IsIso (WeilConjectures.PurityFiniteSetting.purityAdjunctionSingleMap E U L
      U.mapDerivedCategory (DerivedCategory.singleFunctor C 0)
      (DerivedCategory.singleFunctor D 0) a ad (U.mapDerivedCategorySingleFunctor 0) M) := by
  let P := (CochainComplex.singleFunctor C 0).obj M
  have hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P := by
    apply CochainComplex.kFlat_of_isStrictlyLE_of_flat P 0
    intro n
    by_cases hn : n = 0
    · subst n
      exact ObjectProperty.prop_of_iso _
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).symm hM
    · exact ObjectProperty.flat_of_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M n hn)
  have hr := Etale.derivedRepresentative_isIso E U a ad P hP
  rw [← Etale.mapComplex_unit_formula] at hr
  unfold WeilConjectures.PurityFiniteSetting.purityAdjunctionSingleMap
  erw [← reductionSingleAdjunct E U a ad M]
  infer_instance
end FlatSingle

set_option backward.isDefEq.respectTransparency false in
-- Composition of scalar adjunctions identifies the normalized map with an isomorphism.
private theorem reductionTateOrdinaryScalar_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    IsIso (((etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _).symm
      (reductionEtaleTateMap φ T N hA hB)) := by
  let J := T.smallEtaleTopology
  let rA := finiteEtaleTwistScalar N A hA
  let rB := finiteEtaleTwistScalar N B hB
  have hr : rB = φ.comp rA := by
    apply Subsingleton.elim
  let a := (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} rA).whiskerRight
    T.Etaleᵒᵖ |>.comp (sheafificationAdjunction J (ModuleCat.{u + 1} A))
  let b := (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} rB).whiskerRight
    T.Etaleᵒᵖ |>.comp (sheafificationAdjunction J (ModuleCat.{u + 1} B))
  let c := a.comp (etaleSheafExtendScalarsAdjunction φ T)
  let r : Sheaf.restrictScalars J φ ⋙
      (sheafToPresheaf J (ModuleCat.{u + 1} A) ⋙
        (Functor.whiskeringRight T.Etaleᵒᵖ _ _).obj (ModuleCat.restrictScalars rA)) ≅
      sheafToPresheaf J (ModuleCat.{u + 1} B) ⋙
        (Functor.whiskeringRight T.Etaleᵒᵖ _ _).obj (ModuleCat.restrictScalars rB) :=
    NatIso.ofComponents (fun L ↦
    Functor.isoWhiskerLeft L.obj (ModuleCat.restrictScalarsComp' rA φ rB hr).symm)
    (by intro L M f; ext W x; rfl)
  let e := (c.ofNatIsoRight r).leftAdjointUniq b
  let P := finiteEtaleMuModulePresheaf T N
  have he : (a.homEquiv _ _
      ((etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _ (e.hom.app P))) =
        b.unit.app P ≫ r.inv.app _ := by
    have hh := Adjunction.homEquiv_leftAdjointUniq_hom_app (c.ofNatIsoRight r) b P
    rw [Adjunction.homEquiv_ofNatIsoRight_apply] at hh
    have hh' := (Iso.eq_comp_inv (r.app _)).2 hh
    exact hh'
  have hτ : (etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _ (e.hom.app P) =
      reductionEtaleTateMap φ T N hA hB := by
    apply (reductionEtaleTateMap_existsUnique φ T N hA hB).unique
      (y₁ := (etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _ (e.hom.app P))
      (y₂ := reductionEtaleTateMap φ T N hA hB) ?_
      (reductionEtaleTateMap_existsUnique φ T N hA hB).exists.choose_spec
    intro W x z
    have hh := congrArg (fun η ↦ (η.app W) z) he
    change _ = _ at hh
    let τ : finiteEtaleTateLine T N A hA ⟶
        (Sheaf.restrictScalars J φ).obj (finiteEtaleTateLine T N B hB) :=
      (etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _ (e.hom.app P)
    have h1 : τ.hom.app W (finiteEtaleTateOneGenerator A N T hA W 1 z) =
        finiteEtaleTateOneGenerator B N T hB W 1 z := hh
    have hs (R : Type (u + 1)) [CommRing R] (hR : (N : R) = 0) (v : R) :
        finiteEtaleTateOneGenerator R N T hR W v z =
          v • finiteEtaleTateOneGenerator R N T hR W 1 z := by
      let _ := AddCommGroup.zmodModule (finiteEtaleMu_annihilated T N W)
      let q := (toSheafify J (P ⋙ ModuleCat.extendScalars
        (finiteEtaleTwistScalar N R hR))).app W
      change q (@TensorProduct.tmul (ZMod N) _ _ _ _ _
        (Module.compHom _ (finiteEtaleTwistScalar N R hR)) _ v z) =
          v • q (@TensorProduct.tmul (ZMod N) _ _ _ _ _
            (Module.compHom _ (finiteEtaleTwistScalar N R hR)) _ (1 : R) z)
      rw [← map_smul]
      congr 1
      simpa only [mul_one] using
        (ModuleCat.ExtendScalars.smul_tmul (finiteEtaleTwistScalar N R hR)
          v 1 (show P.obj W from z)).symm
    change τ.hom.app W (finiteEtaleTateOneGenerator A N T hA W x z) = _
    rw [hs A hA x, map_smul]
    change φ x • (show (finiteEtaleTateLine T N B hB).obj.obj W from
      τ.hom.app W (finiteEtaleTateOneGenerator A N T hA W 1 z)) = _
    have h1B : (show (finiteEtaleTateLine T N B hB).obj.obj W from
        τ.hom.app W (finiteEtaleTateOneGenerator A N T hA W 1 z)) =
          finiteEtaleTateOneGenerator B N T hB W 1 z := h1
    exact (congrArg (fun t : (finiteEtaleTateLine T N B hB).obj.obj W ↦ φ x • t) h1B).trans
      (hs B hB (φ x)).symm
  have heq : ((etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _).symm
      (reductionEtaleTateMap φ T N hA hB) = e.hom.app P := by
    apply ((etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _).injective
    exact (Equiv.apply_symm_apply _ _).trans hτ.symm
  rw [heq]
  infer_instance

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
  have hα : IsIso (WeilConjectures.PurityFiniteSetting.purityScalarSingleMap φ T
      (finiteEtaleTateLine T N A hA)) := by
    let E := etaleSheafExtendScalars φ T
    let U := Sheaf.restrictScalars T.smallEtaleTopology φ
    let : E.PreservesKFlatQuasiIso := Etale.extension_preservesKFlatQuasiIso φ T
    exact reductionFlatSingleAdjunct_isIso E U (etaleSheafExtendScalarsAdjunction φ T)
      (L := Etale.scalarExtension φ T) (Etale.purityScalarAdjunction φ T)
      (finiteEtaleTateLine T N A hA) (reductionTateLineFlat T N A hA hT)
  have := reductionTateOrdinaryScalar_isIso φ T N hA hB
  unfold reductionEtaleTateExtensionMap
  infer_instance

end ReductionScalarProof

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

end AlgebraicGeometry.ProEtale
