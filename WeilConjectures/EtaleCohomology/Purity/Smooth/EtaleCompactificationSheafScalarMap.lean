/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleCompactificationGraphMap
public import WeilConjectures.SixFunctors.Etale.LowerShriek.BaseChange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.SixFunctors.EtaleOpenTensorDefs
public import WeilConjectures.AlgebraicGeometry.ScalarPullbackRepresentativeData
public import WeilConjectures.EtaleCohomology.Purity.Smooth.EtaleSheafProjectionData
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import all WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import all WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
import all WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import all WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities
import all WeilConjectures.SixFunctors.EtaleOpenTensorDefs
import all WeilConjectures.EtaleCohomology.Purity.Smooth.EtaleProjectionSectionNormalization
import WeilConjectures.CategoryTheory.Sites.SheafComposePushforwardMonoidal
import WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionCalculus
import WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Mathlib.CategoryTheory.Sites.Subsheaf
import WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.EtaleCohomology.EtaleSectionZeroOpen
import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality
import WeilConjectures.AlgebraicGeometry.ClosedProperSupportLocality
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.Morphisms.FpqcDescent
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.ProperMorphismFpqcDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import WeilConjectures.AlgebraicGeometry.ProperSupportCompositeRange
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionImage
import WeilConjectures.AlgebraicGeometry.OpenExtensionProperSupportRange
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.AlgebraicGeometry.ProperSupportExchangeRange
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility
import WeilConjectures.SecSmoothPurity.ProperSupportPullbackSectionMap
import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalk
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Defs
import WeilConjectures.SixFunctors.OpenClosed.Complex
import WeilConjectures.AlgebraicGeometry.ProperGeometricPointExchange
import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.ProperStrictLocalFibreSections
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
import WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
import WeilConjectures.AlgebraicGeometry.QcqsGeometricExchangeFactorization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative
import WeilConjectures.AlgebraicGeometry.EtaleUnitSectionRestriction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.SmallStrictLocalSectionMapsSupplement
import WeilConjectures.AlgebraicGeometry.GeometricPointPullbackStalk
import WeilConjectures.AlgebraicGeometry.GeometricPointCanonicalGerm
import WeilConjectures.AlgebraicGeometry.OpenImmersionExtensionZeroBaseChange
import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalkCore
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import WeilConjectures.Compactification.BaseChange
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.BaseChange.Pasting
import WeilConjectures.AlgebraicGeometry.SupportedExteriorProduct
import WeilConjectures.AlgebraicGeometry.EtaleFiniteCompactificationSheafIso
import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphSheafNormalization
import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportNormalizationDataSupplement
import WeilConjectures.SixFunctors.BaseChange.Etale
import WeilConjectures.ConstructibleSheaf.EtaleMorphismDescent
import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization

/-! # The ordinary compactified étale coefficient mate on sheet generators

Source: Stacks Project, more-etale.tex, Tags 0GKF and 0GL6;
etale-cohomology.tex, Tags 03S5 and 0F4L; sites-modules.tex, Tag 03EL
(blueprint: lem-sp-etale-compactification-sheaf-scalar-map).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

/-- The ordinary coefficient/direct-image map, with the specified geometric counit.
It is the B-geometric adjunct of scalar/pullback reassociation followed by scalar
extension of the A-geometric counit, rather than an unspecified comparison.
Source: Stacks, Tags 03EL and 0GL6
(blueprint: lem-sp-etale-compactification-sheaf-scalar-map). -/
def compactificationOrdinaryScalarMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V) :
    lowerStar (ModuleCat.{u + 1} A) r ⋙ ProEtale.etaleSheafExtendScalars φ V ⟶
      ProEtale.etaleSheafExtendScalars φ W ⋙ lowerStar (ModuleCat.{u + 1} B) r :=
  (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r)
    (TwoSquare.mk _ _ _ _ (scalarSheafPullbackIso φ r).hom)).natTrans

/-- The ordinary constant-coefficient pullback identification. Its second factor
is the canonical inverse-image unit isomorphism, so it pulls every local coefficient
section back along the same lift as the module section.
Source: Stacks, Tags 03EL and 0GKF
(blueprint: lem-sp-etale-compactification-sheaf-scalar-map). -/
def compactificationCoefficientPullbackIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) :
    (upperStar (ModuleCat.{u + 1} A) e).obj (scalarCoefficientSheaf φ V) ≅
      scalarCoefficientSheaf φ U :=
  (upperStarRestrictScalarsIsoSheaf φ e).app (𝟙_ _) ≪≫
    (Sheaf.restrictScalars U.smallEtaleTopology φ).mapIso
      (Functor.Monoidal.εIso (upperStar (ModuleCat.{u + 1} B) e)).symm

/-- The image of a local pure tensor in ordinary scalar extension. The coefficient
is a section of B_T, not merely an element of the constant ring B. The existing
balancing map supplies the canonical B tensor M versus M tensor B identification.
Source: Stacks, Tags 03EK and 0GKF
(blueprint: lem-sp-etale-compactification-sheaf-scalar-map). -/
def compactificationScalarTensorSection
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {T : Scheme.{u}}
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (S : T.Etale) (m : M.obj.obj (op S))
    (b : (scalarCoefficientSheaf φ T).obj.obj (op S)) :
    ((ProEtale.etaleSheafExtendScalars φ T).obj M).obj.obj (op S) :=
  (scalarSheafTensorMap φ T M).hom.app (op S)
    (etaleSheafTensorSection A M (scalarCoefficientSheaf φ T) S m b)

-- Keep the sheafification constructions behind their adjunction APIs.
attribute [local irreducible] upperStar ProEtale.etaleSheafExtendScalars
  etaleLowerShriek openImmersionLowerShriek
  upperStarLowerStarAdjunction ProEtale.etaleSheafExtendScalarsAdjunction
  Sheaf.monoidalCategory

private theorem cached_groth (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1}
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance

attribute [local instance] cached_groth supportedHasSheafify

private def sum_scalar_iso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] :
    etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ⋙
        ProEtale.etaleSheafExtendScalars φ V ≅
      ProEtale.etaleSheafExtendScalars φ U ⋙
        etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance :=
  ((etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).comp
    (ProEtale.etaleSheafExtendScalarsAdjunction φ V)).leftAdjointUniq
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ U).comp
      (etaleLowerShriekAdjunction (ModuleCat.{u + 1} B) e inferInstance))

private theorem compactification_support_factor
    (A : Type (u + 1)) [CommRing A]
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] [IsSeparated e] [QuasiCompact e]
    :
    ∃ (L : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
        Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
      (ι : L ⟶ lowerStar (ModuleCat.{u + 1} A) e),
      (∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (S : V.Etale),
        Function.Injective ((ι.app M).hom.app (op S))) ∧
      ∀ d : Compactification e,
        ∃ α : openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i ⋙
            lowerStar (ModuleCat.{u + 1} A) d.g ≅ L,
          α.hom ≫ ι = compactificationSheafToDirectImage A d := by
  obtain ⟨L, ι, hi, hp, ho, σ, _, hσ, _, _⟩ := properSupportSheafComposition A
  refine ⟨L e, ι e, fun M S ↦ (hi _ _ e M S).1, ?_⟩
  intro d
  rcases d with ⟨Z, p, j, rfl, hpp, hj⟩
  have := hpp
  have := hj
  obtain ⟨oj, hoj⟩ := ho U Z j
  have hpi : ∀ M, IsIso ((ι p).app M) := hp Z V p
  have : IsIso (ι p) := NatIso.isIso_of_isIso_app (ι p)
  let α := Functor.isoWhiskerRight oj (lowerStar (ModuleCat.{u + 1} A) p) ≪≫
    Functor.isoWhiskerLeft (L j) (asIso (ι p)).symm ≪≫ σ U Z V j p
  refine ⟨α, ?_⟩
  apply NatTrans.ext
  funext M
  dsimp only [α, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app]
  rw [Category.assoc, Category.assoc, hσ]
  have hc : (asIso (ι p)).inv.app ((L j).obj M) ≫
      (ι p).app ((L j).obj M) = 𝟙 _ := (asIso (ι p)).inv_hom_id_app _
  rw [reassoc_of% hc, ← Functor.map_comp_assoc]
  change (lowerStar (ModuleCat.{u + 1} A) p).map
    ((oj.hom ≫ ι j).app M) ≫ _ = _
  rw [hoj]
  rfl

private theorem compactification_graph_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] [IsSeparated e] [QuasiCompact e]
    [IsLocallyNoetherian V] [CompactSpace V]
    (c : Compactification e) : IsIso (etaleCompactificationGraphMap A e c) := by
  classical
  obtain ⟨L, ι, hi, hfac⟩ := compactification_support_factor A e
  obtain ⟨Z, j, p, hj, hjq, hpf, hcomm⟩ :=
    e.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite
  have := hj
  have := hpf
  let d : Compactification e := ⟨Z, p, j, hcomm.symm, inferInstance, hj⟩
  have := isIso_etaleCompactificationGraphMap_of_isFinite A e d
  obtain ⟨α, hα⟩ := hfac c
  obtain ⟨β, hβ⟩ := hfac d
  have heq : etaleCompactificationGraphMap A e c ≫ α.hom =
      etaleCompactificationGraphMap A e d ≫ β.hom := by
    ext M S x
    apply hi M S.unop
    have h₁ := compactSupportGraphSheafComparison_normalization A e c M
    have h₂ := compactSupportGraphSheafComparison_normalization A e d M
    have he : (etaleCompactificationGraphMap A e c).app M ≫ α.hom.app M ≫ ι.app M =
        (etaleCompactificationGraphMap A e d).app M ≫ β.hom.app M ≫ ι.app M := by
      rw [← NatTrans.comp_app, hα, h₁, ← NatTrans.comp_app, hβ, h₂]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app
      (congrArg (fun f ↦ f.hom) he) S) x
  have : IsIso (etaleCompactificationGraphMap A e c ≫ α.hom) := by
    rw [heq]
    infer_instance
  exact IsIso.of_isIso_comp_right _ α.hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem literal_scalar_pullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] :
    (upperStarRestrictScalarsIsoSheaf φ e).hom =
      Functor.whiskerLeft (Sheaf.restrictScalars V.smallEtaleTopology φ)
        (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e inferInstance).hom ≫
      Functor.whiskerRight
        (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} B) e inferInstance).inv
        (Sheaf.restrictScalars U.smallEtaleTopology φ) := by
  let a := Sheaf.restrictCoextendScalarsAdj V.smallEtaleTopology φ
  let b := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e
  let c := upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) e
  let d := Sheaf.restrictCoextendScalarsAdj U.smallEtaleTopology φ
  let b' := localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) e inferInstance
  let c' := localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} B) e inferInstance
  have hadj : a.comp b' = c'.comp d := by
    apply Adjunction.ext
    apply NatTrans.ext
    funext M
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext S
    change ((a.comp b').unit.app M).hom.app S = ((c'.comp d).unit.app M).hom.app S
    simp only [Adjunction.comp_unit_app]
    dsimp only [a, b', c', d]
    let siteAdj := MorphismProperty.Over.mapPullbackAdj @Etale ⊤ e
      (inferInstance : Etale e) trivial
    let t := M.obj.map (siteAdj.counit.app S.unop).op
    change ((Sheaf.restrictCoextendScalarsAdj V.smallEtaleTopology φ).unit.app M).hom.app S ≫
        (ModuleCat.coextendScalars φ).map ((ModuleCat.restrictScalars φ).map t) =
      t ≫ ((Sheaf.restrictCoextendScalarsAdj U.smallEtaleTopology φ).unit.app
        ((localizationRestriction (ModuleCat B) e inferInstance).obj M)).hom.app _
    rw [restrictCoextendScalarsAdj_unit_app_hom_app,
      restrictCoextendScalarsAdj_unit_app_hom_app]
    exact ((ModuleCat.restrictCoextendScalarsAdj.{u + 1} φ).unit.naturality t).symm
  change ((a.comp b).leftAdjointUniq (c.comp d)).hom = _
  have hleft := leftUniq_whiskerLeft a b b'
  have hright := leftUniq_whiskerRight c' c d
  have hcomp := congrArg₂ (fun f g ↦ f ≫ g) hleft hright
  calc
    _ = ((a.comp b).leftAdjointUniq (a.comp b')).hom ≫
        ((c'.comp d).leftAdjointUniq (c.comp d)).hom := by
      rw [← hadj, Adjunction.leftAdjointUniq_trans]
    _ = _ := by
      refine hcomp.trans ?_
      rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem ordinary_scalar_mate_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {W V : Scheme.{u}} (r : W ⟶ V)
    (M : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (ProEtale.etaleSheafExtendScalarsAdjunction φ V).unit.app
        ((lowerStar (ModuleCat.{u + 1} A) r).obj M) ≫
      (Sheaf.restrictScalars V.smallEtaleTopology φ).map
        ((compactificationOrdinaryScalarMate φ r).app M) =
      (lowerStar (ModuleCat.{u + 1} A) r).map
        ((ProEtale.etaleSheafExtendScalarsAdjunction φ W).unit.app M) := by
  have ht := iterated_mateEquiv_conjugateEquiv
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r)
    (ProEtale.etaleSheafExtendScalarsAdjunction φ V)
    (ProEtale.etaleSheafExtendScalarsAdjunction φ W)
    (TwoSquare.mk _ _ _ _ (scalarSheafPullbackIso φ r).hom)
  have h := unit_mateEquiv
    (ProEtale.etaleSheafExtendScalarsAdjunction φ W)
    (ProEtale.etaleSheafExtendScalarsAdjunction φ V)
    (TwoSquare.mk _ _ _ _ (compactificationOrdinaryScalarMate φ r)) M
  change _ ≫ (mateEquiv _ _ (mateEquiv _ _
    (TwoSquare.mk _ _ _ _ (scalarSheafPullbackIso φ r).hom))).app _ = _ at h
  dsimp only [TwoSquare.natTrans] at ht
  rw [ht] at h
  simp only [scalarSheafPullbackIso, conjugateIsoEquiv_symm_apply_hom,
    Equiv.apply_symm_apply, lowerStarCompRestrictScalarsIso, Iso.symm_hom,
    Iso.refl_inv, NatTrans.id_app, TwoSquare.mk, Functor.id_obj, Functor.comp_obj] at h
  erw [Category.comp_id] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem scalar_open_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U W : Scheme.{u}} (j : U ⟶ W) [IsOpenImmersion j]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).unit.app M ≫
      (upperStar (ModuleCat.{u + 1} A) j).map
        ((ProEtale.etaleSheafExtendScalarsAdjunction φ W).unit.app _) ≫
      (upperStar (ModuleCat.{u + 1} A) j).map
        ((Sheaf.restrictScalars W.smallEtaleTopology φ).map
          ((openScalarExtensionZero φ j).hom.app M)) ≫
      (upperStarRestrictScalarsIsoSheaf φ j).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} B) j).obj
          ((ProEtale.etaleSheafExtendScalars φ U).obj M)) =
    (ProEtale.etaleSheafExtendScalarsAdjunction φ U).unit.app M ≫
      (Sheaf.restrictScalars U.smallEtaleTopology φ).map
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j).unit.app
          ((ProEtale.etaleSheafExtendScalars φ U).obj M)) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).comp
      (ProEtale.etaleSheafExtendScalarsAdjunction φ W))
    (((ProEtale.etaleSheafExtendScalarsAdjunction φ U).comp
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)).ofNatIsoRight
        (openRestrictScalarsIso φ j)) M
  have h' := congrArg (fun t ↦ t ≫ (upperStarRestrictScalarsIsoSheaf φ j).hom.app
    ((openImmersionLowerShriek (ModuleCat.{u + 1} B) j).obj
      ((ProEtale.etaleSheafExtendScalars φ U).obj M))) h
  simp only [Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_map, Category.assoc] at h'
  rw [← openRestrictScalarsIso_inv_eq] at h'
  erw [Iso.hom_inv_id_app, Category.comp_id] at h'
  rw [openRestrictScalarsIso_inv_eq] at h'
  exact h'

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem scalar_open_to_direct
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U W : Scheme.{u}} (j : U ⟶ W) [IsOpenImmersion j]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (ProEtale.etaleSheafExtendScalarsAdjunction φ W).unit.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj M) ≫
      (Sheaf.restrictScalars W.smallEtaleTopology φ).map
        ((openScalarExtensionZero φ j).hom.app M) ≫
      (Sheaf.restrictScalars W.smallEtaleTopology φ).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} B) j).app
          ((ProEtale.etaleSheafExtendScalars φ U).obj M)) =
    (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) j).app M ≫
      (lowerStar (ModuleCat.{u + 1} A) j).map
        ((ProEtale.etaleSheafExtendScalarsAdjunction φ U).unit.app M) := by
  let N := (ProEtale.etaleSheafExtendScalars φ U).obj M
  have hc := mateEquiv_counit
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) j)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j)
    (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIsoSheaf φ j).hom) N
  have hm := underived_mate φ j
  dsimp only [TwoSquare.natTrans] at hm
  rw [hm] at hc
  simp only [lowerStarRestrictScalarsIso, Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp] at hc
  refine openImmersionLowerShriek_lowerStar_hom_ext (ModuleCat.{u + 1} A) j
    (f₁ := (show (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj M ⟶
      (lowerStar (ModuleCat.{u + 1} A) j).obj
        ((Sheaf.restrictScalars U.smallEtaleTopology φ).obj N) from
      (ProEtale.etaleSheafExtendScalarsAdjunction φ W).unit.app _ ≫
      (Sheaf.restrictScalars W.smallEtaleTopology φ).map
        ((openScalarExtensionZero φ j).hom.app M) ≫
      (Sheaf.restrictScalars W.smallEtaleTopology φ).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} B) j).app N)))
    (f₂ := (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) j).app M ≫
      (lowerStar (ModuleCat.{u + 1} A) j).map
        ((ProEtale.etaleSheafExtendScalarsAdjunction φ U).unit.app M)) ?_
  simp only [Functor.map_comp, Category.assoc]
  calc
    _ = (ProEtale.etaleSheafExtendScalarsAdjunction φ U).unit.app M := by
      erw [hc]
      have hn := (upperStarRestrictScalarsIsoSheaf φ j).hom.naturality
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} B) j).app N)
      dsimp only [Functor.comp_map] at hn
      erw [reassoc_of% hn]
      rw [reassoc_of% (scalar_open_unit φ j M)]
      rw [← Functor.map_comp, ← Functor.map_comp,
        unit_map_openImmersionLowerShriekToLowerStar_app_counit,
        CategoryTheory.Functor.map_id, Category.comp_id]
    _ = _ := by
      erw [(upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).counit_naturality]
      erw [unit_map_openImmersionLowerShriekToLowerStar_app_counit_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem scalar_compactification_to_direct
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) (c : Compactification e)
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (ProEtale.etaleSheafExtendScalarsAdjunction φ V).unit.app
        ((lowerStar (ModuleCat.{u + 1} A) c.g).obj
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).obj M)) ≫
      (Sheaf.restrictScalars V.smallEtaleTopology φ).map
        ((compactificationOrdinaryScalarMate φ c.g).app _) ≫
      (Sheaf.restrictScalars V.smallEtaleTopology φ).map
        ((lowerStar (ModuleCat.{u + 1} B) c.g).map
          ((openScalarExtensionZero φ c.i).hom.app M)) ≫
      (Sheaf.restrictScalars V.smallEtaleTopology φ).map
        ((compactificationSheafToDirectImage B c).app
          ((ProEtale.etaleSheafExtendScalars φ U).obj M)) =
    (compactificationSheafToDirectImage A c).app M ≫
      (lowerStar (ModuleCat.{u + 1} A) e).map
        ((ProEtale.etaleSheafExtendScalarsAdjunction φ U).unit.app M) := by
  rw [reassoc_of% (ordinary_scalar_mate_unit φ c.g _)]
  simp only [compactificationSheafToDirectImage, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  have hc : (Sheaf.restrictScalars V.smallEtaleTopology φ).map
      ((lowerStarComp (ModuleCat.{u + 1} B) c.i c.g e c.comm).hom.app
        ((ProEtale.etaleSheafExtendScalars φ U).obj M)) =
      (lowerStarComp (ModuleCat.{u + 1} A) c.i c.g e c.comm).hom.app
        ((Sheaf.restrictScalars U.smallEtaleTopology φ).obj
          ((ProEtale.etaleSheafExtendScalars φ U).obj M)) := rfl
  rw [hc]
  change (lowerStar (ModuleCat.{u + 1} A) c.g).map
      ((ProEtale.etaleSheafExtendScalarsAdjunction φ c.Z).unit.app _) ≫
    (lowerStar (ModuleCat.{u + 1} A) c.g).map
      ((Sheaf.restrictScalars c.Z.smallEtaleTopology φ).map
        ((openScalarExtensionZero φ c.i).hom.app M)) ≫
    (lowerStar (ModuleCat.{u + 1} A) c.g).map
      ((Sheaf.restrictScalars c.Z.smallEtaleTopology φ).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} B) c.i).app _)) ≫ _ = _
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc]
  erw [scalar_open_to_direct φ c.i M]
  rw [Functor.map_comp, Category.assoc]
  exact congrArg ((lowerStar (ModuleCat.{u + 1} A) c.g).map
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app M) ≫ ·)
      ((lowerStarComp (ModuleCat.{u + 1} A) c.i c.g e c.comm).hom.naturality
        ((ProEtale.etaleSheafExtendScalarsAdjunction φ U).unit.app M))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem scalar_sum_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).unit.app M ≫
      (localizationRestriction (ModuleCat.{u + 1} A) e inferInstance).map
        ((ProEtale.etaleSheafExtendScalarsAdjunction φ V).unit.app
          ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M)) ≫
      (localizationRestriction (ModuleCat.{u + 1} A) e inferInstance).map
        ((Sheaf.restrictScalars V.smallEtaleTopology φ).map
          ((sum_scalar_iso φ e).hom.app M)) =
    (ProEtale.etaleSheafExtendScalarsAdjunction φ U).unit.app M ≫
      (Sheaf.restrictScalars U.smallEtaleTopology φ).map
        ((etaleLowerShriekAdjunction (ModuleCat.{u + 1} B) e inferInstance).unit.app _) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).comp
      (ProEtale.etaleSheafExtendScalarsAdjunction φ V))
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ U).comp
      (etaleLowerShriekAdjunction (ModuleCat.{u + 1} B) e inferInstance)) M
  simpa only [sum_scalar_iso, Sheaf.restrictScalars, Adjunction.comp_unit_app,
    Functor.comp_map, Category.assoc, Functor.comp_obj, Functor.id_obj] using h

private theorem transported_unit_app
    {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {G H : D ⥤ C}
    (adj : F ⊣ G) (i : G ≅ H) (M : C) :
    (adj.ofNatIsoRight i).unit.app M = adj.unit.app M ≫ i.hom.app _ := by
  rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.homEquiv_id]

section
attribute [local semireducible] etaleLowerShriek

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem sum_unit_to_direct
    (A : Type (u + 1)) [CommRing A] {U V : Scheme.{u}} (e : U ⟶ V)
    [Etale e] [IsSeparated e]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).unit.app M ≫
      (localizationRestriction (ModuleCat.{u + 1} A) e inferInstance).map
        (etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) e M) =
      (lowerStarUnit (ModuleCat.{u + 1} A) e).app M := by
  have hu : (etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) e).unit.app M =
      (etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).unit.app M := by
    let i := upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e inferInstance
    have h₁ := transported_unit_app
      (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance) i M
    have h₂ := transported_unit_app
      (etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance) i.symm M
    calc
      _ = (etaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) e inferInstance).unit.app M ≫ i.hom.app _ := h₁
      _ = ((etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).unit.app M ≫
          i.inv.app _) ≫ i.hom.app _ := by
        dsimp only [etaleLowerShriekUpperStarAdjunction, etaleLowerShriekAdjunction,
          etaleLowerShriek, localizationRestriction] at h₂ ⊢
        exact congrArg (fun t ↦ t ≫ i.hom.app _) h₂
      _ = _ := by
        rw [Category.assoc, Iso.inv_hom_id_app]
        exact Category.comp_id _
  have h := ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) e).homEquiv
    M ((lowerStar (ModuleCat.{u + 1} A) e).obj M)).apply_symm_apply
      ((lowerStarUnit (ModuleCat.{u + 1} A) e).app M)
  change (etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) e).unit.app M ≫
    (localizationRestriction (ModuleCat.{u + 1} A) e inferInstance).map
      (etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) e M) = _ at h
  rwa [hu] at h

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem scalar_sum_to_direct
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] [IsSeparated e]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (ProEtale.etaleSheafExtendScalarsAdjunction φ V).unit.app
        ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M) ≫
      (Sheaf.restrictScalars V.smallEtaleTopology φ).map
        ((sum_scalar_iso φ e).hom.app M) ≫
      (Sheaf.restrictScalars V.smallEtaleTopology φ).map
        (etaleLowerShriekToLowerStar (ModuleCat.{u + 1} B) e
          ((ProEtale.etaleSheafExtendScalars φ U).obj M)) =
    etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) e M ≫
      (lowerStar (ModuleCat.{u + 1} A) e).map
        ((ProEtale.etaleSheafExtendScalarsAdjunction φ U).unit.app M) := by
  apply ((etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).homEquiv
    M _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  erw [reassoc_of% (scalar_sum_unit φ e M), reassoc_of% (sum_unit_to_direct A e M)]
  change (ProEtale.etaleSheafExtendScalarsAdjunction φ U).unit.app M ≫
    (Sheaf.restrictScalars U.smallEtaleTopology φ).map
      ((etaleLowerShriekAdjunction (ModuleCat.{u + 1} B) e inferInstance).unit.app _) ≫
    (Sheaf.restrictScalars U.smallEtaleTopology φ).map
      ((localizationRestriction (ModuleCat.{u + 1} B) e inferInstance).map
        (etaleLowerShriekToLowerStar (ModuleCat.{u + 1} B) e _)) = _
  rw [← Functor.map_comp, sum_unit_to_direct]
  erw [sheafCompose_map_lowerStarUnit_app (ModuleCat.{u + 1} B) e
    (ModuleCat.{u + 1} A) (ModuleCat.restrictScalars φ)]
  exact (lowerStarUnit (ModuleCat.{u + 1} A) e).naturality
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ U).unit.app M)


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem scalar_graph_compat
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V)
    [Etale e] [IsSeparated e] [QuasiCompact e] (c : Compactification e)
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (ProEtale.etaleSheafExtendScalars φ V).map
        ((etaleCompactificationGraphMap A e c).app M) ≫
      (compactificationOrdinaryScalarMate φ c.g).app _ ≫
      (lowerStar (ModuleCat.{u + 1} B) c.g).map
        ((openScalarExtensionZero φ c.i).hom.app M) =
    (sum_scalar_iso φ e).hom.app M ≫
      (etaleCompactificationGraphMap B e c).app
        ((ProEtale.etaleSheafExtendScalars φ U).obj M) := by
  obtain ⟨L, ι, hi, hfac⟩ := compactification_support_factor B e
  obtain ⟨α, hα⟩ := hfac c
  let N := (ProEtale.etaleSheafExtendScalars φ U).obj M
  have hmono_app (S : V.Etaleᵒᵖ) : Mono ((ι.app N).hom.app S) :=
    (ModuleCat.mono_iff_injective _).2 (hi N S.unop)
  have : Mono (ι.app N).hom := NatTrans.mono_of_mono_app _
  have hmono : Mono (ι.app N) :=
    Sheaf.Hom.mono_of_presheaf_mono V.smallEtaleTopology (ModuleCat.{u + 1} B) _
  have he : α.hom.app N ≫ ι.app N =
      (compactificationSheafToDirectImage B c).app N := by
    exact congrArg (fun t ↦ t.app N) hα
  have : Mono ((compactificationSheafToDirectImage B c).app N) := by
    rw [← he]
    have : Mono (α.hom.app N) := inferInstanceAs (Mono ((α.app N).hom))
    exact mono_comp (α.hom.app N) (ι.app N)
  apply (cancel_mono ((compactificationSheafToDirectImage B c).app N)).1
  apply ((ProEtale.etaleSheafExtendScalarsAdjunction φ V).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  erw [← (ProEtale.etaleSheafExtendScalarsAdjunction φ V).unit.naturality_assoc]
  have hcomp := scalar_compactification_to_direct φ e c M
  have hpre := congrArg (fun t ↦ (etaleCompactificationGraphMap A e c).app M ≫ t) hcomp
  have ha := congrArg (fun t ↦ t ≫ (lowerStar (ModuleCat.{u + 1} A) e).map
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ U).unit.app M))
    (compactSupportGraphSheafComparison_normalization A e c M)
  have hb := congrArg (fun t ↦
    (ProEtale.etaleSheafExtendScalarsAdjunction φ V).unit.app
        ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M) ≫
      (Sheaf.restrictScalars V.smallEtaleTopology φ).map ((sum_scalar_iso φ e).hom.app M) ≫
      (Sheaf.restrictScalars V.smallEtaleTopology φ).map t)
    (compactSupportGraphSheafComparison_normalization B e c N)
  simp only [Functor.map_comp] at hb
  exact hpre.trans (ha.trans ((scalar_sum_to_direct φ e M).symm.trans hb.symm))


private lemma scalar_tensor_section_action
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {T : Scheme.{u}}
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (S : T.Etale)
    (m : M.obj.obj (op S)) (b : (scalarCoefficientSheaf φ T).obj.obj (op S)) :
    compactificationScalarTensorSection φ M S m b =
      ((ρ_ ((ProEtale.etaleSheafExtendScalars φ T).obj M)).hom.hom.app (op S))
        (etaleSheafTensorSection B _ (𝟙_ _) S
          (((ProEtale.etaleSheafExtendScalarsAdjunction φ T).unit.app M).hom.app (op S) m)
          b) := by
  let N := (ProEtale.etaleSheafExtendScalars φ T).obj M
  let η := (ProEtale.etaleSheafExtendScalarsAdjunction φ T).unit.app M
  have h := congr_app (μ_sheafToPresheaf_comp_map_μ_sheafCompose T.smallEtaleTopology
    (ModuleCat.restrictScalars.{u + 1} φ) N (𝟙_ _)) (op S)
  simp only [NatTrans.comp_app] at h
  have hη := congr_app (Functor.LaxMonoidal.μ_natural_left
    (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) η
      (scalarCoefficientSheaf φ T)) (op S)
  simp only [NatTrans.comp_app, Monoidal.whiskerRight_app] at hη
  change (η.hom.app (op S) ▷ _) ≫ _ = _ ≫ (η ▷ _).hom.app (op S) at hη
  have ht : (η.hom.app (op S) ▷ _ : _ ⟶ _)
      (m ⊗ₜ[A] b) = (η.hom.app (op S) m) ⊗ₜ[A] b := by
    exact TensorProduct.map_tmul _ _ _ _
  have hη' := congrArg (fun f ↦ f (m ⊗ₜ[A] b)) hη
  simp only [ModuleCat.comp_apply] at hη'
  erw [ht] at hη'
  have h' := congrArg (fun f ↦ f ((η.hom.app (op S) m) ⊗ₜ[A] b)) h
  simp only [ModuleCat.comp_apply] at h'
  dsimp only [compactificationScalarTensorSection, scalarSheafTensorMap,
    etaleSheafTensorSection, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  simp only [ModuleCat.comp_apply]
  dsimp only [η, Functor.id_obj] at hη'
  erw [← hη']
  change ((ρ_ N).hom.hom.app (op S)) (_) = _
  congr 1
  erw [h']
  change ((Functor.LaxMonoidal.μ (sheafToPresheaf T.smallEtaleTopology
    (ModuleCat.{u + 1} B)) N (𝟙_ _)).app (op S))
      ((Functor.LaxMonoidal.μ (ModuleCat.restrictScalars.{u + 1} φ)
    (N.obj.obj (op S)) ((𝟙_ _ : Sheaf T.smallEtaleTopology (ModuleCat B)).obj.obj
      (op S))) ((η.hom.app (op S) m) ⊗ₜ[A] b)) = _
  rw [ModuleCat.restrictScalars_μ_tmul]

private instance map_continuous {U V : Scheme.{u}} {e : U ⟶ V} (h : Etale e) :
    (MorphismProperty.Over.map ⊤ h).IsContinuous U.smallEtaleTopology V.smallEtaleTopology :=
  inferInstanceAs ((MorphismProperty.Over.map ⊤ h).IsContinuous
    (U.smallGrothendieckTopology @Etale) (V.smallGrothendieckTopology @Etale))

private noncomputable instance restriction_lax
    (B : Type (u + 1)) [CommRing B] {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] :
    (localizationRestriction (ModuleCat.{u + 1} B) e inferInstance).LaxMonoidal :=
  inferInstanceAs
    ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).sheafPushforwardContinuous
      (ModuleCat.{u + 1} B)
      U.smallEtaleTopology V.smallEtaleTopology).LaxMonoidal

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem literal_coefficient_unit
    (B : Type (u + 1)) [CommRing B] {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] :
    Functor.LaxMonoidal.ε (localizationRestriction (ModuleCat.{u + 1} B) e
        inferInstance) ≫
      (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} B) e inferInstance).inv.app (𝟙_ _) ≫
      (Functor.Monoidal.εIso (upperStar (ModuleCat.{u + 1} B) e)).inv = 𝟙 _ := by
  erw [← NatTrans.IsMonoidal.unit (τ := (upperStarIsoSheafPushforward
    (ModuleCat.{u + 1} B) e inferInstance).hom)]
  rw [Category.assoc, Iso.hom_inv_id_app_assoc]
  exact (Functor.Monoidal.εIso (upperStar (ModuleCat.{u + 1} B) e)).hom_inv_id

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem literal_action_with_unit
    (B : Type (u + 1)) [CommRing B] {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (k : (localizationRestriction (ModuleCat.{u + 1} B) e inferInstance).obj (𝟙_ _) ⟶
      (𝟙_ (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} B))))
    (hu : ∀ N, Functor.LaxMonoidal.μ
        (localizationRestriction (ModuleCat.{u + 1} B) e inferInstance) N (𝟙_ _) ≫
      (localizationRestriction (ModuleCat.{u + 1} B) e inferInstance).map (ρ_ N).hom =
        ((localizationRestriction (ModuleCat.{u + 1} B) e inferInstance).obj N ◁ k) ≫
          (ρ_ ((localizationRestriction (ModuleCat.{u + 1} B) e inferInstance).obj N)).hom)
    (N : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)) (S : U.Etale)
    (x : N.obj.obj (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj S)))
    (b : (𝟙_ (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B))).obj.obj
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj S))) :
    ((ρ_ N).hom.hom.app
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj S)))
      (etaleSheafTensorSection B N (𝟙_ _) _ x b) =
    ((ρ_ ((localizationRestriction (ModuleCat.{u + 1} B) e inferInstance).obj N)).hom.hom.app
      (op S))
      (etaleSheafTensorSection B _ (𝟙_ _) S x
        (k.hom.app (op S) b)) := by
  let I := localizationRestriction (ModuleCat.{u + 1} B) e inferInstance
  have h := Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    (MorphismProperty.Over.map ⊤ (inferInstance : Etale e)) (ModuleCat.{u + 1} B)
    U.smallEtaleTopology V.smallEtaleTopology N (𝟙_ _) (op S)
  have h' := congrArg (fun t ↦ t ≫ (I.map (ρ_ N).hom).hom.app (op S)) h
  rw [Category.assoc] at h'
  change _ ≫ ((Functor.LaxMonoidal.μ I N (𝟙_ _) ≫ I.map (ρ_ N).hom).hom.app
    (op S)) = _ at h'
  rw [hu N] at h'
  have hv := congr_app (Functor.LaxMonoidal.μ_natural_right
    (sheafToPresheaf U.smallEtaleTopology (ModuleCat.{u + 1} B))
      ((I.obj N)) k) (op S)
  simp only [NatTrans.comp_app, Monoidal.whiskerLeft_app] at hv
  have hx := congrArg (fun t ↦ t (x ⊗ₜ[B] b)) h'
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ModuleCat.comp_apply] at hx
  have hv' := congrArg (fun t ↦ t (x ⊗ₜ[B] b)) hv
  simp only [ModuleCat.comp_apply] at hv'
  erw [← hv'] at hx
  have ht : (_ ◁ k.hom.app (op S)) (x ⊗ₜ[B] b) =
      x ⊗ₜ[B] (k.hom.app (op S) b) := TensorProduct.map_tmul _ _ _ _
  erw [ht] at hx
  exact hx.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem literal_action
    (B : Type (u + 1)) [CommRing B] {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (N : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)) (S : U.Etale)
    (x : N.obj.obj (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj S)))
    (b : (𝟙_ (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B))).obj.obj
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj S))) :
    ((ρ_ N).hom.hom.app
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj S)))
      (etaleSheafTensorSection B N (𝟙_ _) _ x b) =
    ((ρ_ ((localizationRestriction (ModuleCat.{u + 1} B) e inferInstance).obj N)).hom.hom.app
      (op S))
      (etaleSheafTensorSection B _ (𝟙_ _) S x
        ((((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} B) e inferInstance).inv.app
            (𝟙_ _) ≫
          (Functor.Monoidal.εIso (upperStar (ModuleCat.{u + 1} B) e)).inv).hom.app
            (op S)) b)) := by
  let I := localizationRestriction (ModuleCat.{u + 1} B) e inferInstance
  let k : I.obj (𝟙_ _) ⟶ (𝟙_ _) :=
    (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} B) e inferInstance).inv.app
      (𝟙_ _) ≫ (Functor.Monoidal.εIso (upperStar (ModuleCat.{u + 1} B) e)).inv
  have he : Functor.LaxMonoidal.ε I ≫ k = 𝟙 _ := literal_coefficient_unit B e
  have : IsIso (Functor.LaxMonoidal.ε I) := by
    erw [← NatTrans.IsMonoidal.unit (τ := (upperStarIsoSheafPushforward
      (ModuleCat.{u + 1} B) e inferInstance).hom)]
    infer_instance
  have hk : k = inv (Functor.LaxMonoidal.ε I) := by
    apply (cancel_epi (Functor.LaxMonoidal.ε I)).1
    rw [he, IsIso.hom_inv_id]
  have hu (P : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)) :
      Functor.LaxMonoidal.μ I P (𝟙_ _) ≫ I.map (ρ_ P).hom =
        (I.obj P ◁ k) ≫ (ρ_ (I.obj P)).hom := by
    rw [Functor.LaxMonoidal.right_unitality I P,
      ← MonoidalCategory.whiskerLeft_comp_assoc, hk, IsIso.inv_hom_id]
    simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp]
  exact literal_action_with_unit B e k hu N S x b

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem scalar_coefficient_lift
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (S : U.Etale)
    (b : (scalarCoefficientSheaf φ V).obj.obj
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj S))) :
    (compactificationCoefficientPullbackIso φ e).hom.hom.app (op S)
      (etaleLiftSection A e (scalarCoefficientSheaf φ V) S b) =
    (((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} B) e inferInstance).inv.app (𝟙_ _) ≫
      (Functor.Monoidal.εIso (upperStar (ModuleCat.{u + 1} B) e)).inv).hom.app (op S)) b := by
  have hl := congrArg (fun f ↦ f b)
    (etaleLiftSection_iso A e (scalarCoefficientSheaf φ V) S)
  simp only [ModuleCat.comp_apply] at hl
  change (((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e
    inferInstance).inv.app (scalarCoefficientSheaf φ V)).hom.app (op S)) b =
      etaleLiftSection A e (scalarCoefficientSheaf φ V) S b at hl
  rw [← hl]
  have h := congrArg (fun t ↦ t.app (𝟙_ _)) (literal_scalar_pullback φ e)
  dsimp only [Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app] at h
  have hc := congrArg (fun t ↦ t ≫
    (Sheaf.restrictScalars U.smallEtaleTopology φ).map
      (Functor.Monoidal.εIso (upperStar (ModuleCat.{u + 1} B) e)).inv) h
  have hi := (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e
    inferInstance).inv_hom_id_app (scalarCoefficientSheaf φ V)
  have hi' := congrArg (fun f ↦ f b)
    (congr_app (Sheaf.hom_ext_iff.1 hi) (op S))
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
    NatTrans.comp_app, ModuleCat.comp_apply, NatTrans.id_app, ModuleCat.id_apply] at hi'
  have hx := congrArg (fun (t :
    (upperStar (ModuleCat.{u + 1} A) e).obj (scalarCoefficientSheaf φ V) ⟶ _) ↦
      t.hom.app (op S)
        (((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e
          inferInstance).inv.app (scalarCoefficientSheaf φ V)).hom.app (op S) b)) hc
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ModuleCat.comp_apply] at hx
  erw [hi'] at hx
  exact hx


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem action_natural
    (B : Type (u + 1)) [CommRing B] {T : Scheme.{u}}
    {M N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)} (f : M ⟶ N)
    (S : T.Etale) (x : M.obj.obj (op S))
    (b : (𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))).obj.obj (op S)) :
    f.hom.app (op S) ((ρ_ M).hom.hom.app (op S)
      (etaleSheafTensorSection B M (𝟙_ _) S x b)) =
    (ρ_ N).hom.hom.app (op S)
      (etaleSheafTensorSection B N (𝟙_ _) S (f.hom.app (op S) x) b) := by
  have h := congr_app (Functor.LaxMonoidal.μ_natural_left
    (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) f (𝟙_ _)) (op S)
  simp only [NatTrans.comp_app, Monoidal.whiskerRight_app] at h
  have h' := congrArg (fun t ↦ t ≫ (ρ_ N).hom.hom.app (op S)) h
  rw [Category.assoc] at h'
  change _ = _ ≫ ((f ▷ _ ≫ (ρ_ N).hom).hom.app (op S)) at h'
  rw [rightUnitor_naturality] at h'
  have hx := congrArg (fun t ↦ t (x ⊗ₜ[B] b)) h'
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ModuleCat.comp_apply] at hx
  have ht : (f.hom.app (op S) ▷ _) (x ⊗ₜ[B] b) =
      (f.hom.app (op S) x) ⊗ₜ[B] b := TensorProduct.map_tmul _ _ _ _
  erw [ht] at hx
  exact hx.symm

private theorem sum_section_eq_unit
    (A : Type (u + 1)) [CommRing A] {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (S : U.Etale) (x : M.obj.obj (op S)) :
    etaleSumSection A e M S x =
      ((etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).unit.app M).hom.app
        (op S) x := by
  erw [projection_sum_unit A e M S]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem scalar_unit_sheet
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (S : U.Etale) (x : M.obj.obj (op S)) :
    ((sum_scalar_iso φ e).hom.app M).hom.app
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj S))
      (((ProEtale.etaleSheafExtendScalarsAdjunction φ V).unit.app _).hom.app
        (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj S))
        (etaleSumSection A e M S x)) =
    etaleSumSection B e ((ProEtale.etaleSheafExtendScalars φ U).obj M) S
      (((ProEtale.etaleSheafExtendScalarsAdjunction φ U).unit.app M).hom.app (op S) x) := by
  rw [sum_section_eq_unit, sum_section_eq_unit]
  have h := congrArg (fun (t : M ⟶ _) ↦ t.hom.app (op S) x)
    (scalar_sum_unit φ e M)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ModuleCat.comp_apply, localizationRestriction_map_hom_app, Sheaf.restrictScalars,
    sheafCompose_map_hom, Functor.whiskerRight_app] at h
  erw [ModuleCat.restrictScalars.map_apply, ModuleCat.restrictScalars.map_apply] at h
  exact h

/-- The specified ordinary compactified B-linear counit mate is the local sheet
coefficient map. The two isomorphisms nu are fixed by their inverses being the
already constructed graph-extension maps; rho is fixed by its local tensor formula.
Using natural transformations records both naturality in M and étale restriction.

Source: Stacks, more-etale.tex, Tags 0GKF and 0GL6; etale-cohomology.tex,
Tags 03S5 and 0F4L; sites-modules.tex, Tag 03EL
(blueprint: lem-sp-etale-compactification-sheaf-scalar-map).

Proof:
1. Apply lem-pur-etale-sheaf-projection-map with N = B_V. The constant-ring
inverse-image comparison of prop-weil-pbc-inverse-image-modules-exact pulls b back
along each lift. The resulting balanced pairing is B-linear and defines rho.
2. The pure-tensor normalization of
lem-weil-pbc-algebraic-inverse-image-tensor-comparison identifies the reassociation
in pi with the inverse-image tensor comparison and the constant-ring pullback.
3. Transpose the pairing using lem-sfb-site-inverse-image-bilinear-adjunction.
The geometric triangle identity cancels the first unit/counit pair, and the second
factor is the constant coefficient pullback. Thus pi sends t tensor b to
 t tensor gamma_B(b) in sections over W times_V S.
4. The graph normalization of lem-asd-etale-compact-support-normalization identifies
nu_A inverse with extension of the given sheet components by zero. The map
openScalarExtensionZero from lem-coef-etale-open-tensor preserves these components.
Reading them with nu_B therefore gives x_s tensor b_s on every lift.
5. By lem-pc-sites-module-sheafification-tensor the source is the sheafification of
the local finite-sum tensor presheaf. Pure tensors and individual lift summands
generate it. The uniqueness in def-weil-pbc-sheafification proves the equality.
6. On a module map a both paths give a(x_s) tensor b_s; under restriction the
coefficients and lifts restrict together. Additivity handles merging lifts, empty
supports and the zero sheaf. For B = 0 every tensor is zero, while a unital map
from A = 0 forces B = 0. No flatness or globally split sheet cover is used. -/
theorem etaleCompactificationSheafScalarMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian V] [CompactSpace V]
    (c : Compactification e) :
    ∃ (νA : openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
          lowerStar (ModuleCat.{u + 1} A) c.g ≅
        etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance)
      (νB : openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i ⋙
          lowerStar (ModuleCat.{u + 1} B) c.g ≅
        etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance),
      νA.inv = etaleCompactificationGraphMap A e c ∧
      νB.inv = etaleCompactificationGraphMap B e c ∧
      ∃ ρ : etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ⋙
            ProEtale.etaleSheafExtendScalars φ V ⟶
          ProEtale.etaleSheafExtendScalars φ U ⋙
            etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance,
        (∀ M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A),
          (ProEtale.etaleSheafExtendScalars φ V).map (νA.inv.app M) ≫
              (compactificationOrdinaryScalarMate φ c.g).app
                ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).obj M) ≫
              (lowerStar (ModuleCat.{u + 1} B) c.g).map
                ((openScalarExtensionZero φ c.i).hom.app M) ≫
              νB.hom.app ((ProEtale.etaleSheafExtendScalars φ U).obj M) = ρ.app M) ∧
        ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (S : U.Etale)
          (x : M.obj.obj (op S))
          (b : (scalarCoefficientSheaf φ V).obj.obj
            (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj S))),
          (ρ.app M).hom.app
              (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj S))
              (compactificationScalarTensorSection φ _
                ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj S)
                (etaleSumSection A e M S x) b) =
            etaleSumSection B e ((ProEtale.etaleSheafExtendScalars φ U).obj M) S
              (compactificationScalarTensorSection φ M S x
                ((compactificationCoefficientPullbackIso φ e).hom.hom.app (op S)
                  (etaleLiftSection A e (scalarCoefficientSheaf φ V) S b))) := by
  have := compactification_graph_isIso A e c
  have := compactification_graph_isIso B e c
  refine ⟨(asIso (etaleCompactificationGraphMap A e c)).symm,
    (asIso (etaleCompactificationGraphMap B e c)).symm, rfl, rfl, ?_⟩
  let ρ := (sum_scalar_iso φ e).hom
  refine ⟨ρ, ?_, ?_⟩
  · intro M
    dsimp only [ρ]
    have h := scalar_graph_compat φ e c M
    have h' := congrArg (fun t ↦ t ≫
      (asIso (etaleCompactificationGraphMap B e c)).inv.app
        ((ProEtale.etaleSheafExtendScalars φ U).obj M)) h
    have hc := (asIso (etaleCompactificationGraphMap B e c)).hom_inv_id_app
      ((ProEtale.etaleSheafExtendScalars φ U).obj M)
    simp only [asIso_hom] at hc
    simp only [Category.assoc, hc] at h'
    erw [Category.comp_id] at h'
    exact h'
  · intro M S x b
    dsimp only [ρ]
    rw [scalar_tensor_section_action]
    erw [action_natural B ((sum_scalar_iso φ e).hom.app M)]
    rw [scalar_unit_sheet]
    erw [literal_action B e _ S]
    rw [scalar_tensor_section_action, scalar_coefficient_lift]
    simp only [sum_section_eq_unit]
    exact (action_natural B
      ((etaleLowerShriekAdjunction (ModuleCat.{u + 1} B) e inferInstance).unit.app
        ((ProEtale.etaleSheafExtendScalars φ U).obj M)) S
      (((ProEtale.etaleSheafExtendScalarsAdjunction φ U).unit.app M).hom.app (op S) x)
      _).symm

end AlgebraicGeometry.Etale
