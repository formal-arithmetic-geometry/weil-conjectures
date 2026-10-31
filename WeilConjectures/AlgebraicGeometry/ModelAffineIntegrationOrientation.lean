/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompositionModelOrientationDefinitions

import WeilConjectures.AlgebraicGeometry.ModelAffineIntegrationOrientationNormalized
import WeilConjectures.AlgebraicGeometry.AffineIntegrationDirectSumCoordinates
import WeilConjectures.AlgebraicGeometry.AffineStandardSectionOrientationBaseChange
import WeilConjectures.AlgebraicGeometry.OrderedTateCoefficientComposition
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackDerivedCoherence
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedTensorPullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! # A step of the model orientation descent argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

attribute [local implicit_reducible] diagonalTwist diagonalOrdinaryDualizing
  Etale.dualizingComplex

private theorem oriented_locality (P : PurityFiniteSetting.{u})
    {W X B : Scheme.{u}} (r : ℕ) (f : X ⟶ B)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension r f]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (j : W ⟶ X) [Etale j] [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    [SmoothOfRelativeDimension r (j ≫ f)]
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := P.noetherian aB
    letI := P.noetherian (f ≫ aB)
    letI := P.noetherian ((j ≫ f) ≫ aB)
    letI := Dnc.compactifiable P f aB
    letI := Dnc.compactifiable P (j ≫ f) aB
    (Etale.ordinaryFinitePullback P.Coefficient j).map
        (P.chartDualizingUnit f ≪≫ P.chartOrdinaryOrientation r f aB).hom ≫
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t j (P.diagonalExponent_isUnit (f ≫ aB)) r).hom =
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) j).app _ ≪≫
        (Etale.tensorMateEtalePrecompLocalityIso P.Coefficient N j f).app (𝟙_ _)).hom ≫
        (P.chartDualizingUnit (j ≫ f) ≪≫
          P.chartOrdinaryOrientation r (j ≫ f) aB).hom := by
  let := P.noetherian aB
  let := P.noetherian (f ≫ aB)
  let := P.noetherian ((j ≫ f) ≫ aB)
  let := Dnc.compactifiable P f aB
  let := Dnc.compactifiable P (j ≫ f) aB
  let ell := Functor.isoWhiskerLeft
      (Etale.rightDerivedUpperShriek P.Coefficient f)
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) j) ≪≫
    Etale.tensorMateEtalePrecompLocalityIso P.Coefficient N j f
  have hu := ell.hom.naturality (smoothPurityUnitIso P.Coefficient B).inv
  have h := P.chartOrientation_etale_restriction r f aB j N t
  simp only [Iso.trans_hom, Functor.map_comp, Category.assoc]
  rw [h]
  simpa only [chartDualizingUnit, diagonalEtaleLocality, ell, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Etale.ordinaryFinitePullback,
    Etale.dualizingComplex, diagonalOrdinaryDualizing, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app,
    NatTrans.comp_app, Functor.comp_map, Category.assoc] using!
    congrArg (fun z ↦ z ≫ (P.chartOrdinaryOrientation r (j ≫ f) aB).hom) hu

private theorem section_locality (P : PurityFiniteSetting.{u})
    {W X B : Scheme.{u}} (r : ℕ) (f : X ⟶ B)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension r f]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (j : W ⟶ X) [Etale j] [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    (q : W ⟶ B) [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q]
    [SmoothOfRelativeDimension r q] (w : j ≫ f = q)
    (s : B ⟶ X) (s' : B ⟶ W) (hs : s' ≫ j = s)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := P.noetherian aB
    letI := P.noetherian (f ≫ aB)
    letI := P.noetherian (q ≫ aB)
    letI := Dnc.compactifiable P f aB
    letI := Dnc.compactifiable P q aB
    P.chartSectionEtaleRestriction N j f q w s s' hs ≪≫
        P.chartSectionOrientation r q aB s' t =
      P.chartSectionOrientation r f aB s t := by
  subst q
  subst s
  let := P.noetherian aB
  let := P.noetherian (f ≫ aB)
  let := P.noetherian ((j ≫ f) ≫ aB)
  let := Dnc.compactifiable P f aB
  let := Dnc.compactifiable P (j ≫ f) aB
  let S := Etale.ordinaryFinitePullback P.Coefficient s'
  let R := Etale.ordinaryFinitePullback P.Coefficient (s' ≫ j)
  let L := P.chartDualizingUnit f ≪≫ P.chartOrdinaryOrientation r f aB
  let L' := P.chartDualizingUnit (j ≫ f) ≪≫ P.chartOrdinaryOrientation r (j ≫ f) aB
  let ell := (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) j).app _ ≪≫
      (Etale.tensorMateEtalePrecompLocalityIso P.Coefficient N j f).app (𝟙_ _)
  let c := Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) s' j
  have h := oriented_locality P r f aB j N t
  have ht := Etale.orderedTateCoefficientComposition P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates t s' j (s' ≫ j) rfl
    (P.diagonalExponent_isUnit (f ≫ aB))
    (P.diagonalExponent_isUnit ((j ≫ f) ≫ aB)) r
  have hn := c.hom.naturality L.hom
  apply Iso.ext
  simp only [chartSectionEtaleRestriction, eqToIso_refl, Iso.trans_refl,
    chartSectionOrientation, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc]
  change c.hom.app _ ≫ S.map ell.hom ≫ S.map L'.hom ≫ _ = R.map L.hom ≫ _
  rw [← S.map_comp_assoc, ← h, S.map_comp, ← Category.assoc,
    ← Category.assoc]
  dsimp only [Functor.comp_map] at hn
  erw [← hn]
  simp only [Category.assoc]
  erw [ht]
  rfl

private theorem beta_presentation (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (x : U ⟶ DiagonalPasting.A d V) [Etale x]
    (hx : x ≫ DiagonalPasting.pr d V = h)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    P.chartDiagonalBeta d h aV t =
      P.chartNormalCoordinateComparison d h aV x hx N ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
          (by
            letI := DiagonalPasting.affineDimension d U
            exact P.chartSectionOrientation d (DiagonalPasting.pr d U) (h ≫ aV)
              (DiagonalPasting.zero d U) t) := by
  let := P.noetherian (h ≫ aV)
  let q := Scheme.Hom.normalConeProj (pullback.fst h h) (pullback.diagonal h)
  let z := (pullback.diagonal h).normalConeZeroSection
  let : SmoothOfRelativeDimension d q :=
    (Scheme.Hom.normalConeData d (pullback.diagonal_fst h)).smoothOfRelativeDimension_proj
  let := Dnc.normalQuasiCompact d (pullback.fst h h)
    (pullback.diagonal h) (pullback.diagonal_fst h)
  let := Dnc.normalCompactifiable P d (pullback.fst h h) (h ≫ aV)
    (pullback.diagonal h) (pullback.diagonal_fst h)
  let := P.noetherian (q ≫ (h ≫ aV))
  let := DiagonalPasting.affineDimension d U
  let := (chartNormalCoordinateMap_spec d h x hx).1
  have hs := section_locality P d (DiagonalPasting.pr d U) (h ≫ aV)
    (chartNormalCoordinateMap d h x hx) q (chartNormalCoordinateMap_spec d h x hx).2.1
    (DiagonalPasting.zero d U) z (chartNormalCoordinateMap_spec d h x hx).2.2 N t
  dsimp only [chartNormalCoordinateComparison, chartDiagonalBeta]
  have hs' := congrArg (fun k ↦
    (P.chartSectionEtaleRestriction N (chartNormalCoordinateMap d h x hx)
      (DiagonalPasting.pr d U) q (chartNormalCoordinateMap_spec d h x hx).2.1
      (DiagonalPasting.zero d U) z (chartNormalCoordinateMap_spec d h x hx).2.2).symm ≪≫ k) hs
  simp only [Iso.symm_self_id_assoc] at hs'
  erw [hs']
  simp only [Functor.mapIso_trans, Iso.trans_assoc]
  rfl

private theorem model_zero_presentation (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (r : ℕ)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := DiagonalPasting.affineDimension r B
    P.modelOrientationZero P.modelAffineCanonicalGamma B r aB =
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.mapIso
        (P.chartSectionOrientation r (DiagonalPasting.pr r B) aB
          (DiagonalPasting.zero r B)
          t) := by
  let tc := Etale.projectiveLineTraceTransport P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates
  have ht : t = tc := Etale.ordinaryFiniteTwistTransport_unique _ _ _ t tc
  subst t
  let := P.noetherian aB
  let := P.noetherian (DiagonalPasting.pr r B ≫ aB)
  let := DiagonalPasting.affineDimension r B
  let := Dnc.compactifiable P (DiagonalPasting.pr r B) aB
  have h := (P.chartOrdinaryOrientation_spec r (DiagonalPasting.pr r B) aB).2
  unfold modelOrientationZero modelAffineCanonicalGamma
  dsimp only [Iso.symm_symm_eq]
  rw [h]
  simp only [Iso.symm_self_id_assoc]
  unfold modelOrientationTwistPullback
  erw [← Iso.trans_assoc
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (DiagonalPasting.zero r B)).leftDerivedFunctor.mapIso
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) (DiagonalPasting.A r B)).mapDerivedCategory.mapIso
          (P.chartOrdinaryOrientation r (DiagonalPasting.pr r B) aB)))]
  erw [Dnc.pullComparison_naturality]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, ← Functor.mapIso_trans]
  simp only [chartSectionOrientation, Functor.mapIso_trans, Iso.trans_assoc]
  rfl

private theorem beta_model (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (x : U ⟶ DiagonalPasting.A d V) [Etale x]
    (hx : x ≫ DiagonalPasting.pr d V = h)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    P.chartDiagonalBeta d h aV t =
      P.chartNormalCoordinateComparison d h aV x hx N ≪≫
        P.modelOrientationZero P.modelAffineCanonicalGamma U d (h ≫ aV) := by
  rw [model_zero_presentation P U (h ≫ aV) d t]
  exact beta_presentation P d h aV x hx t N

private theorem model_zero_baseChange (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V] (r : ℕ) (f : U ⟶ V)
    [LocallyOfFiniteType f] [QuasiCompact f]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV] :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
        (P.modelOrientationZero P.modelAffineCanonicalGamma V r aV) ≪≫
      P.modelOrientationTwistPullback f aV r =
      P.compatibleStandardPullback r f aV ≪≫
        P.modelOrientationZero P.modelAffineCanonicalGamma U r (f ≫ aV) := by
  let := DiagonalPasting.affineDimension r V
  let := DiagonalPasting.affineDimension r U
  let t := Etale.projectiveLineTraceTransport P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates
  rw [model_zero_presentation P V aV r t,
    model_zero_presentation P U (f ≫ aV) r t]
  have h := P.affine_standard_section_orientation_baseChange r f aV t
  dsimp only [Etale.ordinaryFinitePullback] at h
  unfold modelOrientationTwistPullback compatibleStandardPullback
  erw [← Iso.trans_assoc, Dnc.pullComparison_naturality]
  simp only [Iso.trans_assoc, ← Functor.mapIso_trans]
  erw [h]
  rfl

/-- The ordered integration comparisons give normalized affine orientations, their
zero-section multiplication, and the three normal-coordinate beta identifications.
Source: thm-pur-composition-coherence.proof.md, Step 1, expanded in model descent
Steps 2--5 (blueprint: lem-pur-model-affine-integration-orientation).

Proof: identify the ordered affine comparison at every positive coefficient level
with the integration transpose. Its inverse is the normalized vector-bundle orientation
by projection purity agreement. Transport through the prescribed ordered coordinate
isomorphism to obtain G; no arbitrary affine frame is selected. The identity adjunction
at rank zero gives the unit equation. Apply integration-normalized direct-sum purity
to the two coordinate bundles and transport its projection and compositor through
the proper/open site comparisons. Coefficient-counit normalization rewrites its
coefficient-dependent transpose as theta applied to the unit transpose. Naturality
and cancellation of these invertible transposes give the affine equation. Pull back
along the total zero section; the prescribed base-change maps identify its two factors
with b_d and b_e, proving zero-section multiplication. The normal-bundle frames of the
compatible DNC charts identify their integration-normalized beta maps with these b_r.
The same unit and empty-frame formulas handle zero rank and empty bases. -/
theorem model_affine_integration_orientation (P : PurityFiniteSetting.{u}) (d e : ℕ) :
    ∃ G : P.ModelAffineGamma,
      P.ModelGammaNormalization G ∧ P.ModelGammaZeroNormalization ∧
      (∀ (B : Scheme.{u}) [IsAffine B] (aB : B ⟶ Spec (.of P.field.k))
        [LocallyOfFiniteType aB] [QuasiCompact aB],
        ModelAffineOrientationEquation P G B d e aB ∧
          ModelZeroOrientationEquation P G B d e aB) ∧
      ∀ (U V T : Scheme.{u}) [IsAffine U] [IsAffine V] [IsAffine T]
        (f : U ⟶ V) (g : V ⟶ T)
        [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
        [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
        [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
        (aT : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT] [QuasiCompact aT],
          ModelChartBetaIdentification P G d e f g aT := by
  obtain ⟨hn, hz⟩ := P.model_affine_integration_orientation_normalized
  refine ⟨P.modelAffineCanonicalGamma, hn, hz, ?_, ?_⟩
  · intro B _ aB _ _
    exact P.affine_integration_directSum_coordinates B d e aB
  · intro U V T _ _ _ f g _ _ _ _ _ _ _ _ aT _ _
    let := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
    intro x y _ _ hx hy t N
    let := (composition_compatible_tangent_normal P d e f g aT x y hx hy).2.1
    refine ⟨beta_model P d f (g ≫ aT) x hx t N, ?_, ?_⟩
    · rw [beta_model P e g aT y hy t N, Functor.mapIso_trans, Iso.trans_assoc,
        model_zero_baseChange]
    · simpa only [modelOrientationZero, ← Category.assoc] using!
        beta_model P (d + e) (f ≫ g) aT (compatibleCompositeChart d e f g x y)
          (composition_compatible_tangent_normal P d e f g aT x y hx hy).2.2 t N

end WeilConjectures.PurityFiniteSetting
