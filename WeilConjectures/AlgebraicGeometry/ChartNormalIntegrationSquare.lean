/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralChartComparisons
public import WeilConjectures.AlgebraicGeometry.ChartDncVectorFactorData
public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
import all WeilConjectures.AlgebraicGeometry.SectionExceptionalFibreCoherence
import all WeilConjectures.AlgebraicGeometry.DiagonalEtaleSourceEndpoint
import WeilConjectures.AlgebraicGeometry.FiniteBundleSectionAdjointBaseChange
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

/-! # Integration under the actual normal differential

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-orientation/
sk-prop-sp-orientation-charts.proof.md, Steps 2--4; parent comparison proof Step 8.
(blueprint: lem-pur-chart-normal-integration-square).

The equation uses the actual normal-square comparison, the integration-normalized
normal-bundle identification, and the canonical shifted Tate coefficient pullback.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting.ChartComparisons

private theorem section_locality_square (P : PurityFiniteSetting.{u})
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    {B B' X X' Y Y' : Scheme.{u}}
    [IsNoetherian B] [IsNoetherian B'] [IsNoetherian X] [IsNoetherian X']
    [IsNoetherian Y] [IsNoetherian Y']
    (d : ℕ) (f : X ⟶ B) (f' : X' ⟶ B') (q : Y ⟶ B) (q' : Y' ⟶ B')
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f']
    [HasCompactification q] [HasCompactification q']
    [QuasiCompact f'] [QuasiCompact q']
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d q]
    [HasInvertibleExponent P.Coefficient X] [HasInvertibleExponent P.Coefficient Y]
    (a : Y ⟶ X) [Etale a] [IsSeparated a] [QuasiCompact a]
    (a' : Y' ⟶ X') [Etale a'] [IsSeparated a'] [QuasiCompact a']
    (ha : a ≫ f = q) (ha' : a' ≫ f' = q')
    (s : B ⟶ X) (s' : B' ⟶ X') (z : B ⟶ Y) (z' : B' ⟶ Y')
    (hz : z ≫ a = s) (hz' : z' ≫ a' = s')
    (b : B' ⟶ B) (r : X' ⟶ X) (v : Y' ⟶ Y)
    (sq : IsPullback r f' f b) (sqv : IsPullback v q' q b)
    (hs : s' ≫ r = b ≫ s) (hzz : z' ≫ v = b ≫ z)
    (hcomm : a' ≫ r = v ≫ a) :
    (Etale.ordinaryFinitePullback P.Coefficient b).mapIso
        (P.chartSectionEtaleRestriction N a f q ha s z hz) ≪≫
        Dnc.sectionBaseChange P.Coefficient d q sqv z z' hzz =
      Dnc.sectionBaseChange P.Coefficient d f sq s s' hs ≪≫
        P.chartSectionEtaleRestriction N a' f' q' ha' s' z' hz' := by
  have hac : HasCompactification (a ≫ f) := HasCompactification.of_eq ha.symm
  have hac' : HasCompactification (a' ≫ f') := HasCompactification.of_eq ha'.symm
  have squ : IsPullback v a' a r := by
    have ho := sqv
    rw [← ha, ← ha'] at ho
    exact ho.of_bot hcomm.symm sq
  have hd := Etale.structural_locality_baseChange P.Coefficient a f a' f' q ha q' ha'
    b r v sq squ sqv
  have hc := Etale.section_pullback_locality_comp P.Coefficient b
    s s' z z' a a' r v hs.symm hzz.symm hz hz' squ.w
    (Etale.dualizingComplex P.Coefficient f)
  have hn := ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      b z).symm ≪≫
    Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      z' v (b ≫ z) hzz.symm).hom.naturality
    (Etale.sectionStructuralLocalityIso P.Coefficient a f q ha).hom
  have hloc := DiagonalEtaleComparison.locality_tensorMate_congr
    P.Coefficient N a f q ha
  have hloc' := DiagonalEtaleComparison.locality_tensorMate_congr
    P.Coefficient N a' f' q' ha'
  simp only [Functor.comp_map, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc] at hn
  unfold Etale.sectionCoherencePullbackIso at hd hc
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc] at hd hc
  apply Iso.ext
  dsimp only [chartSectionEtaleRestriction, Dnc.sectionBaseChange,
    Etale.sectionInvariant, Etale.dualizingComplex]
  rw [← hloc, ← hloc']
  simp only [Etale.ordinaryFinitePullback,
    Iso.trans_hom, Iso.app_hom, Iso.app_inv, Iso.symm_hom, Functor.mapIso_hom,
    asIso_hom, Functor.map_comp, Category.assoc]
  erw [reassoc_of% hn]
  rw [← CategoryTheory.Functor.map_comp, ← hd]
  simp only [Functor.map_comp]
  erw [reassoc_of% hc]
  have hn' := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    z' a' s' hz'.symm).hom.naturality
    (Etale.dualizingComplexBaseChangeMap P.Coefficient sq)
  simp only [Functor.comp_map] at hn'
  erw [← reassoc_of% hn']
  simp only [Etale.dualizingComplex]

private theorem invert_integration_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} {X' Y' : D} (o : X ≅ Y) (o' : X' ≅ Y')
    (c : F.obj X ≅ X') (t : F.obj Y ≅ Y')
    (h : F.map o.inv ≫ c.hom = t.hom ≫ o'.inv) :
    F.mapIso o ≪≫ t = c ≪≫ o' := by
  apply Iso.ext
  apply (cancel_epi (F.mapIso o).inv).mp
  simp only [Iso.trans_hom, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change t.hom = (F.map o.inv ≫ c.hom) ≫ o'.hom
  rw [h, Category.assoc, o'.inv_hom_id, Category.comp_id]

private theorem compared_integration_square
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    (F : C ⥤ D) (G : E ⥤ H) (ν : C ⥤ E) (ν' : D ⥤ H)
    {X T : C} {X' T' : D} {S : E} {S' : H}
    (γ : S ≅ ν.obj X) (γ' : S' ≅ ν'.obj X')
    (c : F.obj X ≅ X') (b : X ≅ T) (b' : X' ≅ T') (t : F.obj T ≅ T')
    (pX : G.obj (ν.obj X) ≅ ν'.obj (F.obj X))
    (pT : G.obj (ν.obj T) ≅ ν'.obj (F.obj T))
    (hn : G.mapIso (ν.mapIso b) ≪≫ pT = pX ≪≫ ν'.mapIso (F.mapIso b))
    (hb : F.mapIso b ≪≫ t = c ≪≫ b') :
    γ' ≪≫ ν'.mapIso c.symm ≪≫ pX.symm ≪≫ G.mapIso γ.symm ≪≫
        G.mapIso (γ ≪≫ ν.mapIso b) ≪≫ pT ≪≫ ν'.mapIso t =
      γ' ≪≫ ν'.mapIso b' := by
  calc
    _ = γ' ≪≫ ν'.mapIso c.symm ≪≫ pX.symm ≪≫
        (G.mapIso (ν.mapIso b) ≪≫ pT) ≪≫ ν'.mapIso t := by
      simp only [Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_assoc,
        Iso.symm_self_id_assoc]
    _ = γ' ≪≫ ν'.mapIso (c.symm ≪≫ F.mapIso b ≪≫ t) := by
      rw [hn]
      simp only [Functor.mapIso_trans, Iso.trans_assoc, Iso.symm_self_id_assoc]
    _ = γ' ≪≫ ν'.mapIso b' := by rw [hb, Iso.symm_self_id_assoc]

/-- Integration commutes with the actual normal differential of every etale chart map.
Source: orientation-charts proof, Steps 2--4; parent comparison proof Step 8.
(blueprint: lem-pur-chart-normal-integration-square).

Proof: normalGeometry makes the actual normal differential Cartesian and preserves
its zero section. Conjugate it by the canonical conormal models, whose projection and
zero-section equations give a Cartesian bundle square. Counit-normalized etale locality
commutes with exceptional exchange; pull this equation to the sections. The zero-section
integration adjunct commutes with the bundle square by bundleSectionAdjoint_baseChange.
Invert the adjunct square, identifying its normalized Tate transport with t by uniqueness,
and compose it with the locality square. Finally apply site-comparison naturality and
cancel the normal-section and model comparisons. The argument applies unchanged in rank
zero, on the empty scheme, and for arbitrary finite ramified coefficients. -/
theorem chart_normal_integration_square (P : PurityFiniteSetting.{u})
    {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B : Chart V d} (e : Map C B)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    r P aV e ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e.hom).leftDerivedFunctor.mapIso
        (ChartFactors.beta P d B.proj aV N) ≪≫
      (Dnc.pullComparison P e.hom (P.diagonalTwistEtale B.X d) ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) C.X).mapDerivedCategory.mapIso
          (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates t e.hom
            (P.diagonalExponent_isUnit (B.proj ≫ aV)) d)) =
      ChartFactors.beta P d C.proj aV N := by
  let := P.noetherian (B.proj ≫ aV)
  let := P.noetherian (C.proj ≫ aV)
  let := (chartDiagonalNormalBundle d B.proj).1
  let := (chartDiagonalNormalBundle d C.proj).1
  let pB := pullback.fst B.proj B.proj
  let pC := pullback.fst C.proj C.proj
  let sB := pullback.diagonal B.proj
  let sC := pullback.diagonal C.proj
  let πB := Scheme.Hom.normalConeProj pB sB
  let πC := Scheme.Hom.normalConeProj pC sC
  let zB := sB.normalConeZeroSection
  let zC := sC.normalConeZeroSection
  let FB := ConormalGradedAlgebra.piece sB 1
  let FC := ConormalGradedAlgebra.piece sC 1
  let qB := VectorBundleZeroSection.π B.X d FB
  let qC := VectorBundleZeroSection.π C.X d FC
  let wB := VectorBundleZeroSection.zero B.X d FB
  let wC := VectorBundleZeroSection.zero C.X d FC
  let MB := chartNormalModel d B.proj
  let MC := chartNormalModel d C.proj
  have hMB : MB.hom ≫ πB = qB := (chartNormal_model_exists d B.proj).exists.choose_spec.2.1
  have hMC : MC.hom ≫ πC = qC := (chartNormal_model_exists d C.proj).exists.choose_spec.2.1
  have hzB : wB ≫ MB.hom = zB := (chartNormal_model_exists d B.proj).exists.choose_spec.2.2
  have hzC : wC ≫ MC.hom = zC := (chartNormal_model_exists d C.proj).exists.choose_spec.2.2
  let n := DiagonalEtaleComparison.normalMap d B.proj C.proj e.hom e.over_eq
  have hn := DiagonalEtaleComparison.normalGeometry d B.proj C.proj e.hom e.over_eq
  let v := MC.hom ≫ n ≫ MB.inv
  have hcomm : MC.hom ≫ n = v ≫ MB.hom := by simp [v]
  have sqv : IsPullback v qC qB e.hom := by
    apply hn.1.of_iso' MC MB (Iso.refl _) (Iso.refl _)
    · exact hcomm
    · simpa using hMC
    · simpa using hMB
    · simp
  have hzv : wC ≫ v = e.hom ≫ wB := by
    dsimp only [v]
    rw [← Category.assoc, hzC, ← Category.assoc, hn.2, Category.assoc]
    have hb : zB ≫ MB.inv = wB := by
      rw [← hzB, Category.assoc, MB.hom_inv_id, Category.comp_id]
    exact congrArg (fun k ↦ e.hom ≫ k) hb
  let : SmoothOfRelativeDimension d πB :=
    (Scheme.Hom.normalConeData d (pullback.diagonal_fst B.proj)).smoothOfRelativeDimension_proj
  let : SmoothOfRelativeDimension d πC :=
    (Scheme.Hom.normalConeData d (pullback.diagonal_fst C.proj)).smoothOfRelativeDimension_proj
  let := SmoothOfRelativeDimension.smooth d πB
  let := SmoothOfRelativeDimension.smooth d πC
  let := Dnc.normalQuasiCompact d pB sB (pullback.diagonal_fst B.proj)
  let := Dnc.normalQuasiCompact d pC sC (pullback.diagonal_fst C.proj)
  let := Dnc.normalCompactifiable P d pB (B.proj ≫ aV) sB (pullback.diagonal_fst B.proj)
  let := Dnc.normalCompactifiable P d pC (C.proj ≫ aV) sC (pullback.diagonal_fst C.proj)
  let := P.noetherian (πB ≫ B.proj ≫ aV)
  let := P.noetherian (πC ≫ C.proj ≫ aV)
  let := (Etale.vectorIntegration_geometry B.X d FB).1
  let := (Etale.vectorIntegration_geometry B.X d FB).2.1
  let := (Etale.vectorIntegration_geometry C.X d FC).1
  let := (Etale.vectorIntegration_geometry C.X d FC).2.1
  let := Dnc.compactifiable P qB (B.proj ≫ aV)
  let := Dnc.compactifiable P qC (C.proj ≫ aV)
  let := P.noetherian (qB ≫ B.proj ≫ aV)
  let := P.noetherian (qC ≫ C.proj ≫ aV)
  let : IsSeparated πB := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsSeparated MB.hom, hMB]
    infer_instance
  let : SmoothOfRelativeDimension d qB := by
    rw [← hMB]
    exact MorphismProperty.RespectsIso.precomp _ _ _ inferInstance
  let := Dnc.invertibleExponent P (πB ≫ B.proj ≫ aV)
  let := Dnc.invertibleExponent P (qB ≫ B.proj ≫ aV)
  let cB := P.chartSectionEtaleRestriction N MB.hom πB qB hMB zB wB hzB
  let cC := P.chartSectionEtaleRestriction N MC.hom πC qC hMC zC wC hzC
  let cn := Dnc.sectionBaseChange P.Coefficient d πB hn.1 zB zC hn.2
  let cv := Dnc.sectionBaseChange P.Coefficient d qB sqv wB wC hzv
  have hlocal : (Etale.ordinaryFinitePullback P.Coefficient e.hom).mapIso cB ≪≫ cv =
      cn ≪≫ cC :=
    section_locality_square P N d πB πC qB qC MB.hom MC.hom hMB hMC
      zB zC wB wC hzB hzC e.hom n v hn.1 sqv hn.2 hzv hcomm
  let oB := Etale.FiniteRingSectionDeformation.bundleOrientation P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates B.X (P.diagonalExponent_isUnit (B.proj ≫ aV)) d FB
  let oC := Etale.FiniteRingSectionDeformation.bundleOrientation P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates C.X (P.diagonalExponent_isUnit (C.proj ≫ aV)) d FC
  let τ := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates t e.hom
    (P.diagonalExponent_isUnit (B.proj ≫ aV)) d
  have ht := Etale.ordinaryFiniteTwistTransport_unique P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates t
    (purityTwistTransport P.Coefficient P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates)
  have hi := Etale.FiniteRingSectionDeformation.bundleSectionAdjoint_baseChange
    P.Coefficient P.diagonalExponent (pow_pos P.coefficients.prime.out.pos P.level)
    P.diagonalExponent_annihilates (P.diagonalExponent_isUnit (B.proj ≫ aV))
    (P.diagonalExponent_isUnit (C.proj ≫ aV)) d FB FC e.hom v sqv hzv
  have hor : (Etale.ordinaryFinitePullback P.Coefficient e.hom).mapIso oB ≪≫ τ =
      cv ≪≫ oC := by
    apply invert_integration_square
    dsimp only [oB, oC, Etale.FiniteRingSectionDeformation.bundleOrientation,
      Iso.symm_inv, asIso_hom, cv, Dnc.sectionBaseChange, Iso.trans_hom,
      Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom, τ]
    rw [ht]
    exact hi
  have hβ : (Etale.ordinaryFinitePullback P.Coefficient e.hom).mapIso (cB ≪≫ oB) ≪≫ τ =
      cn ≪≫ (cC ≪≫ oC) := by
    rw [Functor.mapIso_trans, Iso.trans_assoc, hor, ← Iso.trans_assoc, hlocal,
      Iso.trans_assoc]
  have hcomp := compared_integration_square
    (Etale.ordinaryFinitePullback P.Coefficient e.hom)
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e.hom).leftDerivedFunctor
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) B.X).mapDerivedCategory
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) C.X).mapDerivedCategory
    (Dnc.normalComparison P d pB (B.proj ≫ aV) sB (pullback.diagonal_fst B.proj))
    (Dnc.normalComparison P d pC (C.proj ≫ aV) sC (pullback.diagonal_fst C.proj))
    cn (cB ≪≫ oB) (cC ≪≫ oC) τ
    (Dnc.pullComparison P e.hom (Dnc.normalEtale P d pB
      (B.proj ≫ aV) sB (pullback.diagonal_fst B.proj)))
    (Dnc.pullComparison P e.hom (P.diagonalTwistEtale B.X d))
    (Dnc.pullComparison_naturality P e.hom (cB ≪≫ oB)) hβ
  simpa only [r, normal, DiagonalEtaleComparison.normal, ChartFactors.beta,
    ChartFactors.normalBundleComparison, cB, cC, oB, oC, cn, τ,
    Functor.mapIso_trans, Iso.trans_assoc] using hcomp

end WeilConjectures.PurityFiniteSetting.ChartComparisons
