/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.VectorTensorSiteEquations

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleZeroSection
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SmoothPurity.Ringed.RingedTopoiDerivedTensorPullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerMap
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegration
public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorBundlePurity
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import all WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.VectorLocalTraceExponent
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.SupportedProjectiveChernComparison
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.OrderedIntegrationComparison
import all WeilConjectures.AlgebraicGeometry.Comparison.ComparisonOpenTensorCoherence
public import WeilConjectures.AlgebraicGeometry.Open.OpenProjectionSiteTransport
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedSiteAdjunctionTranspose
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundlePurity
import all WeilConjectures.AlgebraicGeometry.Vector.VectorBundlePurity
import all WeilConjectures.AlgebraicGeometry.Bounded.BoundedSiteAdjunctionTranspose
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.VectorTensorProjectionComparison
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.VectorTensorOrdinaryNormalization

/-! # Site comparison of normalized vector-bundle integration
Source: Stacks 099R, 09AF and 0B65; main-20261015, vector-bundle integration
(blueprint: lem-pur-vector-integration-site-comparison).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite
variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

/-- The displayed canonical comparison equations, packaged as a proposition.
Source: Stacks 099R, 09AF, 0B65 and the vector-bundle integration formulas
(blueprint: lem-pur-vector-integration-site-comparison). -/
def ProjectiveCompatibility (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (hI : (ProjectiveLine.infinity S).ker.IsInvertible)
    (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) : Prop :=
    ((comparison (Scheme.finiteTateCoefficient l E n) S).map
        (Etale.projectiveLineTraceDatum (l ^ (r + 1))
          (pow_pos (Fact.out : l.Prime).pos _) _ hA S
          (by simpa only [Nat.cast_pow] using hS.pow (r + 1))).decomposition.hom ≫
      (directImage (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S ↘ S)
        (linePlus l E n r hA (ProjectiveLine S))).hom =
      projectiveSum l E n r hA S ≫ projectiveB l E n S hS hI r hA) ∧
    ((directImage (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S ↘ S)
        (linePlus l E n r hA (ProjectiveLine S))).hom ≫
      projectiveTrace l E n S hS hI r hA =
      (comparison (Scheme.finiteTateCoefficient l E n) S).map
        (Etale.projectiveLineTrace (l ^ (r + 1))
          (pow_pos (Fact.out : l.Prime).pos _) _ hA S
          (by simpa only [Nat.cast_pow] using hS.pow (r + 1)))) ∧
    projectiveH l E n S hS hI r hA ≫ projectiveTrace l E n S hS hI r hA =
      𝟙 (unit (Scheme.finiteTateCoefficient l E n) S)

private theorem mate_adjunct
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') {U : C ⥤ C'} {V : D ⥤ D'}
    (e : U ⋙ L' ≅ L ⋙ V) {X : C} {Y : D} (g : L.obj X ⟶ Y) :
    U.map (a.homEquiv X Y g) ≫ (mateEquiv a b e.hom).app Y =
      b.homEquiv _ _ (e.hom.app X ≫ V.map g) := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  have hn := (mateEquiv a b e.hom).naturality g
  change U.map (R.map g) ≫ (mateEquiv a b e.hom).app Y =
    (mateEquiv a b e.hom).app (L.obj X) ≫ R'.map (V.map g) at hn
  rw [hn]
  rw [← Category.assoc, unit_mateEquiv]
  simp only [Functor.id_obj, Category.assoc]

private theorem directImage_eq_push (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (directImage A f J).hom = geoP1PushComparison A f J.obj := by
  unfold directImage
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom]
  rw [← pushComparison_plus A f J]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  change (comparison A Y).map (𝟙 ((Etale.ordinaryFinitePushforward A f).obj J.obj)) ≫
    geoP1PushComparison A f J.obj = _
  exact (congrArg (fun v ↦ v ≫ geoP1PushComparison A f J.obj)
    ((comparison A Y).map_id _)).trans (Category.id_comp _)

private theorem directImage_adjunct (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : Etale.DerivedCategoryModule A Y)
    (J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (g : (Etale.ordinaryFinitePullback A f).obj K ⟶ J.obj) :
    (comparison A Y).map
        ((Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _ g) ≫
      (directImage A f J).hom =
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
      ((pullback A f).inv.app K ≫ (comparison A X).map g) := by
  have h := mate_adjunct
    (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (geoP1PullComparison A f) g
  rw [mate_app_homEquiv] at h
  rw [directImage_eq_push A f J]
  unfold pullback
  exact h

/-- Comparison carries the ordinary decomposition to the two actual supported-Kummer
components. Source: projective-line trace and Stacks 099R, 0B65
(blueprint: lem-pur-vector-integration-site-comparison).
Proof: the mate's counit equation carries the adjunct of the ordinary Kummer class
to the supported pro-etale class. At the identity it carries the shifted twisted
unit. The two biproduct injections detect equality. Invert the decomposition and
compose with the second projection for the trace equation and its +1 normalization.
-/
theorem projectiveComparison (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (hI : (ProjectiveLine.infinity S).ker.IsInvertible)
    (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    ProjectiveCompatibility l E n S hS hI r hA := by
  let A := Scheme.finiteTateCoefficient l E n
  let N := l ^ (r + 1)
  let D := Etale.projectiveLineTraceDatum N (pow_pos (Fact.out : l.Prime).pos _) A hA S
    (by simpa only [N, Nat.cast_pow] using hS.pow (r + 1))
  have hu : (comparison A S).map
      (Etale.ordinaryFiniteP1Unit A N hA
        (Etale.projectiveLineTraceTransport N (pow_pos (Fact.out : l.Prime).pos _) A hA)
        S (by simpa only [N, Nat.cast_pow] using hS.pow (r + 1))) ≫
        (directImage A (ProjectiveLine S ↘ S) (linePlus l E n r hA (ProjectiveLine S))).hom =
      projectiveU l E n S hS r hA := by
    unfold Etale.ordinaryFiniteP1Unit projectiveU
    with_unfolding_all
      simpa only [Adjunction.homEquiv_unit, Etale.ordinaryFinitePushforward] using
      directImage_adjunct A (ProjectiveLine S ↘ S) _
        (linePlus l E n r hA (ProjectiveLine S))
        (Etale.ordinaryFiniteShiftedLinePullback A N hA
          (Etale.projectiveLineTraceTransport N (pow_pos (Fact.out : l.Prime).pos _) A hA)
          (ProjectiveLine S ↘ S)
          (by simpa only [N, Nat.cast_pow] using hS.pow (r + 1))).hom
  have hh : (comparison A S).map
      (Etale.ordinaryFiniteP1ChernPushforward A N hA S D.chern) ≫
        (directImage A (ProjectiveLine S ↘ S) (linePlus l E n r hA (ProjectiveLine S))).hom =
      projectiveH l E n S hS hI r hA := by
    have h := directImage_adjunct A (ProjectiveLine S ↘ S)
      (Etale.ordinaryFiniteUnit A S) (linePlus l E n r hA (ProjectiveLine S))
      ((Etale.ordinaryFiniteUnitPullback A (ProjectiveLine S ↘ S)).hom ≫ D.chern)
    rw [Etale.ordinaryFiniteP1ChernPushforward, h]
    unfold projectiveH
    congr 1
    rw [supportedProjectiveChern_comparison l E n S hS hI r hA]
    unfold pullbackUnit geoP1UnitPullback pullback
    simp only [Iso.trans_hom, Iso.symm_inv, Functor.mapIso_hom, Category.assoc]
    rw [← Functor.map_comp]
    with_unfolding_all rfl
  have hb : (comparison A S).map D.decomposition.hom ≫
      (directImage A (ProjectiveLine S ↘ S) (linePlus l E n r hA (ProjectiveLine S))).hom =
      projectiveSum l E n r hA S ≫ projectiveB l E n S hS hI r hA := by
    rw [D.decomposition_hom]
    let := preservesBinaryBiproducts_of_preservesBinaryCoproducts (comparison A S)
    unfold projectiveSum projectiveB
    change _ = ((comparison A S).mapBiprod
      ((Etale.ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)
      (Etale.ordinaryFiniteUnit A S)).hom ≫ _
    apply (cancel_epi ((comparison A S).mapBiprod
      ((Etale.ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)
      (Etale.ordinaryFiniteUnit A S)).inv).mp
    rw [← Category.assoc, biprod.mapBiprod_inv_map_desc, Iso.inv_hom_id_assoc]
    with_unfolding_all
      ext <;> simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc,
        biprod.inl_desc, biprod.inr_desc, hu, hh]
  refine ⟨hb, ?_, ?_⟩
  · unfold projectiveTrace geoP1Trace Etale.projectiveLineTrace
    let := projectiveB_isIso l E n S hS hI r hA
    apply (cancel_epi ((comparison A S).map D.decomposition.hom)).mp
    rw [reassoc_of% hb]
    simp only [asIso_inv, IsIso.hom_inv_id_assoc, projectiveSum]
    change _ = (comparison A S).map D.decomposition.hom ≫
      (comparison A S).map (D.decomposition.inv ≫ biprod.snd)
    rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_assoc]
    with_unfolding_all exact biprod.lift_snd _ _
  · unfold projectiveTrace geoP1Trace
    let := projectiveB_isIso l E n S hS hI r hA
    have hi : projectiveH l E n S hS hI r hA =
        biprod.inr ≫ projectiveB l E n S hS hI r hA := by
      simp only [projectiveB, biprod.inr_desc]
    rw [hi]
    simp only [Category.assoc, asIso_inv, IsIso.hom_inv_id_assoc]
    with_unfolding_all exact biprod.inr_snd

private theorem counit_square_of_unit
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') {U : C ⥤ C'} {V : D ⥤ D'}
    (e : U ⋙ L' ≅ L ⋙ V) (t : R ⋙ U ≅ V ⋙ R')
    (h : ∀ K, b.unit.app (U.obj K) ≫ R'.map (e.hom.app K) =
      U.map (a.unit.app K) ≫ t.hom.app (L.obj K)) (K : D) :
    V.map (a.counit.app K) = e.inv.app (R.obj K) ≫
      L'.map (t.hom.app K) ≫ b.counit.app (V.obj K) := by
  have hh : e.hom.app (R.obj K) ≫ V.map (a.counit.app K) =
      L'.map (t.hom.app K) ≫ b.counit.app (V.obj K) := by
    apply (b.homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
    rw [h]
    simp only [Category.assoc]
    have hn := t.hom.naturality (a.counit.app K)
    change U.map (R.map (a.counit.app K)) ≫ t.hom.app K =
      t.hom.app (L.obj (R.obj K)) ≫ R'.map (V.map (a.counit.app K)) at hn
    rw [← hn]
    simp only [← Category.assoc, ← U.map_comp, a.right_triangle_components]
    simp only [Category.assoc]
    rw [b.unit_naturality_assoc]
    simp only [Functor.comp_obj, b.right_triangle_components, Category.comp_id]
    exact (congrArg (fun f ↦ f ≫ t.hom.app K) (U.map_id (R.obj K))).trans
      (Category.id_comp _)
  rw [← cancel_epi (e.hom.app (R.obj K))]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  rw [hh]

/-- Exact extension comparison preserves the actual open counit.
Source: Stacks 09AF (blueprint: lem-pur-vector-integration-site-comparison).
Proof: both routes restrict to the identity. Transpose using the open adjunction;
its Hom bijection gives equality. Apply termwise to complexes and localize.
-/
theorem openCounitComparison {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (G : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparison A X).map
        (((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).ofNatIsoRight
            (Etale.leftDerivedUpperStarIsoMapDerivedCategory
              (ModuleCat.{u + 1} A) j).symm).counit.app G) =
      (openProjectionExtensionComparison A j).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj G) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
        ((openProjectionRestrictionComparison A j).hom.app G) ≫
      (openAdjunction A j).counit.app ((comparison A X).obj G) := by
  let B := ModuleCat.{u + 1} A
  let a := Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction B j
  let b := derivedOpenImmersionLowerShriekUpperStarAdjunction B j
  let e := (openProjectionExtensionComparison A j).symm
  let t := Functor.mapDerivedCategorySquareIso
    (F₁ := Etale.upperStar B j) (F₂ := comparisonUpperStar B U)
    (G₁ := comparisonUpperStar B X) (G₂ := upperStar B j)
    (supportSiteComparisonCoefficientPullbackIso B j)
  have h := counit_square_of_unit a b e t
    (comparison_derived_extension_mate A j) G
  dsimp only [a, b, e, t] at h
  rw [supportComparison_eq A j] at h
  simp only [openAdjunction, Adjunction.ofNatIsoRight_counit,
    openProjectionRestrictionComparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp,
    Iso.symm_hom, Iso.symm_inv, Category.assoc]
  rw [h]
  have hn := (openProjectionExtensionComparison A j).hom.naturality
    ((Etale.leftDerivedUpperStarIsoMapDerivedCategory B j).hom.app G)
  change (comparison A X).map
      ((Etale.openImmersionLowerShriek B j).mapDerivedCategory.map
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory B j).hom.app G)) ≫
      (openProjectionExtensionComparison A j).hom.app
        ((Etale.upperStar B j).mapDerivedCategory.obj G) =
    (openProjectionExtensionComparison A j).hom.app
        ((Etale.upperStar B j).leftDerivedFunctor.obj G) ≫
      (openImmersionLowerShriek B j).mapDerivedCategory.map
        ((comparison A U).map
          ((Etale.leftDerivedUpperStarIsoMapDerivedCategory B j).hom.app G)) at hn
  simp only [Iso.symm_inv]
  rw [reassoc_of% hn]
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.mapDerivedCategoryNatIso_symm, Functor.map_comp, Category.assoc]
  have hp := (openImmersionLowerShriek B j).mapDerivedCategory.map_comp
    ((leftDerivedUpperStarIsoMapDerivedCategory B j).inv.app ((comparison A X).obj G))
    ((leftDerivedUpperStarIsoMapDerivedCategory B j).hom.app ((comparison A X).obj G))
  rw [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id] at hp
  rw [← reassoc_of% hp]

/-- The displayed canonical comparison equations, packaged as a proposition.
Source: Stacks 099R, 09AF, 0B65 and the vector-bundle integration formulas
(blueprint: lem-pur-vector-integration-site-comparison). -/
def IntegrationCompatibility (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] : Prop :=
    VectorNormalization l E n S r hA d F hS
      (vectorIntegration l E n S r hA d F hS) ∧
    (vectorSite l E n S r hA d F hS).inv ≫
        vectorIntegration l E n S r hA d F hS =
      (comparison (Scheme.finiteTateCoefficient l E n) S).map
        (Etale.vectorBundleIntegration (l ^ (r + 1))
          (pow_pos (Fact.out : l.Prime).pos _) (Scheme.finiteTateCoefficient l E n) hA S
          (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F)

private theorem compared_pullback_unit (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : Etale.DerivedCategoryModule A Y} (g : K ⟶ Etale.ordinaryFiniteUnit A Y) :
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map
        ((comparison A Y).map g) ≫ (pullbackUnit A f).hom =
      (pullback A f).inv.app K ≫ (comparison A X).map
        ((Etale.ordinaryFinitePullback A f).map g ≫
          (Etale.ordinaryFiniteUnitPullback A f).hom) := by
  have hn := (pullback A f).inv.naturality g
  dsimp only [Functor.comp_map] at hn
  unfold pullbackUnit geoP1UnitPullback
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  unfold pullback at hn ⊢
  with_unfolding_all
    erw [← Category.assoc, hn, Category.assoc, ← CategoryTheory.Functor.map_comp]

private theorem localIntegration_comparison (S : Scheme.{u}) [IsNoetherian S]
    (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] (hS : IsUnit (l : Γ(S, ⊤)))
    (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V) :
    localIntegration l E n S hS r hA d F V e =
      (comparison (Scheme.finiteTateCoefficient l E n) V.toScheme).map
        (Etale.vectorIntegrationLocalTrace (l ^ (r + 1))
          (pow_pos (Fact.out : l.Prime).pos _) _ hA
          (Etale.projectiveLineTraceTransport _ (pow_pos (Fact.out : l.Prime).pos _) _ hA)
          (Etale.projectiveLineTraceDatum _ (pow_pos (Fact.out : l.Prime).pos _) _ hA)
          S (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F V e) := by
  let : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  unfold localIntegration
  rw [orderedIntegration_comparison]
  rw [← Functor.map_comp]
  unfold chartPrefix Etale.vectorIntegrationLocalTrace
  simp only [Category.assoc]

private theorem normalization_comparison (S : Scheme.{u}) [IsNoetherian S]
    (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] (hS : IsUnit (l : Γ(S, ⊤)))
    (g : Etale.vectorIntegrationSource (Scheme.finiteTateCoefficient l E n)
      (l ^ (r + 1)) hA S d F ⟶
        Etale.ordinaryFiniteUnit (Scheme.finiteTateCoefficient l E n) S)
    (hg : Etale.VectorIntegrationNormalization (l ^ (r + 1))
      (pow_pos (Fact.out : l.Prime).pos _) _ hA S
      (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F g) :
    VectorNormalization l E n S r hA d F hS
      ((vectorSite l E n S r hA d F hS).hom ≫
        (comparison (Scheme.finiteTateCoefficient l E n) S).map g) := by
  unfold VectorNormalization
  intro V e
  simp only [Functor.map_comp, Category.assoc]
  rw [compared_pullback_unit, localIntegration_comparison l E n S r hA d F,
    hg (Etale.projectiveLineTraceTransport _ (pow_pos (Fact.out : l.Prime).pos _) _ hA)
      (Etale.projectiveLineTraceDatum _ (pow_pos (Fact.out : l.Prime).pos _) _ hA) V e]

/-- The independent local pro-etale integrations glue and compare with the actual
ordinary global trace. Source: vector-bundle integration; Stacks 09AF, 099R
(blueprint: lem-pur-vector-integration-site-comparison).
Proof: compare the projective counit by inverse projection, tensor trace and the
unit equation. Restrict by the compared open counit, then induct on coordinates.
Pasting the compact-support comparisons gives the same chart prefixes. On each
frame this is the ordinary trace. Sources and targets are degree zero, so equality
glues by sheaf-Hom descent. Rank zero uses the identity tower; the empty base has
the unique morphism. None of these steps imposes flatness of A over Z/l^r.
-/
theorem vectorIntegrationSiteComparison (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    IntegrationCompatibility l E n S hS r hA d F := by
  unfold IntegrationCompatibility vectorIntegration
  let g := Etale.vectorBundleIntegration (l ^ (r + 1))
    (pow_pos (Fact.out : l.Prime).pos _) (Scheme.finiteTateCoefficient l E n) hA S
    (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F
  have hg : Etale.VectorIntegrationNormalization (l ^ (r + 1))
      (pow_pos (Fact.out : l.Prime).pos _) (Scheme.finiteTateCoefficient l E n) hA S
      (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F g :=
    (Etale.existsUnique_vectorIntegrationGluing (l ^ (r + 1))
      (pow_pos (Fact.out : l.Prime).pos _) (Scheme.finiteTateCoefficient l E n) hA S
      (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F).2.exists.choose_spec.2
  have ht := (existsUniqueVectorIntegration l E n S r hA d F hS).exists.choose_spec
  refine ⟨ht, ?_⟩
  apply (cancel_epi (vectorSite l E n S r hA d F hS).hom).mp
  rw [Iso.hom_inv_id_assoc]
  exact (existsUniqueVectorIntegration l E n S r hA d F hS).unique ht
    (normalization_comparison l E n S r hA d F hS g hg)

private theorem tensor_integration_square
    {C D : Type*} [Category C] [Category D]
    (V : C ⥤ D) (T : C ⥤ C) (U : D ⥤ D) (c : T ⋙ V ≅ V ⋙ U)
    {W Z I K : C} {W' Z' : D} (e : W' ≅ V.obj W)
    (b : Z' ≅ V.obj Z) (pe : Z ≅ T.obj W) (pp : Z' ≅ U.obj W')
    (t : W ⟶ I) (t' : W' ⟶ V.obj I) (r : T.obj I ⟶ K)
    (hp : c.hom.app W ≫ U.map e.inv ≫ pp.inv = V.map pe.inv ≫ b.inv)
    (ht : e.inv ≫ t' = V.map t) :
    b.inv ≫ pp.hom ≫ U.map t' ≫ c.inv.app I ≫ V.map r =
      V.map (pe.hom ≫ T.map t ≫ r) := by
  apply (cancel_epi (V.map pe.inv)).mp
  simp only [Functor.map_comp]
  rw [← reassoc_of% hp]
  simp only [Iso.inv_hom_id_assoc]
  rw [← U.map_comp_assoc, ht]
  have hn := c.hom.naturality t
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  simp only [Iso.hom_inv_id_app_assoc, ← V.map_comp_assoc, pe.inv_hom_id_assoc]

section TensorComparisonProof
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence
  Functor.mapDerivedCategory Etale.derivedTensor derivedTensor
  derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso compactSupportSiteComparison
attribute [local implicit_reducible] Etale.vectorBundlePurityLower
  Etale.vectorBundlePurityCompactification Etale.vectorIntegrationSource

-- Share elaborated instance proofs using Lean's ordinary proof abstraction cache.
-- This changes only the proof term; the kernel checks the result as usual.
open Lean Meta in
private meta def shareTensorInstances (proof : Expr) (helpers : Array Name) :
    MetaM Expr := do
  let proof ← Meta.transform proof (skipConstInApp := true) (pre := fun expr => do
    if let .const n us := expr.getAppFn then
      if helpers.contains n then
        let ci ← getConstInfo n
        return .visit ((← instantiateValueLevelParams ci us (allowOpaque := true)).beta
          expr.getAppArgs)
    if ← AbstractNestedProofs.isNonTrivialProof expr then
      let ty ← inferType expr
      if let .const n _ := ty.getAppFn then
        if isClass (← getEnv) n then
          let expr ← abstractProof expr (postprocessType := fun ty => abstractNestedProofs ty)
          return .done expr
    return .continue)
  if proof.hasSorry then
    throwError "Instance proof sharing left an unfinished proof"
  return proof

open Lean Meta Elab Tactic
set_option linter.style.multiGoal false in
private theorem tensor_data
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (K : Etale.DerivedCategoryModule A S)
    (hK : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) S K)
    (hW : DerivedCategory.TStructure.t.plus
      (Etale.vectorIntegrationCoefficient A N hA S d F))
    (t : genericVectorSource A N hA S d F ⟶ unit A S)
    (e : genericVectorSource A N hA S d F ≅
      (comparison A S).obj (Etale.vectorIntegrationSource A N hA S d F))
    (he : e = (compactSupportSiteComparison A
      (Etale.vectorBundlePurityCompactification S d F)).app ⟨_, hW⟩)
    (htrace : e.inv ≫ t = (comparison A S).map
      (Etale.vectorBundleIntegration N hN A hA S hS d F)) :
    Nonempty (TensorCompatibilityData A N hN hA S hS d F K t e) := by
  run_tac do
    withMainContext do
      let g ← getMainGoal
      let h ← mkFreshExprSyntheticOpaqueMVar (← g.getType)
      g.setTag h.mvarId!.name
      replaceMainGoal [h.mvarId!, g]
  · obtain ⟨hM, pe, pp, hpe, hpp, hp⟩ := vectorTensorProjectionComparison A N hN hA
      S hS d F K hK hW
      e he
    let ae := ordinaryTensorIntegrate A S K (Etale.vectorIntegrationSource A N hA S d F)
      _ pe (Etale.vectorBundleIntegration N hN A hA S hS d F)
    let ap := proTensorIntegrate A S K (genericVectorSource A N hA S d F) _ pp
      t
    have hi : (compactSupportSiteComparison A
        (Etale.vectorBundlePurityCompactification S d F)).inv.app ⟨_, hM⟩ ≫ ap =
        (comparison A S).map ae := by
      unfold ap ae proTensorIntegrate ordinaryTensorIntegrate rightUnit
      simp only [Iso.trans_hom, Iso.symm_hom]
      have hp' := hp
      simp only [tensorComparison, Iso.app_hom] at hp'
      with_unfolding_all
        simpa only [comparison, geoP1Comparison, tensorComparison, Iso.app_inv,
          Functor.comp_obj, ObjectProperty.ι_obj, Functor.mapIso, Category.assoc] using
          tensor_integration_square (comparison A S)
            ((Etale.derivedTensor (ModuleCat.{u + 1} A) S).obj K)
            ((derivedTensor (ModuleCat.{u + 1} A) S).obj ((comparison A S).obj K))
            (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
              (ModuleCat.{u + 1} A) K)
            e
            ((compactSupportSiteComparison A
              (Etale.vectorBundlePurityCompactification S d F)).app ⟨_, hM⟩)
            pe pp (Etale.vectorBundleIntegration N hN A hA S hS d F)
            t
            (Etale.derivedTensorRightUnitor (ModuleCat.{u + 1} A) S K).hom hp'
            htrace
    have ht := boundedSiteTranspose_compatible A
      (Etale.vectorBundlePurityCompactification S d F) (genericVectorExceptional A S d F)
      (Etale.vectorBundlePurityAdjunction A S d F) ⟨_, hM⟩ K ae ap hi
    have hpur : IsIso ((Etale.vectorBundlePurityAdjunction A S d F).homEquiv _ K ae) := by
      dsimp only [ae, ordinaryTensorIntegrate]
      obtain ⟨p, hp, h⟩ := (Etale.purityAtModulus N hN A hA S hS d F).2.2.2.2 K
      have he : p = pe := Iso.ext_inv (hp.trans hpe.symm)
      subst p
      with_unfolding_all exact h
    refine ⟨{
      hM := hM
      pe := pe
      pp := pp
      ae := ae
      ap := ap
      ordinary_formula := HEq.rfl
      pro_formula := HEq.rfl
      ordinary_projection := hpe
      pro_projection := hpp
      projection_square := hp.heq
      integration_square := hi.heq
      transpose_square := ht.heq
      ordinary_purity := hpur
      ordinary_normalization := ?_ }⟩
    exact vectorTensorOrdinaryNormalization A N hN hA S hS d F K pe hpe
  · run_tac do
      withMainContext do
        let g ← getMainGoal
        let h : MVarId := ⟨← g.getTag⟩
        let proof ← instantiateMVars (mkMVar h)
        if proof.hasMVar then
          throwError "The intermediate tensor proof has unresolved goals"
        let proof ← shareTensorInstances proof #[``tensor_integration_square]
        g.assign proof
        replaceMainGoal []

set_option linter.unusedVariables false in
/-- Tensor projection, integration, and the bounded etale-origin transposes compare.
The projection inverses are specified by equality of their inverses with the actual
maps. Source: Stacks 0944, 0GL1 and 0B65
(blueprint: lem-pur-vector-integration-site-comparison).
Proof: the proper square is the counit-mate tensor square, and the open square is
the unit-normalized open projection square. Paste them. The ordinary projection
is invertible on finite-Tor inputs, hence so is the compared projection. Invert
the square, tensor the global trace equation and apply the normalized unit map.
The bounded Hom chain gives the transpose equation with rho. Ordinary purity
identifies the inverse of the adjunct with its integration-normalized bundle map.
-/
theorem vectorTensorComparison (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) S)
    (hK : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) S K) :
    TensorCompatibility l E n S hS r hA d F K hK := by
  let A := Scheme.finiteTateCoefficient l E n
  let N := l ^ (r + 1)
  have hN : 0 < N := pow_pos (Fact.out : l.Prime).pos _
  have hSN : IsUnit (N : Γ(S, ⊤)) := by
    simpa only [N, Nat.cast_pow] using hS.pow (r + 1)
  exact tensor_data A N hN hA S hSN d F K hK
    (vectorCoefficient_plus l E n S r hA d F hS)
    (vectorIntegration l E n S r hA d F hS) (vectorSite l E n S r hA d F hS)
    (by unfold vectorSite; rfl)
    (vectorIntegrationSiteComparison l E n S hS r hA d F).2

end TensorComparisonProof

private theorem ordinary_normalized_integration_unique
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d]
    (g : Etale.vectorIntegrationSource A N hA S d F ⟶ Etale.ordinaryFiniteUnit A S)
    (hg : Etale.VectorIntegrationNormalization N hN A hA S hS d F g) :
    g = Etale.vectorBundleIntegration N hN A hA S hS d F := by
  let p := Etale.vectorIntegrationGluing N hN A hA S hS d F
  have hp := (Etale.existsUnique_vectorIntegrationGluing N hN A hA S hS d F).2
  have hpn := hp.exists.choose_spec
  obtain ⟨a, ha⟩ := (DerivedCategory.singleFunctor _ 0).map_surjective (p.1.inv ≫ g)
  have hga : p.1.hom ≫ (DerivedCategory.singleFunctor _ 0).map a = g := by
    rw [ha, ← Category.assoc, p.1.hom_inv_id, Category.id_comp]
  have heq : (p.1, a) = p := hp.unique ⟨hpn.1, by rwa [hga]⟩ hpn
  have hea : a = p.2 := congrArg Prod.snd heq
  rw [← hga, hea]
  rfl

private theorem ordinary_integration_transition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (hA : (N : A) = 0) (hA' : (M : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (M : Γ(S, ⊤)))
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (v : Etale.vectorIntegrationCoefficient A M hA' S d F ⟶
      Etale.vectorIntegrationCoefficient A N hA S d F)
    (hlocal : ∀ (ts : Etale.OrdinaryFiniteTwistTransport A M hA')
      (Ds : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (M : Γ(T, ⊤))),
        Etale.OrdinaryFiniteP1Datum A M hA' ts T hT)
      (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V),
      (Etale.ordinaryFinitePullback A V.ι).map
        ((Etale.vectorBundlePurityLower A S d F).map v) ≫
          Etale.vectorIntegrationLocalTrace N hN A hA
            (Etale.projectiveLineTraceTransport N hN A hA)
            (Etale.projectiveLineTraceDatum N hN A hA) S hS d F V e =
          Etale.vectorIntegrationLocalTrace M hM A hA' ts Ds S hS' d F V e) :
    (Etale.vectorBundlePurityLower A S d F).map v ≫
      Etale.vectorBundleIntegration N hN A hA S hS d F =
        Etale.vectorBundleIntegration M hM A hA' S hS' d F := by
  apply ordinary_normalized_integration_unique
  intro ts Ds V e
  simp only [Functor.map_comp, Category.assoc]
  have hnorm : Etale.VectorIntegrationNormalization N hN A hA S hS d F
      (Etale.vectorBundleIntegration N hN A hA S hS d F) :=
    (Etale.existsUnique_vectorIntegrationGluing N hN A hA S hS d F).2.exists.choose_spec.2
  rw [hnorm (Etale.projectiveLineTraceTransport N hN A hA)
    (Etale.projectiveLineTraceDatum N hN A hA) V e]
  exact hlocal ts Ds V e

private theorem trace_transition_of_comparison
    {C D : Type*} [Category C] [Category D] (V : C ⥤ D)
    {X X' Y : C} {Z Z' : D} (g : X' ⟶ X) (f : Z' ⟶ Z)
    (e : Z ≅ V.obj X) (e' : Z' ≅ V.obj X')
    (a : X ⟶ Y) (a' : X' ⟶ Y) (t : Z ⟶ V.obj Y) (t' : Z' ⟶ V.obj Y)
    (hn : f ≫ e.hom = e'.hom ≫ V.map g)
    (ht : g ≫ a = a') (hc : e.inv ≫ t = V.map a)
    (hc' : e'.inv ≫ t' = V.map a') : f ≫ t = t' := by
  apply (cancel_epi e'.inv).mp
  have he : e'.inv ≫ f = V.map g ≫ e.inv := by
    apply (cancel_mono e.hom).mp
    simp only [Category.assoc, hn, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, he, Category.assoc, hc, ← V.map_comp, ht, hc']

private theorem trace_transition_of_natural_comparison
    {B C D : Type*} [Category B] [Category C] [Category D]
    (L : B ⥤ C) (P : B ⥤ D) (V : C ⥤ D) (e : P ≅ L ⋙ V)
    {X X' : B} {Y : C} (v : X' ⟶ X)
    (a : L.obj X ⟶ Y) (a' : L.obj X' ⟶ Y)
    (t : P.obj X ⟶ V.obj Y) (t' : P.obj X' ⟶ V.obj Y)
    (ht : L.map v ≫ a = a')
    (hc : (e.app X).inv ≫ t = V.map a)
    (hc' : (e.app X').inv ≫ t' = V.map a') : P.map v ≫ t = t' := by
  exact trace_transition_of_comparison V (L.map v) (P.map v) (e.app X) (e.app X')
    a a' t t' (e.hom.naturality v) ht hc hc'

/-- Exponent transitions preserve the independent global integration.
Source: root projections, ordered traces and degree-zero gluing
(blueprint: lem-pur-vector-integration-site-comparison).
Proof: projections commute with the supported Kummer boundary; thus decomposition,
inverse and trace agree after transition. Restrict with the open counit and iterate
the coordinate maps. Equality on frames glues. The tensor and transpose statements
are independent of exponent by their formulas and Hom naturality as well.
-/
theorem vectorExponentIndependence (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r r' : ℕ) (h : r ≤ r')
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hA' : ((l ^ (r' + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (Etale.vectorBundlePurityCompactification S d F)).map
      ((comparison (Scheme.finiteTateCoefficient l E n) _).map
        ((Etale.ordinaryFinitePullback _ (VectorBundleZeroSection.π S d F)).map
          (baseExponentComparison l E n S hS r r' h hA hA' d).hom)) ≫
      vectorIntegration l E n S r hA d F hS =
        vectorIntegration l E n S r' hA' d F hS := by
  let v := (Etale.ordinaryFinitePullback (Scheme.finiteTateCoefficient l E n)
    (VectorBundleZeroSection.π S d F)).map
    (baseExponentComparison l E n S hS r r' h hA hA' d).hom
  let t := Etale.vectorBundleIntegration (l ^ (r + 1))
    (pow_pos (Fact.out : l.Prime).pos _) (Scheme.finiteTateCoefficient l E n) hA S
    (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F
  let t' := Etale.vectorBundleIntegration (l ^ (r' + 1))
    (pow_pos (Fact.out : l.Prime).pos _) (Scheme.finiteTateCoefficient l E n) hA' S
    (by simpa only [Nat.cast_pow] using hS.pow (r' + 1)) d F
  have ht : (Etale.vectorBundlePurityLower (Scheme.finiteTateCoefficient l E n)
      S d F).map v ≫ t = t' := by
    apply ordinary_integration_transition
    intro ts Ds V e
    exact vectorIntegrationLocalTrace_exponentTransition l E n S hS r r' h hA hA' d F
      _ _ ts Ds V e
  let w :
      (⟨_, vectorCoefficient_plus l E n S r' hA' d F hS⟩ : DerivedCategory.Plus _) ⟶
        (⟨_, vectorCoefficient_plus l E n S r hA d F hS⟩ : DerivedCategory.Plus _) :=
    ObjectProperty.homMk (by
      unfold Etale.vectorIntegrationCoefficient
      exact v)
  have hc := (vectorIntegrationSiteComparison l E n S hS r hA d F).2
  have hc' := (vectorIntegrationSiteComparison l E n S hS r' hA' d F).2
  have hh := trace_transition_of_natural_comparison
    (DerivedCategory.Plus.ι ⋙ Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (Etale.vectorBundlePurityCompactification S d F))
    (DerivedCategory.Plus.ι ⋙ comparison (Scheme.finiteTateCoefficient l E n) _ ⋙
      rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
        (Etale.vectorBundlePurityCompactification S d F))
    (comparison (Scheme.finiteTateCoefficient l E n) S)
    (compactSupportSiteComparison (Scheme.finiteTateCoefficient l E n)
      (Etale.vectorBundlePurityCompactification S d F)) w t t' _ _
    (by simpa only [Functor.comp_map, ObjectProperty.ι_map,
      ObjectProperty.homMk_hom, w, id_eq, Etale.vectorBundlePurityLower] using ht)
    (by simpa only [Iso.app_inv, vectorSite] using hc)
    (by simpa only [Iso.app_inv, vectorSite] using hc')
  simpa only [Functor.comp_map, ObjectProperty.ι_map, ObjectProperty.homMk_hom,
    w, id_eq] using hh




/-- Root-normalized twist comparison, arbitrary scheme pullback, and exponent transitions.
Source: Stacks 03PK and 099R (blueprint: lem-pur-vector-integration-site-comparison).
Proof: finite reduction is induced by root projection after tensoring with A.
Generators determine the comparison, every pullback square, and every exponent
transition. Repeated tensor gives all powers, including the constant zero power.
A common larger exponent compares any two annihilators. No flatness of A is used.
-/
theorem twistCompatibility :
    (∀ (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
      (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (k : ℕ),
      Scheme.IsFiniteTateSiteComparison l E n T r hA k (twistComparison l E n T hT r hA k)) ∧
    (∀ (T T' : Scheme.{u}) (v : T' ⟶ T)
      (hT : IsUnit (l : Γ(T, ⊤))) (hT' : IsUnit (l : Γ(T', ⊤)))
      (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (k : ℕ),
      ∃ (c : (Etale.upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) v).obj
          (Scheme.finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≅
            Scheme.finiteEtaleTateTwist T' (l ^ (r + 1)) _ hA k)
        (d : (ProEtale.upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) v).obj
          (Scheme.finiteTateProSheaf l E n T k) ≅ Scheme.finiteTateProSheaf l E n T' k),
      Scheme.IsFiniteTateEtalePullback l E n T v r hA k c ∧
      Scheme.IsFiniteTateProPullback l E n T v k d ∧
      (ProEtale.upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) v).mapIso
          (twistComparison l E n T hT r hA k) ≪≫ d =
        (ProEtale.comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) v).app
            (Scheme.finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) T').mapIso c ≪≫
          twistComparison l E n T' hT' r hA k) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤))) (r r' : ℕ) (_h : r ≤ r')
      (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
      (hA' : ((l ^ (r' + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (k : ℕ),
      ∃! t : Scheme.finiteEtaleTateTwist T (l ^ (r' + 1)) _ hA' k ≅
          Scheme.finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k,
        Scheme.IsFiniteTateEtaleTransition l E n T r r' hA hA' k t ∧
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) T).mapIso t ≪≫
            twistComparison l E n T hT r hA k =
            twistComparison l E n T hT r' hA' k) := by
  unfold twistComparison
  exact ⟨(Scheme.finite_tate_site_descent l E n).choose_spec.1,
    (Scheme.finite_tate_site_descent l E n).choose_spec.2.1,
    (Scheme.finite_tate_site_descent l E n).choose_spec.2.2.1⟩

/-- Finite-type specialization of the displayed map equations.
Source: the finite-field conventions and the node statement
(blueprint: lem-pur-vector-integration-site-comparison). -/
def FiniteTypeSiteCompatibility (P : WeilConjectures.PurityFiniteSetting.{u})
    (m : ℕ) (S : Scheme.{u}) (aS : S ⟶ Spec (CommRingCat.of P.field.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] : Prop :=
    letI : IsNoetherian S := isNoetherian_of_locallyOfFiniteType aS
    ∃ hS : IsUnit (P.coefficients.l : Γ(S, ⊤)),
      ∀ (r : ℕ)
        (hA : ((P.coefficients.l ^ (r + 1) : ℕ) :
          Scheme.finiteTateCoefficient P.coefficients.l P.extension m) = 0),
      ProjectiveCompatibility P.coefficients.l P.extension m S hS (infinityCartier S) r hA ∧
      IntegrationCompatibility P.coefficients.l P.extension m S hS r hA d F ∧
      ∀ (K : Etale.DerivedCategoryModule
        (Scheme.finiteTateCoefficient P.coefficients.l P.extension m) S)
        (hK : Etale.DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient P.coefficients.l P.extension m)) S K),
        TensorCompatibility P.coefficients.l P.extension m S hS r hA d F K hK

/-- The exact finite-field, arbitrary positive finite-level specialization, with no
separatedness hypothesis on S. Noetherianity and invertibility of l are consequences.
Source: finite purity conventions and node statement
(blueprint: lem-pur-vector-integration-site-comparison).
Proof: finite type over a field makes S Noetherian. Since l differs from the fixed
characteristic, l is invertible on S. Apply the preceding map equations at every
annihilating exponent and every bounded constructible finite-Tor coefficient.
-/
theorem finiteTypeSiteComparison (P : WeilConjectures.PurityFiniteSetting.{u})
    (m : ℕ) (S : Scheme.{u}) (aS : S ⟶ Spec (CommRingCat.of P.field.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    FiniteTypeSiteCompatibility P m S aS d F := by
  let : IsNoetherian S := isNoetherian_of_locallyOfFiniteType aS
  have hS : IsUnit (P.coefficients.l : Γ(S, ⊤)) := by
    apply S.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    simpa only [map_natCast] using P.coefficientPrime_isUnit_stalk S aS x
  refine ⟨hS, ?_⟩
  intro r hA
  exact ⟨projectiveComparison P.coefficients.l P.extension m S hS (infinityCartier S) r hA,
    vectorIntegrationSiteComparison P.coefficients.l P.extension m S hS r hA d F,
    fun K hK ↦ vectorTensorComparison P.coefficients.l P.extension m S hS r hA d F K hK⟩

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
