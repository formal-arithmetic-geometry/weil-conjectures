/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FinitePullbackStrictTower.FinitePullbackStrictTowerRepresentative
public import WeilConjectures.DeligneLaumon.FiniteReductionTower.FiniteReductionTowerResolvingModel
import WeilConjectures.DeligneLaumon.FinitePullbackStrictTower.FinitePullbackStrictTowerLocalizedZigzag
import all WeilConjectures.Algebra.Homology.RingedKFlatSingleTensorComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Localization.Construction
import all Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all Mathlib.CategoryTheory.Functor.Currying
import all Mathlib.CategoryTheory.Whiskering
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Mathlib.CategoryTheory.Localization.Prod
import all Mathlib.Algebra.Homology.BifunctorFlip
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Localization.CalculusOfFractions
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import all WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement

/-! # Construction of the normalized representative comparison

Source: Stacks Project, Tags 099N(5), 0G7E, 06XN, 03EL and 0FNH.
(blueprint: lem-a1-finite-pullback-representative-construction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  WeilConjectures.unrestrictedIntegralReductionFunctor
  WeilConjectures.CompletedTowerIndependent.pull
attribute [local irreducible] WeilConjectures.completedIntegralCoefficientSheafUnrestricted
attribute [local implicit_reducible] WeilConjectures.completedIntegralCommRingSheafUnrestricted
  CategoryTheory.sheafCompose
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.CompletedTowerIndependent
namespace WeilConjectures.FinitePullbackStrictTower
attribute [local implicit_reducible] comparisonZQ
  KoszulNormalization BalancedNormalization ReductionNormalization
attribute [local irreducible] comparisonKoszulIso comparisonBalancedIso
  comparisonKoszulDiagramIso comparisonBalancedDiagramIso
attribute [local implicit_reducible] asIso
attribute [local implicit_reducible] H tensorReduction augmentation G diagramPull
  finiteComplex pulledReduction transpose PrincipalQuotientCompletion.transpose
  koszulTowerComplex HomologicalComplex.asFunctor
  PrincipalKoszulStrictReplacement.sourceTower PrincipalKoszulStrictReplacement.targetTower
  FinitePullbackStrictTowerData.G FinitePullbackStrictTowerData.koszuls
  FinitePullbackStrictTowerData.reductions FinitePullbackStrictTowerData.diagramPull
  FinitePullbackStrictTowerData.finite FinitePullbackStrictTowerData.augmentation
  FinitePullbackStrictTowerData.H FinitePullbackStrictTowerData.tensorReduction
  FinitePullbackStrictTowerData.finiteComplex
  CompletedTowerIndependent.towerPull koszulTowerComplexMap
  PrincipalKoszulStrictReplacement.tensorWith
  PrincipalKoszulStrictReplacement.sourceTowerMap PrincipalKoszulStrictReplacement.targetTowerMap
  CategoryTheory.Functor.mapHomologicalComplex
attribute [local irreducible] CategoryTheory.Functor.map₂HomologicalComplex
  SheafOfModules.KFlatTotalTensorModel.tensor
attribute [local irreducible] CompletedTowerIndependent.reductionPair
  CompletedTowerIndependent.derivedPull CompletedTowerIndependent.derivedCounit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{t}} (g : X ⟶ Y)

private theorem extendResolvingIso
    {C : Type*} {D : Type*} {Z : Type*} [Category* C] [Category* D] [Category* Z]
    (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    (good : C → Prop) (R : C ⥤ C) (η : R ⟶ 𝟭 C)
    (hR : ∀ P, good (R.obj P)) (hη : ∀ P, IsIso (Q.map (η.app P)))
    (F G : D ⥤ Z) (e : ∀ P, good P → (F.obj (Q.obj P) ≅ G.obj (Q.obj P)))
    (he : ∀ {P P'} (f : P ⟶ P') (hP : good P) (hP' : good P'),
      F.map (Q.map f) ≫ (e P' hP').hom = (e P hP).hom ≫ G.map (Q.map f)) :
    ∃ b : F ≅ G, ∀ P (hP : good P), b.hom.app (Q.obj P) = (e P hP).hom := by
  have : ∀ P, IsIso ((Functor.whiskerRight η Q).app P) := hη
  have : IsIso (Functor.whiskerRight η Q) := NatIso.isIso_of_isIso_app _
  let q : R ⋙ Q ≅ Q := asIso (Functor.whiskerRight η Q)
  let eR : (R ⋙ Q) ⋙ F ≅ (R ⋙ Q) ⋙ G :=
    NatIso.ofComponents (fun P ↦ e (R.obj P) (hR P))
      (fun f ↦ he (R.map f) (hR _) (hR _))
  let n : Q ⋙ F ≅ Q ⋙ G :=
    Functor.isoWhiskerRight q.symm F ≪≫ eR ≪≫ Functor.isoWhiskerRight q G
  let ff := Localization.fullyFaithfulWhiskeringLeft Q W Z
  let b : F ≅ G := ff.preimageIso n
  refine ⟨b, ?_⟩
  intro P hP
  have hb : b.hom.app (Q.obj P) = n.hom.app P :=
    NatTrans.congr_app (ff.map_preimage n.hom) P
  rw [hb]
  change F.map (q.inv.app P) ≫ (e (R.obj P) (hR P)).hom ≫
    G.map (q.hom.app P) = _
  change F.map (q.inv.app P) ≫
    ((e (R.obj P) (hR P)).hom ≫ G.map (Q.map (η.app P))) = _
  rw [← he (η.app P) (hR P) hP]
  simp only [← F.map_comp_assoc]
  change F.map (q.inv.app P ≫ q.hom.app P) ≫ _ = _
  simp only [Iso.inv_hom_id_app, F.map_id, Category.id_comp]
  rfl


private theorem extendGoodIso
    (B : DerivedCategory (Modules l E Y) ⥤ DerivedCategory (Towers l E X))
    (e : ∀ P, integralOperationsGoodComplex l E Y P →
      ((pulledReduction l E g).obj (DerivedCategory.Q.obj P) ≅
        B.obj (DerivedCategory.Q.obj P)))
    (he : ∀ {P P'} (f : P ⟶ P')
      (hP : integralOperationsGoodComplex l E Y P)
      (hP' : integralOperationsGoodComplex l E Y P'),
      (pulledReduction l E g).map (DerivedCategory.Q.map f) ≫ (e P' hP').hom =
        (e P hP).hom ≫ B.map (DerivedCategory.Q.map f)) :
    ∃ b : pulledReduction l E g ≅ B,
      ∀ P (hP : integralOperationsGoodComplex l E Y P),
        b.hom.app (DerivedCategory.Q.obj P) = (e P hP).hom := by
  obtain ⟨F, η, hη, hk, hflat⟩ := SheafOfModules.functorial_resolution
    (completedIntegralCommRingSheafUnrestricted l E Y)
  have hi P : IsIso (DerivedCategory.Q.map (η.app P)) := by
    have := hη P
    infer_instance
  exact extendResolvingIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules l E Y) (.up ℤ))
    (integralOperationsGoodComplex l E Y) F η
    (fun P ↦ ⟨hk P, hflat P⟩) hi (pulledReduction l E g) B e he


private def isoComposite
    {A : Type*} [Category* A] {W X Y Z : A}
    (i : W ≅ X) (z : X ⟶ Y) (h : Z ⟶ Y) (hz : IsIso z) (hh : IsIso h) : W ≅ Z :=
  i ≪≫ (@asIso _ _ _ _ z hz) ≪≫ (@asIso _ _ _ _ h hh).symm

private theorem comp_inv_comp
    {A : Type*} [Category* A] {W X Y Z : A}
    (f : W ⟶ X) (z : X ⟶ Y) (h : Z ⟶ Y) [IsIso h] :
    (f ≫ z ≫ inv h) ≫ h = f ≫ z := by
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

private theorem isoComposite_beta
    {A : Type*} [Category* A] {W X Y Z : A}
    (i : W ≅ X) (z : X ⟶ Y) (h : Z ⟶ Y) (hz : IsIso z) (hh : IsIso h) :
    (isoComposite i z h hz hh).hom ≫ h = i.hom ≫ z := by
  let := hh
  exact comp_inv_comp i.hom z h

private theorem naturalityByMono
    {A : Type*} [Category* A] {U U' H H' D D' B B' : A}
    (a : U ⟶ U') (m : H ⟶ H') (d : D ⟶ D') (c : B ⟶ B')
    (chi : U ⟶ H) (chi' : U' ⟶ H') (z : H ⟶ D) (z' : H' ⟶ D')
    (beta : B ⟶ D) (beta' : B' ⟶ D') (e : U ⟶ B) (e' : U' ⟶ B')
    [Mono beta'] (hchi : a ≫ chi' = chi ≫ m) (hbeta : c ≫ beta' = beta ≫ d)
    (hz : m ≫ z' = z ≫ d) (he : e ≫ beta = chi ≫ z)
    (he' : e' ≫ beta' = chi' ≫ z') : a ≫ e' = e ≫ c := by
  apply (cancel_mono beta').1
  simp only [Category.assoc]
  rw [he', hbeta, ← Category.assoc a chi', hchi, Category.assoc chi m z', hz]
  simpa only [Category.assoc] using congrArg (· ≫ d) he.symm

private theorem isoTriple_isIso
    {A : Type*} [Category* A] {U V W Z : A}
    (i : U ≅ V) (a : V ⟶ W) (j : W ≅ Z) (ha : IsIso a) :
    IsIso (i.hom ≫ a ≫ j.hom) := by
  let := ha
  infer_instance

private theorem comparisonZQ_isIso
    (θ : FinitePullbackStrictTowerData.koszuls l E Y ⋙
      FinitePullbackStrictTowerData.diagramPull l E g ≅
        FinitePullbackStrictTowerData.G l E g ⋙ FinitePullbackStrictTowerData.koszuls l E X)
    (lambda : FinitePullbackStrictTowerData.G l E g ⋙
      FinitePullbackStrictTowerData.reductions l E X ≅ FinitePullbackStrictTowerData.finite l E g)
    (hAugTower : ∀ P, integralOperationsGoodComplex l E Y P →
      QuasiIso ((transpose l E X).map (augmentation l E X ((G l E g).obj P))))
    (P : CochainComplex (Modules l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) : IsIso (comparisonZQ l E g θ lambda P) := by
  have : QuasiIso ((transpose l E X).map
      (augmentation l E X ((G l E g).obj P))) := hAugTower P hP
  have hq : IsIso (DerivedCategory.Q.map ((transpose l E X).map
      (augmentation l E X ((G l E g).obj P)))) := by infer_instance
  exact isoTriple_isIso (comparisonKoszulIso l E g θ P)
    (DerivedCategory.Q.map ((transpose l E X).map
      (augmentation l E X ((G l E g).obj P))))
    (comparisonBalancedIso l E g lambda P) hq

private def comparisonIso
    (R : FiniteReductionTower.ResolvingModel l E g)
    (θ : FinitePullbackStrictTowerData.koszuls l E Y ⋙
      FinitePullbackStrictTowerData.diagramPull l E g ≅
        FinitePullbackStrictTowerData.G l E g ⋙ FinitePullbackStrictTowerData.koszuls l E X)
    (lambda : FinitePullbackStrictTowerData.G l E g ⋙
      FinitePullbackStrictTowerData.reductions l E X ≅ FinitePullbackStrictTowerData.finite l E g)
    (hIso : ∀ P, integralOperationsGoodComplex l E Y P →
      IsIso (comparisonZQ l E g θ lambda P))
    (P : CochainComplex (Modules l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) :=
  isoComposite (R.chi P hP) (comparisonZQ l E g θ lambda P) (R.B.counit.app P)
    (hIso P hP) (R.B.computes P hP)

attribute [local irreducible] isoComposite

private theorem comparisonIso_beta
    (R : FiniteReductionTower.ResolvingModel l E g)
    (θ : FinitePullbackStrictTowerData.koszuls l E Y ⋙
      FinitePullbackStrictTowerData.diagramPull l E g ≅
        FinitePullbackStrictTowerData.G l E g ⋙ FinitePullbackStrictTowerData.koszuls l E X)
    (lambda : FinitePullbackStrictTowerData.G l E g ⋙
      FinitePullbackStrictTowerData.reductions l E X ≅ FinitePullbackStrictTowerData.finite l E g)
    (hIso : ∀ P, integralOperationsGoodComplex l E Y P →
      IsIso (comparisonZQ l E g θ lambda P))
    (P : CochainComplex (Modules l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) :
    (comparisonIso l E g R θ lambda hIso P hP).hom ≫ R.B.counit.app P =
      (R.chi P hP).hom ≫ (comparisonZQ l E g θ lambda P) := by
  unfold comparisonIso
  exact isoComposite_beta (R.chi P hP) (comparisonZQ l E g θ lambda P)
    (R.B.counit.app P) (hIso P hP)
    (R.B.computes P hP)

private theorem comparisonIso_naturality
    (R : FiniteReductionTower.ResolvingModel l E g)
    (θ : FinitePullbackStrictTowerData.koszuls l E Y ⋙
      FinitePullbackStrictTowerData.diagramPull l E g ≅
        FinitePullbackStrictTowerData.G l E g ⋙ FinitePullbackStrictTowerData.koszuls l E X)
    (lambda : FinitePullbackStrictTowerData.G l E g ⋙
      FinitePullbackStrictTowerData.reductions l E X ≅ FinitePullbackStrictTowerData.finite l E g)
    (hIso : ∀ P, integralOperationsGoodComplex l E Y P →
      IsIso (comparisonZQ l E g θ lambda P))
    {P P' : CochainComplex (Modules l E Y) ℤ} (f : P ⟶ P')
    (hP : integralOperationsGoodComplex l E Y P)
    (hP' : integralOperationsGoodComplex l E Y P') :
    (derivedPull l E g).map
      ((reductionPair l E Y).functor.map (DerivedCategory.Q.map f)) ≫
      (comparisonIso l E g R θ lambda hIso P' hP').hom =
    (comparisonIso l E g R θ lambda hIso P hP).hom ≫
      R.B.functor.map (DerivedCategory.Q.map f) := by
  let : IsIso (R.B.counit.app P) := R.B.computes P hP
  let : IsIso (R.B.counit.app P') := R.B.computes P' hP'
  have hzn := comparisonZQ_naturality l E g θ lambda f
  exact naturalityByMono
    ((derivedPull l E g).map
      ((reductionPair l E Y).functor.map (DerivedCategory.Q.map f)))
    (DerivedCategory.Q.map
      (((towerPull l E g).mapHomologicalComplex (.up ℤ)).map
        ((transpose l E Y).map (PrincipalKoszulStrictReplacement.sourceTowerMap l E Y f))))
    (DerivedCategory.Q.map ((integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).map f))
    (R.B.functor.map (DerivedCategory.Q.map f))
    (R.chi P hP).hom (R.chi P' hP').hom
    (comparisonZQ l E g θ lambda P) (comparisonZQ l E g θ lambda P')
    (R.B.counit.app P) (R.B.counit.app P')
    (comparisonIso l E g R θ lambda hIso P hP).hom
    (comparisonIso l E g R θ lambda hIso P' hP').hom
    (R.chi_naturality f hP hP') (R.beta_naturality f hP hP') hzn
    (comparisonIso_beta l E g R θ lambda hIso P hP)
    (comparisonIso_beta l E g R θ lambda hIso P' hP')


private def comparisonReductionH
    (R : FiniteReductionTower.ResolvingModel l E g)
    (P : CochainComplex (Modules l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) :=
  (R.reductionIso P hP).symm ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map ((transpose l E Y).map
      (PrincipalKoszulStrictReplacement.comparison l E Y P)))
      (R.augmentation_invertible P hP)).symm

set_option maxHeartbeats 800000 in
-- Explicit transposition and localization need this heartbeat budget.
/-- Construct the normalized representative comparison from compatible resolving models.
Source: Stacks 099N(5), 0G7E and 06XN. Compose the localized Koszul, augmentation,
and balanced maps, invert the universal counit, and extend the resulting natural isomorphism
along the localization by functorial flat K-flat resolution. Naturality at the resolution
augmentation gives the prescribed value on every good representative. Cancellation verifies
the reduction normalization and the full zigzag.
(blueprint: lem-a1-finite-pullback-representative-construction). -/
theorem representative_from_models
    (R : FiniteReductionTower.ResolvingModel l E g)
    (θ : FinitePullbackStrictTowerData.koszuls l E Y ⋙
      FinitePullbackStrictTowerData.diagramPull l E g ≅
        FinitePullbackStrictTowerData.G l E g ⋙ FinitePullbackStrictTowerData.koszuls l E X)
    (lambda : FinitePullbackStrictTowerData.G l E g ⋙
      FinitePullbackStrictTowerData.reductions l E X ≅ FinitePullbackStrictTowerData.finite l E g)
    (hθ : ∀ P, FinitePullbackStrictTowerData.KoszulNormalization l E g P (θ.app P))
    (hlambda : ∀ P,
      FinitePullbackStrictTowerData.BalancedNormalization l E g P (lambda.app P))
    (hgood : ∀ P, integralOperationsGoodComplex l E Y P →
      integralOperationsGoodComplex l E X ((G l E g).obj P))
    (hlevels : ∀ P, integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      integralOperationsGoodComplex l E X
        (((diagramPull l E g).obj (H l E Y P)).obj (op n)))
    (hAug : ∀ P, integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      QuasiIso ((augmentation l E X ((G l E g).obj P)).app (op n)))
    (hAugTower : ∀ P, integralOperationsGoodComplex l E Y P →
      QuasiIso ((transpose l E X).map (augmentation l E X ((G l E g).obj P)))) :
    Nonempty (RepresentativeComparison l E g) := by
  classical
  let hIso := comparisonZQ_isIso l E g θ lambda hAugTower
  obtain ⟨b, hb⟩ := extendGoodIso l E g R.B.functor
    (comparisonIso l E g R θ lambda hIso)
    (fun f hP hP' ↦ comparisonIso_naturality l E g R θ lambda hIso f hP hP')
  refine ⟨{
    B := R.B
    b := b
    reductionIso := R.normalizationIso
    reduction_normalization := fun P hP ↦ R.normalization P hP
    koszulIso := fun P _ ↦ comparisonKoszulDiagramIso l E g θ P
    koszul_normalization := fun P _ ↦ by
      simp only [comparisonKoszulDiagramIso]
      with_unfolding_all exact hθ P
    balancedIso := fun P _ ↦ comparisonBalancedDiagramIso l E g lambda P
    balanced_normalization := fun P _ ↦ by
      simp only [comparisonBalancedDiagramIso]
      with_unfolding_all exact hlambda P
    pull_good := hgood
    koszul_pull_good := hlevels
    middle_quasiIso := hAug
    reductionH := comparisonReductionH l E g R
    reductionH_normalization := ?_
    zigzag := ?_ }⟩
  · intro P hP
    let : IsIso (DerivedCategory.Q.map ((transpose l E Y).map
        (PrincipalKoszulStrictReplacement.comparison l E Y P))) :=
      R.augmentation_invertible P hP
    dsimp only [comparisonReductionH, Iso.trans_hom, Iso.symm_hom, asIso_inv]
    rw [Functor.map_comp, Functor.map_comp]
    simp only [augmentation, Category.assoc, IsIso.inv_hom_id_assoc]
    apply (cancel_epi (R.reductionIso P hP).hom).1
    simp only [Iso.hom_inv_id_assoc]
    convert (R.reduction_computation P hP).symm using 0
  · intro P hP
    rw [hb P hP, comparisonIso_beta l E g R θ lambda hIso P hP]
    rw [R.chi_formula P hP]
    change (derivedPull l E g).map ((comparisonReductionH l E g R P hP).hom) ≫
      (derivedCounit l E g).app ((transpose l E Y).obj (H l E Y P)) ≫
      DerivedCategory.Q.map ((transpose l E X).map (comparisonKoszulDiagramIso l E g θ P).hom) ≫
      DerivedCategory.Q.map ((transpose l E X).map
        (augmentation l E X ((G l E g).obj P))) ≫
      DerivedCategory.Q.map ((transpose l E X).map
        (comparisonBalancedDiagramIso l E g lambda P).hom) = _
    simp only [comparisonZQ, comparisonKoszulIso, comparisonBalancedIso,
      comparisonKoszulChainIso, comparisonBalancedChainIso,
      Functor.mapIso_hom]
    exact (Category.assoc
      ((derivedPull l E g).map (comparisonReductionH l E g R P hP).hom)
      ((derivedCounit l E g).app ((transpose l E Y).obj (H l E Y P)))
      (DerivedCategory.Q.map ((transpose l E X).map (comparisonKoszulDiagramIso l E g θ P).hom) ≫
        DerivedCategory.Q.map ((transpose l E X).map
          (augmentation l E X ((G l E g).obj P))) ≫
        DerivedCategory.Q.map ((transpose l E X).map
          (comparisonBalancedDiagramIso l E g lambda P).hom))).symm


end WeilConjectures.FinitePullbackStrictTower
