/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumCompletedSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
public import Mathlib.CategoryTheory.Sites.CompatibleSheafification
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison
import all WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantCoefficientEquivalence
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedQuotientUnitNormalization
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
public import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
public import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence

/-! # The normalized quotient Roos triangle on explicit Koszul completion

Source: blueprint order 1248; Stacks Tags 091Z and 099M.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
attribute [local instance 30000] HasDerivedCategory.standard
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
variable (d : ProEtaleAdicCoefficientDatum A)

private def reconstructionRestrictId
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    pbcRestrict (𝟙 R) ≅ 𝟭 (pbcModules T R) :=
  NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk
        (fun U ↦ (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U))
        (fun {U V} f ↦ by ext x; rfl))) (fun _ ↦ by ext U x; rfl)

private def reconstructionPresentationBackEquiv (D : AdicCoefficientDatum A) :
    adicDatumModules T (intrinsicPresentationDatum D) ≌ pbcModules T (pbcAdicCompletion T D) :=
  CategoryTheory.Equivalence.mk (intrinsicPresentationModulesBack T D)
    (intrinsicPresentationModules T D)
    ((pbcRestrictComp (pbcCompletedComparison T D).hom (pbcCompletedComparison T D).inv
        (𝟙 _) (pbcCompletedComparison T D).hom_inv_id ≪≫
      reconstructionRestrictId T _).symm)
    (intrinsicPresentationRoundTrip T D).symm

private theorem reconstructionUnit_section
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : pbcModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcScalarAdjunction φ).unit.app M).val.app U x = pbcTensorSection φ M U 1 x :=
  (pbcScalarAdjunction_exists φ).exists.choose_spec M U x

private theorem reconstructionComp_section
    {R S R' : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ R') (χ : R ⟶ R') (h : φ ≫ ψ = χ)
    (M : pbcModules T R') (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcRestrictComp φ ψ χ h).hom.app M).val.app U x = x :=
  (pbcRestrictComp_exists φ ψ χ h).exists.choose_spec M U x

private def productTransport
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {V : ℕ → C} {W : ℕ → D} [HasProduct V] [HasProduct W]
    [HasProduct (fun n ↦ F.obj (V n))] [PreservesLimit (Discrete.functor V) F]
    (a : ∀ n, F.obj (V n) ≅ W n) : F.obj (∏ᶜ V) ≅ ∏ᶜ W :=
  PreservesProduct.iso F V ≪≫
    { hom := Limits.Pi.map (fun n ↦ (a n).hom)
      inv := Limits.Pi.map (fun n ↦ (a n).inv)
      hom_inv_id := by apply Pi.hom_ext; intro n; simp [Category.assoc]
      inv_hom_id := by apply Pi.hom_ext; intro n; simp [Category.assoc] }

private theorem productTransport_π
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {V : ℕ → C} {W : ℕ → D} [HasProduct V] [HasProduct W]
    [HasProduct (fun n ↦ F.obj (V n))] [PreservesLimit (Discrete.functor V) F]
    (a : ∀ n, F.obj (V n) ≅ W n) (n : ℕ) :
    (productTransport F a).hom ≫ Pi.π W n = F.map (Pi.π V n) ≫ (a n).hom := by
  dsimp only [productTransport, Iso.trans_hom]
  rw [Category.assoc, Pi.map_π, PreservesProduct.iso_hom,
    ← Category.assoc, piComparison_comp_π]

private theorem productTransport_transition
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive]
    {V : ℕ → C} {W : ℕ → D} [HasProduct V] [HasProduct W]
    [HasProduct (fun n ↦ F.obj (V n))] [PreservesLimit (Discrete.functor V) F]
    (a : ∀ n, F.obj (V n) ≅ W n)
    (f : ∀ n, V (n + 1) ⟶ V n) (g : ∀ n, W (n + 1) ⟶ W n)
    (ha : ∀ n, F.map (f n) ≫ (a n).hom = (a (n + 1)).hom ≫ g n) :
    F.map (towerTransitionEndomorphism f) ≫ (productTransport F a).hom =
      (productTransport F a).hom ≫ towerTransitionEndomorphism g := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, productTransport_π, towerTransitionEndomorphism,
    towerProductShift, Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
    Pi.lift_π, Functor.map_sub]
  simp only [reassoc_of% (productTransport_π F a)]
  rw [F.map_id, Category.id_comp]
  congr 1
  rw [← F.map_comp_assoc, Pi.lift_π, Functor.map_comp, Category.assoc, ha]

private theorem reflectRoosTriangle
    {C D : Type*} [Category C] [Category D] [HasZeroObject C] [HasZeroObject D]
    [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.Full] [F.Faithful]
    {V : ℕ → C} {W : ℕ → D} [HasProduct V] [HasProduct W]
    (f : ∀ n, V (n + 1) ⟶ V n) (g : ∀ n, W (n + 1) ⟶ W n)
    {L : C} {L' : D} (a : F.obj L ≅ L') (b : F.obj (∏ᶜ V) ≅ ∏ᶜ W)
    (hb : F.map (towerTransitionEndomorphism f) ≫ b.hom =
      b.hom ≫ towerTransitionEndomorphism g)
    (p' : L' ⟶ ∏ᶜ W) (δ' : (∏ᶜ W) ⟶ L'⟦(1 : ℤ)⟧)
    (h : IsDerivedLimitTriangle g L' p' δ') :
    ∃ (p : L ⟶ ∏ᶜ V) (δ : (∏ᶜ V) ⟶ L⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle f L p δ ∧ F.map p ≫ b.hom = a.hom ≫ p' := by
  let p := F.preimage (a.hom ≫ p' ≫ b.inv)
  let δ := F.preimage (b.hom ≫ δ' ≫ (shiftFunctor D (1 : ℤ)).map a.inv ≫
    (F.commShiftIso (1 : ℤ)).inv.app L)
  have hp : F.map p ≫ b.hom = a.hom ≫ p' := by simp [p]
  refine ⟨p, δ, (F.map_distinguished_iff _).mp ?_, hp⟩
  apply Pretriangulated.isomorphic_distinguished _ h _
  refine Pretriangulated.Triangle.isoMk _ _ a b b ?_ ?_ ?_
  · exact hp
  · exact hb
  · change (F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app L) ≫
      (shiftFunctor D (1 : ℤ)).map a.hom = b.hom ≫ δ'
    simp [δ, ← Functor.map_comp]

private theorem reflectNormalizedRoos
    {C D : Type*} [Category C] [Category D] [HasZeroObject C] [HasZeroObject D]
    [HasShift C ℤ] [HasShift D ℤ] [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.Full] [F.Faithful] [F.Additive]
    {V : ℕ → C} {W : ℕ → D} [HasProduct V] [HasProduct W]
    [HasProduct (fun n ↦ F.obj (V n))] [PreservesLimit (Discrete.functor V) F]
    (a : ∀ n, F.obj (V n) ≅ W n)
    (f : ∀ n, V (n + 1) ⟶ V n) (g : ∀ n, W (n + 1) ⟶ W n)
    (ha : ∀ n, F.map (f n) ≫ (a n).hom = (a (n + 1)).hom ≫ g n)
    {X L : C} {L' : D} (e : F.obj L ≅ L')
    (p' : L' ⟶ ∏ᶜ W) (δ' : (∏ᶜ W) ⟶ L'⟦(1 : ℤ)⟧)
    (h : IsDerivedLimitTriangle g L' p' δ')
    (u : X ⟶ L) (v : ∀ n, X ⟶ V n)
    (hu : ∀ n, F.map u ≫ e.hom ≫ p' ≫ Pi.π W n = F.map (v n) ≫ (a n).hom) :
    ∃ (p : L ⟶ ∏ᶜ V) (δ : (∏ᶜ V) ⟶ L⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle f L p δ ∧ ∀ n, u ≫ p ≫ Pi.π V n = v n := by
  let b := productTransport F a
  obtain ⟨p, δ, hδ, hp⟩ := reflectRoosTriangle F f g e b
    (productTransport_transition F a f g ha) p' δ' h
  refine ⟨p, δ, hδ, fun n ↦ F.map_injective ?_⟩
  apply (cancel_mono (a n).hom).1
  simp only [Functor.map_comp, Category.assoc]
  rw [← productTransport_π F a n, reassoc_of% hp]
  exact hu n

attribute [local irreducible] reductionChange


section Presentation
variable (D : AdicCoefficientDatum A)

private def nativeRoundTrip : 𝟭 (adicDatumModules T (intrinsicPresentationDatum D)) ≅
    intrinsicPresentationModulesBack T D ⋙ intrinsicPresentationModules T D :=
  (pbcRestrictComp (pbcCompletedComparison T D).hom (pbcCompletedComparison T D).inv
    (𝟙 _) (pbcCompletedComparison T D).hom_inv_id ≪≫
      reconstructionRestrictId T _).symm

attribute [local irreducible] pbcCompletedComparison intrinsicPresentationRoundTrip
  nativeRoundTrip reconstructionRestrictId

attribute [local irreducible] comparisonChangeAdjunction

attribute [local irreducible] adicDatumOrdinaryAdjunction pbcScalarAdjunction

private theorem actualFiberToStrict
    (r : ℕ) (f : Fin r → A) (hf : Ideal.span (Set.range f) = D.ideal)
    (C : CochainComplex (pbcModules T (pbcAdicCompletion T D)) ℤ)
    (hC : CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion T D) C) :
    let J := (completedReductionComplexTowerFunctor T D).obj C
    ∃ e : DerivedCategory.Q.obj (intrinsicCompletionComplex T D r f C) ≅
        (completedRlim T (pbcAdicCompletion T D)).obj (DerivedCategory.Q.obj J),
      ∀ n : ℕ, DerivedCategory.Q.map (intrinsicCompletionComplexUnit T D r f C) ≫
          e.hom ≫ (completedRlimProjection T (pbcAdicCompletion T D) n).app
            (DerivedCategory.Q.obj J) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (pbcScalarAdjunction (pbcAdicProjection T D n)).unit (.up ℤ)).app C) ≫
          (reductionTowerEvaluation T (reductionModuleRing T (pbcAdicCompletion T D)) n
            ).mapDerivedCategoryFactors.inv.app J := by
  dsimp only
  let R := completedRlim T (pbcAdicCompletion T D)
  let J := (completedReductionComplexTowerFunctor T D).obj C
  let ε := derivedCochainCounit (completedReductionModuleTowerFunctor T D)
    (completedReductionTower T D) (completedReductionTowerCounit D T)
  obtain ⟨hε, hεunit⟩ := completedQuotientUnitNormalization T D C hC
  have : IsIso (ε.app C) := hε
  obtain ⟨c, hc⟩ := completedKoszulQuotientComparison T D r f hf
    (DerivedCategory.Q.obj C) C (Iso.refl _)
  let e := c ≪≫ R.mapIso (asIso (ε.app C))
  refine ⟨e, fun n ↦ ?_⟩
  have hc' : DerivedCategory.Q.map (intrinsicCompletionComplexUnit T D r f C) ≫
      c.hom = (completedQuotientCompletionUnit T D).app (DerivedCategory.Q.obj C) := by
    simpa only [intrinsicCompletionUnit, Iso.refl_inv, Category.id_comp,
      completedQuotientCompletionUnit, NatTrans.comp_app, Functor.whiskerRight_app] using hc
  dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  simp only [Category.assoc]
  erw [reassoc_of% hc']
  erw [reassoc_of% hεunit]
  erw [cochainRightUnit_app_eq]
  erw [completedRlimProjection_unit]
  rw [← DerivedCategory.Q.map_comp_assoc]
  congr 1
  apply congrArg DerivedCategory.Q.map
  ext q U x
  change (((completedQuotientOrdinaryUnit T D C).f q ≫
    limit.π ((completedReductionModuleTowerFunctor T D).obj (C.X q)) (op n)).val.app U x) = _
  rw [completedQuotientOrdinaryUnit_projection]
  exact ((completedReductionModuleUnit_exists D T).exists.choose_spec (C.X q) n U x).trans
    (reconstructionUnit_section T (pbcAdicProjection T D n) (C.X q) U x).symm

attribute [local irreducible] productTransport

end Presentation

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- Before imposing completeness, the explicit completion has the normalized
Roos triangle of the canonical derived quotient reductions.

Source: current blueprint def-pe-derived-complete and def-weil-derived-limit,
refining fix-prop-adjunctions; Stacks Project, Tag 08TC.
(blueprint: lem-weil-pbc-completed-koszul-reduction-roos-triangle).

Proof: repleteness gives exact countable products of internal modules, hence
countable products in their derived category. On a K-flat representative P,
ordinary tensor reduction computes the canonical derived quotient reductions.
The published roos_isDerivedLimit theorem transports the mapping-cocone triangle
through these unit-compatible level comparisons. Compose its product-unit equation
with the nth product projection. This is the old argument's final normalization,
now directly in the pulled-back condensed coefficient category. The canonical
completion model and augmentation are those of AdicCompletion, without a change
of coefficient rings or a new choice of completion. The argument includes P=0,
the empty scheme, and positive level one. No completeness, boundedness, flatness
of the finite quotient, or constructibility assumption is made on K. -/
theorem completedKoszulReductionRoosTriangle
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (P : CochainComplex (AdicCompletion.Modules l E X) ℤ)
    (hP : (HomologicalComplex.quasiIso (AdicCompletion.Modules l E X) (.up ℤ)).kFlat P)
    (e : DerivedCategory.Q.obj P ≅ K) :
    ∃ hp : HasProduct (AdicCompletion.integralLevel l E X K),
      letI := hp
      ∃ (p : DerivedCategory.Q.obj (AdicCompletion.roos l E X P) ⟶
          ∏ᶜ (AdicCompletion.integralLevel l E X K))
        (δ : ∏ᶜ (AdicCompletion.integralLevel l E X K) ⟶
          (DerivedCategory.Q.obj (AdicCompletion.roos l E X P))⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle (AdicCompletion.integralStep l E X K) _ p δ ∧
          ∀ n : ℕ, AdicCompletion.completionMap l E X K P e ≫ p ≫
            Pi.π (AdicCompletion.integralLevel l E X K) n =
              (Mod.derivedExtendMapDerivedCategoryAdjunction
                (AdicCompletion.quotient l E X n)).unit.app K := by
  let : CountableAB4Star (AdicCompletion.Modules l E X) :=
    .of_epi_π_app_zero (Mod.epiπAppZeroOfEpi
      Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat)
  let := derivedCategory_hasCountableProducts (AdicCompletion.Modules l E X)
  obtain ⟨p, δ, hδ, hp⟩ := AdicCompletion.roos_isDerivedLimit l E X K P hP e
  refine ⟨inferInstance, p, δ, hδ, fun n ↦ ?_⟩
  have hn := congrArg (fun z ↦ z ≫ Pi.π (AdicCompletion.integralLevel l E X K) n) hp
  simpa only [Category.assoc, Pi.lift_π] using hn

end AlgebraicGeometry.Scheme
