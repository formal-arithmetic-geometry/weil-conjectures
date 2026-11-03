/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.Normalized.NormalizedDVREffectivity
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
public import WeilConjectures.SmoothPurity.Compact.CompactSupportReductionTowerFunctorSpec
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.SixFunctors.Coefficient.CoefficientDuality
public import WeilConjectures.SmoothPurity.Integral.IntegralRationalQbarCompactSupport
public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
public import WeilConjectures.SmoothPurity.Supporting.DirectImagesConstructible
public import WeilConjectures.Mathlib.Topology.KrullDimension

public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.SixFunctors.Finite.FiniteDualizing
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRStrictRealization

/-! # Strict Roos realization of the finite dualizing tower

The unchanged integral mapping-complex, compact-support, and limit constructions
are recorded here so that the finite bounds and mapping-limit steps can use the
same objects independently of the assembly theorem.

Source: current blueprint prop-coef-integral-dualizing, inverse-limit assertion
(blueprint: lem-coef-integral-dualizing-roos-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The published sheafification instance with both universes specified.
Source: blueprint order 1455, ordinary coefficient sheaves
(blueprint: prop-coef-integral-dualizing). -/
instance integralDualizingRingSheafify (Y : Scheme.{u}) :
    HasSheafify (ProEt.topology Y) CommRingCat.{u + 1} :=
  integralCoefficientRingSheafify.{u, u} Y

/-- The coefficient ring in the section universe, with only a carrier lift.
Source: blueprint order 2145, D(R) (blueprint: prop-coef-integral-dualizing). -/
abbrev integralDualizingCoefficients := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)

/-- The actual constant scalar map to sections of the completion.
Source: blueprint order 2145, global derived mapping complexes
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingScalar (Y : Scheme.{u}) (U : Y.ProEtᵒᵖ) :
    integralDualizingCoefficients l E →+*
      (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U :=
  (((integralConstantToCompletionOfUniverses.{u, u} l E Y).hom.app U).hom).comp
    (((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      ((toSheafify (D := CommRingCat.{u + 1}) (ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj
          (CommRingCat.of (integralDualizingCoefficients l E)))).app U)).hom)

/-- Ordinary global sections with their actual R action, evaluated at the final object.
Source: blueprint order 2145, global derived mapping complexes
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingSections (Y : Scheme.{u}) :
    scalarReductionSource l E Y ⥤ ModuleCat.{u + 1} (integralDualizingCoefficients l E) :=
  SheafOfModules.evaluation _ (op (ProEt.mk (𝟙 Y))) ⋙
    ModuleCat.restrictScalars (integralDualizingScalar l E Y (op (ProEt.mk (𝟙 Y))))

/-- Evaluation and scalar restriction are additive, with the existing module structures.
Source: blueprint order 2145 (blueprint: prop-coef-integral-dualizing). -/
instance integralDualizingSections_additive (Y : Scheme.{u}) :
    (integralDualizingSections l E Y).Additive :=
  inferInstanceAs (SheafOfModules.forget _ ⋙
    PresheafOfModules.evaluation _ (op (ProEt.mk (𝟙 Y))) ⋙
    ModuleCat.restrictScalars (integralDualizingScalar l E Y (op (ProEt.mk (𝟙 Y))))).Additive

/-- Derived sections computed on the published K-injective replacements.
Source: blueprint order 2145, global derived mapping complexes
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingDerivedSections (Y : Scheme.{u}) :
    DerivedCategory (scalarReductionSource l E Y) ⥤
      DerivedCategory.{u + 1} (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) :=
  letI := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u}
    (ProEt.topology Y) (completedIntegralCommRingSheafUnrestricted l E Y)).1
  (integralDualizingSections l E Y).rightDerivedFunctor

/-- Global derived Hom is RΓ of the recorded internal derived Hom.
Source: blueprint order 2145, definition of RHom_X
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingGlobalHom (Y : Scheme.{u})
    (M : DerivedCategory (scalarReductionSource l E Y)) :
    (sfIntegralConstructibleCategory l E Y)ᵒᵖ ⥤
      DerivedCategory.{u + 1} (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) :=
  (sfIntegralConstructible l E Y).ι.op ⋙
    (Functor.curry.obj (derivedInternalHomOfUniverses.{u + 1, u, u}
      (ProEt.topology Y) (completedIntegralCommRingSheafUnrestricted l E Y))).flip.obj M ⋙
      integralDualizingDerivedSections l E Y

/-- Total right derived inverse limit on strict completed-coefficient towers.
The chosen functor has the right-derived universal property, so is unique up to the
unique comparison compatible with its derived unit. Its data is not an arbitrary cone.
Source: blueprint order 2145 and Stacks 0940--0941
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingLimit (Y : Scheme.{u}) :
    DerivedCategory (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ⥤
      DerivedCategory (scalarReductionSource l E Y) :=
  (ringedStrictTowerHomotopyLimitOfUniverses.{u + 2, u + 1, u, u}
    (ProEt.topology Y) (completedIntegralCoefficientSheafUnrestricted l E Y)
    (completedIntegralCoefficient_mul_commUnrestricted l E Y)).choose

open CategoryTheory.Pretriangulated in
private theorem roosProductTransport
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {A B : ℕ → C} [HasProduct A] [HasProduct B]
    (f : ∀ n, A (n + 1) ⟶ A n) (g : ∀ n, B (n + 1) ⟶ B n)
    {M N : C} (e : M ≅ N) (a : ∀ n, A n ≅ B n)
    (ht : ∀ n, (a (n + 1)).hom ≫ g n = f n ≫ (a n).hom)
    (p : M ⟶ ∏ᶜ A) (δ : (∏ᶜ A) ⟶ M⟦(1 : ℤ)⟧)
    (h : IsDerivedLimitTriangle f M p δ) :
    ∃ (q : N ⟶ ∏ᶜ B) (δ' : (∏ᶜ B) ⟶ N⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle g N q δ' := by
  let b : (∏ᶜ A) ≅ (∏ᶜ B) :=
    { hom := Limits.Pi.map (fun n ↦ (a n).hom)
      inv := Limits.Pi.map (fun n ↦ (a n).inv)
      hom_inv_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc]
      inv_hom_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc] }
  refine ⟨e.inv ≫ p ≫ b.hom, b.inv ≫ δ ≫ (shiftFunctor C (1 : ℤ)).map e.hom, ?_⟩
  exact (distinguished_iff_of_iso (Triangle.isoMk _ _ e b b
    (by simp) (towerTransitionEndomorphism_natural_backward f g (fun n ↦ (a n).hom) ht).symm
    (by simp))).mp h

private theorem invertComparisonSquare
    {C : Type*} [Category C] {A B A' B' : C}
    (f : A ⟶ B) (g : A' ⟶ B') (a : A ≅ A') (b : B ≅ B')
    (h : f ≫ b.hom = a.hom ≫ g) : a.inv ≫ f = g ≫ b.inv := by
  calc
    a.inv ≫ f = a.inv ≫ (f ≫ b.hom) ≫ b.inv := by simp [Category.assoc]
    _ = g ≫ b.inv := by rw [h]; simp [Category.assoc]

private abbrev rawDerivedTowerEvaluation
    (A : Type*) [Category A] [Abelian A] [HasDerivedCategory A]
    [HasDerivedCategory (ℕᵒᵖ ⥤ A)] (n : ℕ) :
    DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory A :=
  ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory

private def rawDerivedTowerTransition
    (A : Type*) [Category A] [Abelian A] [HasDerivedCategory A]
    [HasDerivedCategory (ℕᵒᵖ ⥤ A)] {m n : ℕ} (h : n ≤ m) :
    rawDerivedTowerEvaluation A m ⟶ rawDerivedTowerEvaluation A n :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)) _ _
    (rawDerivedTowerEvaluation A m) (rawDerivedTowerEvaluation A n)
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map (homOfLE h).op)
        (ComplexShape.up ℤ)) DerivedCategory.Q)

private theorem integralDualizing_roos_triangle (Y : Scheme.{u})
    (Z : DerivedCategory (ℕᵒᵖ ⥤
      ringedSiteModules.{u + 1} (completedIntegralCoefficientSheafUnrestricted l E Y))) :
    let A := ringedSiteModules.{u + 1} (completedIntegralCoefficientSheafUnrestricted l E Y)
    let RF := (ringedStrictTowerHomotopyLimitOfUniverses.{u + 2, u + 1, u, u}
      (ProEt.topology Y) (completedIntegralCoefficientSheafUnrestricted l E Y)
      (completedIntegralCoefficient_mul_commUnrestricted l E Y)).choose
    let : HasCountableProducts (DerivedCategory A) :=
      integralOperationsDerivedCountableProducts l E Y
    ∃ (p : RF.obj Z ⟶ ∏ᶜ fun n : ℕ ↦ (rawDerivedTowerEvaluation A n).obj Z)
      (δ : (∏ᶜ fun n : ℕ ↦ (rawDerivedTowerEvaluation A n).obj Z) ⟶
        (RF.obj Z)⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle
        (fun n : ℕ ↦ (rawDerivedTowerTransition A n.le_succ).app Z)
        (RF.obj Z) p δ := by
  let A := ringedSiteModules.{u + 1} (completedIntegralCoefficientSheafUnrestricted l E Y)
  let C := DerivedCategory.Q.objPreimage Z
  let z : DerivedCategory.Q.obj C ≅ Z := DerivedCategory.Q.objObjPreimageIso Z
  obtain ⟨η, _, _, _, hshift, hproducts, F, ε, p, δ, _, hroos, _⟩ :=
    (ringedStrictTowerHomotopyLimitOfUniverses.{u + 2, u + 1, u, u}
      (ProEt.topology Y) (completedIntegralCoefficientSheafUnrestricted l E Y)
      (completedIntegralCoefficient_mul_commUnrestricted l E Y)).choose_spec
  let ev (n : ℕ) := (evaluation ℕᵒᵖ A).obj (op n)
  let tc (n : ℕ) := (NatTrans.mapHomologicalComplex
    ((evaluation ℕᵒᵖ A).map (homOfLE n.le_succ).op) (.up ℤ)).app C
  let c (n : ℕ) : (F.obj (DerivedCategory.Q.obj C)).obj (op n) ≅
      DerivedCategory.Q.obj ((ev n).mapHomologicalComplex (.up ℤ) |>.obj C) :=
    (ε.app C).app (op n)
  have hc (n : ℕ) : (c (n + 1)).hom ≫ DerivedCategory.Q.map (tc n) =
      (F.obj (DerivedCategory.Q.obj C)).map (homOfLE n.le_succ).op ≫ (c n).hom := by
    exact ((ε.hom.app C).naturality (homOfLE n.le_succ).op).symm
  let a (n : ℕ) : (F.obj (DerivedCategory.Q.obj C)).obj (op n) ≅
      (rawDerivedTowerEvaluation A n).obj Z :=
    c n ≪≫ ((ev n).mapDerivedCategoryFactors.app C).symm ≪≫
      (rawDerivedTowerEvaluation A n).mapIso z
  have ht (n : ℕ) :
      (a (n + 1)).hom ≫ (rawDerivedTowerTransition A n.le_succ).app Z =
        (F.obj (DerivedCategory.Q.obj C)).map (homOfLE n.le_succ).op ≫ (a n).hom := by
    have hf : (rawDerivedTowerTransition A n.le_succ).app
        (DerivedCategory.Q.obj C) ≫ (ev n).mapDerivedCategoryFactors.hom.app C =
      (ev (n + 1)).mapDerivedCategoryFactors.hom.app C ≫
        DerivedCategory.Q.map (tc n) := by
      dsimp only [ev, A, tc]
      simp only [rawDerivedTowerTransition, Localization.liftNatTrans_app,
        Localization.Lifting.iso, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
      rfl
    have hf' : (ev (n + 1)).mapDerivedCategoryFactors.inv.app C ≫
        (rawDerivedTowerTransition A n.le_succ).app (DerivedCategory.Q.obj C) =
        DerivedCategory.Q.map (tc n) ≫ (ev n).mapDerivedCategoryFactors.inv.app C :=
      invertComparisonSquare _ _ ((ev (n + 1)).mapDerivedCategoryFactors.app C)
        ((ev n).mapDerivedCategoryFactors.app C) hf
    dsimp only [a, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app,
      Functor.mapIso_hom]
    rw [Category.assoc, Category.assoc,
      (rawDerivedTowerTransition A n.le_succ).naturality z.hom]
    rw [reassoc_of% hf']
    simpa only [Category.assoc] using congrArg
      (fun k ↦ k ≫ (ev n).mapDerivedCategoryFactors.inv.app C ≫
        (rawDerivedTowerEvaluation A n).map z.hom) (hc n)
  let := hproducts
  let hp : HasProduct (fun n : ℕ ↦ (F.obj (DerivedCategory.Q.obj C)).obj (op n)) :=
    inferInstance
  have hr := hroos (DerivedCategory.Q.obj C)
  let : HasCountableProducts (DerivedCategory A) :=
    integralOperationsDerivedCountableProducts l E Y
  exact roosProductTransport _ _
    (((ringedStrictTowerHomotopyLimitOfUniverses.{u + 2, u + 1, u, u}
      (ProEt.topology Y) (completedIntegralCoefficientSheafUnrestricted l E Y)
      (completedIntegralCoefficient_mul_commUnrestricted l E Y)).choose).mapIso z) a ht
    (p (DerivedCategory.Q.obj C)) (δ (DerivedCategory.Q.obj C)) hr

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The compactification supplied by Nagata over the given field.
Source: blueprint order 2145, a:X→s (blueprint: prop-coef-integral-dualizing). -/
def integralDualizingCompactification : Compactification (X ↘ Spec (.of D.k)) :=
  letI := hasCompactification_of_finiteType_over_field D.k X (Spec (.of D.k))
    (X ↘ Spec (.of D.k))
  HasCompactification.compactification (X ↘ Spec (.of D.k))

/-- The published coherent compact-support reduction functor, including all transitions
and all derived morphisms. Its evaluation and transition characterizations determine its
coherent tower up to isomorphism. Only normalized scalar structures from that construction
are used to extract the functor.
Source: blueprint order 2145 and Bhatt--Scholze 6.7.6
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingCompactTower :
    DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (ℕᵒᵖ ⥤ scalarReductionSource l E (Spec (.of D.k))) := by
  let h := exists_compactSupportReductionTower l E D.k X (Spec (.of D.k))
    (X ↘ Spec (.of D.k)) (finiteFieldDatumPrimeUnit D l hl)
      (integralDualizingCompactification D X)
  letI := h.choose
  letI := h.choose_spec.choose
  exact h.choose_spec.choose_spec.2.2.choose

/-- Integral compact support followed by coefficient-point sections, with its map action.
Source: blueprint order 2145, C=Γ(s,Ra_!K)
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingCompactSections : sfIntegralConstructibleCategory l E X ⥤
    DerivedCategory.{u + 1} (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) :=
  (sfIntegralConstructible l E X).ι ⋙ integralDualizingCompactTower l E D hl X ⋙
    integralDualizingLimit l E (Spec (.of D.k)) ⋙
      integralDualizingDerivedSections l E (Spec (.of D.k))

/-- A Roos limit presentation of the coherent normalized tower, with the actual counit
reductions and their compatibility with every quotient transition. This is a predicate on
real objects and maps, using the published countable products and effectivity comparisons.
Source: blueprint order 2145, first display and transition paragraph
(blueprint: prop-coef-integral-dualizing). -/
def IntegralDualizingLimitPresentation (T : NormalizedDVRTower l E X D hl)
    (M : DerivedCategory (scalarReductionSource l E X)) : Prop :=
  letI : HasCountableProducts (completedIntegralDerivedCategory l E X D hl) :=
    integralOperationsDerivedCountableProducts l E X
  ∃ (p : M ⟶ ∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)
    (δ : (∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower) ⟶
      M⟦(1 : ℤ)⟧),
    IsDerivedLimitTriangle
      (fun n : ℕ ↦ (normalizedDVRTowerTransition l E X D hl n.le_succ).app T.tower)
        M p δ ∧
    (∀ n : ℕ, IsIso (normalizedDVRCounitComparison l E X D hl T M p n)) ∧
    ∀ (m n : ℕ) (h : n ≤ m),
      normalizedDVRCounitComparison l E X D hl T M p m ≫ T.tau h =
        normalizedDVRReductionTransition l E X D hl h M ≫
          (normalizedDVRRes l E X h).map
            (normalizedDVRCounitComparison l E X D hl T M p n)

/-- A strict normalized realization of the finite dualizing objects, together with
its Roos triangle for the published total derived inverse limit.

Source: current blueprint prop-coef-integral-dualizing, first proof paragraph,
its inverse-limit assertion and compatibility with lem-coef-finite-dualizing;
Stacks Tags 0940 and 0941 (blueprint: lem-coef-integral-dualizing-roos-model).

Proof: use the counit-defined finite comparisons and their unit and cocycle identities.
Their scalar adjuncts give the semilinear transitions. Restrict to completed coefficients;
canonical restriction coherence gives an inverse diagram in the derived category.
Choose K-injective representatives of its objects and chain maps representing successor
transitions. Compose these maps to obtain a strict sequence of complexes, then transpose
it to a complex of sequences. Its localization gives the strict tower and its evaluation
isomorphisms. Normalization follows from invertibility of the finite comparisons and
the scalar adjunction. The published total derived limit has an auxiliary evaluation
functor and a Roos triangle. On a complex representing the strict tower, its factorization
isomorphism identifies the auxiliary evaluation with the canonical derived evaluation,
including every transition. Transport the limit object, product and distinguished
triangle along these isomorphisms. The explicit product isomorphism works for the
published product witness even when it differs from the witness used by the limit theorem.
No constructibility or duality conclusion is asserted here. -/
theorem integralDualizing_roos_model (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))] :
    ∃ (T : NormalizedDVRTower l E X D hl)
      (e : ∀ n : ℕ, T.M n ≅ integralDualizingFiniteTerm l E D X n),
      (∀ {m n : ℕ} (h : n ≤ m),
        T.tau h ≫ (normalizedDVRRes l E X h).map (e n).hom =
          (e m).hom ≫
            (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _
              (integralDualizingFiniteComparison l E D X hl h)) ∧
      (letI : HasCountableProducts (completedIntegralDerivedCategory l E X D hl) :=
        integralOperationsDerivedCountableProducts l E X
       ∃ (p : (integralDualizingLimit l E X).obj T.tower ⟶
          ∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)
         (δ : (∏ᶜ fun n : ℕ ↦
          (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower) ⟶
          ((integralDualizingLimit l E X).obj T.tower)⟦(1 : ℤ)⟧),
         IsDerivedLimitTriangle
           (fun n : ℕ ↦ (normalizedDVRTowerTransition l E X D hl n.le_succ).app T.tower)
           ((integralDualizingLimit l E X).obj T.tower) p δ) := by
  obtain ⟨_, _, _, hi, hu, hc⟩ := finiteDualizingCoefficientComparisons l E D X hl
  obtain ⟨Z, e, he⟩ := normalizedDVR_strict_realization l E X D hl
    (integralDualizingFiniteTerm l E D X)
    (fun h ↦ integralDualizingExceptionalTransition l E D X hl h)
    hu (fun h₁ h₂ ↦ hc h₁ h₂)
  let T : NormalizedDVRTower l E X D hl :=
    { M := integralDualizingFiniteTerm l E D X
      tau := fun h ↦ integralDualizingExceptionalTransition l E D X hl h
      tau_refl := hu
      tau_comp := fun h₁ h₂ ↦ hc h₁ h₂
      tower := Z
      evaluationIso := e
      tower_tau := fun h ↦ he h
      normalization := by
        intro m n h P
        let a := Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)
        let v := integralDualizingFiniteComparison l E D X hl h
        have : IsIso v := hi h
        have hb : Function.Bijective (fun f : integralDualizingFiniteTerm l E D X n ⟶ P ↦
            v ≫ f) := by
          constructor
          · intro f g hfg
            exact (cancel_epi v).mp hfg
          · intro f
            exact ⟨inv v ≫ f, by simp⟩
        have hb' := (a.homEquiv _ _).bijective.comp hb
        convert hb' using 1
        funext f
        simpa only [v, integralDualizingFiniteComparison, a, Equiv.apply_symm_apply,
          Function.comp_apply] using (a.homEquiv_naturality_right v f).symm }
  refine ⟨T, fun n ↦ Iso.refl _, ?_, ?_⟩
  · intro m n h
    dsimp only [T, Iso.refl_hom]
    rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
    exact (Equiv.apply_symm_apply
      ((Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _) _).symm
  · exact integralDualizing_roos_triangle l E X Z

end WeilConjectures
