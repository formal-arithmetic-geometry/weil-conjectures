/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q87
-/
module

public import Sheaf.Paper.PointDerivedHomModels
public import Sheaf.Paper.PointFibreDerivedTensor
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.Paper.IntegralDerivedOperations
public import Sheaf.Paper.PointSectionsBalancingCompletion
import Sheaf.Paper.CompletedLineTensorCoherence
import all Sheaf.Paper.PointFibreDerivedTensorModels
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! # Models and proved auxiliary lemmas for point completion

Source: main-20261015 blueprint, point-dualizing-complex proof, second sentence;
Bhatt--Scholze, Definition 3.4.10 and Lemmas 3.4.11--3.4.12.
(blueprint: def-pod-point-evaluation-completion-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Check the large derived-category terms synchronously.
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] HasDerivedCategory.standard
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.Q
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.mapDerivedCategoryFactors
  WeilConjectures.integralOperationsRoosFunctor WeilConjectures.integralOperationsRoos
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] WeilConjectures.IntegralHom.ordinaryTensorObjZero
  WeilConjectures.IntegralHom.ordinaryTensorZero
attribute [-instance] WeilConjectures.PointDerivedHom.derivedSheaves
  WeilConjectures.PointDerivedHom.derivedModules
attribute [-instance] WeilConjectures.PointDerivedHom.abSheafify
  WeilConjectures.PointDerivedHom.abLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped TensorProduct ChangeOfRings

namespace WeilConjectures.PointEvaluationCompletion

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

local instance (priority := 5000) : EssentiallySmall.{u + 1} (Spec (.of D.k)).ProEt :=
  essentiallySmallSelf.{u} _

local instance (priority := 5000) :
    HasSheafify (Scheme.ProEt.topology (Spec (.of D.k))) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} (Spec (.of D.k))

local instance (priority := 5000) :
    (Scheme.ProEt.topology (Spec (.of D.k))).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} (Spec (.of D.k))

/-- Lifted valuation ring. Source: coefficient conventions
(blueprint: lem-pod-point-evaluation-completion-normalization). -/
abbrev R := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)

/-- Completed coefficient sheaf, on the original small site. Source: Bhatt--Scholze 3.4.10
(blueprint: lem-pod-point-evaluation-completion-normalization). -/
abbrev B := completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))

/-- The recorded ambient module category. Source: Bhatt--Scholze 3.4.10
(blueprint: lem-pod-point-evaluation-completion-normalization). -/
abbrev Mod := integralTowerModules l E (Spec (.of D.k))

/-- The fixed standard sheaf localization. Source: Stacks 05RU
(blueprint: lem-pod-point-evaluation-completion-normalization). -/
abbrev Q := @DerivedCategory.Q (Mod D l E) _ _ (HasDerivedCategory.standard _)

/-- The fixed module localization used by point sections. Source: Stacks 05RU
(blueprint: lem-pod-point-evaluation-completion-normalization). -/
abbrev QR := @DerivedCategory.Q (ModuleCat.{u + 1} (R l E)) _ _
  (HasDerivedCategory.ofIsGrothendieckAbelian _)

/-- The coefficient complex B[0]. Source: blueprint coefficient conventions
(blueprint: lem-pod-point-evaluation-completion-normalization). -/
abbrev coefficient := (CochainComplex.singleFunctor (Mod D l E) 0).obj
  (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k))))

/-- The actual signed total tensor. Source: Stacks 06YM
(blueprint: lem-pod-point-evaluation-completion-normalization). -/
abbrev total (C J : CochainComplex (Mod D l E) ℤ) :=
  PointDerivedHom.total.{u, u} D.k (B D l E) C J

/-- The identity scalar-extension quotient tower. Source: Bhatt--Scholze 3.4.10
(blueprint: lem-pod-point-evaluation-completion-normalization). -/
abbrev tower := integralScalarTowerFunctor l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k))

/-- Its specified shifted cone, including its functorial map on both coordinates.
Source: Bhatt--Scholze 3.4.10; Stacks 0941
(blueprint: lem-pod-point-evaluation-completion-normalization). -/
abbrev completion := integralScalarComplexFunctor l E E (AlgHom.id ℚ_[l] E)
  (Spec (.of D.k))

/-- Identity-extension augmentation: quotient-product and zero shifted-product coordinates.
Source: finite-free completed scalar comparison, identity case
(blueprint: lem-pod-point-evaluation-completion-normalization). -/
abbrev unit := completedScalarIdentityUnit l E (Spec (.of D.k))

/-- Balancing is required on every local tensor generator, not merely on cohomology.
Source: node proof step 2, Bhatt--Scholze 3.4.10
(blueprint: lem-pod-point-evaluation-completion-normalization). -/
@[no_expose] def Balanced (C J : CochainComplex (Mod D l E) ℤ)
    (rho : (integralOperationsTensorTowerFunctor l E (Spec (.of D.k))).obj (C, J) ≅
      (tower D l E).obj (total D l E C J)) : Prop :=
  ∀ (n : ℕ) (p j : ℤ) (U : (Spec (.of D.k)).ProEtᵒᵖ)
    (a b : (integralCoefficientCommRingSheaf l E (Spec (.of D.k)) n).obj.obj U)
    (x : (C.X p).val.obj U) (y : (J.X j).val.obj U),
    ((rho.hom.app (op n)).f (p + j)).val.app U
      (integralOperationsTotalTensorSection l E (Spec (.of D.k)) n C J p j U
        (unrestrictedIntegralTensorSection l E (Spec (.of D.k)) n (C.X p) U a x)
        (unrestrictedIntegralTensorSection l E (Spec (.of D.k)) n (J.X j) U b y)) =
      integralScalarTensorSection l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k)) n
        ((total D l E C J).X (p + j)) U (a * b)
          (PointDerivedHom.totalElement.{u, u} D.k (B D l E) C J p j U x y)

/-- The existing completed-tensor representative isomorphism with its endpoints explicit.
Source: Bhatt--Scholze 3.4.10; integral operations on good complexes
(blueprint: lem-pod-point-evaluation-completion-normalization). -/
@[no_expose] def tensorModelIso
    (C J : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory) :
    (Q D l E).obj ((integralOperationsTensorComplexFunctor l E (Spec (.of D.k))).obj
      (C.obj, J.obj)) ≅
    (integralCompletedTensor l E (Spec (.of D.k))).obj
      ((Q D l E).obj C.obj, (Q D l E).obj J.obj) :=
  (integralCompletedTensorComparison l E (Spec (.of D.k))).symm.app (C, J)

/-- The canonical completion comparison, transported through balancing and the existing
completed-tensor representative comparison. Source: node proof steps 1--3
(blueprint: lem-pod-point-evaluation-completion-normalization). -/
@[no_expose] def chi
    (C J : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (rho : (integralOperationsTensorTowerFunctor l E (Spec (.of D.k))).obj
        (C.obj, J.obj) ≅ (tower D l E).obj (total D l E C.obj J.obj)) :
    (Q D l E).obj (total D l E C.obj J.obj) ⟶
      (integralCompletedTensor l E (Spec (.of D.k))).obj
        ((Q D l E).obj C.obj, (Q D l E).obj J.obj) :=
  (Q D l E).map (((unit D l E).app (total D l E C.obj J.obj)) ≫
      (integralOperationsRoosFunctor.mapIso rho).inv) ≫
    (tensorModelIso D l E C J).hom

/-- The actual chain augmentation into the tensor's specified Roos model.
Source: node proof steps 2--4, Bhatt--Scholze 3.4.10
(blueprint: lem-pod-point-evaluation-completion-normalization). -/
@[no_expose] def chainChi
    (C J : CochainComplex (Mod D l E) ℤ)
    (rho : (integralOperationsTensorTowerFunctor l E (Spec (.of D.k))).obj
        (C, J) ≅ (tower D l E).obj (total D l E C J)) :
    total D l E C J ⟶
      (integralOperationsTensorComplexFunctor l E (Spec (.of D.k))).obj (C, J) :=
  (unit D l E).app (total D l E C J) ≫
    (integralOperationsRoosFunctor.mapIso rho).inv

/-- The recorded point completion chain map precomposed with the actual module unit.
Source: node proof step 6, Stacks 07A4 and 0941
(blueprint: lem-pod-point-evaluation-completion-normalization). -/
@[no_expose] def unitCompletion
    (hl : l ≠ D.p) (S : PointIntegralTensorData D l hl E)
    (canonical : PointIntegralTensorCanonical D l hl E S)
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
    (C J : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (eta : P ⟶ (pointIntegralComplexSections D l E).obj C.obj) :
    P ⊗ (pointIntegralComplexSections D l E).obj J.obj ⟶
      (pointIntegralComplexSections D l E).obj
        ((integralOperationsTensorComplexFunctor l E (Spec (.of D.k))).obj (C.obj, J.obj)) :=
  (MonoidalCategory.tensor (CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)).map
    (X := (P, (pointIntegralComplexSections D l E).obj J.obj))
    (Y := ((pointIntegralComplexSections D l E).obj C.obj,
      (pointIntegralComplexSections D l E).obj J.obj))
    (Prod.mkHom eta (𝟙 ((pointIntegralComplexSections D l E).obj J.obj))) ≫
    canonical.completion C J

/-- The strict completion of a pairing, with both cone coordinates fixed by functoriality.
Source: node proof steps 4--5, Bhatt--Scholze 3.4.10
(blueprint: lem-pod-point-evaluation-completion-normalization). -/
@[no_expose] def completedPairing
    (C J : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (rho : (integralOperationsTensorTowerFunctor l E (Spec (.of D.k))).obj
        (C.obj, J.obj) ≅ (tower D l E).obj (total D l E C.obj J.obj))
    (e : total D l E C.obj J.obj ⟶ coefficient D l E)
    (b : (Q D l E).obj (coefficient D l E) ≅
      (Q D l E).obj ((completion D l E).obj (coefficient D l E))) :
    (integralCompletedTensor l E (Spec (.of D.k))).obj
      ((Q D l E).obj C.obj, (Q D l E).obj J.obj) ⟶
        (Q D l E).obj (coefficient D l E) :=
  (tensorModelIso D l E C J).inv ≫
    (Q D l E).map ((integralOperationsRoosFunctor.mapIso rho).hom ≫
      (completion D l E).map e) ≫ b.inv

/-- Actual tensor of the unit P to sections(C) with a section of J, localized in the
same module derived category. Source: node proof step 6
(blueprint: lem-pod-point-evaluation-completion-normalization). -/
@[no_expose] def inverseTensorComparison (hl : l ≠ D.p) (S : PointIntegralTensorData D l hl E)
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
    (C J : CochainComplex (Mod D l E) ℤ)
    (hC : finiteTorConstructibleIntegral l E (Spec (.of D.k)) ((Q D l E).obj C))
    (hJ : finiteTorConstructibleIntegral l E (Spec (.of D.k)) ((Q D l E).obj J))
    (eta : P ⟶ (pointIntegralComplexSections D l E).obj C) :
    (QR l E).obj P ⊗ (pointFibreIntegralAmbient D l E).obj ((Q D l E).obj J) ⟶
      (pointFibreIntegralAmbient D l E).obj
        ((integralCompletedTensor l E (Spec (.of D.k))).obj
          ((Q D l E).obj C, (Q D l E).obj J)) :=
  (MonoidalCategory.tensor _).map
    (Prod.mkHom ((QR l E).map eta ≫ (pointIntegralDerivedFactors D l E).inv.app C)
      (𝟙 ((pointFibreIntegralAmbient D l E).obj ((Q D l E).obj J)))) ≫
    (pointIntegralTensorComparison D l hl E S
      ⟨(Q D l E).obj C, hC⟩ ⟨(Q D l E).obj J, hJ⟩).inv

/-- Termwise completed constant realization, in a strictly normalized presentation L.
Source: Stacks 03EK and node hypotheses
(blueprint: lem-pod-point-evaluation-completion-normalization). -/
abbrev model (L : ModuleCat.{u + 1} (R l E) ⥤ Mod D l E) [L.Additive]
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ) :=
  (L.mapHomologicalComplex (.up ℤ)).obj P

attribute [local semireducible] WeilConjectures.integralOperationsRoosFunctor
  WeilConjectures.integralOperationsRoos

/-- Finite quotient coordinate of the fixed augmentation. Source: node proof steps 3--4
(blueprint: lem-pod-point-evaluation-completion-normalization). -/
@[no_expose] def quotient (K : CochainComplex (Mod D l E) ℤ) (n : ℕ) :
    K ⟶ ((tower D l E).obj K).obj (op n) :=
  (unit D l E).app K ≫
    CochainComplex.mappingCocone.fst
      (completedScalarRoosEndomorphism l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k)) K) ≫
    Pi.π (fun n ↦ ((tower D l E).obj K).obj (op n)) n

/-- Both chain coordinates, with quotient indexing n+1. Source: node proof steps 3--4
(blueprint: lem-pod-point-evaluation-completion-normalization). -/
@[no_expose] def UnitCoordinates (K : CochainComplex (Mod D l E) ℤ) : Prop :=
  (∀ (i : ℤ) (n : ℕ) (U : (Spec (.of D.k)).ProEtᵒᵖ) (x : (K.X i).val.obj U),
    ((quotient D l E K n).f i).val.app U x =
      integralScalarTensorSection l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k)) n
        (K.X i) U 1 x) ∧
  ∀ i : ℤ, ((unit D l E).app K).f i ≫
    (CochainComplex.mappingCocone.snd
      (completedScalarRoosEndomorphism l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k)) K)).v
        i (i + -1) rfl = 0

/-- The completion normalization equation for the sections balancing map.
Source: node proof step 6 (blueprint: lem-pod-point-evaluation-completion-normalization). -/
@[no_expose] def betaCompletionEquation
    (hl : l ≠ D.p) (S : PointIntegralTensorData D l hl E)
    (canonical : PointIntegralTensorCanonical D l hl E S)
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
    (C J : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (rho : (integralOperationsTensorTowerFunctor l E (Spec (.of D.k))).obj
      (C.obj, J.obj) ≅ (tower D l E).obj (total D l E C.obj J.obj))
    (eta : P ⟶ (pointIntegralComplexSections D l E).obj C.obj)
    (beta : P ⊗ (pointIntegralComplexSections D l E).obj J.obj ⟶
      (pointIntegralComplexSections D l E).obj (total D l E C.obj J.obj)) : Prop :=
  PointSectionsCompletionEquation D l E hl S canonical P C J rho eta beta

attribute [local irreducible] WeilConjectures.integralOperationsRoosFunctor
  WeilConjectures.integralOperationsRoos
attribute [local irreducible] completedScalarChangeData integralScalarReductionWitness

-- Keep the coefficient presentation conversion abstract in the complex argument.
private theorem bounded_good (K : CochainComplex (Mod D l E) ℤ) (b : ℤ)
    [K.IsStrictlyLE b]
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology (Spec (.of D.k))) (R := B D l E) (K.X i)) :
    integralOperationsGoodComplex l E (Spec (.of D.k)) K := by
  exact ⟨SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    (B D l E) K b hflat, hflat⟩

private theorem coefficient_good :
    integralOperationsGoodComplex l E (Spec (.of D.k)) (coefficient D l E) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients (B D l E)
  let := SheafOfModules.monoidalCategory (B D l E)
  let := SheafOfModules.symmetricCategory (B D l E)
  let := SheafOfModules.tensorPreadditive (B D l E)
  have (M : Mod D l E) : (MonoidalCategory.tensorLeft M).Additive :=
    SheafOfModules.tensorLeft_additive_independent (B D l E) M
  have (M : Mod D l E) : (MonoidalCategory.tensorRight M).Additive :=
    Functor.additive_of_iso (F := MonoidalCategory.tensorLeft M)
      (BraidedCategory.tensorLeftIsoTensorRight M)
  have hk : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology (Spec (.of D.k))) (R := B D l E)
      (coefficient D l E) := by
    intro Z hZ
    exact fun i ↦ (hZ i).of_iso (HomologicalComplex.rightUnitor Z).symm
  refine ⟨hk, ?_⟩
  intro i
  have hf : ObjectProperty.flat ((coefficient D l E).X i) := by
    by_cases hi : i = 0
    · subst i
      exact ObjectProperty.prop_unit (ObjectProperty.flat (A := Mod D l E))
    · have hz : IsZero ((coefficient D l E).X i) :=
        HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) 0 _ i hi
      have hF : IsZero (MonoidalCategory.tensorRight ((coefficient D l E).X i)) :=
        (MonoidalCategory.tensorRight _).isZero
          (fun M ↦ (MonoidalCategory.tensorLeft M).map_isZero hz)
      have := (MonoidalCategory.tensorRight _).preservesLimitsOfSize_of_isZero hF
      have := (MonoidalCategory.tensorRight _).preservesColimitsOfSize_of_isZero hF
      have hr : exactFunctor (Mod D l E) (Mod D l E)
          (MonoidalCategory.tensorRight ((coefficient D l E).X i)) := by
        rw [exactFunctor_iff]
        constructor <;> infer_instance
      exact ⟨(exactFunctor _ _).prop_of_iso
        (BraidedCategory.tensorLeftIsoTensorRight _).symm hr, hr⟩
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso (B D l E) _).symm hf.2

private theorem unit_coordinates (K : CochainComplex (Mod D l E) ℤ) :
    UnitCoordinates D l E K := by
  have h := (completedScalarIdentityUnit_existsUnique l E (Spec (.of D.k))).exists.choose_spec
  constructor
  · intro i n U x
    exact h.1 K i n U x
  · intro i
    exact h.2 K i

private theorem chain_naturality {K H : CochainComplex (Mod D l E) ℤ} (f : K ⟶ H) :
    (unit D l E).app K ≫ (completion D l E).map f = f ≫ (unit D l E).app H :=
  ((unit D l E).naturality f).symm

private theorem quotient_naturality {K H : CochainComplex (Mod D l E) ℤ} (f : K ⟶ H)
    (n : ℕ) :
    quotient D l E K n ≫ ((tower D l E).map f).app (op n) =
      f ≫ quotient D l E H n := by
  ext i U x
  change (((integralScalarReduction l E E (AlgHom.id ℚ_[l] E)
      (Spec (.of D.k)) n).map (f.f i)).val.app U)
        (((quotient D l E K n).f i).val.app U x) =
    ((quotient D l E H n).f i).val.app U ((f.f i).val.app U x)
  rw [(unit_coordinates D l E K).1, (unit_coordinates D l E H).1]
  let φ := integralScalarRho l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k)) n
  let k : SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ (K.X i) ⟶
      SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ (H.X i) :=
    { app := fun V ↦ (ModuleCat.extendScalars.{u + 1} (φ.hom.app V).hom).map ((f.f i).val.app V)
      naturality := SheafOfModules.changeOfRingsHom_naturality φ (K.X i) (f.f i) }
  let : Module ((B D l E).obj.obj U) ((K.X i).val.obj U) :=
    ((K.X i).val.obj U).isModule
  let z : (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ (K.X i)).obj U :=
    (1 : (integralCoefficientCommRingSheaf l E (Spec (.of D.k)) n).obj.obj U)
      ⊗ₜ[(B D l E).obj.obj U, (φ.hom.app U).hom] x
  have ht := congrArg (fun η ↦ (η.app U).hom z)
    (toSheafify_naturality (Scheme.ProEt.topology (Spec (.of D.k)))
      ((PresheafOfModules.toPresheaf _).map k))
  change (toSheafify _ (SheafOfModules.changeOfRingsPresheaf φ (H.X i)).presheaf).app U
      ((ModuleCat.extendScalars.{u + 1} (φ.hom.app U).hom).map ((f.f i).val.app U) z) = _ at ht
  dsimp only [z] at ht
  erw [ModuleCat.ExtendScalars.map_tmul] at ht
  let e := integralScalarReductionIso l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k)) n
  have hn := congrArg (fun a ↦ a.val.app U
    ((toSheafify _ (SheafOfModules.changeOfRingsPresheaf φ (K.X i)).presheaf).app U z))
    (e.inv.naturality (f.f i)).symm
  exact hn.trans (congrArg (fun y ↦ ((e.inv.app (H.X i)).val.app U) y) ht.symm)

attribute [local semireducible] DerivedCategory.Q
  HasDerivedCategory.ofIsGrothendieckAbelian
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.mapDerivedCategoryFactors

private theorem unit_isIso
    (K : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) ((Q D l E).obj K.obj)) :
    IsIso ((Q D l E).map ((unit D l E).app K.obj)) := by
  have hc := CompletedLineTensor.intrinsic_complete l E (Spec (.of D.k))
    ⟨(Q D l E).obj K.obj, hK⟩
  have h := (CompletedLineTensor.unit_normalization l E (Spec (.of D.k))).1 K hc
  rw [← h]
  exact IsIso.comp_isIso'
    (Iso.isIso_inv (CompletedLineTensor.unit l E (Spec (.of D.k)) _ hc))
    (Iso.isIso_hom ((integralScalarExtensionComparisonOfUniverses l E E
      (AlgHom.id ℚ_[l] E) (Spec (.of D.k))).app K))

attribute [local irreducible] DerivedCategory.Q
  HasDerivedCategory.ofIsGrothendieckAbelian
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.mapDerivedCategoryFactors
attribute [local irreducible] completedScalarIdentityUnit completedScalarIdentityMultiplication
  completedScalarComparison integralScalarExtensionOfUniverses
  integralScalarExtensionComparisonOfUniverses pointIntegralDerivedFactors

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

-- Transport a chain square using the sections factorization and tensorator naturality.
private theorem sections_tensor_transport
    {𝒜 : Type u₁} {ℬ : Type u₂} {𝒞 : Type u₃} {𝒟 : Type u₄}
    [Category.{v₁} 𝒜] [Category.{v₂} ℬ] [Category.{v₃} 𝒞] [Category.{v₄} 𝒟]
    [MonoidalCategory 𝒜] [MonoidalCategory ℬ]
    (Q₀ : 𝒞 ⥤ 𝒟) (Γ : 𝒞 ⥤ 𝒜) (Λ : 𝒜 ⥤ ℬ) (F : 𝒟 ⥤ ℬ)
    [Λ.LaxMonoidal] (factors : Q₀ ⋙ F ≅ Γ ⋙ Λ)
    {P : 𝒜} {X Y K T : 𝒞} {Z : 𝒟}
    (eta : P ⟶ Γ.obj X) (beta : P ⊗ Γ.obj Y ⟶ Γ.obj K)
    (c : K ⟶ T) (κ : Γ.obj X ⊗ Γ.obj Y ⟶ Γ.obj T)
    (r : Q₀.obj T ⟶ Z) (χ : Q₀.obj K ⟶ Z)
    (τ : F.obj (Q₀.obj X) ⊗ F.obj (Q₀.obj Y) ⟶ F.obj Z)
    (hbeta : beta ≫ Γ.map c =
      (MonoidalCategory.tensor 𝒜).map (Prod.mkHom eta (𝟙 (Γ.obj Y))) ≫ κ)
    (hχ : χ = Q₀.map c ≫ r)
    (hτ : τ = (MonoidalCategory.tensor ℬ).map
        (Prod.mkHom (factors.hom.app X) (factors.hom.app Y)) ≫
      Functor.LaxMonoidal.μ Λ (Γ.obj X) (Γ.obj Y) ≫ Λ.map κ ≫
        factors.inv.app T ≫ F.map r) :
    Functor.LaxMonoidal.μ Λ P (Γ.obj Y) ≫ Λ.map beta ≫
        factors.inv.app K ≫ F.map χ =
      (MonoidalCategory.tensor ℬ).map
        (Prod.mkHom (𝟙 (Λ.obj P)) (factors.inv.app Y)) ≫
      (MonoidalCategory.tensor ℬ).map
        (Prod.mkHom (Λ.map eta ≫ factors.inv.app X) (𝟙 (F.obj (Q₀.obj Y)))) ≫ τ := by
  rw [hχ, F.map_comp, hτ]
  have hn := factors.inv.naturality c
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, ← Λ.map_comp_assoc, hbeta, Λ.map_comp]
  simp only [Category.assoc]
  simp only [MonoidalCategory.tensor_map]
  have hm := Functor.LaxMonoidal.μ_natural Λ eta (𝟙 (Γ.obj Y))
  rw [← reassoc_of% hm]
  simp only [CategoryTheory.Functor.map_id]
  simp only [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Functor.comp_obj, Category.assoc, Category.comp_id, Category.id_comp,
    Iso.inv_hom_id_app]

-- Functorial cancellation for a completed pairing, without unfolding its cone model.
-- Map a unit followed by a model isomorphism without expanding either model.
private theorem isIso_map_iso
    {𝒞 : Type u₃} {𝒟 : Type u₄}
    [Category.{v₃} 𝒞] [Category.{v₄} 𝒟]
    (F : 𝒞 ⥤ 𝒟) {X Y T : 𝒞} {Z : 𝒟}
    (f : X ⟶ Y) (r : Y ≅ T) (s : F.obj T ≅ Z)
    (hf : IsIso (F.map f)) : IsIso (F.map (f ≫ r.hom) ≫ s.hom) := by
  rw [F.map_comp]
  exact IsIso.comp_isIso'
    (IsIso.comp_isIso' hf (Iso.isIso_hom (F.mapIso r))) (Iso.isIso_hom s)

private theorem localized_pairing_square
    {𝒞 : Type u₃} {𝒟 : Type u₄}
    [Category.{v₃} 𝒞] [Category.{v₄} 𝒟]
    (F : 𝒞 ⥤ 𝒟) (H : 𝒞 ⥤ 𝒞) (eta : 𝟭 𝒞 ⟶ H)
    {X Y T : 𝒞} {Z : 𝒟} (r : H.obj X ≅ T) (t : F.obj T ≅ Z)
    (b : F.obj Y ≅ F.obj (H.obj Y)) (e : X ⟶ Y)
    (hb : b.hom = F.map (eta.app Y)) :
    (F.map (eta.app X ≫ r.hom) ≫ t.hom) ≫
      (t.inv ≫ F.map (r.inv ≫ H.map e) ≫ b.inv) = F.map e := by
  have hr : F.map r.hom ≫ F.map r.inv = 𝟙 _ := by
    rw [← F.map_comp, Iso.hom_inv_id, F.map_id]
  calc
    _ = F.map (eta.app X) ≫ F.map (H.map e) ≫ b.inv := by
      simp only [Category.assoc, F.map_comp]
      rw [reassoc_of% t.hom_inv_id, reassoc_of% hr]
    _ = F.map e := by
      rw [← F.map_comp_assoc, ← eta.naturality, Functor.id_map, F.map_comp]
      rw [Category.assoc, ← hb, Iso.hom_inv_id, Category.comp_id]

private theorem total_good (C J : CochainComplex (Mod D l E) ℤ)
    (hC : integralOperationsGoodComplex l E (Spec (.of D.k)) C)
    (hJ : integralOperationsGoodComplex l E (Spec (.of D.k)) J) :
    integralOperationsGoodComplex l E (Spec (.of D.k)) (total D l E C J) := by
  have ht :=
    SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model.{u + 1, u, u + 1, u + 2}
      (B D l E) C J hC.1 hJ.1 hC.2 hJ.2
  exact ⟨ht.1, ht.2.1⟩

-- The construction-owned equation is definitionally the original chain square.
private theorem beta_completion_chain
    (hl : l ≠ D.p) (S : PointIntegralTensorData D l hl E)
    (canonical : PointIntegralTensorCanonical D l hl E S)
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
    (C J : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (rho : (integralOperationsTensorTowerFunctor l E (Spec (.of D.k))).obj
      (C.obj, J.obj) ≅ (tower D l E).obj (total D l E C.obj J.obj))
    (eta : P ⟶ (pointIntegralComplexSections D l E).obj C.obj)
    (beta : P ⊗ (pointIntegralComplexSections D l E).obj J.obj ⟶
      (pointIntegralComplexSections D l E).obj (total D l E C.obj J.obj))
    (h : betaCompletionEquation D l E hl S canonical P C J rho eta beta) :
  beta ≫ (pointIntegralComplexSections D l E).map (chainChi D l E C.obj J.obj rho) =
    unitCompletion D l E hl S canonical P C J eta := h

-- A parent-presentation interface for the strict quotient tower construction.
private theorem balanced_tower_api (C J : CochainComplex (Mod D l E) ℤ) :
    ∃ rho : (integralOperationsTensorTowerFunctor l E (Spec (.of D.k))).obj (C, J) ≅
      (tower D l E).obj (total D l E C J), Balanced D l E C J rho := by
  exact point_balanced_quotient_tower D l E C J

-- Normalize the imported section model at abstract good complexes.
private theorem sections_balancing_api
    (hl : l ≠ D.p) (S : PointIntegralTensorData D l hl E)
    (canonical : PointIntegralTensorCanonical D l hl E S)
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
    (C J : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (rho : (integralOperationsTensorTowerFunctor l E (Spec (.of D.k))).obj
      (C.obj, J.obj) ≅ (tower D l E).obj (total D l E C.obj J.obj))
    (hbal : Balanced D l E C.obj J.obj rho)
    (eta : P ⟶ (pointIntegralComplexSections D l E).obj C.obj) :
    ∃ beta : P ⊗ (pointIntegralComplexSections D l E).obj J.obj ⟶
      (pointIntegralComplexSections D l E).obj (total D l E C.obj J.obj),
    (∀ (p j : ℤ) (x : P.X p)
      (h : ((pointIntegralComplexSections D l E).obj J.obj).X j),
      (beta.f (p + j)).hom
        ((HomologicalComplex.ιTensorObj P ((pointIntegralComplexSections D l E).obj J.obj)
          p j (p + j) rfl).hom (x ⊗ₜ[R l E] h)) =
      PointDerivedHom.totalElement.{u, u} D.k (B D l E) C.obj J.obj p j
        (op (PointDerivedHom.finalObject D.k)) ((eta.f p).hom x) h) ∧
    betaCompletionEquation D l E hl S canonical P C J rho eta beta := by
  exact point_sections_balancing_completion D l E hl S canonical P C J rho hbal eta


attribute [local irreducible] WeilConjectures.IntegralHom.totalTensor
  WeilConjectures.integralOperationsTensorTowerFunctor WeilConjectures.integralScalarTowerFunctor

attribute [local irreducible] integralOperationsGoodComplex

end WeilConjectures.PointEvaluationCompletion
