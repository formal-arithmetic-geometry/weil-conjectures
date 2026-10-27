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
public import Sheaf.Paper.PointEvaluationCompletionModels
import all Sheaf.Paper.PointEvaluationCompletionModels
import all Sheaf.Paper.PointFibreDerivedTensorModels

/-! # Strict completion of point pairings and inverse tensor comparison

Source: main-20261015 blueprint, point-dualizing-complex proof, second sentence;
Bhatt--Scholze, Definition 3.4.10 and Lemmas 3.4.11--3.4.12.
(blueprint: lem-pod-point-evaluation-completion-normalization).
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

attribute [local irreducible] completedScalarChangeData integralScalarReductionWitness
attribute [local irreducible] completedScalarIdentityUnit completedScalarIdentityMultiplication
  completedScalarComparison integralScalarExtensionOfUniverses
  integralScalarExtensionComparisonOfUniverses pointIntegralDerivedFactors
attribute [local irreducible] WeilConjectures.IntegralHom.totalTensor
  WeilConjectures.integralOperationsTensorTowerFunctor WeilConjectures.integralScalarTowerFunctor
attribute [local irreducible] integralOperationsGoodComplex

set_option maxHeartbeats 600000 in
-- The large conjunction compares the fixed derived-category and tensor instances.
/-- Strict completion of every pairing, and the normalization of the actual point tensorator.
Source: main-20261015 blueprint point-dualizing-complex proof, second sentence;
Bhatt--Scholze 3.4.10--3.4.12
(blueprint: lem-pod-point-evaluation-completion-normalization).

Proof: bounded-above flatness gives good representatives for C and J; the
K-flat total tensor theorem gives the same for their signed total. The balanced
quotient tower lemma supplies rho and its local scalar multiplication formula.
Constructibility supplies intrinsic derived completeness. The normalized
completed scalar unitor theorem expresses the actual localized identity-extension
unit as a composite of isomorphisms. Apply it to the total and B[0].
Their defining theorem gives both coordinates, and naturality gives the strict
chain square and every quotient square. Expanding completedPairing and cancelling
the two model isomorphisms proves its composite with chi is Q(e). Invertibility
of chi proves uniqueness directly. Finally, sections balancing gives beta with
its generator formula and completion square. Naturality of localization's tensor
comparison and of pointIntegralDerivedFactors transports that square to the
inverse tensorator equation, using the comparison field of the canonical witness.
No equality-detection assertion about finite derived reductions is used. -/
theorem point_evaluation_completion_normalization
    (hl : l ≠ D.p) (S : PointIntegralTensorData D l hl E)
    (canonical : PointIntegralTensorCanonical D l hl E S)
    (L : ModuleCat.{u + 1} (R l E) ⥤ Mod D l E) [L.Additive]
    (hobj : ∀ M : ModuleCat.{u + 1} (R l E),
      L.obj M = PointDerivedHom.extensionObject.{u, u} D.k (B D l E)
        (PointDerivedHom.coefficientMap.{u, u} D.k l E 1 true) M)
    (_hmap : ∀ (M N : ModuleCat.{u + 1} (R l E)) (f : M ⟶ N),
      HEq (L.map f) (PointDerivedHom.extensionMorphism.{u, u} D.k (B D l E)
        (PointDerivedHom.coefficientMap.{u, u} D.k l E 1 true) f))
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
    (_hP : ∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b)
    (_hPproj : ∀ i : ℤ, Module.Projective (R l E) (P.X i) ∧
      Module.Finite (R l E) (P.X i))
    (J : CochainComplex (Mod D l E) ℤ)
    (_hJ : ∃ a b : ℤ, J.IsStrictlyGE a ∧ J.IsStrictlyLE b)
    (_hJflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology (Spec (.of D.k))) (R := B D l E) (J.X i))
    (_hCflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology (Spec (.of D.k))) (R := B D l E) ((model D l E L P).X i))
    (eta : P ⟶ (pointIntegralComplexSections D l E).obj (model D l E L P))
    (_heta : ∀ (i : ℤ) (x : P.X i), (eta.f i).hom x =
      PointDerivedHom.generator.{u, u} D.k (B D l E)
        (PointDerivedHom.coefficientMap.{u, u} D.k l E 1 true) L hobj (P.X i)
        (op (PointDerivedHom.finalObject D.k)) 1 x)
    [QuasiIso eta]
    (_hBsections : Function.Bijective (pointIntegralSectionMap l E D.k))
    (_hB : sfIntegralConstructible l E (Spec (.of D.k))
      ((Q D l E).obj (coefficient D l E)))
    (hC : finiteTorConstructibleIntegral l E (Spec (.of D.k))
      ((Q D l E).obj (model D l E L P)))
    (hJ : finiteTorConstructibleIntegral l E (Spec (.of D.k)) ((Q D l E).obj J))
    (_hT : sfIntegralConstructible l E (Spec (.of D.k))
      ((Q D l E).obj (total D l E (model D l E L P) J)))
    (e : total D l E (model D l E L P) J ⟶ coefficient D l E) :
    ∃ (goodC : integralOperationsGoodComplex l E (Spec (.of D.k)) (model D l E L P))
      (goodJ : integralOperationsGoodComplex l E (Spec (.of D.k)) J),
    ∃ rho : (integralOperationsTensorTowerFunctor l E (Spec (.of D.k))).obj
        (model D l E L P, J) ≅ (tower D l E).obj (total D l E (model D l E L P) J),
    Balanced D l E (model D l E L P) J rho ∧
    IsIso (chi D l E ⟨model D l E L P, goodC⟩ ⟨J, goodJ⟩ rho) ∧
    UnitCoordinates D l E (total D l E (model D l E L P) J) ∧
    UnitCoordinates D l E (coefficient D l E) ∧
    (∀ n : ℕ, quotient D l E (total D l E (model D l E L P) J) n ≫
      ((tower D l E).map e).app (op n) = e ≫ quotient D l E (coefficient D l E) n) ∧
    ((unit D l E).app (total D l E (model D l E L P) J) ≫
      (completion D l E).map e = e ≫ (unit D l E).app (coefficient D l E)) ∧
    ∃ b : (Q D l E).obj (coefficient D l E) ≅
      (Q D l E).obj ((completion D l E).obj (coefficient D l E)),
    b.hom = (Q D l E).map ((unit D l E).app (coefficient D l E)) ∧
    (∃! v : (integralCompletedTensor l E (Spec (.of D.k))).obj
        ((Q D l E).obj (model D l E L P), (Q D l E).obj J) ⟶
          (Q D l E).obj (coefficient D l E),
      chi D l E ⟨model D l E L P, goodC⟩ ⟨J, goodJ⟩ rho ≫ v = (Q D l E).map e) ∧
    chi D l E ⟨model D l E L P, goodC⟩ ⟨J, goodJ⟩ rho ≫
      completedPairing D l E ⟨model D l E L P, goodC⟩ ⟨J, goodJ⟩ rho e b =
      (Q D l E).map e ∧
    ∃ beta : P ⊗ (pointIntegralComplexSections D l E).obj J ⟶
      (pointIntegralComplexSections D l E).obj (total D l E (model D l E L P) J),
    (∀ (p j : ℤ) (x : P.X p)
      (h : ((pointIntegralComplexSections D l E).obj J).X j),
      (beta.f (p + j)).hom
        ((HomologicalComplex.ιTensorObj P ((pointIntegralComplexSections D l E).obj J)
          p j (p + j) rfl).hom (x ⊗ₜ[R l E] h)) =
      PointDerivedHom.totalElement.{u, u} D.k (B D l E) (model D l E L P) J p j
        (op (PointDerivedHom.finalObject D.k)) ((eta.f p).hom x) h) ∧
    betaCompletionEquation D l E hl S canonical P
      ⟨model D l E L P, goodC⟩ ⟨J, goodJ⟩ rho eta beta ∧
    Functor.LaxMonoidal.μ (QR l E) P ((pointIntegralComplexSections D l E).obj J) ≫
      (QR l E).map beta ≫
      (pointIntegralDerivedFactors D l E).inv.app (total D l E (model D l E L P) J) ≫
      (pointFibreIntegralAmbient D l E).map
        (chi D l E ⟨model D l E L P, goodC⟩ ⟨J, goodJ⟩ rho) =
      (MonoidalCategory.tensor _).map
        (Prod.mkHom (𝟙 ((QR l E).obj P)) ((pointIntegralDerivedFactors D l E).inv.app J)) ≫
      inverseTensorComparison D l E hl S P (model D l E L P) J hC hJ eta := by
  let b := Classical.choose (Classical.choose_spec _hP)
  have hb : P.IsStrictlyLE b := (Classical.choose_spec (Classical.choose_spec _hP)).2
  have hmodel : CochainComplex.IsStrictlyLE (model D l E L P) b := by
    let _ := hb
    dsimp only [model]
    infer_instance
  have goodC : integralOperationsGoodComplex l E (Spec (.of D.k)) (model D l E L P) :=
    bounded_good D l E _ b _hCflat
  let d := Classical.choose (Classical.choose_spec _hJ)
  have hd : J.IsStrictlyLE d := (Classical.choose_spec (Classical.choose_spec _hJ)).2
  have goodJ : integralOperationsGoodComplex l E (Spec (.of D.k)) J :=
    bounded_good D l E J d _hJflat
  have goodT := total_good D l E (model D l E L P) J goodC goodJ
  have hrho := balanced_tower_api D l E (model D l E L P) J
  let rho : (integralOperationsTensorTowerFunctor l E (Spec (.of D.k))).obj
      (model D l E L P, J) ≅ (tower D l E).obj (total D l E (model D l E L P) J) :=
    hrho.choose
  have hbal : Balanced D l E (model D l E L P) J rho := hrho.choose_spec
  have huT := unit_isIso D l E ⟨_, goodT⟩ _hT
  have huB := unit_isIso D l E ⟨_, coefficient_good D l E⟩ _hB
  have hchi : IsIso (chi D l E ⟨_, goodC⟩ ⟨J, goodJ⟩ rho) := by
    exact isIso_map_iso (Q D l E)
      ((unit D l E).app (total D l E (model D l E L P) J))
      (integralOperationsRoosFunctor.mapIso rho).symm
      (tensorModelIso D l E ⟨_, goodC⟩ ⟨J, goodJ⟩) huT
  let b := asIso ((Q D l E).map ((unit D l E).app (coefficient D l E)))
  have hb : b.hom = (Q D l E).map ((unit D l E).app (coefficient D l E)) := rfl
  have hpair : chi D l E ⟨_, goodC⟩ ⟨J, goodJ⟩ rho ≫
      completedPairing D l E ⟨_, goodC⟩ ⟨J, goodJ⟩ rho e b = (Q D l E).map e := by
    exact localized_pairing_square (Q D l E) (completion D l E) (unit D l E)
      (integralOperationsRoosFunctor.mapIso rho).symm
      (tensorModelIso D l E ⟨_, goodC⟩ ⟨J, goodJ⟩) b e hb
  have hsections := sections_balancing_api D l E hl S
    canonical P ⟨_, goodC⟩ ⟨J, goodJ⟩ rho hbal eta
  let beta : P ⊗ (pointIntegralComplexSections D l E).obj J ⟶
      (pointIntegralComplexSections D l E).obj (total D l E (model D l E L P) J) :=
    hsections.choose
  have hbeta : ∀ (p j : ℤ) (x : P.X p)
      (h : ((pointIntegralComplexSections D l E).obj J).X j),
      (beta.f (p + j)).hom
        ((HomologicalComplex.ιTensorObj P ((pointIntegralComplexSections D l E).obj J)
          p j (p + j) rfl).hom (x ⊗ₜ[R l E] h)) =
      PointDerivedHom.totalElement.{u, u} D.k (B D l E) (model D l E L P) J p j
        (op (PointDerivedHom.finalObject D.k)) ((eta.f p).hom x) h :=
    hsections.choose_spec.1
  have hbetaComp : betaCompletionEquation D l E hl S canonical P
      ⟨_, goodC⟩ ⟨J, goodJ⟩ rho eta beta := hsections.choose_spec.2
  have hbetaChain : beta ≫ (pointIntegralComplexSections D l E).map
      (chainChi D l E (model D l E L P) J rho) =
      unitCompletion D l E hl S canonical P ⟨_, goodC⟩ ⟨J, goodJ⟩ eta :=
    beta_completion_chain D l E hl S canonical P ⟨_, goodC⟩ ⟨J, goodJ⟩ rho eta beta hbetaComp
  refine ⟨goodC, goodJ, rho, hbal, hchi, unit_coordinates D l E _,
    unit_coordinates D l E _, fun n ↦ quotient_naturality D l E e n,
    chain_naturality D l E e, b, hb, ?_, hpair, beta, hbeta, hbetaComp, ?_⟩
  · refine ⟨completedPairing D l E ⟨_, goodC⟩ ⟨J, goodJ⟩ rho e b, hpair, ?_⟩
    intro v hv
    have : Epi (chi D l E ⟨_, goodC⟩ ⟨J, goodJ⟩ rho) := IsIso.epi_of_iso _
    exact (cancel_epi (chi D l E ⟨_, goodC⟩ ⟨J, goodJ⟩ rho)).1 (hv.trans hpair.symm)
  · have htau := eq_of_heq (canonical.comparison ⟨_, goodC⟩ ⟨J, goodJ⟩ hC hJ)
    dsimp only [pointIntegralGoodDerivedObject] at htau
    apply sections_tensor_transport (Q D l E) (pointIntegralComplexSections D l E)
      (QR l E) (pointIntegralTowerFibre D l E) (pointIntegralDerivedFactors D l E)
      eta beta (chainChi D l E (model D l E L P) J rho)
      (canonical.completion ⟨_, goodC⟩ ⟨J, goodJ⟩)
      (tensorModelIso D l E ⟨_, goodC⟩ ⟨J, goodJ⟩).hom
      (chi D l E ⟨_, goodC⟩ ⟨J, goodJ⟩ rho)
      (pointIntegralTensorComparison D l hl E S
        ⟨(Q D l E).obj (model D l E L P), hC⟩ ⟨(Q D l E).obj J, hJ⟩).inv
      hbetaChain rfl
    dsimp only [pointIntegralCanonicalComparison, tensorModelIso,
      Iso.app_hom, Iso.symm_hom, pointIntegralTowerFibre] at htau ⊢
    exact htau

attribute [instance] WeilConjectures.IntegralHom.ordinaryTensorObjZero
  WeilConjectures.IntegralHom.ordinaryTensorZero
attribute [instance] WeilConjectures.PointDerivedHom.derivedSheaves
  WeilConjectures.PointDerivedHom.derivedModules
  WeilConjectures.PointDerivedHom.abSheafify
  WeilConjectures.PointDerivedHom.abLocallyBijective

end WeilConjectures.PointEvaluationCompletion
