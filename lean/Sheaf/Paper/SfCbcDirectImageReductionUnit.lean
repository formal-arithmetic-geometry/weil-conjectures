/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.Paper.ConstantTowerDirectImageNormalization
public import Sheaf.Paper.CompleteCoefficientDatum
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.CompletedPullbackAdjunction
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
public import Sheaf.Paper.ProjectionMateExact
import all Sheaf.Paper.ConstantTowerDirectImageNormalization
import all Sheaf.Paper.ProEtaleConstantReductionModels
import Sheaf.Paper.ProEtaleConstantReductionTower
import all Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.CategoryTheory.NormalizedAugmentationTransport

/-!
# Direct-image reduction and the completion unit

Source: Stacks Project, proetale.tex, Tag 099N (3), (4), and sites-cohomology.tex,
Tags 0B56, 0944 and 0A07; strict-diagram refinement of fix-lem-exchanges, Step 5
(blueprint: lem-sf-cbc-direct-image-reduction-unit).

All reductions, augmentations, projection mates and limit comparisons are the
specified constructions of ConstantTowerDirectImageNormalization. The index n
means exponent n+1. Derived towers are localized strict diagrams.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- Avoid replaying dependent scalar-extension conversions during tactic linting.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.StrictTower.DirectImageReduction
open ConstantNormalization
attribute [local irreducible] HasDerivedCategory.standard constantSheaf
  CochainComplex.IsKFlatIndependentCoefficients proEtaleConstantInverseImageMap
  proEtaleRingModulePullbackObj proEtaleRingModulePullbackMap proEtaleRingModuleAdjunction
attribute [local instance 2000] towers_hasDerivedCategory
  proEtaleRingModules_hasDerivedCategory

variable {A : Type (u + 1)} [CommRing A] (I : Ideal A)

/-- Completion is the total limit of the canonical strict quotient reduction.
Source: Stacks 099M, 099N
(blueprint: lem-sf-cbc-direct-image-reduction-unit). -/
def completion (T : Scheme.{u}) :
    DerivedCategory (Modules A T) ⥤ DerivedCategory (Modules A T) :=
  reduction I T ⋙ L A T

/-- The completion unit is the limit of tensoring with the quotient augmentation,
using the specified inverse of the constant-tower limit identification.
Source: Stacks 099M, 099N
(blueprint: lem-sf-cbc-direct-image-reduction-unit). -/
def unit (T : Scheme.{u}) : 𝟭 (DerivedCategory (Modules A T)) ⟶ completion I T :=
  (deltaLimit A T).inv ≫ Functor.whiskerRight (augmentation I T) (L A T)

/-- The natural transformation rho is L(h) followed by the inverse of the
underived-composite normalized direct-image/limit comparison, without evaluation.
Source: Stacks 0A07, 099N
(blueprint: lem-sf-cbc-direct-image-reduction-unit). -/
def comparison {U V : Scheme.{u}} (f : U ⟶ V) :
    push A f ⋙ completion I V ⟶ completion I U ⋙ push A f :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (projection I f) (L A V) ≫
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (reduction I U) (limitPush A f).inv ≫
          (Functor.associator _ _ _).inv

/-- The canonical finite-quotient tensor/pullback comparison. Evaluating the
K-flat-normalized whole-tower tensor comparison gives scalar-extension balancing
with the constant sheaf A/I^(n+1). This defines its actual map, not an arbitrary iso.
Source: Stacks 07A4, 0B56
(blueprint: lem-sf-cbc-direct-image-reduction-unit). -/
def finiteTensorPull {U V : Scheme.{u}} (f : U ⟶ V) (n : ℕ) :
    (reduction I V ⋙ ev A V n) ⋙ pull A f ≅
      pull A f ⋙ (reduction I U ⋙ ev A U n) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (reduction I V) (evalG A f n).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (reductionPull I f) (ev A U n) ≪≫
          Functor.associator _ _ _

/-- The finite-P_n projection morphism is the adjunction mate of tensor balancing,
hence the adjunct of pullback-tensor comparison followed by counit tensor identity.
Its source and target use the canonical evaluation models of derived tensor.
Source: Stacks 0B56, 0944
(blueprint: lem-sf-cbc-direct-image-reduction-unit). -/
def finiteProjection {U V : Scheme.{u}} (f : U ⟶ V) (n : ℕ) :
    push A f ⋙ (reduction I V ⋙ ev A V n) ⟶
      (reduction I U ⋙ ev A U n) ⋙ push A f :=
  mateEquiv
    (proEtaleRingDerivedAdjunction f (coefficients A V) (coefficients A U)
      (constantRingIso A f))
    (proEtaleRingDerivedAdjunction f (coefficients A V) (coefficients A U)
      (constantRingIso A f)) (finiteTensorPull I f n).hom

section NormalizedSquares
universe a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄
variable {C : Type a₁} [Category.{b₁} C] [Abelian C] [HasDerivedCategory.{c₁} C]
  {D : Type a₂} [Category.{b₂} D] [Abelian D] [HasDerivedCategory.{c₂} D]
  {T : Type a₃} [Category.{b₃} T] [Abelian T] [HasDerivedCategory.{c₃} T]
  {W : Type a₄} [Category.{b₄} W] [Abelian W] [HasDerivedCategory.{c₄} W]

private theorem normalized_square_naturality
    (P₀ P : C ⥤ T) (Q₀ Q : D ⥤ W) (F : C ⥤ D) (H : T ⥤ W)
    [P₀.Additive] [P.Additive] [Q₀.Additive] [Q.Additive] [F.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (RP₀ RP : DerivedCategory C ⥤ DerivedCategory T)
    (RQ₀ RQ : DerivedCategory D ⥤ DerivedCategory W)
    (cP₀ : DerivedCategory.Qh ⋙ RP₀ ⟶ P₀.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (cP : DerivedCategory.Qh ⋙ RP ⟶ P.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (cQ₀ : DerivedCategory.Qh ⋙ RQ₀ ⟶ Q₀.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (cQ : DerivedCategory.Qh ⋙ RQ ⟶ Q.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (e : P ⋙ H ≅ F ⋙ Q) (s : P₀ ⋙ H ≅ F ⋙ Q₀)
    (τ : RP ⋙ H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ RQ)
    (τ₀ : RP₀ ⋙ H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ RQ₀)
    (α : P₀ ⟶ P) (β : Q₀ ⟶ Q) (δ : RP₀ ⟶ RP) (ε : RQ₀ ⟶ RQ)
    (hd : ∀ K, δ.app (DerivedCategory.Qh.obj K) ≫ cP.app K =
      cP₀.app K ≫ DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory α (.up ℤ)).app K))
    (he : ∀ K, ε.app (DerivedCategory.Qh.obj K) ≫ cQ.app K =
      cQ₀.app K ≫ DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory β (.up ℤ)).app K))
    (hc : Functor.whiskerRight α H ≫ e.hom =
      s.hom ≫ Functor.whiskerLeft F β)
    (K : HomotopyCategory C (.up ℤ))
    [IsIso (cQ.app ((F.mapHomotopyCategory (.up ℤ)).obj K))]
    (ht : IsReductionPullAt P Q F H RP RQ cP cQ e τ K)
    (ht₀ : IsReductionPullAt P₀ Q₀ F H RP₀ RQ₀ cP₀ cQ₀ s τ₀ K) :
    H.mapDerivedCategory.map (δ.app (DerivedCategory.Qh.obj K)) ≫
        τ.hom.app (DerivedCategory.Qh.obj K) =
      τ₀.hom.app (DerivedCategory.Qh.obj K) ≫
        ε.app (F.mapDerivedCategory.obj (DerivedCategory.Qh.obj K)) := by
  apply (cancel_mono (RQ.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
    cQ.app ((F.mapHomotopyCategory (.up ℤ)).obj K))).mp
  simp only [Category.assoc]
  rw [ht, ← H.mapDerivedCategory.map_comp_assoc, hd, H.mapDerivedCategory.map_comp]
  have hn := H.mapDerivedCategoryFactorsh.hom.naturality
    ((NatTrans.mapHomotopyCategory α (.up ℤ)).app K)
  change H.mapDerivedCategory.map (DerivedCategory.Qh.map
      ((NatTrans.mapHomotopyCategory α (.up ℤ)).app K)) ≫
      H.mapDerivedCategoryFactorsh.hom.app ((P.mapHomotopyCategory (.up ℤ)).obj K) =
    H.mapDerivedCategoryFactorsh.hom.app ((P₀.mapHomotopyCategory (.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map ((H.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory α (.up ℤ)).app K)) at hn
  rw [Category.assoc, reassoc_of% hn, ← DerivedCategory.Qh.map_comp,
    homotopy_square_naturality P₀ P Q₀ Q F H α β e s hc K,
    DerivedCategory.Qh.map_comp]
  have hnε := ε.naturality (F.mapDerivedCategoryFactorsh.hom.app K)
  change RQ₀.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
      ε.app (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj K)) =
    ε.app (F.mapDerivedCategory.obj (DerivedCategory.Qh.obj K)) ≫
      RQ.map (F.mapDerivedCategoryFactorsh.hom.app K) at hnε
  rw [← reassoc_of% hnε, he]
  simpa only [Category.assoc] using congrArg
    (fun t ↦ t ≫ DerivedCategory.Qh.map
      ((NatTrans.mapHomotopyCategory β (.up ℤ)).app
        ((F.mapHomotopyCategory (.up ℤ)).obj K))) ht₀.symm

private theorem model_normalization
    (P : C ⥤ T) (Q : D ⥤ W) (F : C ⥤ D) (H : T ⥤ W)
    [P.Additive] [Q.Additive] [F.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    {M : CochainComplex C ℤ → Prop} {N : CochainComplex D ℤ → Prop}
    (DP : DerivedReductionModelData P M)
    (DQ : DerivedReductionModelData Q N)
    (e : P ⋙ H ≅ F ⋙ Q)
    (τ : DP.reduction ⋙ H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ DQ.reduction)
    (h : OrderedExchange.ModelPullNormalized P Q F H DP DQ e τ)
    (K : CochainComplex C ℤ) (hK : M K) :
    IsReductionPullAt P Q F H DP.reduction DQ.reduction DP.counit DQ.counit e τ
      ((HomotopyCategory.quotient _ (.up ℤ)).obj K) := by
  have h' := (OrderedExchange.modelPull_normalized_iff P Q F H DP DQ e τ K).mpr (h K hK)
  simpa only [IsReductionPullAt, OrderedExchange.modelPullTargetCounit,
    OrderedExchange.modelPullSourceCounit, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp, Category.comp_id] using h'

private def homotopyNatIso {B E : Type*} [Category B] [Category E]
    [Preadditive B] [Preadditive E] (F G : B ⥤ E) [F.Additive] [G.Additive]
    (e : F ≅ G) : F.mapHomotopyCategory (.up ℤ) ≅ G.mapHomotopyCategory (.up ℤ) where
  hom := NatTrans.mapHomotopyCategory e.hom (.up ℤ)
  inv := NatTrans.mapHomotopyCategory e.inv (.up ℤ)
  hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
    NatTrans.mapHomotopyCategory_id]
  inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
    NatTrans.mapHomotopyCategory_id]

set_option genSizeOf false in
set_option genInjectivity false in
private structure DerivedIsoData
    {B E : Type*} [Category B] [Category E] [Abelian B] [Abelian E]
    [HasDerivedCategory B] [HasDerivedCategory E]
    (P Q : B ⥤ E) [P.Additive] [Q.Additive]
    (RP RQ : DerivedCategory B ⥤ DerivedCategory E)
    (cp : DerivedCategory.Qh ⋙ RP ⟶ P.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (cq : DerivedCategory.Qh ⋙ RQ ⟶ Q.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (e : P ≅ Q) where
  iso : RP ≅ RQ
  fac : ∀ K : HomotopyCategory B (.up ℤ),
    iso.hom.app (DerivedCategory.Qh.obj K) ≫ cq.app K =
      cp.app K ≫ DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K)

private def makeDerivedIsoData
    {B E : Type*} [Category B] [Category E] [Abelian B] [Abelian E]
    [HasDerivedCategory B] [HasDerivedCategory E]
    (P Q : B ⥤ E) [P.Additive] [Q.Additive]
    (RP RQ : DerivedCategory B ⥤ DerivedCategory E)
    (cp : DerivedCategory.Qh ⋙ RP ⟶ P.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (cq : DerivedCategory.Qh ⋙ RQ ⟶ Q.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [RP.IsLeftDerivedFunctor cp (HomotopyCategory.quasiIso B (.up ℤ))]
    [RQ.IsLeftDerivedFunctor cq (HomotopyCategory.quasiIso B (.up ℤ))]
    (e : P ≅ Q) : DerivedIsoData P Q RP RQ cp cq e where
  iso := Functor.leftDerivedNatIso RP RQ cp cq (HomotopyCategory.quasiIso B (.up ℤ))
    (Functor.isoWhiskerRight (homotopyNatIso P Q e) DerivedCategory.Qh)
  fac K := Functor.leftDerivedNatTrans_app RP RQ cp cq
    (HomotopyCategory.quasiIso B (.up ℤ)) _ K

private theorem normalized_models_comparison
    (P₀ P : C ⥤ T) (Q₀ Q : D ⥤ W) (F : C ⥤ D) (H : T ⥤ W)
    [P₀.Additive] [P.Additive] [Q₀.Additive] [Q.Additive] [F.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (RP₀ RP : DerivedCategory C ⥤ DerivedCategory T)
    (RQ₀ RQ : DerivedCategory D ⥤ DerivedCategory W)
    (cP₀ : DerivedCategory.Qh ⋙ RP₀ ⟶ P₀.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (cP : DerivedCategory.Qh ⋙ RP ⟶ P.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (cQ₀ : DerivedCategory.Qh ⋙ RQ₀ ⟶ Q₀.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (cQ : DerivedCategory.Qh ⋙ RQ ⟶ Q.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (e : P ⋙ H ≅ F ⋙ Q) (s : P₀ ⋙ H ≅ F ⋙ Q₀)
    (τ : RP ⋙ H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ RQ)
    (τ₀ : RP₀ ⋙ H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ RQ₀)
    (α : P₀ ≅ P) (β : Q₀ ≅ Q)
    (δ : DerivedIsoData P₀ P RP₀ RP cP₀ cP α)
    (ε : DerivedIsoData Q₀ Q RQ₀ RQ cQ₀ cQ β)
    (hc : Functor.whiskerRight α.hom H ≫ e.hom =
      s.hom ≫ Functor.whiskerLeft F β.hom)
    (S : ObjectProperty (CochainComplex C ℤ))
    (res : ∀ E : CochainComplex C ℤ, ∃ (K : CochainComplex C ℤ) (t : K ⟶ E),
      S K ∧ QuasiIso t)
    (hi : ∀ E, S E → IsIso (cQ.app ((F.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient _ (.up ℤ)).obj E))))
    (ht : ∀ E, S E → IsReductionPullAt P Q F H RP RQ cP cQ e τ
      ((HomotopyCategory.quotient _ (.up ℤ)).obj E))
    (ht₀ : ∀ E, S E → IsReductionPullAt P₀ Q₀ F H RP₀ RQ₀ cP₀ cQ₀ s τ₀
      ((HomotopyCategory.quotient _ (.up ℤ)).obj E)) :
    Functor.whiskerRight δ.iso.hom H.mapDerivedCategory ≫ τ.hom =
      τ₀.hom ≫ Functor.whiskerLeft F.mapDerivedCategory ε.iso.hom := by
  apply natTrans_ext_on_resolving_complexes S res
  intro E hE
  have := hi E hE
  exact normalized_square_naturality P₀ P Q₀ Q F H RP₀ RP RQ₀ RQ cP₀ cP cQ₀ cQ
    e s τ τ₀ α.hom β.hom δ.iso.hom ε.iso.hom δ.fac ε.fac hc
    ((HomotopyCategory.quotient _ (.up ℤ)).obj E) (ht E hE) (ht₀ E hE)


private theorem normalized_model_comparison
    (P₀ P : C ⥤ T) (Q₀ Q : D ⥤ W) (F : C ⥤ D) (H : T ⥤ W)
    [P₀.Additive] [P.Additive] [Q₀.Additive] [Q.Additive] [F.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (RP₀ : DerivedCategory C ⥤ DerivedCategory T)
    (RQ₀ : DerivedCategory D ⥤ DerivedCategory W)
    (cP₀ : DerivedCategory.Qh ⋙ RP₀ ⟶ P₀.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (cQ₀ : DerivedCategory.Qh ⋙ RQ₀ ⟶ Q₀.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    {M : CochainComplex C ℤ → Prop} {N : CochainComplex D ℤ → Prop}
    (DP : DerivedReductionModelData P M) (DQ : DerivedReductionModelData Q N)
    (e : P ⋙ H ≅ F ⋙ Q) (s : P₀ ⋙ H ≅ F ⋙ Q₀)
    (τ : DP.reduction ⋙ H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ DQ.reduction)
    (τ₀ : RP₀ ⋙ H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ RQ₀)
    (α : P₀ ≅ P) (β : Q₀ ≅ Q)
    (δ : DerivedIsoData P₀ P RP₀ DP.reduction cP₀ DP.counit α)
    (ε : DerivedIsoData Q₀ Q RQ₀ DQ.reduction cQ₀ DQ.counit β)
    (hc : Functor.whiskerRight α.hom H ≫ e.hom =
      s.hom ≫ Functor.whiskerLeft F β.hom)
    (res : ∀ E : CochainComplex C ℤ, ∃ (K : CochainComplex C ℤ) (t : K ⟶ E),
      (M K ∧ N ((F.mapHomologicalComplex (.up ℤ)).obj K)) ∧ QuasiIso t)
    (ht : OrderedExchange.ModelPullNormalized P Q F H DP DQ e τ)
    (ht₀ : ∀ E, M E → IsReductionPullAt P₀ Q₀ F H RP₀ RQ₀ cP₀ cQ₀ s τ₀
      ((HomotopyCategory.quotient _ (.up ℤ)).obj E)) :
    Functor.whiskerRight δ.iso.hom H.mapDerivedCategory ≫ τ.hom =
      τ₀.hom ≫ Functor.whiskerLeft F.mapDerivedCategory ε.iso.hom := by
  exact normalized_models_comparison P₀ P Q₀ Q F H RP₀ DP.reduction RQ₀ DQ.reduction
    cP₀ DP.counit cQ₀ DQ.counit e s τ τ₀ α β δ ε hc
    (fun E ↦ M E ∧ N ((F.mapHomologicalComplex (.up ℤ)).obj E)) res
    (fun E hE ↦ DQ.isIso_counit _ hE.2)
    (fun E hE ↦ model_normalization P Q F H DP DQ e τ ht E hE.1)
    (fun E hE ↦ ht₀ E hE.1)

end NormalizedSquares

namespace Presentation
open AlgebraicGeometry.Scheme
variable (d : AdicCoefficientDatum A)

private theorem quotient_comm (T : Scheme.{u}) (n : ℕ) :
    quotient d.ideal T n ≫ (pbcLevelConstantComparison T d n).hom =
      OrderedExchange.quotient d T n := by
  symm
  dsimp only [OrderedExchange.quotient, exchangeScalar,
    AdicCoefficientDatum.projection, completedReductionProjection, pbcCompletedComparison]
  rw [Category.assoc]
  erw [HasLimit.isoOfNatIso_hom_π]
  rw [← Category.assoc]
  erw [(adicDatumScalar_exists T
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
      quotientFinite := d.quotientFinite }).exists.choose_spec n]
  rfl

private def levelMap (T : Scheme.{u}) (n : ℕ) :
    level d.ideal T n ⟶ OrderedExchange.level d T n where
  app M := (step_map_exists T (quotient d.ideal T n)
    (OrderedExchange.quotient d T n) (pbcLevelConstantComparison T d n).hom
    (quotient_comm d T n) M (OrderedExchange.levelUnitMap d T n M)
    (OrderedExchange.levelUnitMap_apply d T n M)).choose
  naturality := by
    intro M N a
    apply level_hom_ext T (quotient d.ideal T n) M _
    intro W s x
    change ((step_map_exists T (quotient d.ideal T n)
      (OrderedExchange.quotient d T n) (pbcLevelConstantComparison T d n).hom
      (quotient_comm d T n) N (OrderedExchange.levelUnitMap d T n N)
      (OrderedExchange.levelUnitMap_apply d T n N)).choose).val.app W
      (((level d.ideal T n).map a).val.app W _) =
        ((OrderedExchange.level d T n).map a).val.app W _
    rw [tensorSection_map]
    erw [(step_map_exists T (quotient d.ideal T n)
      (OrderedExchange.quotient d T n) (pbcLevelConstantComparison T d n).hom
      (quotient_comm d T n) N (OrderedExchange.levelUnitMap d T n N)
      (OrderedExchange.levelUnitMap_apply d T n N)).choose_spec]
    erw [(step_map_exists T (quotient d.ideal T n)
      (OrderedExchange.quotient d T n) (pbcLevelConstantComparison T d n).hom
      (quotient_comm d T n) M (OrderedExchange.levelUnitMap d T n M)
      (OrderedExchange.levelUnitMap_apply d T n M)).choose_spec]
    exact (OrderedExchange.tensorSection_map d T n a W _ x).symm

private theorem levelMap_formula (T : Scheme.{u}) (n : ℕ) (M : Modules A T)
    (W : T.ProEtᵒᵖ) (s : (coefficients (A ⧸ d.ideal ^ (n + 1)) T).obj.obj W)
    (x : M.val.obj W) :
    ((levelMap d T n).app M).val.app W
        (reductionTensorSection T (quotient d.ideal T n) M W s x) =
      reductionTensorSection T (OrderedExchange.quotient d T n) M W
        ((pbcLevelConstantComparison T d n).hom.hom.app W s) x :=
  (step_map_exists T (quotient d.ideal T n)
    (OrderedExchange.quotient d T n) (pbcLevelConstantComparison T d n).hom
    (quotient_comm d T n) M (OrderedExchange.levelUnitMap d T n M)
    (OrderedExchange.levelUnitMap_apply d T n M)).choose_spec W s x

attribute [local irreducible] levelMap

private theorem quotient_inv_comm (T : Scheme.{u}) (n : ℕ) :
    OrderedExchange.quotient d T n ≫ (pbcLevelConstantComparison T d n).inv =
      quotient d.ideal T n := by
  rw [← quotient_comm, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private def levelInv (T : Scheme.{u}) (n : ℕ) :
    OrderedExchange.level d T n ⟶ level d.ideal T n where
  app M := (step_map_exists T (OrderedExchange.quotient d T n)
    (quotient d.ideal T n) (pbcLevelConstantComparison T d n).inv
    (quotient_inv_comm d T n) M (levelUnitMap d.ideal T n M)
    (levelUnitMap_apply d.ideal T n M)).choose
  naturality := by
    intro M N a
    apply level_hom_ext T (OrderedExchange.quotient d T n) M _
    intro W s x
    change ((step_map_exists T (OrderedExchange.quotient d T n)
      (quotient d.ideal T n) (pbcLevelConstantComparison T d n).inv
      (quotient_inv_comm d T n) N (levelUnitMap d.ideal T n N)
      (levelUnitMap_apply d.ideal T n N)).choose).val.app W
      (((OrderedExchange.level d T n).map a).val.app W _) =
        ((level d.ideal T n).map a).val.app W _
    rw [OrderedExchange.tensorSection_map]
    erw [(step_map_exists T (OrderedExchange.quotient d T n)
      (quotient d.ideal T n) (pbcLevelConstantComparison T d n).inv
      (quotient_inv_comm d T n) N (levelUnitMap d.ideal T n N)
      (levelUnitMap_apply d.ideal T n N)).choose_spec]
    erw [(step_map_exists T (OrderedExchange.quotient d T n)
      (quotient d.ideal T n) (pbcLevelConstantComparison T d n).inv
      (quotient_inv_comm d T n) M (levelUnitMap d.ideal T n M)
      (levelUnitMap_apply d.ideal T n M)).choose_spec]
    exact (tensorSection_map d.ideal T n a W _ x).symm

private theorem levelInv_formula (T : Scheme.{u}) (n : ℕ) (M : Modules A T)
    (W : T.ProEtᵒᵖ) (s : (d.finiteRing T n).obj.obj W) (x : M.val.obj W) :
    ((levelInv d T n).app M).val.app W
        (reductionTensorSection T (OrderedExchange.quotient d T n) M W s x) =
      reductionTensorSection T (quotient d.ideal T n) M W
        ((pbcLevelConstantComparison T d n).inv.hom.app W s) x :=
  (step_map_exists T (OrderedExchange.quotient d T n)
    (quotient d.ideal T n) (pbcLevelConstantComparison T d n).inv
    (quotient_inv_comm d T n) M (levelUnitMap d.ideal T n M)
    (levelUnitMap_apply d.ideal T n M)).choose_spec W s x

attribute [local irreducible] levelInv

private def levelIso (T : Scheme.{u}) (n : ℕ) :
    level d.ideal T n ≅ OrderedExchange.level d T n where
  hom := levelMap d T n
  inv := levelInv d T n
  hom_inv_id := by
    apply NatTrans.ext
    funext M
    apply level_hom_ext T (quotient d.ideal T n) M _
    intro W s x
    change ((levelInv d T n).app M).val.app W
      (((levelMap d T n).app M).val.app W _) = _
    rw [levelMap_formula, levelInv_formula]
    congr 1
    exact ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.hom.app W) (pbcLevelConstantComparison T d n).hom_inv_id) s
  inv_hom_id := by
    apply NatTrans.ext
    funext M
    apply level_hom_ext T (OrderedExchange.quotient d T n) M _
    intro W s x
    change ((levelMap d T n).app M).val.app W
      (((levelInv d T n).app M).val.app W _) = _
    rw [levelInv_formula, levelMap_formula]
    congr 1
    exact ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.hom.app W) (pbcLevelConstantComparison T d n).inv_hom_id) s

private theorem levelIso_step (T : Scheme.{u}) (n : ℕ) (M : Modules A T) :
    ((step_existsUnique d.ideal T n).exists.choose).app M ≫
        (levelIso d T n).hom.app M =
      (levelIso d T (n + 1)).hom.app M ≫ (OrderedExchange.step d T n).app M := by
  apply level_hom_ext T (quotient d.ideal T (n + 1)) M _
  intro W s x
  change ((levelMap d T n).app M).val.app W
      ((((step_existsUnique d.ideal T n).exists.choose).app M).val.app W _) =
    ((OrderedExchange.step d T n).app M).val.app W
      (((levelMap d T (n + 1)).app M).val.app W _)
  rw [(step_existsUnique d.ideal T n).exists.choose_spec, levelMap_formula,
    levelMap_formula]
  erw [(OrderedExchange.step_existsUnique d T n).exists.choose_spec]
  congr 1
  have h := pbcConstantSystemComparison_naturality T d
    (homOfLE (Nat.le_succ n)).op
  have hs : (adicLisseRingSystem T d.ideal).map (homOfLE (Nat.le_succ n)).op =
      quotientStep d.ideal T n := by
    simp only [adicLisseRingSystem, Functor.ofOpSequence_map_homOfLE_succ]
    rfl
  rw [hs] at h
  have h' := ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app W) h) s
  change _ = _ at h'
  exact h' 

private def ordinaryIso (T : Scheme.{u}) :
    reductionModule d.ideal T ≅ OrderedExchange.reductionModule d T :=
  NatIso.ofComponents
    (fun M ↦ NatIso.ofComponents (fun n ↦ (levelIso d T n.unop).app M)
      (by
        intro n m a
        let t : (reductionModule d.ideal T).obj M ⟶
            (OrderedExchange.reductionModule d T).obj M :=
          NatTrans.ofOpSequence (fun n ↦ (levelIso d T n).hom.app M) (by
            intro n
            simpa only [reductionModule, OrderedExchange.reductionModule,
              Functor.flip_obj_map, Functor.ofOpSequence_map_homOfLE_succ,
              OrderedExchange.step] using levelIso_step d T n M)
        exact t.naturality a))
    (by
      intro M N a
      apply NatTrans.ext
      funext n
      exact (levelIso d T n.unop).hom.naturality a)

private theorem levelPull_square {U V : Scheme.{u}} (f : U ⟶ V) (n : ℕ)
    (M : Modules A V) :
    (modulePullback A f).map ((levelIso d V n).hom.app M) ≫
        (OrderedExchange.levelPullIso d f n).hom.app M =
      ((ordinaryReductionPull d.ideal f).hom.app M).app (Opposite.op n) ≫
        (levelIso d U n).hom.app ((modulePullback A f).obj M) := by
  let a := proEtaleRingModuleAdjunction f (coefficients A V) (coefficients A U)
    (constantRingIso A f)
  apply (a.homEquiv _ _).injective
  apply level_hom_ext V (quotient d.ideal V n) M _
  intro W s x
  have hn := congrArg (fun k ↦ k.val.app W
    (reductionTensorSection V (quotient d.ideal V n) M W s x))
    (a.unit.naturality ((levelIso d V n).hom.app M))
  change ((OrderedExchange.levelPullIso d f n).hom.app M).val.app
      ((proEtaleBaseChange f).op.obj W)
      (((modulePullback A f).map ((levelIso d V n).hom.app M)).val.app
        ((proEtaleBaseChange f).op.obj W) ((a.unit.app _).val.app W _)) = _
  change (a.unit.app _).val.app W (((levelMap d V n).app M).val.app W _) =
    (((modulePullback A f).map ((levelIso d V n).hom.app M)).val.app
      ((proEtaleBaseChange f).op.obj W) ((a.unit.app _).val.app W _)) at hn
  rw [← hn]
  change ((OrderedExchange.levelPullIso d f n).hom.app M).val.app
      ((proEtaleBaseChange f).op.obj W)
      ((a.unit.app _).val.app W (((levelMap d V n).app M).val.app W _)) =
    ((levelMap d U n).app ((modulePullback A f).obj M)).val.app
      ((proEtaleBaseChange f).op.obj W)
      ((((ordinaryReductionPull d.ideal f).hom.app M).app (Opposite.op n)).val.app
        ((proEtaleBaseChange f).op.obj W) ((a.unit.app _).val.app W _))
  rw [levelMap_formula]
  erw [OrderedExchange.levelPullIso_tensor]
  obtain ⟨W⟩ := W
  erw [(ordinaryReductionPull_existsUnique d.ideal f).exists.choose_spec]
  erw [levelMap_formula]
  have hc : (constantRingIso (A ⧸ d.ideal ^ (n + 1)) f).hom ≫
      (pbcLevelConstantComparison U d n).hom =
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
      (pbcLevelConstantComparison V d n).hom ≫ (d.finiteRingIso f n).hom := by
    simp only [AdicCoefficientDatum.finiteRingIso, Iso.trans_hom,
      Functor.mapIso_hom, Iso.symm_hom, asIso_hom]
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id]
    erw [(proEtaleSheafInverseImage f CommRingCat.{u + 1}).map_id]
    rw [Category.id_comp]
    rfl
  have h := restrictionDirectImageMap_square f
    (coefficients (A ⧸ d.ideal ^ (n + 1)) V) (d.finiteRing V n)
    (coefficients (A ⧸ d.ideal ^ (n + 1)) U) (d.finiteRing U n)
    (pbcLevelConstantComparison V d n).hom (pbcLevelConstantComparison U d n).hom
    (constantRingIso (A ⧸ d.ideal ^ (n + 1)) f) (d.finiteRingIso f n) hc
  have ht := ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app (Opposite.op W)) h) s
  rw [constantRingDirectImageMap] at ht
  exact congrArg (fun t : (d.finiteRing U n).obj.obj
      (Opposite.op ((proEtaleBaseChange f).obj W)) ↦
    reductionTensorSection U (OrderedExchange.quotient d U n)
      ((modulePullback A f).obj M) (Opposite.op ((proEtaleBaseChange f).obj W)) t
      ((a.unit.app M).val.app (Opposite.op W) x)) ht

private theorem ordinaryPull_square {U V : Scheme.{u}} (f : U ⟶ V) :
    Functor.whiskerRight (ordinaryIso d V).hom (towerPullback A f) ≫
        (OrderedExchange.ordinaryReductionPullIso d f).hom =
      (ordinaryReductionPull d.ideal f).hom ≫
        Functor.whiskerLeft (modulePullback A f) (ordinaryIso d U).hom := by
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  change (modulePullback A f).map ((levelIso d V n.unop).hom.app M) ≫
      (OrderedExchange.levelPullIso d f n.unop).hom.app M =
    ((ordinaryReductionPull d.ideal f).hom.app M).app n ≫
      (levelIso d U n.unop).hom.app ((modulePullback A f).obj M)
  exact levelPull_square d f n.unop M

attribute [local irreducible] ordinaryIso levelIso
  reduction reductionModel reductionCounit reductionModule
  OrderedExchange.reduction OrderedExchange.reductionData
  OrderedExchange.reductionCounit OrderedExchange.reductionModule

private def comparisonData (T : Scheme.{u}) :
    DerivedIsoData (reductionModule d.ideal T) (OrderedExchange.reductionModule d T)
      (reduction d.ideal T) (OrderedExchange.reduction d T)
      (reductionCounit d.ideal T) (OrderedExchange.reductionCounit d T)
      (ordinaryIso d T) := by
  unfold reduction OrderedExchange.reduction reductionCounit OrderedExchange.reductionCounit
  let P := reductionModel d.ideal T
  let Q := OrderedExchange.reductionData d T
  letI : P.functor.IsLeftDerivedFunctor P.counit
      (HomotopyCategory.quasiIso (Modules A T) (.up ℤ)) := P.universal
  letI : Q.reduction.IsLeftDerivedFunctor Q.counit
      (HomotopyCategory.quasiIso (Modules A T) (.up ℤ)) := Q.isLeftDerived
  exact makeDerivedIsoData (reductionModule d.ideal T) (OrderedExchange.reductionModule d T)
    P.functor Q.reduction P.counit Q.counit (ordinaryIso d T)

attribute [local irreducible] comparisonData
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  OrderedExchange.reductionPullIso reductionPull
  OrderedExchange.ordinaryReductionPullIso ordinaryReductionPull

attribute [local semireducible] OrderedExchange.reduction OrderedExchange.reductionCounit
attribute [local irreducible] OrderedExchange.ReductionPullNormalized
  OrderedExchange.ModelPullNormalized IsReductionPullAt

private theorem ordered_normalization_raw {U V : Scheme.{u}} (f : U ⟶ V) :
    OrderedExchange.ReductionPullNormalized d f (OrderedExchange.reductionPullIso d f) := by
  unfold OrderedExchange.reductionPullIso
  exact (OrderedExchange.reductionPullIso_existsUnique d f).choose_spec.1

set_option backward.isDefEq.respectTransparency.types true in
private theorem derivedPull_square {U V : Scheme.{u}} (f : U ⟶ V) :
    Functor.whiskerRight ((comparisonData d V).iso).hom (G A f) ≫
        (OrderedExchange.reductionPullIso d f).hom =
      (reductionPull d.ideal f).hom ≫
        Functor.whiskerLeft (pull A f) ((comparisonData d U).iso).hom := by
  have hn := ordered_normalization_raw d f
  unfold OrderedExchange.ReductionPullNormalized at hn
  exact normalized_model_comparison
    (reductionModule d.ideal V) (OrderedExchange.reductionModule d V)
    (reductionModule d.ideal U) (OrderedExchange.reductionModule d U)
    (modulePullback A f) (towerPullback A f)
    (reduction d.ideal V) (reduction d.ideal U)
    (reductionCounit d.ideal V) (reductionCounit d.ideal U)
    (OrderedExchange.reductionData d V) (OrderedExchange.reductionData d U)
    (OrderedExchange.ordinaryReductionPullIso d f) (ordinaryReductionPull d.ideal f)
    (OrderedExchange.reductionPullIso d f) (reductionPull d.ideal f)
    (ordinaryIso d V) (ordinaryIso d U) (comparisonData d V) (comparisonData d U)
    (ordinaryPull_square d f)
    (fun E ↦ by
      obtain ⟨K, a, hK, ha, hp⟩ := pullback_adapted_resolution A f E
      exact ⟨K, a, ⟨hK, hp⟩, ha⟩)
    hn (reductionPull_normalization d.ideal f)


private theorem projection_square {U V : Scheme.{u}} (f : U ⟶ V)
    (K : DerivedCategory (Modules A U)) :
    ((comparisonData d V).iso).hom.app ((push A f).obj K) ≫ OrderedExchange.projection d f K =
      (projection d.ideal f).app K ≫ (R A f).map (((comparisonData d U).iso).hom.app K) := by
  let a := proEtaleRingDerivedAdjunction f (coefficients A V) (coefficients A U)
    (constantRingIso A f)
  have hp : (mateEquiv a (adj A f)
      (TwoSquare.mk _ _ _ _ (OrderedExchange.reductionPullIso d f).hom)).app K =
        OrderedExchange.projection d f K := by
    unfold OrderedExchange.projection
    exact ((adj A f).homEquiv _ _).symm_apply_eq.mp
      (mateEquiv_counit a (adj A f)
        (TwoSquare.mk _ _ _ _ (OrderedExchange.reductionPullIso d f).hom) K)
  rw [← hp]
  exact mates_naturality
    (proEtaleRingDerivedAdjunction f (coefficients A V) (coefficients A U)
      (constantRingIso A f)) (adj A f) ((comparisonData d V).iso).hom ((comparisonData d U).iso).hom
    (reductionPull d.ideal f).hom (OrderedExchange.reductionPullIso d f).hom
    (fun M ↦ congr_app (derivedPull_square d f) M) K

private theorem strictProjection_isIso {U V : Scheme.{u}} (f : U ⟶ V)
    (K : DerivedCategory (Modules A U)) : IsIso ((projection d.ideal f).app K) := by
  have := OrderedExchange.projection_isIso d f K
  have hc : IsIso ((projection d.ideal f).app K ≫
      (R A f).map (((comparisonData d U).iso).hom.app K)) := by
    rw [← projection_square d f K]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hc

end Presentation

private theorem finiteProjection_evaluation {U V : Scheme.{u}} (f : U ⟶ V) (n : ℕ)
    (K : DerivedCategory (Modules A U)) :
    (ev A V n).map ((projection I f).app K) ≫
        (evalR A f n).app ((reduction I U).obj K) = (finiteProjection I f n).app K := by
  let a := proEtaleRingDerivedAdjunction f (coefficients A V) (coefficients A U)
    (constantRingIso A f)
  let α := TwoSquare.mk _ _ _ _ (reductionPull I f).hom
  let β := TwoSquare.mk _ _ _ _ (evalG A f n).inv
  have h := congrArg (fun z ↦ z.natTrans.app K) (mateEquiv_vcomp a (adj A f) a α β)
  have hab : α.hComp β = TwoSquare.mk _ _ _ _ (finiteTensorPull I f n).hom := by
    rfl
  have hp : (mateEquiv a (adj A f) α).app K = (projection I f).app K := rfl
  have he : mateEquiv (adj A f) a β = evalR A f n := rfl
  rw [hab] at h
  simp only [TwoSquare.vComp, TwoSquare.natTrans, TwoSquare.mk,
    NatTrans.comp_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp,
    Category.comp_id] at h
  change (finiteProjection I f n).app K =
    (ev A V n).map ((mateEquiv a (adj A f) α).app K) ≫
      (mateEquiv (adj A f) a β).app ((reduction I U).obj K) at h
  rw [hp, he] at h
  exact h.symm

attribute [local irreducible] reduction reductionModel reductionCounit
  projection deltaLimit augmentation limitPush chi

/-- Strict direct-image reduction, naturality and completion-unit normalization.
Source: Stacks 099N (3), (4), 0A07, 0B56 and 0944; agent refinement of
fix-lem-exchanges Step 5
(blueprint: lem-sf-cbc-direct-image-reduction-unit).

Proof:
1. Naturality of the diagram-site projection mate and the constant comparison chi
makes h natural. Clause (4) of constantTowerDirectImageNormalization gives the
strict augmentation square h i = Q(i) chi for arbitrary F.
2. Naturality of limitPush on i, clause (3) of the same normalization theorem,
and the definition of unit give L(h) eta = b P(eta). Composing with b inverse
gives comparison eta = P(eta), before any evaluation of tower morphisms.
3. Naturality of h and b gives naturality of comparison, with the stated formula.
4. Compare the canonical constant-sheaf quotient tensor towers with the existing
original-site reduction towers. The constant-to-function coefficient isomorphisms
commute with quotient transitions. Their pure tensor maps commute with ordinary
pullback; the universal derived counits therefore give compatible derived
isomorphisms. Naturality of adjunction mates identifies the two projection maps.
The existing strict projection theorem makes this map invertible, using the
perfectness of each finite quotient independently.
5. Pasting the reduction/pullback square with the evaluation/pullback square
identifies each evaluated projection with the specified finiteProjection. Hence
these finite projection maps are invertible. Specialize Step 2 to K for the final
unit equation. No uniform bound on finite-projective representatives is used. -/
theorem directImageReductionUnit (d : CompleteCoefficientDatum A)
    (_hfinite : ∀ n : ℕ, Finite (A ⧸ d.ideal ^ (n + 1)))
    {U V : Scheme.{u}} (f : U ⟶ V) :
    (∀ F : DerivedCategory (Modules A U),
      (unit d.ideal V).app ((push A f).obj F) ≫ (comparison d.ideal f).app F =
        (push A f).map ((unit d.ideal U).app F)) ∧
    (∀ (F F' : DerivedCategory (Modules A U)) (t : F ⟶ F'),
      (completion d.ideal V).map ((push A f).map t) ≫ (comparison d.ideal f).app F' =
        (comparison d.ideal f).app F ≫ (push A f).map ((completion d.ideal U).map t)) ∧
    (∀ (F F' : DerivedCategory (Modules A U)) (t : F ⟶ F'),
      (reduction d.ideal V).map ((push A f).map t) ≫ (projection d.ideal f).app F' =
        (projection d.ideal f).app F ≫ (R A f).map ((reduction d.ideal U).map t)) ∧
    (∀ K : DerivedCategory (Modules A U), IsIso ((unit d.ideal U).app K) →
      IsIso ((projection d.ideal f).app K) ∧
      (∀ n : ℕ,
        (ev A V n).map ((projection d.ideal f).app K) ≫
            (evalR A f n).app ((reduction d.ideal U).obj K) =
          (finiteProjection d.ideal f n).app K) ∧
      (∀ n : ℕ, IsIso ((finiteProjection d.ideal f n).app K)) ∧
      (unit d.ideal V).app ((push A f).obj K) ≫
          (L A V).map ((projection d.ideal f).app K) =
        (push A f).map ((unit d.ideal U).app K) ≫
          (limitPush A f).hom.app ((reduction d.ideal U).obj K)) := by
  obtain ⟨_, _, hnorm, haug⟩ := constantTowerDirectImageNormalization d f
  have hn (F : DerivedCategory (Modules A U)) :
      (push A f).map ((deltaLimit A U).inv.app F) ≫
          (limitPush A f).hom.app ((delta A U).obj F) =
        (deltaLimit A V).inv.app ((push A f).obj F) ≫
          (L A V).map ((chi A f).hom.app F) := by
    have h := hnorm F
    apply (cancel_mono ((L A V).map ((chi A f).inv.app F) ≫
      (deltaLimit A V).hom.app ((push A f).obj F))).mp
    calc
      _ = 𝟙 _ := by simpa only [Category.assoc] using h
      _ = _ := by
        simp only [Category.assoc]
        rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
        erw [(L A V).map_id]
        simp only [Category.id_comp, Iso.inv_hom_id_app]
        rfl
  obtain ⟨hu, _⟩ := normalized_augmentation_transport
    (delta A U) (reduction d.ideal U) (delta A V) (reduction d.ideal V)
    (L A U) (L A V) (augmentation d.ideal U) (augmentation d.ideal V)
    (deltaLimit A U) (deltaLimit A V) (push A f) (R A f)
    (chi A f) (limitPush A f) (projection d.ideal f) haug hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F
    change ((deltaLimit A V).inv.app ((push A f).obj F) ≫
        (L A V).map ((augmentation d.ideal V).app ((push A f).obj F))) ≫
      (𝟙 _ ≫ (L A V).map ((projection d.ideal f).app F) ≫
        𝟙 _ ≫ (limitPush A f).inv.app ((reduction d.ideal U).obj F) ≫ 𝟙 _) = _
    simp only [Category.id_comp, Category.comp_id]
    exact (hu F).2
  · intro F F' t
    exact (comparison d.ideal f).naturality t
  · intro F F' t
    exact (projection d.ideal f).naturality t
  · intro K hK
    let e : AdicCoefficientDatum A :=
      { toCompleteCoefficientDatum := d, quotientFinite := _hfinite }
    have hp : IsIso ((projection d.ideal f).app K) :=
      Presentation.strictProjection_isIso e f K
    have hf (n : ℕ) : IsIso ((finiteProjection d.ideal f n).app K) := by
      rw [← finiteProjection_evaluation]
      have : IsIso (evalR A f n) := evalR_isIso A f n
      infer_instance
    refine ⟨hp, ?_, hf, ?_⟩
    · intro n
      exact finiteProjection_evaluation d.ideal f n K
    · exact (hu K).1

end AlgebraicGeometry.ProEtale.StrictTower.DirectImageReduction
