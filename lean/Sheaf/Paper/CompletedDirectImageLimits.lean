/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.Paper.CompletedPullback
public import Sheaf.Paper.FourArrows
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Paper.StratumCompletionUnitRestriction
import all Sheaf.Paper.AdicCoefficientDatum
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all Sheaf.Paper.ConstantTowerDirectImageNormalization
import all Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization
import all Sheaf.CategoryTheory.DirectImageRoosNormalization
import all Sheaf.Paper.CompletedRlimFunctor

/-!
# The canonical direct-image/derived-limit comparison

Source: blueprint proper base change, direct image and limits; Stacks Tag 099N
and Cohomology on Sites, lemma-Rf-commutes-with-Rlim
(blueprint: prop-weil-pbc-direct-image-limits).

## Main statements

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.directImageRlimIso`:
  the recorded construction or statement of this node.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Dependent scalar-extension proofs should not be replayed by tactic linting.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] completedAdicChangeData completedReductionCoefficient
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
attribute [local irreducible] CochainComplex.IsKFlatIndependentCoefficients
attribute [local instance 2000] reductionModulesHasDerivedCategory
  reductionTowerHasDerivedCategory
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U V : Scheme.{t}} (f : U ⟶ V)

/-- The ordinary direct image on strict towers applies the actual module functor levelwise.
Source: blueprint direct image and limits (blueprint: prop-weil-pbc-direct-image-limits). -/
abbrev AdicCoefficientDatum.towerModulePush : d.towers U ⥤ d.towers V :=
  (Functor.whiskeringRight _ _ _).obj
    (proEtaleRingModuleDirectImage f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f))

/-- Direct image of strict towers is additive termwise.
Source: blueprint direct image and limits (blueprint: prop-weil-pbc-direct-image-limits). -/
instance AdicCoefficientDatum.towerModulePush_additive :
    (d.towerModulePush f).Additive := inferInstance

/-- The canonical termwise module adjunction on strict towers.
Source: blueprint direct image and limits (blueprint: prop-weil-pbc-direct-image-limits). -/
def AdicCoefficientDatum.towerModuleAdjunction :
    d.towerModulePull f ⊣ d.towerModulePush f :=
  (proEtaleRingModuleAdjunction f (d.completedRing V) (d.completedRing U)
    (d.integralRingIso f)).whiskerRight ℕᵒᵖ

/-- The total right derived direct image in the abelian category of strict towers.
Source: blueprint direct image and limits (blueprint: prop-weil-pbc-direct-image-limits). -/
abbrev AdicCoefficientDatum.towerPush := (d.towerModulePush f).rightDerivedFunctor

/-- The derived tower adjunction comes from its canonical ordinary adjunction.
Source: blueprint direct image and limits (blueprint: prop-weil-pbc-direct-image-limits). -/
def AdicCoefficientDatum.towerAdjunction : d.towerPull f ⊣ d.towerPush f :=
  (d.towerModuleAdjunction f).mapDerivedCategoryRightDerivedAdjunction

private theorem evaluationMapKInjective
    (B : Type*) [Category B] [Abelian B]
    (J : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) [J.IsKInjective] (n : ℕᵒᵖ) :
    CochainComplex.IsKInjective
      ((((CategoryTheory.evaluation ℕᵒᵖ B).obj n).mapHomologicalComplex (.up ℤ)).obj J) :=
  tower_evaluation_isKInjective B J n

private theorem evaluationPreservesKInjective (B : Type*) [Category B] [Abelian B]
    (n : ℕᵒᵖ) : ((CategoryTheory.evaluation ℕᵒᵖ B).obj n).PreservesKInjectiveComplexes :=
  ⟨fun J _ ↦ evaluationMapKInjective B J n⟩


/-- Evaluation of strict towers preserves K-injective complexes: its left adjoint
is the exact sum of copies indexed by arrows into the chosen level.
Source: blueprint direct image and limits, evaluation clause; Stacks 079P
(blueprint: prop-weil-pbc-direct-image-limits).
Proof: the left adjoint is left Kan extension from the one-object subcategory.
Its values are sums of copies indexed by arrows into the evaluation index. These
sums are exact in the Grothendieck module category. Adjunction transports maps from
acyclic complexes to null-homotopic maps into the given K-injective tower. -/
@[instance]
theorem completedTowerEvaluation_kinjective (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) (n : ℕ)
    (J : CochainComplex (reductionTowerCategory T (reductionModuleRing T R)) ℤ)
    [J.IsKInjective] :
    CochainComplex.IsKInjective
      (((reductionTowerEvaluation T (reductionModuleRing T R) n).mapHomologicalComplex
        (.up ℤ)).obj J) := by
  exact evaluationMapKInjective _ J (Opposite.op n)

set_option linter.defProp false in
/-- The exact K-injective normalization of tower direct-image evaluation.
Source: blueprint direct image and limits, evaluation clause; Stacks 099N
(blueprint: prop-weil-pbc-direct-image-limits). -/
def AdicCoefficientDatum.IsTowerPushEvaluation (n : ℕ)
    (α : d.towerPush f ⋙
        reductionTowerDerivedEvaluation V (reductionModuleRing V (d.completedRing V)) n ≅
        reductionTowerDerivedEvaluation U (reductionModuleRing U (d.completedRing U)) n ⋙
          d.push f) : Prop :=
  ∀ (J : CochainComplex (d.towers U) ℤ) [J.IsKInjective],
        (reductionTowerDerivedEvaluation V
            (reductionModuleRing V (d.completedRing V)) n).map
            ((d.towerModulePush f).rightDerivedFunctorObjQIso J).hom ≫
          (reductionTowerEvaluation V
            (reductionModuleRing V (d.completedRing V)) n).mapDerivedCategoryFactors.hom.app
              (((d.towerModulePush f).mapHomologicalComplex (.up ℤ)).obj J) =
        α.hom.app (DerivedCategory.Q.obj J) ≫
          (d.push f).map ((reductionTowerEvaluation U
            (reductionModuleRing U (d.completedRing U)) n).mapDerivedCategoryFactors.hom.app J) ≫
          ((proEtaleRingModuleDirectImage f (d.completedRing V) (d.completedRing U)
            (d.integralRingIso f)).rightDerivedFunctorObjQIso
              (((reductionTowerEvaluation U
                (reductionModuleRing U (d.completedRing U)) n).mapHomologicalComplex
                  (.up ℤ)).obj J)).hom

private theorem quotientHomId {B : Type*} [Category B] [Abelian B]
    [HasDerivedCategory B] (J : CochainComplex B ℤ) :
    (DerivedCategory.quotientCompQhIso B).hom.app J = 𝟙 (DerivedCategory.Q.obj J) := rfl

private theorem quotientInvId {B : Type*} [Category B] [Abelian B]
    [HasDerivedCategory B] (J : CochainComplex B ℤ) :
    (DerivedCategory.quotientCompQhIso B).inv.app J = 𝟙 (DerivedCategory.Q.obj J) := rfl

private theorem homotopyFactorsInvId {B C : Type*} [Category B] [Category C]
    [Abelian B] [Abelian C] (F : B ⥤ C) [F.Additive] (J : CochainComplex B ℤ) :
    (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app J = 𝟙 _ := rfl


section NormalizedTowerEvaluation
attribute [local instance] evaluationPreservesKInjective

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizedTowerEvaluation
    (B C : Type*) [Category B] [Category C] [Abelian B] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasDerivedCategory (ℕᵒᵖ ⥤ C)]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
    (G : B ⥤ C) [G.Additive] (n : ℕᵒᵖ) :
    let F := (Functor.whiskeringRight ℕᵒᵖ B C).obj G
    let EU := (CategoryTheory.evaluation ℕᵒᵖ B).obj n
    let EV := (CategoryTheory.evaluation ℕᵒᵖ C).obj n
    ∃! e : F.rightDerivedFunctor ⋙ EV.mapDerivedCategory ≅
        EU.mapDerivedCategory ⋙ G.rightDerivedFunctor,
      ∀ (J : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) [J.IsKInjective],
        EV.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso J).hom ≫
          EV.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) =
        e.hom.app (DerivedCategory.Q.obj J) ≫
          G.rightDerivedFunctor.map (EU.mapDerivedCategoryFactors.hom.app J) ≫
            (G.rightDerivedFunctorObjQIso ((EU.mapHomologicalComplex (.up ℤ)).obj J)).hom := by
  let F := (Functor.whiskeringRight ℕᵒᵖ B C).obj G
  let EU := (CategoryTheory.evaluation ℕᵒᵖ B).obj n
  let EV := (CategoryTheory.evaluation ℕᵒᵖ C).obj n
  have : EU.PreservesKInjectiveComplexes := ⟨fun J _ ↦
    tower_evaluation_isKInjective B J n⟩
  let α := Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F EV
  let β := Functor.mapDerivedCategoryCompRightDerivedFunctorUnit EU G
  let e := Functor.rightDerivedUnique (F.rightDerivedFunctor ⋙ EV.mapDerivedCategory)
    (EU.mapDerivedCategory ⋙ G.rightDerivedFunctor) α β
    (HomotopyCategory.quasiIso ((ℕᵒᵖ ⥤ B)) (.up ℤ))
  have he : ∀ (J : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) [J.IsKInjective],
      EV.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso J).hom ≫
        EV.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) =
      e.hom.app (DerivedCategory.Q.obj J) ≫
        G.rightDerivedFunctor.map (EU.mapDerivedCategoryFactors.hom.app J) ≫
          (G.rightDerivedFunctorObjQIso ((EU.mapHomologicalComplex (.up ℤ)).obj J)).hom := by
    intro J hJ
    have hh : α ≫ Functor.whiskerLeft DerivedCategory.Qh e.hom = β := by
      simp [e]
    have h := NatTrans.congr_app hh ((HomotopyCategory.quotient _ _).obj J)
    dsimp only [α, β, Functor.rightDerivedFunctorCompMapDerivedCategoryUnit,
      Functor.mapDerivedCategoryCompRightDerivedFunctorUnit, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.comp_map] at h
    simp only [Category.id_comp, Category.comp_id, Category.assoc] at h
    have hEV : EV.mapDerivedCategoryFactorsh.app
        ((HomotopyCategory.quotient _ _).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj J)) =
        EV.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (.up ℤ)).obj J) := by
      apply Iso.ext
      have hv := EV.mapDerivedCategoryFactorsh_hom_app
        ((F.mapHomologicalComplex (.up ℤ)).obj J)
      rw [quotientHomId, quotientInvId, homotopyFactorsInvId] at hv
      erw [EV.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id,
        Category.id_comp, Category.comp_id] at hv
      erw [Category.comp_id] at hv
      exact hv
    have hEU : EU.mapDerivedCategoryFactorsh.app
        ((HomotopyCategory.quotient _ _).obj J) = EU.mapDerivedCategoryFactors.app J := by
      apply Iso.ext
      have hu := EU.mapDerivedCategoryFactorsh_hom_app J
      rw [quotientHomId, quotientInvId, homotopyFactorsInvId] at hu
      erw [EU.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id,
        Category.id_comp, Category.comp_id] at hu
      erw [Category.comp_id] at hu
      exact hu
    have hidF : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ EV)) (.up ℤ)).inv.app
        ((HomotopyCategory.quotient _ _).obj J) = 𝟙 _ := rfl
    have hidG : (Functor.mapHomotopyCategoryCompIso (Iso.refl (EU ⋙ G)) (.up ℤ)).inv.app
        ((HomotopyCategory.quotient _ _).obj J) = 𝟙 _ := rfl
    rw [hidF, hidG] at h
    erw [DerivedCategory.Qh.map_id, Category.id_comp, Category.id_comp] at h
    change EV.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient _ _).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj J)) ≫
        EV.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ _).obj J)) ≫ e.hom.app (DerivedCategory.Q.obj J) =
      G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
        ((EU.mapHomologicalComplex (.up ℤ)).obj J)) ≫
        G.rightDerivedFunctor.map (EU.mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient _ _).obj J)) at h
    change (EV.mapDerivedCategoryFactorsh.app _).inv ≫ _ =
      _ ≫ G.rightDerivedFunctor.map (EU.mapDerivedCategoryFactorsh.app _).inv at h
    erw [hEV, hEU] at h
    let qα := (EV.mapDerivedCategoryFactors.app
        ((F.mapHomologicalComplex (.up ℤ)).obj J)).symm ≪≫
      EV.mapDerivedCategory.mapIso (asIso (F.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj J)))
    let qβ := asIso (G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
        ((EU.mapHomologicalComplex (.up ℤ)).obj J))) ≪≫
      G.rightDerivedFunctor.mapIso (EU.mapDerivedCategoryFactors.app J).symm
    have hh' : qα.hom ≫ e.hom.app (DerivedCategory.Q.obj J) = qβ.hom := by
      simpa only [qα, qβ, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
        asIso_hom, Category.assoc] using h
    have hh'' := congrArg (fun k ↦ qα.inv ≫ k ≫ qβ.inv) hh'
    have hfinal : qα.inv = e.hom.app (DerivedCategory.Q.obj J) ≫ qβ.inv := by
      simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
        Category.comp_id] using hh''.symm
    change EV.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso J).hom ≫
        EV.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) =
      e.hom.app (DerivedCategory.Q.obj J) ≫
        G.rightDerivedFunctor.map (EU.mapDerivedCategoryFactors.hom.app J) ≫
          (G.rightDerivedFunctorObjQIso
            ((EU.mapHomologicalComplex (.up ℤ)).obj J)).hom
    dsimp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, asIso_inv]
    simp only [quotientHomId, quotientInvId, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_comp, Category.id_comp]
    erw [EV.mapDerivedCategory.map_id, Category.comp_id]
    erw [Category.comp_id]
    simpa only [qα, qβ, Iso.trans_inv, Iso.symm_inv, Iso.app_hom,
      Iso.app_inv, Functor.mapIso_inv, asIso_inv, Category.assoc] using hfinal
  refine ⟨e, he, ?_⟩
  intro a ha
  apply Iso.ext
  apply NatTrans.ext
  funext M
  obtain ⟨J, hJ, ⟨i⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
  have := hJ
  have h := (ha J).symm.trans (he J)
  have hi : a.hom.app (DerivedCategory.Q.obj J) =
      e.hom.app (DerivedCategory.Q.obj J) := by
    exact (cancel_mono _).1 h
  apply (cancel_epi ((F.rightDerivedFunctor ⋙ EV.mapDerivedCategory).map i.inv)).1
  rw [a.hom.naturality, e.hom.naturality, hi]


end NormalizedTowerEvaluation

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The levelwise direct image comparison is fixed on K-injective towers by the
identity of the two termwise evaluations. It is a natural isomorphism.
Source: blueprint direct image and limits, first clause; Stacks 099N
(blueprint: prop-weil-pbc-direct-image-limits).
Proof: evaluation preserves K-injectives by its exact left adjoint. Thus each side
is computed by evaluating the same termwise direct image of a K-injective tower.
The two factorization maps and universal derived units give the displayed equation.
It descends through localization; every tower has such a resolution, so the equation
uniquely specifies the natural comparison. -/
theorem AdicCoefficientDatum.towerPushEvaluation_existsUnique (n : ℕ) :
    ∃! α : d.towerPush f ⋙
        reductionTowerDerivedEvaluation V (reductionModuleRing V (d.completedRing V)) n ≅
        reductionTowerDerivedEvaluation U (reductionModuleRing U (d.completedRing U)) n ⋙
          d.push f,
      d.IsTowerPushEvaluation f n α := by
  exact normalizedTowerEvaluation
    (ringedSiteModules.{t + 1} (reductionModuleRing U (d.completedRing U)))
    (ringedSiteModules.{t + 1} (reductionModuleRing V (d.completedRing V)))
    (proEtaleRingModuleDirectImage f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f)) (Opposite.op n)

/-- The canonical tower direct-image evaluation comparison, retaining its model equation.
Source: blueprint direct image and limits (blueprint: prop-weil-pbc-direct-image-limits). -/
def AdicCoefficientDatum.towerPushEvaluation (n : ℕ) :
    d.towerPush f ⋙
        reductionTowerDerivedEvaluation V (reductionModuleRing V (d.completedRing V)) n ≅
      reductionTowerDerivedEvaluation U (reductionModuleRing U (d.completedRing U)) n ⋙
        d.push f :=
  (d.towerPushEvaluation_existsUnique f n).choose

/-- The canonical comparison is the conjugate of the identity constant/pullback square.
It is therefore the comparison of the two composite right adjoints, including their units.
No arbitrary isomorphism of the resulting objects is chosen.
Source: blueprint direct image and limits; lemma-Rf-commutes-with-Rlim
(blueprint: prop-weil-pbc-direct-image-limits). -/
def AdicCoefficientDatum.directImageRlimIso :
    completedRlim U (d.completedRing U) ⋙ d.push f ≅
      d.towerPush f ⋙ completedRlim V (d.completedRing V) :=
  conjugateIsoEquiv
    ((proEtaleRingDerivedAdjunction f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f)).comp (d.constantRlimAdjunction U))
    ((d.constantRlimAdjunction V).comp (d.towerAdjunction f))
    (d.derivedConstantPullbackIso f)

/-- The product comparison is the product of the actual direct-image projections,
followed by the normalized evaluation comparisons.
Source: blueprint direct image and limits, derived-product clause
(blueprint: prop-weil-pbc-direct-image-limits). -/
def AdicCoefficientDatum.directImageProductComparison
    (M : DerivedCategory (d.towers U))
    [HasProduct (completedTowerDerivedSequence U d M)]
    [HasProduct (completedTowerDerivedSequence V d ((d.towerPush f).obj M))] :
    (d.push f).obj (∏ᶜ (completedTowerDerivedSequence U d M)) ⟶
      ∏ᶜ (completedTowerDerivedSequence V d ((d.towerPush f).obj M)) :=
  Pi.lift (fun n ↦ (d.push f).map
    (Pi.π (completedTowerDerivedSequence U d M) n) ≫
      (d.towerPushEvaluation f n).inv.app M)

set_option backward.isDefEq.respectTransparency false in
private theorem mappedProductComparison_isIso
    {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    [PreservesLimitsOfShape (Discrete ℕ) G]
    (X : ℕ → C) (Y : ℕ → D) [HasProduct X] [HasProduct Y]
    (e : ∀ n, G.obj (X n) ≅ Y n) :
    IsIso (Pi.lift (fun n ↦ G.map (Pi.π X n) ≫ (e n).hom)) := by
  let : HasProduct (fun n ↦ G.obj (X n)) :=
    hasProduct_of_equiv_of_iso Y (fun n ↦ G.obj (X n)) (Equiv.refl ℕ) e
  let i : (∏ᶜ fun n ↦ G.obj (X n)) ≅ ∏ᶜ Y :=
    { hom := Pi.lift (fun n ↦ Pi.π (fun n ↦ G.obj (X n)) n ≫ (e n).hom)
      inv := Pi.lift (fun n ↦ Pi.π Y n ≫ (e n).inv)
      hom_inv_id := by
        apply Pi.hom_ext
        intro n
        simp only [Category.assoc, Pi.lift_π, Pi.lift_π_assoc,
          Iso.hom_inv_id, Category.comp_id, Category.id_comp]
      inv_hom_id := by
        apply Pi.hom_ext
        intro n
        simp only [Category.assoc, Pi.lift_π, Pi.lift_π_assoc,
          Iso.inv_hom_id, Category.comp_id, Category.id_comp] }
  have h : Pi.lift (fun n ↦ G.map (Pi.π X n) ≫ (e n).hom) =
      piComparison G X ≫ i.hom := by
    apply Pi.hom_ext
    intro n
    simp only [i, Category.assoc, Pi.lift_π, piComparison_comp_π_assoc]
  rw [h]
  have : IsIso (piComparison G X) := inferInstance
  have : IsIso i.hom := i.isIso_hom
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem directImageProductComparison_isIso
    (M : DerivedCategory (d.towers U))
    [HasProduct (completedTowerDerivedSequence U d M)]
    [HasProduct (completedTowerDerivedSequence V d ((d.towerPush f).obj M))] :
    IsIso (d.directImageProductComparison f M) := by
  let := (proEtaleRingDerivedAdjunction f (d.completedRing V) (d.completedRing U)
    (d.integralRingIso f)).isRightAdjoint
  exact mappedProductComparison_isIso (d.push f)
    (completedTowerDerivedSequence U d M)
    (completedTowerDerivedSequence V d ((d.towerPush f).obj M))
    (fun n ↦ ((d.towerPushEvaluation f n).app M).symm)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] CategoryTheory.towerNormalization_preservesFiniteLimits
  CategoryTheory.towerNormalization_preservesFiniteColimits

private theorem evaluationSquare_inverse
    {B C : Type*} [Category B] [Category C] [Abelian B] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasDerivedCategory (ℕᵒᵖ ⥤ C)]
    (P : C ⥤ B) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (n : ℕᵒᵖ) :
    ((Functor.mapDerivedCategoryCompIso ((CategoryTheory.evaluation ℕᵒᵖ C).obj n) P).symm ≪≫
      Functor.mapDerivedCategoryNatIso (Iso.refl _) ≪≫
      Functor.mapDerivedCategoryCompIso ((Functor.whiskeringRight ℕᵒᵖ C B).obj P)
        ((CategoryTheory.evaluation ℕᵒᵖ B).obj n)).hom =
    ((Functor.mapDerivedCategoryCompIso ((Functor.whiskeringRight ℕᵒᵖ C B).obj P)
      ((CategoryTheory.evaluation ℕᵒᵖ B).obj n)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (Iso.refl _) ≪≫
      Functor.mapDerivedCategoryCompIso ((CategoryTheory.evaluation ℕᵒᵖ C).obj n) P).inv := by
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    ← Functor.mapDerivedCategoryNatIso_symm, Iso.refl_symm,
    Functor.mapDerivedCategoryNatIso_refl, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryEvaluation_mate
    {B C : Type*} [Category B] [Category C]
    {L : C ⥤ B} {R : B ⥤ C} (adj : L ⊣ R) (n : ℕᵒᵖ) :
    (mateEquiv (adj.whiskerRight ℕᵒᵖ) adj
      (TwoSquare.mk ((CategoryTheory.evaluation ℕᵒᵖ C).obj n)
        ((Functor.whiskeringRight ℕᵒᵖ C B).obj L) L
        ((CategoryTheory.evaluation ℕᵒᵖ B).obj n) (𝟙 _))).natTrans =
      𝟙 (((Functor.whiskeringRight ℕᵒᵖ B C).obj R) ⋙ (CategoryTheory.evaluation ℕᵒᵖ C).obj n) := by
  ext M
  simp only [mateEquiv_apply, TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app, NatTrans.id_app,
    Functor.comp_obj, Functor.comp_map, Category.id_comp]
  erw [R.map_id, Category.id_comp, Category.comp_id]
  change adj.unit.app (R.obj (M.obj n)) ≫
    R.map (((adj.whiskerRight ℕᵒᵖ).counit.app M).app n) = 𝟙 _
  rw [Adjunction.whiskerRight_counit_app_app]
  exact adj.right_triangle_components _

attribute [local instance] evaluationPreservesKInjective

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem evaluationComparison_mate
    {B C : Type*} [Category B] [Category C] [Abelian B] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasDerivedCategory (ℕᵒᵖ ⥤ C)]
    [Abelian.HasKInjectiveResolutions B]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
    (P : C ⥤ B) (G : B ⥤ C) [P.Additive] [G.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (adj : P ⊣ G) (n : ℕᵒᵖ)
    (β : ((Functor.whiskeringRight ℕᵒᵖ B C).obj G).rightDerivedFunctor ⋙
        ((CategoryTheory.evaluation ℕᵒᵖ C).obj n).mapDerivedCategory ≅
      ((CategoryTheory.evaluation ℕᵒᵖ B).obj n).mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (hβ : ∀ (J : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) [J.IsKInjective],
      ((CategoryTheory.evaluation ℕᵒᵖ C).obj n).mapDerivedCategory.map
          (((Functor.whiskeringRight ℕᵒᵖ B C).obj G).rightDerivedFunctorObjQIso J).hom ≫
        ((CategoryTheory.evaluation ℕᵒᵖ C).obj n).mapDerivedCategoryFactors.hom.app
          ((((Functor.whiskeringRight ℕᵒᵖ B C).obj G).mapHomologicalComplex (.up ℤ)).obj J) =
      β.hom.app (DerivedCategory.Q.obj J) ≫ G.rightDerivedFunctor.map
        (((CategoryTheory.evaluation ℕᵒᵖ B).obj n).mapDerivedCategoryFactors.hom.app J) ≫
      (G.rightDerivedFunctorObjQIso
        ((((CategoryTheory.evaluation ℕᵒᵖ B).obj n).mapHomologicalComplex (.up ℤ)).obj J)).hom) :
    β.hom = (mateEquiv (adj.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction
      adj.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _
        ((Functor.mapDerivedCategoryCompIso ((Functor.whiskeringRight ℕᵒᵖ C B).obj P)
          ((CategoryTheory.evaluation ℕᵒᵖ B).obj n)).symm ≪≫
          Functor.mapDerivedCategoryNatIso (Iso.refl _) ≪≫
          Functor.mapDerivedCategoryCompIso ((CategoryTheory.evaluation ℕᵒᵖ C).obj n) P).inv
        )).natTrans := by
  let F := (Functor.whiskeringRight ℕᵒᵖ B C).obj G
  let EU := (CategoryTheory.evaluation ℕᵒᵖ B).obj n
  let EV := (CategoryTheory.evaluation ℕᵒᵖ C).obj n
  let H := (Functor.whiskeringRight ℕᵒᵖ C B).obj P
  have : EU.PreservesKInjectiveComplexes := evaluationPreservesKInjective B n
  let e : F ⋙ EV ≅ EU ⋙ G := Iso.refl _
  let q : EV ⋙ P ≅ H ⋙ EU := Iso.refl _
  let c := (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F EV).symm ≪≫
    Functor.rightDerivedFunctorNatIso e ≪≫ Functor.rightDerivedFunctorCompIso EU G ≪≫
      Functor.isoWhiskerRight EU.rightDerivedFunctorIsoMapDerivedCategory G.rightDerivedFunctor
  have hc : ∀ (J : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) [J.IsKInjective],
      EV.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso J).hom ≫
        EV.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) =
      c.hom.app (DerivedCategory.Q.obj J) ≫
        G.rightDerivedFunctor.map (EU.mapDerivedCategoryFactors.hom.app J) ≫
          (G.rightDerivedFunctorObjQIso ((EU.mapHomologicalComplex (.up ℤ)).obj J)).hom := by
    intro J hJ
    have h :=
      AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.squareComparison_normalized
        F EU EV G e J
    change c.hom.app (DerivedCategory.Q.obj J) ≫ _ ≫ _ = _ ≫ _ ≫
      DerivedCategory.Q.map (𝟙 _) at h
    erw [DerivedCategory.Q.map_id, Category.comp_id] at h
    exact h.symm
  have heq : c = β := (normalizedTowerEvaluation B C G n).unique hc hβ
  apply (congrArg Iso.hom heq).symm.trans
  have hm := AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.squareComparison_eq_mate
    F EU EV G H P (adj.whiskerRight ℕᵒᵖ) adj q e (ordinaryEvaluation_mate adj n)
  rw [hm]
  exact congrArg (fun k ↦ (mateEquiv
    (adj.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction
    adj.mapDerivedCategoryRightDerivedAdjunction (TwoSquare.mk _ _ _ _ k)).natTrans)
    (evaluationSquare_inverse P n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem towerPushEvaluation_mate (n : ℕ) :
    (d.towerPushEvaluation f n).hom =
      (mateEquiv (d.towerAdjunction f)
        (proEtaleRingDerivedAdjunction f (d.completedRing V) (d.completedRing U)
          (d.integralRingIso f))
        (TwoSquare.mk _ _ _ _ (stratumTowerEvaluationIso d f n).inv)).natTrans := by
  exact evaluationComparison_mate
    (proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f))
    (proEtaleRingModuleDirectImage f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f))
    (proEtaleRingModuleAdjunction f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f)) (op n) (d.towerPushEvaluation f n)
    (d.towerPushEvaluation_existsUnique f n).choose_spec.1

universe w
private def constantEvaluationIso
    (B : Type*) [Category B] [Abelian B]
    [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)] (n : ℕᵒᵖ) :
    (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory ⋙
        ((CategoryTheory.evaluation ℕᵒᵖ B).obj n).mapDerivedCategory ≅ 𝟭 _ :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Functor.constCompEvaluationObj (D := B) n) ≪≫
      Functor.mapDerivedCategoryIdIso _

private theorem constantEvaluation_factors
    (B : Type*) [Category B] [Abelian B]
    [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    (n : ℕᵒᵖ) (J : CochainComplex B ℤ) :
    (constantEvaluationIso B n).hom.app (DerivedCategory.Q.obj J) =
      ((CategoryTheory.evaluation ℕᵒᵖ B).obj n).mapDerivedCategory.map
        ((Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategoryFactors.hom.app J) ≫
      ((CategoryTheory.evaluation ℕᵒᵖ B).obj n).mapDerivedCategoryFactors.hom.app
        (((Functor.const ℕᵒᵖ : B ⥤ _).mapHomologicalComplex (.up ℤ)).obj J) := by
  let D := (Functor.const ℕᵒᵖ : B ⥤ (ℕᵒᵖ ⥤ B))
  let E := (CategoryTheory.evaluation ℕᵒᵖ B).obj n
  change (Functor.mapDerivedCategoryCompIso D E).inv.app (DerivedCategory.Q.obj J) ≫
    (Functor.mapDerivedCategoryNatIso (Iso.refl (𝟭 B))).hom.app (DerivedCategory.Q.obj J) ≫
      (Functor.mapDerivedCategoryIdIso B).hom.app (DerivedCategory.Q.obj J) = _
  rw [Functor.mapDerivedCategoryNatIso_refl]
  simp only [NatTrans.id_app]
  have hi := Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj B
    ((HomotopyCategory.quotient B (.up ℤ)).obj J)
  change (Functor.mapDerivedCategoryIdIso B).hom.app (DerivedCategory.Q.obj J) =
    (𝟭 B).mapDerivedCategoryFactorsh.hom.app _ at hi
  rw [hi]
  erw [AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.factorsh_hom]
  have h := Functor.mapDerivedCategoryCompIso_hom_app_factors D E J
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso D E).hom.app
    (DerivedCategory.Q.obj J))).mp
  simp only [Iso.hom_inv_id_app_assoc]
  erw [Category.id_comp]
  exact h.symm

private theorem derivedCounit_unit
    {B C : Type*} [Category B] [Category C] [Abelian B] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions C]
    {L : B ⥤ C} {R : C ⥤ B} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ R) (J : CochainComplex C ℤ) :
    L.mapDerivedCategory.map
        (R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj J)) ≫
      adj.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Q.obj J) =
    L.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj J) ≫
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app J) := by
  have h := (adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit ((HomotopyCategory.quotient _ _).obj J)
  erw [AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.factorsh_hom L
    ((R.mapHomologicalComplex (.up ℤ)).obj J)] at h
  rw [Adjunction.mapHomotopyCategory_counit_app_quotient] at h
  exact h

private theorem constantLimit_projection_unit
    (B : Type*) [Category B] [Abelian B] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory B] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
    [(lim : (ℕᵒᵖ ⥤ B) ⥤ B).Additive]
    (n : ℕᵒᵖ) (J : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :
    (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj J) ≫
      (constantEvaluationIso B n).inv.app
        ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.obj (DerivedCategory.Q.obj J)) ≫
      ((CategoryTheory.evaluation ℕᵒᵖ B).obj n).mapDerivedCategory.map
        (((constLimAdj : (Functor.const ℕᵒᵖ : B ⥤ _) ⊣ lim)
          ).mapDerivedCategoryRightDerivedAdjunction.counit.app
            (DerivedCategory.Q.obj J)) =
    DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app J) ≫
      ((CategoryTheory.evaluation ℕᵒᵖ B).obj n).mapDerivedCategoryFactors.inv.app J := by
  let E := (CategoryTheory.evaluation ℕᵒᵖ B).obj n
  let C : B ⥤ (ℕᵒᵖ ⥤ B) := Functor.const ℕᵒᵖ
  let L : (ℕᵒᵖ ⥤ B) ⥤ B := lim
  let adj := (constLimAdj : C ⊣ L).mapDerivedCategoryRightDerivedAdjunction
  let e := constantEvaluationIso B n
  let unit := L.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj J)
  have hc := derivedCounit_unit (constLimAdj : C ⊣ L) J
  have hn := e.inv.naturality unit
  change unit ≫ e.inv.app _ = e.inv.app _ ≫ E.mapDerivedCategory.map
    (C.mapDerivedCategory.map unit) at hn
  change unit ≫ (e.inv.app _ ≫ E.mapDerivedCategory.map _) = _
  rw [← Category.assoc, hn, Category.assoc, ← E.mapDerivedCategory.map_comp]
  rw [hc]
  rw [E.mapDerivedCategory.map_comp]
  rw [← Category.assoc]
  have hf := constantEvaluation_factors B n ((L.mapHomologicalComplex (.up ℤ)).obj J)
  have he : e.inv.app _ ≫ E.mapDerivedCategory.map
      (C.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj J)) =
    E.mapDerivedCategoryFactors.inv.app
      ((C.mapHomologicalComplex (.up ℤ)).obj ((L.mapHomologicalComplex (.up ℤ)).obj J)) := by
    apply (cancel_mono (E.mapDerivedCategoryFactors.hom.app _)).mp
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← hf]
    exact e.inv_hom_id_app _
  erw [he]
  exact (E.mapDerivedCategoryFactors.inv.naturality
    (((constLimAdj : C ⊣ L).mapHomologicalComplex (.up ℤ)).counit.app J)).symm

private def limitCounitProjection (T : Scheme.{t}) (n : ℕ) :
    completedRlim T (d.completedRing T) ⟶
      reductionTowerDerivedEvaluation T (reductionModuleRing T (d.completedRing T)) n where
  app M := (constantEvaluationIso (reductionModules T (d.completedRing T)) (op n)).inv.app
      ((completedRlim T (d.completedRing T)).obj M) ≫
    (reductionTowerDerivedEvaluation T (reductionModuleRing T (d.completedRing T)) n).map
      ((d.constantRlimAdjunction T).counit.app M)
  naturality M N a := by
    let E := reductionTowerDerivedEvaluation T (reductionModuleRing T (d.completedRing T)) n
    let L := completedRlim T (d.completedRing T)
    let C := d.derivedConstantTower T
    let e := constantEvaluationIso (reductionModules T (d.completedRing T)) (op n)
    have hn := e.inv.naturality (L.map a)
    change L.map a ≫ e.inv.app (L.obj N) =
      e.inv.app (L.obj M) ≫ E.map (C.map (L.map a)) at hn
    change L.map a ≫ (e.inv.app (L.obj N) ≫ E.map _) =
      (e.inv.app (L.obj M) ≫ E.map _) ≫ E.map a
    rw [← Category.assoc, hn, Category.assoc, ← E.map_comp]
    erw [(d.constantRlimAdjunction T).counit.naturality]
    simp only [E.map_comp, Category.assoc, Functor.id_map]

private theorem limitCounitProjection_unit (T : Scheme.{t}) (n : ℕ)
    (J : CochainComplex (d.towers T) ℤ) :
    (completedRlimUnit T (d.completedRing T)).app ((HomotopyCategory.quotient _ _).obj J) ≫
      (limitCounitProjection d T n).app (DerivedCategory.Q.obj J) =
    DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app J) ≫
      (reductionTowerEvaluation T (reductionModuleRing T
        (d.completedRing T)) n).mapDerivedCategoryFactors.inv.app J := by
  exact constantLimit_projection_unit (reductionModules T (d.completedRing T)) (op n) J

private theorem limitCounitProjection_eq (T : Scheme.{t}) (n : ℕ) :
    limitCounitProjection d T n = completedRlimProjection T (d.completedRing T) n := by
  apply NatTrans.ext
  funext M
  obtain ⟨J, hJ, ⟨i⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
  have := hJ
  have : IsIso ((completedRlimUnit T (d.completedRing T)).app
      ((HomotopyCategory.quotient _ _).obj J)) := completedRlim_computation T _ J
  have hj : (limitCounitProjection d T n).app (DerivedCategory.Q.obj J) =
      (completedRlimProjection T (d.completedRing T) n).app (DerivedCategory.Q.obj J) := by
    apply (cancel_epi ((completedRlimUnit T (d.completedRing T)).app
      ((HomotopyCategory.quotient _ _).obj J))).mp
    exact (limitCounitProjection_unit d T n J).trans
      (completedRlimProjection_unit T (d.completedRing T) J n).symm
  apply (cancel_epi ((completedRlim T (d.completedRing T)).map i.inv)).mp
  rw [(limitCounitProjection d T n).naturality,
    (completedRlimProjection T (d.completedRing T) n).naturality, hj]

private theorem mate_limit_projection
    {B C T S : Type*} [Category B] [Category C] [Category T] [Category S]
    (DX : B ⥤ T) (DY : C ⥤ S) (LX : T ⥤ B) (LY : S ⥤ C)
    (ax : DX ⊣ LX) (ay : DY ⊣ LY) (G : B ⥤ C) (GT : T ⥤ S)
    (EX : T ⥤ B) (EY : S ⥤ C) (cx : DX ⋙ EX ≅ 𝟭 B) (cy : DY ⋙ EY ≅ 𝟭 C)
    (χ : G ⋙ DY ⟶ DX ⋙ GT) (β : GT ⋙ EY ≅ EX ⋙ G)
    (hχ : ∀ N, EY.map (χ.app N) ≫ β.hom.app (DX.obj N) ≫
      G.map (cx.hom.app N) = cy.hom.app (G.obj N)) (M : T) :
    (mateEquiv ax ay (TwoSquare.mk _ _ _ _ χ)).app M ≫
        cy.inv.app (LY.obj (GT.obj M)) ≫ EY.map (ay.counit.app (GT.obj M)) ≫
        β.hom.app M = G.map (cx.inv.app (LX.obj M) ≫ EX.map (ax.counit.app M)) := by
  let κ := (mateEquiv ax ay (TwoSquare.mk _ _ _ _ χ)).natTrans
  have hc := mateEquiv_counit ax ay (TwoSquare.mk _ _ _ _ χ) M
  change DY.map (κ.app M) ≫ ay.counit.app (GT.obj M) =
    χ.app (LX.obj M) ≫ GT.map (ax.counit.app M) at hc
  change κ.app M ≫ _ = _
  apply (cancel_epi (cy.hom.app (G.obj (LX.obj M)))).mp
  have hn := (cy.hom.naturality (κ.app M)).symm
  change cy.hom.app (G.obj (LX.obj M)) ≫ κ.app M =
    EY.map (DY.map (κ.app M)) ≫ cy.hom.app (LY.obj (GT.obj M)) at hn
  rw [← Category.assoc (cy.hom.app (G.obj (LX.obj M))) (κ.app M), hn]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← EY.map_comp_assoc, hc, EY.map_comp, Category.assoc]
  erw [β.hom.naturality]
  dsimp only [Functor.comp_map]
  rw [← hχ (LX.obj M), G.map_comp]
  simp only [Category.assoc, ← G.map_comp, Iso.hom_inv_id_app_assoc]

private theorem pull_constant_evaluation (n : ℕ) (K : d.derived V) :
    (stratumTowerEvaluationIso d f n).inv.app ((d.derivedConstantTower V).obj K) ≫
      (reductionTowerDerivedEvaluation U (reductionModuleRing U (d.completedRing U)) n).map
        ((d.derivedConstantPullbackIso f).hom.app K) ≫
      (constantEvaluationIso (reductionModules U (d.completedRing U)) (op n)).hom.app
        ((d.pull f).obj K) =
    (d.pull f).map
      ((constantEvaluationIso (reductionModules V (d.completedRing V)) (op n)).hom.app K) := by
  let P := proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
    (d.integralRingIso f)
  let EU := reductionTowerEvaluation U (reductionModuleRing U (d.completedRing U)) n
  let EV := reductionTowerEvaluation V (reductionModuleRing V (d.completedRing V)) n
  have h := AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.exact_triangle_square
    (d.constantTower V) (d.constantTower U) P (d.towerModulePull f) EV EU
    (d.constantPullbackIso f) (Iso.refl (EV ⋙ P))
    (Functor.constCompEvaluationObj (D := reductionModules V (d.completedRing V)) (op n))
    (Functor.constCompEvaluationObj (D := reductionModules U (d.completedRing U)) (op n))
    (fun N ↦ by
      change P.map (𝟙 N) ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _
      rw [P.map_id, Category.id_comp, Category.id_comp]) K
  simpa only [constantEvaluationIso, AdicCoefficientDatum.derivedConstantPullbackIso,
    stratumTowerEvaluationIso, Functor.mapDerivedCategorySquareIso, Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    ← Functor.mapDerivedCategoryNatIso_symm, Iso.refl_symm,
    Functor.mapDerivedCategoryNatIso_refl, NatTrans.id_app, Category.id_comp,
    Category.comp_id, Category.assoc, stratumModulePull, P, EU, EV] using h

private theorem push_constant_evaluation (n : ℕ) (K : d.derived U) :
    let χ := (mateEquiv
      (proEtaleRingDerivedAdjunction f (d.completedRing V) (d.completedRing U)
        (d.integralRingIso f)) (d.towerAdjunction f)
      (TwoSquare.mk _ _ _ _ (d.derivedConstantPullbackIso f).hom)).natTrans
    (reductionTowerDerivedEvaluation V (reductionModuleRing V (d.completedRing V)) n).map
        (χ.app K) ≫ (d.towerPushEvaluation f n).hom.app ((d.derivedConstantTower U).obj K) ≫
      (d.push f).map
        ((constantEvaluationIso (reductionModules U (d.completedRing U)) (op n)).hom.app K) =
    (constantEvaluationIso (reductionModules V (d.completedRing V)) (op n)).hom.app
      ((d.push f).obj K) := by
  have h := AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.mates_evaluation
    (proEtaleRingDerivedAdjunction f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f)) (d.towerAdjunction f)
    (d.derivedConstantTower V) (d.derivedConstantTower U)
    (reductionTowerDerivedEvaluation V (reductionModuleRing V (d.completedRing V)) n)
    (reductionTowerDerivedEvaluation U (reductionModuleRing U (d.completedRing U)) n)
    (constantEvaluationIso (reductionModules V (d.completedRing V)) (op n))
    (constantEvaluationIso (reductionModules U (d.completedRing U)) (op n))
    (d.derivedConstantPullbackIso f).hom (stratumTowerEvaluationIso d f n).inv
    (pull_constant_evaluation d f n) K
  change (reductionTowerDerivedEvaluation V
      (reductionModuleRing V (d.completedRing V)) n).map
      ((mateEquiv
        (proEtaleRingDerivedAdjunction f (d.completedRing V) (d.completedRing U)
          (d.integralRingIso f)) (d.towerAdjunction f)
        (TwoSquare.mk _ _ _ _ (d.derivedConstantPullbackIso f).hom)).natTrans.app K) ≫
    (mateEquiv (d.towerAdjunction f)
      (proEtaleRingDerivedAdjunction f (d.completedRing V) (d.completedRing U)
        (d.integralRingIso f))
      (TwoSquare.mk _ _ _ _ (stratumTowerEvaluationIso d f n).inv)).natTrans.app
        ((d.derivedConstantTower U).obj K) ≫
      (d.push f).map
        ((constantEvaluationIso (reductionModules U (d.completedRing U)) (op n)).hom.app K) =
    (constantEvaluationIso (reductionModules V (d.completedRing V)) (op n)).hom.app
      ((d.push f).obj K) at h
  rw [← towerPushEvaluation_mate] at h
  exact h

private theorem directImage_projection (M : DerivedCategory (d.towers U)) (n : ℕ) :
    (d.directImageRlimIso f).hom.app M ≫
      (completedRlimProjection V (d.completedRing V) n).app ((d.towerPush f).obj M) ≫
        (d.towerPushEvaluation f n).hom.app M =
      (d.push f).map ((completedRlimProjection U (d.completedRing U) n).app M) := by
  let a := proEtaleRingDerivedAdjunction f (d.completedRing V) (d.completedRing U)
    (d.integralRingIso f)
  let b := d.towerAdjunction f
  let ax := d.constantRlimAdjunction U
  let ay := d.constantRlimAdjunction V
  let e := TwoSquare.mk _ _ _ _ (d.derivedConstantPullbackIso f).hom
  let chi := mateEquiv a b e
  have h := mate_limit_projection (d.derivedConstantTower U) (d.derivedConstantTower V)
    (completedRlim U (d.completedRing U)) (completedRlim V (d.completedRing V)) ax ay
    (d.push f) (d.towerPush f)
    (reductionTowerDerivedEvaluation U (reductionModuleRing U (d.completedRing U)) n)
    (reductionTowerDerivedEvaluation V (reductionModuleRing V (d.completedRing V)) n)
    (constantEvaluationIso (reductionModules U (d.completedRing U)) (op n))
    (constantEvaluationIso (reductionModules V (d.completedRing V)) (op n))
    chi.natTrans (d.towerPushEvaluation f n) (push_constant_evaluation d f n) M
  have hi := iterated_mateEquiv_conjugateEquiv a b ay ax e
  change (mateEquiv ax ay chi).natTrans = (d.directImageRlimIso f).hom at hi
  change (mateEquiv ax ay chi).natTrans.app M ≫
    (constantEvaluationIso (reductionModules V (d.completedRing V)) (op n)).inv.app _ ≫
      (reductionTowerDerivedEvaluation V
        (reductionModuleRing V (d.completedRing V)) n).map (ay.counit.app _) ≫
        (d.towerPushEvaluation f n).hom.app M = _ at h
  rw [hi] at h
  have h' : (d.directImageRlimIso f).hom.app M ≫
      (limitCounitProjection d V n).app ((d.towerPush f).obj M) ≫
        (d.towerPushEvaluation f n).hom.app M =
      (d.push f).map ((limitCounitProjection d U n).app M) := by
    simpa only [limitCounitProjection, Category.assoc] using h
  simpa only [limitCounitProjection_eq] using h'


universe ub vb uc vc
attribute [local instance] evaluationPreservesKInjective

private theorem canonicalUnit_app
    {B : Type ub} {C : Type uc} [Category.{vb} B] [Category.{vc} C] [Abelian B] [Abelian C]
    [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} C]
    [Abelian.HasKInjectiveResolutions B] (G : B ⥤ C) [G.Additive]
    (J : CochainComplex B ℤ) :
    (CategoryTheory.DirectImageRoosNormalization.canonicalDerivedUnit G).app J =
      G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj J) := by
  simp only [CategoryTheory.DirectImageRoosNormalization.canonicalDerivedUnit,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, quotientHomId, quotientInvId,
    homotopyFactorsInvId]
  erw [DerivedCategory.Qh.map_id, G.rightDerivedFunctor.map_id,
    Category.id_comp, Category.id_comp, Category.comp_id]
  repeat first | erw [Category.id_comp] | erw [Category.comp_id]

private theorem normalizedEvaluation_transitions
    {B : Type ub} {C : Type uc} [Category.{vb} B] [Category.{vc} C] [Abelian B] [Abelian C]
    [IsGrothendieckAbelian.{vb} B] [IsGrothendieckAbelian.{vc} C]
    [IsGrothendieckAbelian.{vb} (ℕᵒᵖ ⥤ B)] [IsGrothendieckAbelian.{vc} (ℕᵒᵖ ⥤ C)]
    [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} C]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ C)]
    (F : C ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G) :
    let GT := (Functor.whiskeringRight ℕᵒᵖ B C).obj G
    let EB := fun n ↦ ((CategoryTheory.evaluation ℕᵒᵖ B).obj n)
    let EC := fun n ↦ ((CategoryTheory.evaluation ℕᵒᵖ C).obj n)
    ∃ β : ∀ n : ℕᵒᵖ, GT.rightDerivedFunctor ⋙ (EC n).mapDerivedCategory ≅
        (EB n).mapDerivedCategory ⋙ G.rightDerivedFunctor,
      (∀ (n : ℕᵒᵖ) (J : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) [J.IsKInjective],
        (EC n).mapDerivedCategory.map (GT.rightDerivedFunctorObjQIso J).hom ≫
          (EC n).mapDerivedCategoryFactors.hom.app
            ((GT.mapHomologicalComplex (.up ℤ)).obj J) =
        (β n).hom.app (DerivedCategory.Q.obj J) ≫
          G.rightDerivedFunctor.map ((EB n).mapDerivedCategoryFactors.hom.app J) ≫
          (G.rightDerivedFunctorObjQIso
            (((EB n).mapHomologicalComplex (.up ℤ)).obj J)).hom) ∧
      (∀ (m n : ℕᵒᵖ) (t : m ⟶ n) (M : DerivedCategory (ℕᵒᵖ ⥤ B)),
        (towerDerivedEvaluationTransition C t).app (GT.rightDerivedFunctor.obj M) ≫
          (β n).hom.app M =
        (β m).hom.app M ≫ G.rightDerivedFunctor.map
          ((towerDerivedEvaluationTransition B t).app M)) := by
  let GT := (Functor.whiskeringRight ℕᵒᵖ B C).obj G
  let EB := fun n ↦ ((CategoryTheory.evaluation ℕᵒᵖ B).obj n)
  let EC := fun n ↦ ((CategoryTheory.evaluation ℕᵒᵖ C).obj n)
  let η := CategoryTheory.DirectImageRoosNormalization.canonicalDerivedUnit G
  let ηT := CategoryTheory.DirectImageRoosNormalization.canonicalDerivedUnit GT
  let := CategoryTheory.DirectImageRoosNormalization.canonicalDerivedUnit_isRightDerived G
  let := CategoryTheory.DirectImageRoosNormalization.canonicalDerivedUnit_isRightDerived GT
  obtain ⟨a, b, ha, hb, β, hβ, _, ht, _⟩ :=
    exists_unique_towerDerivedEvaluation_normalized F G adj
      G.rightDerivedFunctor GT.rightDerivedFunctor η ηT
  refine ⟨β, ?_, ht⟩
  intro n J hJ
  have : (EB n).PreservesKInjectiveComplexes := evaluationPreservesKInjective B n
  have hn := hβ n J hJ
  have hT : ηT.app J = (GT.rightDerivedFunctorObjQIso J).inv := by
    rw [canonicalUnit_app]
    exact (AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.objQIso_inv GT J).symm
  have hG : η.app (((EB n).mapHomologicalComplex (.up ℤ)).obj J) =
      (G.rightDerivedFunctorObjQIso
        (((EB n).mapHomologicalComplex (.up ℤ)).obj J)).inv := by
    rw [canonicalUnit_app]
    exact (AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.objQIso_inv G _).symm
  rw [hT, hG] at hn
  have hh := congrArg (fun k ↦
    (EC n).mapDerivedCategory.map (GT.rightDerivedFunctorObjQIso J).hom ≫
      (EC n).mapDerivedCategoryFactors.hom.app
        ((GT.mapHomologicalComplex (.up ℤ)).obj J) ≫ k ≫
      (G.rightDerivedFunctorObjQIso
        (((EB n).mapHomologicalComplex (.up ℤ)).obj J)).hom) hn
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hh
  erw [Iso.hom_inv_id_app_assoc] at hh
  erw [← (EC n).mapDerivedCategory.map_comp_assoc, Iso.hom_inv_id,
    (EC n).mapDerivedCategory.map_id, Category.id_comp] at hh
  exact hh.symm


private theorem evaluation_transition (m n : ℕᵒᵖ) (t : m ⟶ n)
    (M : DerivedCategory (d.towers U)) :
    (towerDerivedEvaluationTransition
      (reductionModules V (d.completedRing V)) t).app ((d.towerPush f).obj M) ≫
        (d.towerPushEvaluation f n.unop).hom.app M =
      (d.towerPushEvaluation f m.unop).hom.app M ≫ (d.push f).map
        ((towerDerivedEvaluationTransition (reductionModules U (d.completedRing U)) t).app M) := by
  let F := proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
    (d.integralRingIso f)
  let G := proEtaleRingModuleDirectImage f (d.completedRing V) (d.completedRing U)
    (d.integralRingIso f)
  have hg (T : Scheme.{t}) :
      IsGrothendieckAbelian.{t + 1} (reductionModules T (d.completedRing T)) := by
    let R := reductionModuleRing T (d.completedRing T)
    let S := ((AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt).sheafPushforwardContinuous
      RingCat.{t + 1} (proEtaleModelTopology T) (ProEt.topology T)).obj R
    let := SheafOfModules.isGrothendieckAbelian S
    exact IsGrothendieckAbelian.of_equivalence (proEtaleModuleModelEquivalence T R)
  let := hg U
  let := hg V
  let : IsGrothendieckAbelian.{t + 1} (d.towers U) :=
    reductionTower_isGrothendieckAbelian U _
  let : IsGrothendieckAbelian.{t + 1} (d.towers V) :=
    reductionTower_isGrothendieckAbelian V _
  obtain ⟨β, hβ, ht⟩ := normalizedEvaluation_transitions F G
    (proEtaleRingModuleAdjunction f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f))
  have hb (n : ℕᵒᵖ) : β n = d.towerPushEvaluation f n.unop :=
    (d.towerPushEvaluation_existsUnique f n.unop).unique (hβ n)
      (d.towerPushEvaluation_existsUnique f n.unop).choose_spec.1
  simpa only [hb] using ht m n t M

private theorem product_transition
    (M : DerivedCategory (d.towers U))
    [HasProduct (completedTowerDerivedSequence U d M)]
    [HasProduct (completedTowerDerivedSequence V d ((d.towerPush f).obj M))] :
    (d.push f).map (towerTransitionEndomorphism (completedTowerDerivedStep U d M)) ≫
        d.directImageProductComparison f M =
      d.directImageProductComparison f M ≫ towerTransitionEndomorphism
        (completedTowerDerivedStep V d ((d.towerPush f).obj M)) := by
  apply Pi.hom_ext
  intro n
  simp only [AdicCoefficientDatum.directImageProductComparison,
    towerTransitionEndomorphism, towerProductShift, Functor.map_sub,
    Preadditive.sub_comp, Preadditive.comp_sub, Category.comp_id,
    Category.assoc, Pi.lift_π, Pi.lift_π_assoc]
  congr 1
  · erw [(d.push f).map_id, Category.id_comp]
  rw [← (d.push f).map_comp_assoc, Pi.lift_π]
  have h := evaluation_transition d f (op (n + 1)) (op n)
    (homOfLE (Nat.le_succ n)).op M
  have hh := congrArg (fun k ↦ (d.towerPushEvaluation f (n + 1)).inv.app M ≫ k ≫
    (d.towerPushEvaluation f n).inv.app M) h
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app] at hh
  erw [Category.comp_id] at hh
  erw [(d.push f).map_comp, Category.assoc]
  change (d.push f).map (Pi.π (completedTowerDerivedSequence U d M) (n + 1)) ≫
    (d.push f).map ((towerDerivedEvaluationTransition
      (reductionModules U (d.completedRing U)) (homOfLE (Nat.le_succ n)).op).app M) ≫
      (d.towerPushEvaluation f n).inv.app M = _
  rw [← hh]
  rfl


private theorem triangleTransport
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ X⟦(1 : ℤ)⟧)
    (h : Pretriangulated.Triangle.mk a b c ∈ distTriang C)
    {X' Y' Z' : D} (a' : X' ⟶ Y') (b' : Y' ⟶ Z') (c' : Z' ⟶ X'⟦(1 : ℤ)⟧)
    (i : F.obj X ≅ X') (j : F.obj Y ≅ Y') (k : F.obj Z ≅ Z')
    (ha : F.map a ≫ j.hom = i.hom ≫ a')
    (hb : F.map b ≫ k.hom = j.hom ≫ b')
    (hc : (F.map c ≫ (F.commShiftIso (1 : ℤ)).hom.app X) ≫
      i.hom⟦(1 : ℤ)⟧' = k.hom ≫ c') :
    Pretriangulated.Triangle.mk a' b' c' ∈ distTriang D := by
  let e := Pretriangulated.Triangle.isoMk
    (F.mapTriangle.obj (Pretriangulated.Triangle.mk a b c))
    (Pretriangulated.Triangle.mk a' b' c') i j k ha hb hc
  exact (Pretriangulated.distinguished_iff_of_iso e).mp (F.map_distinguished _ h)

/-- The actual product comparison is invertible, and the specified Rlim comparison
is induced by it on the Roos triangles, with the shift maps retained.
Source: blueprint direct image and limits, Roos-triangle clauses; Stacks 099N and 07KC
(blueprint: prop-weil-pbc-direct-image-limits).
Proof: direct image is a right adjoint of exact inverse image. It preserves
K-injective tower models and products. Its ordinary product comparison is the
product of the images of the tower projections; this commutes with every transition,
hence with one minus shift. On a K-injective tower the ordinary limit comparison
is the conjugate of the constant/pullback comparison, exactly the defining
comparison directImageRlimIso. Apply the derived localization to this morphism of
Roos sequences. Exact countable products compute the two derived products, giving
the asserted isomorphism and the first and third squares of the triangle map. -/
theorem AdicCoefficientDatum.directImageRlim_roos
    (M : DerivedCategory (d.towers U))
    [HasProduct (completedTowerDerivedSequence U d M)]
    [HasProduct (completedTowerDerivedSequence V d ((d.towerPush f).obj M))] :
    IsIso (d.directImageProductComparison f M) ∧
      (d.push f).map (towerTransitionEndomorphism (completedTowerDerivedStep U d M)) ≫
          d.directImageProductComparison f M =
        d.directImageProductComparison f M ≫ towerTransitionEndomorphism
          (completedTowerDerivedStep V d ((d.towerPush f).obj M)) ∧
      ∃ (δU : ∏ᶜ (completedTowerDerivedSequence U d M) ⟶
          ((completedRlim U (d.completedRing U)).obj M)⟦(1 : ℤ)⟧)
        (δV : ∏ᶜ (completedTowerDerivedSequence V d ((d.towerPush f).obj M)) ⟶
          ((completedRlim V (d.completedRing V)).obj ((d.towerPush f).obj M))⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle (completedTowerDerivedStep U d M)
          ((completedRlim U (d.completedRing U)).obj M)
          (completedRlimRoosProjection U d M) δU ∧
        IsDerivedLimitTriangle
          (completedTowerDerivedStep V d ((d.towerPush f).obj M))
          ((completedRlim V (d.completedRing V)).obj ((d.towerPush f).obj M))
          (completedRlimRoosProjection V d ((d.towerPush f).obj M)) δV ∧
        (d.directImageRlimIso f).hom.app M ≫
            completedRlimRoosProjection V d ((d.towerPush f).obj M) =
          (d.push f).map (completedRlimRoosProjection U d M) ≫
            d.directImageProductComparison f M ∧
        (d.push f).map δU ≫
            ((d.push f).commShiftIso (1 : ℤ)).hom.app
              ((completedRlim U (d.completedRing U)).obj M) ≫
            ((d.directImageRlimIso f).hom.app M)⟦(1 : ℤ)⟧' =
          d.directImageProductComparison f M ≫ δV := by
  have hi := directImageProductComparison_isIso d f M
  have ht := product_transition d f M
  have hp : (d.directImageRlimIso f).hom.app M ≫
      completedRlimRoosProjection V d ((d.towerPush f).obj M) =
    (d.push f).map (completedRlimRoosProjection U d M) ≫
      d.directImageProductComparison f M := by
    apply Pi.hom_ext
    intro n
    apply (cancel_mono ((d.towerPushEvaluation f n).hom.app M)).mp
    simp only [Category.assoc, completedRlimRoosProjection, Pi.lift_π,
      AdicCoefficientDatum.directImageProductComparison]
    erw [Iso.inv_hom_id_app, Category.comp_id]
    erw [← (d.push f).map_comp]
    erw [Pi.lift_π]
    exact directImage_projection d f M n
  let := hi
  obtain ⟨δU, hU⟩ := completedRlim_roos U d M
  let δV := inv (d.directImageProductComparison f M) ≫ (d.push f).map δU ≫
    ((d.push f).commShiftIso (1 : ℤ)).hom.app
      ((completedRlim U (d.completedRing U)).obj M) ≫
      ((d.directImageRlimIso f).hom.app M)⟦(1 : ℤ)⟧'
  have hb : (d.push f).map δU ≫
      ((d.push f).commShiftIso (1 : ℤ)).hom.app
        ((completedRlim U (d.completedRing U)).obj M) ≫
      ((d.directImageRlimIso f).hom.app M)⟦(1 : ℤ)⟧' =
    d.directImageProductComparison f M ≫ δV := by
    simp only [δV, IsIso.hom_inv_id_assoc]
  refine ⟨hi, ht, δU, δV, hU, ?_, hp, hb⟩
  exact triangleTransport (d.push f) (completedRlimRoosProjection U d M)
    (towerTransitionEndomorphism (completedTowerDerivedStep U d M)) δU hU
    (completedRlimRoosProjection V d ((d.towerPush f).obj M))
    (towerTransitionEndomorphism
      (completedTowerDerivedStep V d ((d.towerPush f).obj M))) δV
    ((d.directImageRlimIso f).app M) (asIso (d.directImageProductComparison f M))
    (asIso (d.directImageProductComparison f M)) hp.symm ht
    ((Category.assoc _ _ _).trans hb)

/-- The ordinary scalar/pullback mate, in the inverse direction of chi.
Source: blueprint four corners and tower compatibility; Stacks 06YY and 0D6D
(blueprint: prop-weil-pbc-direct-image-limits). -/
def completedOrdinaryReductionPullbackInv (n : ℕ) :
    proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
        (d.integralRingIso f) ⋙ proEtaleRingExtension (d.projection U n) ⟶
      proEtaleRingExtension (d.projection V n) ⋙
        proEtaleRingModulePullback f (d.finiteRing V n) (d.finiteRing U n)
          (d.finiteRingIso f n) :=
  (mateEquiv (proEtaleRingExtensionAdjunction (d.projection V n))
    (proEtaleRingExtensionAdjunction (d.projection U n))).symm
      (proEtaleRingRestrictionPullbackInv f (d.completedRing V) (d.finiteRing V n)
        (d.completedRing U) (d.finiteRing U n) (d.projection V n) (d.projection U n)
          (d.integralRingIso f) (d.finiteRingIso f n) (d.projection_comm f n))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized ordinary mate is the invertible tensor balancing map.
Source: blueprint tower compatibility; Stacks 03EL and 06YY
(blueprint: prop-weil-pbc-direct-image-limits).
Proof: the tensor-unit normalized adjunctions compute this mate on pure tensors.
It sends the inverse image of m tensored with p to the inverse image of m tensor p.
The coefficient projection square makes the map quotient-linear. The reverse tensor
reassociation is inverse, as checked on pure tensors and then on sheafifications. -/
theorem completedOrdinaryReductionPullbackInv_isIso (n : ℕ) :
    IsIso (completedOrdinaryReductionPullbackInv d f n) := by
  let av := proEtaleRingExtensionAdjunction (d.projection V n)
  let au := proEtaleRingExtensionAdjunction (d.projection U n)
  let ar := proEtaleRingModuleAdjunction f (d.completedRing V) (d.completedRing U)
    (d.integralRingIso f)
  let az := proEtaleRingModuleAdjunction f (d.finiteRing V n) (d.finiteRing U n)
    (d.finiteRingIso f n)
  let b := proEtaleRingRestrictionPullbackInv f
    (d.completedRing V) (d.finiteRing V n) (d.completedRing U) (d.finiteRing U n)
    (d.projection V n) (d.projection U n) (d.integralRingIso f)
    (d.finiteRingIso f n) (d.projection_comm f n)
  let c := proEtaleRingRestrictionDirectImage f
    (d.completedRing V) (d.finiteRing V n) (d.completedRing U) (d.finiteRing U n)
    (d.projection V n) (d.projection U n) (d.integralRingIso f)
    (d.finiteRingIso f n) (d.projection_comm f n)
  let α := TwoSquare.mk _ _ _ _ b
  have hm : mateEquiv az ar α = TwoSquare.mk _ _ _ _ c.hom := by
    rw [← Equiv.eq_symm_apply]
    apply TwoSquare.ext
    intro M
    simp only [α, b, mateEquiv_symm_apply, proEtaleRingRestrictionPullbackInv,
      proEtaleRingRestrictionPullbackApp, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Functor.comp_map,
      Category.id_comp]
    simp only [TwoSquare.mk, CategoryTheory.Functor.map_id]
    dsimp only [TwoSquare.natTrans, Functor.comp_obj]
    simp only [Category.id_comp]
    exact (Category.comp_id _).symm
  let γ := (mateEquiv av au).symm α
  have hγ : mateEquiv av au γ = α := (mateEquiv av au).apply_symm_apply α
  have : IsIso (conjugateEquiv (av.comp az) (ar.comp au) γ.natTrans) := by
    rw [← iterated_mateEquiv_conjugateEquiv av au ar az γ, hγ, hm]
    change IsIso c.hom
    infer_instance
  change IsIso γ.natTrans
  exact conjugateEquiv_of_iso (av.comp az) (ar.comp au) γ.natTrans

attribute [instance] completedOrdinaryReductionPullbackInv_isIso

/-- The ordinary reduction-level comparison after restriction to completed coefficients.
Source: blueprint tower compatibility (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedReductionLevelPullbackIso (n : ℕ) :
    completedReductionLevel V d n ⋙
        proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
          (d.integralRingIso f) ≅
      proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
        (d.integralRingIso f) ⋙ completedReductionLevel U d n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (proEtaleRingExtension (d.projection V n))
      (@asIso _ _ _ _ (proEtaleRingRestrictionPullbackInv f
        (d.completedRing V) (d.finiteRing V n) (d.completedRing U) (d.finiteRing U n)
        (d.projection V n) (d.projection U n) (d.integralRingIso f)
        (d.finiteRingIso f n) (d.projection_comm f n))
        (proEtaleRingRestrictionPullbackInv_isIso f
          (d.completedRing V) (d.finiteRing V n) (d.completedRing U) (d.finiteRing U n)
          (d.projection V n) (d.projection U n) (d.integralRingIso f)
          (d.finiteRingIso f n) (d.projection_comm f n))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (completedOrdinaryReductionPullbackInv d f n)).symm
      (proEtaleRingRestrictScalars (d.projection U n)) ≪≫
    Functor.associator _ _ _

section TowerPullTransition
attribute [local irreducible] pbcScalarAdjunction proEtaleRingModuleAdjunction
set_option backward.isDefEq.respectTransparency false

private theorem mate_units
    {A B C E : Type*} [Category A] [Category B] [Category C] [Category E]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ E} {R₂ : E ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (P : A ⥤ C) (Q : B ⥤ E) (β : R₁ ⋙ P ⟶ Q ⋙ R₂)
    (X : A)
    [IsIso (((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ β)).app X)] :
    P.map (adj₁.unit.app X) ≫ β.app (L₁.obj X) ≫
      R₂.map (inv (((mateEquiv adj₁ adj₂).symm
        (TwoSquare.mk _ _ _ _ β)).app X)) = adj₂.unit.app (P.obj X) := by
  have h := unit_mateEquiv_symm adj₁ adj₂ (TwoSquare.mk _ _ _ _ β) X
  dsimp only [Functor.id_obj] at h
  rw [← Category.assoc, h, Category.assoc, ← R₂.map_comp,
    IsIso.hom_inv_id, R₂.map_id]
  erw [Category.comp_id]

private theorem levelPullIso_unit (n : ℕ)
    (M : reductionModules V (d.completedRing V)) :
    (proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
        (d.integralRingIso f)).map
        ((proEtaleRingExtensionAdjunction (d.projection V n)).unit.app M) ≫
      (completedReductionLevelPullbackIso d f n).hom.app M =
        (proEtaleRingExtensionAdjunction (d.projection U n)).unit.app
          ((proEtaleRingModulePullback f (d.completedRing V)
            (d.completedRing U) (d.integralRingIso f)).obj M) := by
  have : IsIso (((mateEquiv
      (proEtaleRingExtensionAdjunction (d.projection V n))
      (proEtaleRingExtensionAdjunction (d.projection U n))).symm
        (TwoSquare.mk _ _ _ _ (proEtaleRingRestrictionPullbackInv f
          (d.completedRing V) (d.finiteRing V n) (d.completedRing U)
          (d.finiteRing U n) (d.projection V n) (d.projection U n)
          (d.integralRingIso f) (d.finiteRingIso f n) (d.projection_comm f n)))).app M) := by
    change IsIso ((completedOrdinaryReductionPullbackInv d f n).app M)
    infer_instance
  simp only [completedReductionLevelPullbackIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, asIso_hom, asIso_inv, Iso.symm_hom,
    Category.id_comp, Category.comp_id, NatIso.isIso_inv_app, completedOrdinaryReductionPullbackInv]
  erw [Category.id_comp]
  exact mate_units (proEtaleRingExtensionAdjunction (d.projection V n))
      (proEtaleRingExtensionAdjunction (d.projection U n)) _ _
      (proEtaleRingRestrictionPullbackInv f (d.completedRing V) (d.finiteRing V n)
        (d.completedRing U) (d.finiteRing U n) (d.projection V n) (d.projection U n)
        (d.integralRingIso f) (d.finiteRingIso f n) (d.projection_comm f n)) M

private theorem restrictionPullback_unit
    (RV SV : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (RU SU : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
    (aV : RV ⟶ SV) (aU : RU ⟶ SU)
    (cR : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj RV ≅ RU)
    (cS : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj SV ≅ SU)
    (comm : cR.hom ≫ aU =
      (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map aV ≫ cS.hom)
    (N : proEtaleRingModules V SV) (W : V.ProEtᵒᵖ) (z : N.val.obj W) :
    ((proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm).app N).val.app
        ((proEtaleBaseChange f).op.obj W)
        (((proEtaleRingModuleAdjunction f RV RU cR).unit.app
          ((proEtaleRingRestrictScalars aV).obj N)).val.app W z) =
      ((proEtaleRingModuleAdjunction f SV SU cS).unit.app N).val.app W z := by
  let δ := proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm
  let σ := proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm
  have h := unit_mateEquiv (proEtaleRingModuleAdjunction f SV SU cS)
    (proEtaleRingModuleAdjunction f RV RU cR) (TwoSquare.mk _ _ _ _ σ) N
  have hm := restrictionPullback_mate f RV SV RU SU aV aU cR cS comm
  change (proEtaleRingRestrictScalars aV).map
      ((proEtaleRingModuleAdjunction f SV SU cS).unit.app N) ≫
        (mateEquiv (proEtaleRingModuleAdjunction f SV SU cS)
          (proEtaleRingModuleAdjunction f RV RU cR)
          (TwoSquare.mk _ _ _ _ σ)).natTrans.app _ = _ at h
  rw [hm] at h
  have hz := congrArg (fun k ↦ k.val.app W z) h
  change (δ.hom.app ((proEtaleRingModulePullback f SV SU cS).obj N)).val.app W
      (((proEtaleRingModuleAdjunction f SV SU cS).unit.app N).val.app W z) = _ at hz
  have he := (Classical.choose_spec
    (proEtaleRingRestrictionDirectImage_existsUnique f RV SV RU SU aV aU cR cS comm)).1
      ((proEtaleRingModulePullback f SV SU cS).obj N) W
      (((proEtaleRingModuleAdjunction f SV SU cS).unit.app N).val.app W z)
  exact (he.symm.trans hz).symm

private theorem levelPullIso_one (n : ℕ)
    (M : reductionModules V (d.completedRing V))
    (W : V.ProEtᵒᵖ) (x : M.val.obj W) :
    ((completedReductionLevelPullbackIso d f n).hom.app M).val.app ((proEtaleBaseChange f).op.obj W)
        (((proEtaleRingModuleAdjunction f (d.completedRing V)
          (d.completedRing U) (d.integralRingIso f)).unit.app
            ((completedReductionLevel V d n).obj M)).val.app W
              (reductionTensorSection V (d.projection V n) M W 1 x)) =
      reductionTensorSection U (d.projection U n)
        ((proEtaleRingModulePullback f (d.completedRing V)
          (d.completedRing U) (d.integralRingIso f)).obj M)
        ((proEtaleBaseChange f).op.obj W) 1
        (((proEtaleRingModuleAdjunction f (d.completedRing V)
          (d.completedRing U) (d.integralRingIso f)).unit.app M).val.app W x) := by
  let P := proEtaleRingModulePullback f (d.completedRing V)
    (d.completedRing U) (d.integralRingIso f)
  let Q := proEtaleRingModuleDirectImage f (d.completedRing V)
    (d.completedRing U) (d.integralRingIso f)
  let adj := proEtaleRingModuleAdjunction f (d.completedRing V)
    (d.completedRing U) (d.integralRingIso f)
  let uV := (proEtaleRingExtensionAdjunction (d.projection V n)).unit.app M
  let uU := (proEtaleRingExtensionAdjunction (d.projection U n)).unit.app (P.obj M)
  have h : uV ≫ adj.unit.app ((completedReductionLevel V d n).obj M) ≫
      Q.map ((completedReductionLevelPullbackIso d f n).hom.app M) = adj.unit.app M ≫ Q.map uU := by
    erw [← adj.unit_naturality_assoc]
    rw [← Q.map_comp]
    exact congrArg (adj.unit.app M ≫ ·) (congrArg Q.map (levelPullIso_unit d f n M))
  have hv : uV.val.app W x = reductionTensorSection V (d.projection V n) M W 1 x := by
    simpa only [uV, proEtaleRingExtensionAdjunction, pbcScalarAdjunction,
      pbcTensorSection, reductionTensorSection, proEtaleRingExtension, reductionChange,
      pbcExtend, pbcRestrict, proEtaleRingRestrictScalars] using
      (pbcScalarAdjunction_exists (d.projection V n)).exists.choose_spec M W x
  have hu : uU.val.app ((proEtaleBaseChange f).op.obj W)
        ((adj.unit.app M).val.app W x) =
      reductionTensorSection U (d.projection U n) (P.obj M)
        ((proEtaleBaseChange f).op.obj W) 1 ((adj.unit.app M).val.app W x) := by
    simpa only [uU, proEtaleRingExtensionAdjunction, pbcScalarAdjunction,
      pbcTensorSection, reductionTensorSection, proEtaleRingExtension, reductionChange,
      pbcExtend, pbcRestrict, proEtaleRingRestrictScalars] using
      (pbcScalarAdjunction_exists (d.projection U n)).exists.choose_spec
        (P.obj M) ((proEtaleBaseChange f).op.obj W) ((adj.unit.app M).val.app W x)
  have hx := congrArg (fun k ↦ k.val.app W x) h
  change ((completedReductionLevelPullbackIso d f n).hom.app M).val.app
      ((proEtaleBaseChange f).op.obj W)
      ((adj.unit.app ((completedReductionLevel V d n).obj M)).val.app W (uV.val.app W x)) =
    uU.val.app ((proEtaleBaseChange f).op.obj W) ((adj.unit.app M).val.app W x) at hx
  rw [hv, hu] at hx
  exact hx

open AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization in
private theorem levelPullIso_tensor (n : ℕ)
    (M : reductionModules V (d.completedRing V))
    (W : V.ProEtᵒᵖ) (s : (d.finiteRing V n).obj.obj W) (x : M.val.obj W) :
    ((completedReductionLevelPullbackIso d f n).hom.app M).val.app ((proEtaleBaseChange f).op.obj W)
        (((proEtaleRingModuleAdjunction f (d.completedRing V)
          (d.completedRing U) (d.integralRingIso f)).unit.app
            ((completedReductionLevel V d n).obj M)).val.app W
              (reductionTensorSection V (d.projection V n) M W s x)) =
      reductionTensorSection U (d.projection U n)
        ((proEtaleRingModulePullback f (d.completedRing V)
          (d.completedRing U) (d.integralRingIso f)).obj M)
        ((proEtaleBaseChange f).op.obj W)
        ((proEtaleRingDirectImageMap f (d.finiteRing V n) (d.finiteRing U n)
          (d.finiteRingIso f n)).hom.app W s)
        (((proEtaleRingModuleAdjunction f (d.completedRing V)
          (d.completedRing U) (d.integralRingIso f)).unit.app M).val.app W x) := by
  let σ := proEtaleRingRestrictionPullbackInv f (d.completedRing V) (d.finiteRing V n)
    (d.completedRing U) (d.finiteRing U n) (d.projection V n) (d.projection U n)
    (d.integralRingIso f) (d.finiteRingIso f n) (d.projection_comm f n)
  let N := (proEtaleRingExtension (d.projection V n)).obj M
  let g := (inv (completedOrdinaryReductionPullbackInv d f n)).app M
  let adjR := proEtaleRingModuleAdjunction f (d.completedRing V)
    (d.completedRing U) (d.integralRingIso f)
  let adjS := proEtaleRingModuleAdjunction f (d.finiteRing V n)
    (d.finiteRing U n) (d.finiteRingIso f n)
  let B := (proEtaleBaseChange f).op.obj W
  have hσ (z : N.val.obj W) :
      (σ.app N).val.app B ((adjR.unit.app ((completedReductionLevel V d n).obj M)).val.app W z) =
        ((adjS.unit.app N).val.app W z) :=
    restrictionPullback_unit f _ _ _ _ _ _ _ _ _ N W z
  have h1 := levelPullIso_one d f n M W x
  change (g.val.app B) ((σ.app N).val.app B
    ((adjR.unit.app ((completedReductionLevel V d n).obj M)).val.app W
      (reductionTensorSection V (d.projection V n) M W 1 x))) = _ at h1
  rw [hσ] at h1
  change (g.val.app B) ((σ.app N).val.app B
    ((adjR.unit.app ((completedReductionLevel V d n).obj M)).val.app W
      (reductionTensorSection V (d.projection V n) M W s x))) = _
  rw [hσ]
  have hs := tensorSection_smul V (d.projection V n) M W s 1 x
  rw [mul_one] at hs
  rw [← hs]
  have hsm := ((adjS.unit.app N).val.app W).hom.map_smul s
    (reductionTensorSection V (d.projection V n) M W 1 x)
  change (adjS.unit.app N).val.app W
      (s • reductionTensorSection V (d.projection V n) M W 1 x) =
    @SMul.smul ((d.finiteRing U n).obj.obj B)
      (((proEtaleRingModulePullback f (d.finiteRing V n) (d.finiteRing U n)
        (d.finiteRingIso f n)).obj N).val.obj B) inferInstance
      ((proEtaleRingDirectImageMap f (d.finiteRing V n) (d.finiteRing U n)
        (d.finiteRingIso f n)).hom.app W s)
      ((adjS.unit.app N).val.app W
        (reductionTensorSection V (d.projection V n) M W 1 x)) at hsm
  rw [hsm]
  erw [(g.val.app B).hom.map_smul]
  rw [h1]
  simpa only [mul_one] using tensorSection_smul U (d.projection U n)
    ((proEtaleRingModulePullback f (d.completedRing V)
      (d.completedRing U) (d.integralRingIso f)).obj M) B
    ((proEtaleRingDirectImageMap f (d.finiteRing V n) (d.finiteRing U n)
      (d.finiteRingIso f n)).hom.app W s) 1
    ((adjR.unit.app M).val.app W x)

private theorem finiteRingIso_transition (n : ℕ) :
    (d.finiteRingIso f (n + 1)).hom ≫
      reductionCoefficientMap U d (n + 1) n (Nat.le_succ n) =
    (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map
      (reductionCoefficientMap V d (n + 1) n (Nat.le_succ n)) ≫
        (d.finiteRingIso f n).hom := by
  let a : op (n + 1) ⟶ op n := (homOfLE (Nat.le_succ n)).op
  change (d.finiteRingIso f (n + 1)).hom ≫ (reductionCoefficientSystem U d).map a =
    (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map
      ((reductionCoefficientSystem V d).map a) ≫ (d.finiteRingIso f n).hom
  let eU := pbcConstantSystemComparison U d
  let eV := pbcConstantSystemComparison V d
  let b : adicLisseRingSystem V d.ideal ⋙
      proEtaleSheafInverseImage f CommRingCat.{t + 1} ⟶
      adicLisseRingSystem U d.ideal :=
    NatTrans.ofOpSequence (fun k ↦ (proEtaleConstantComparison f).app
      (CommRingCat.of (A ⧸ d.ideal ^ (k + 1)))) (by
        intro k
        simpa only [Functor.comp_map, adicLisseRingSystem,
          Functor.ofOpSequence_map_homOfLE_succ] using
          (proEtaleConstantComparison f).naturality
            (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (k + 1))))
  have hn := congrArg (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map
    (eV.inv.naturality a)
  have hb := b.naturality a
  have hu := eU.hom.naturality a
  simp only [Functor.map_comp] at hn
  change (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map
      ((reductionCoefficientSystem V d).map a) ≫
        (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map
          (pbcLevelConstantComparison V d n).inv =
    (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map
      (pbcLevelConstantComparison V d (n + 1)).inv ≫
        (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map
          ((adicLisseRingSystem V d.ideal).map a) at hn
  change (adicLisseRingSystem V d.ideal ⋙
    proEtaleSheafInverseImage f CommRingCat.{t + 1}).map a ≫
      (proEtaleConstantComparison f).app (d.ringTower.obj (op n)) =
    (proEtaleConstantComparison f).app (d.ringTower.obj (op (n + 1))) ≫
      (adicLisseRingSystem U d.ideal).map a at hb
  change (adicLisseRingSystem U d.ideal).map a ≫
      (pbcLevelConstantComparison U d n).hom =
    (pbcLevelConstantComparison U d (n + 1)).hom ≫
      (reductionCoefficientSystem U d).map a at hu
  dsimp only [AdicCoefficientDatum.finiteRingIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_hom]
  simp only [Category.assoc]
  erw [← hu]
  rw [← Category.assoc _ _ ((pbcLevelConstantComparison U d n).hom)]
  rw [← hb]
  simp only [Functor.comp_map, Category.assoc]
  rw [← reassoc_of% hn]

open AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization in
private theorem levelPullIso_step (n : ℕ)
    (M : reductionModules V (d.completedRing V)) :
    (proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
        (d.integralRingIso f)).map
          ((completedReductionTransition V d (n + 1) n (Nat.le_succ n)).app M) ≫
        (completedReductionLevelPullbackIso d f n).hom.app M =
      (completedReductionLevelPullbackIso d f (n + 1)).hom.app M ≫
        (completedReductionTransition U d (n + 1) n (Nat.le_succ n)).app
          ((proEtaleRingModulePullback f (d.completedRing V)
            (d.completedRing U) (d.integralRingIso f)).obj M) := by
  let adj := proEtaleRingModuleAdjunction f (d.completedRing V)
    (d.completedRing U) (d.integralRingIso f)
  apply (adj.homEquiv _ _).injective
  apply level_hom_ext V (d.projection V (n + 1)) M
  intro W s x
  let B := (proEtaleBaseChange f).op.obj W
  let P := proEtaleRingModulePullback f (d.completedRing V)
    (d.completedRing U) (d.integralRingIso f)
  have hn := congrArg (fun k ↦ k.val.app W
      (reductionTensorSection V (d.projection V (n + 1)) M W s x))
    (adj.unit.naturality ((completedReductionTransition V d (n + 1) n (Nat.le_succ n)).app M))
  change (adj.unit.app ((completedReductionLevel V d n).obj M)).val.app W
      (((completedReductionTransition V d (n + 1) n (Nat.le_succ n)).app M).val.app W
        (reductionTensorSection V (d.projection V (n + 1)) M W s x)) =
    ((P.map ((completedReductionTransition V d (n + 1) n (Nat.le_succ n)).app M)).val.app B)
      ((adj.unit.app ((completedReductionLevel V d (n + 1)).obj M)).val.app W
        (reductionTensorSection V (d.projection V (n + 1)) M W s x)) at hn
  change ((completedReductionLevelPullbackIso d f n).hom.app M).val.app B
      (((P.map ((completedReductionTransition V d (n + 1) n (Nat.le_succ n)).app M)).val.app B)
        ((adj.unit.app ((completedReductionLevel V d (n + 1)).obj M)).val.app W
          (reductionTensorSection V (d.projection V (n + 1)) M W s x))) =
    ((completedReductionTransition U d (n + 1) n (Nat.le_succ n)).app (P.obj M)).val.app B
      (((completedReductionLevelPullbackIso d f (n + 1)).hom.app M).val.app B
        ((adj.unit.app ((completedReductionLevel V d (n + 1)).obj M)).val.app W
          (reductionTensorSection V (d.projection V (n + 1)) M W s x)))
  rw [← hn]
  erw [(completedReductionTransition_exists V d (n + 1) n (Nat.le_succ n)).exists.choose_spec]
  rw [levelPullIso_tensor, levelPullIso_tensor]
  erw [(completedReductionTransition_exists U d (n + 1) n (Nat.le_succ n)).exists.choose_spec]
  have hq := congrArg (fun z ↦ z.hom.app W s)
    (restrictionDirectImageMap_square f (d.finiteRing V (n + 1)) (d.finiteRing V n)
      (d.finiteRing U (n + 1)) (d.finiteRing U n)
      (reductionCoefficientMap V d (n + 1) n (Nat.le_succ n))
      (reductionCoefficientMap U d (n + 1) n (Nat.le_succ n))
      (d.finiteRingIso f (n + 1)) (d.finiteRingIso f n) (finiteRingIso_transition d f n))
  exact congrArg (fun z ↦ reductionTensorSection U (d.projection U n) (P.obj M) B z
    ((adj.unit.app M).val.app W x)) hq

/-- The level tensor comparisons commute with every quotient transition, including identities.
Source: blueprint tower compatibility, step 1 (blueprint: prop-weil-pbc-direct-image-limits).
Proof: both composites send a local pure tensor to its pullback with the quotient image
of its coefficient. Equality on pure tensors descends through sheafification. Arbitrary
quotient transitions are composites of consecutive ones, with identities included. -/
theorem completedReductionLevelPullbackIso_transition
    (M : reductionModules V (d.completedRing V)) {n m : ℕᵒᵖ} (a : n ⟶ m) :
    ((completedReductionModuleTowerFunctor V d ⋙ d.towerModulePull f).obj M).map a ≫
        (completedReductionLevelPullbackIso d f m.unop).hom.app M =
      (completedReductionLevelPullbackIso d f n.unop).hom.app M ≫
        ((proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
          (d.integralRingIso f) ⋙ completedReductionModuleTowerFunctor U d).obj M).map a := by
  let P := proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
    (d.integralRingIso f)
  let η : ((completedReductionModuleTowerFunctor V d ⋙ d.towerModulePull f).obj M) ⟶
      ((P ⋙ completedReductionModuleTowerFunctor U d).obj M) :=
    NatTrans.ofOpSequence (fun n ↦ (completedReductionLevelPullbackIso d f n).hom.app M)
      (by
        intro n
        change P.map ((completedReductionModuleTower V d M).map
            (homOfLE (Nat.le_succ n)).op) ≫ _ =
          _ ≫ (completedReductionModuleTower U d (P.obj M)).map
            (homOfLE (Nat.le_succ n)).op
        simp only [completedReductionModuleTower, Functor.ofOpSequence_map_homOfLE_succ]
        exact levelPullIso_step d f n M)
  exact η.naturality a

end TowerPullTransition

/-- The actual strict tower isomorphism of ordinary tensor/pullback computations.
Source: blueprint tower compatibility (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedReductionOrdinaryPullbackIso :
    completedReductionModuleTowerFunctor V d ⋙ d.towerModulePull f ≅
      proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
        (d.integralRingIso f) ⋙ completedReductionModuleTowerFunctor U d :=
  NatIso.ofComponents
    (fun M ↦ NatIso.ofComponents
      (fun n ↦ (completedReductionLevelPullbackIso d f n.unop).app M)
      (fun a ↦ completedReductionLevelPullbackIso_transition d f M a))
    (fun a ↦ by
      apply NatTrans.ext
      funext n
      exact (completedReductionLevelPullbackIso d f n.unop).hom.naturality a)

section GenericComparisonPredicate
variable {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasDerivedCategory (ℕᵒᵖ ⥤ C)]
  (F : B ⥤ (ℕᵒᵖ ⥤ B)) [F.Additive] (G : C ⥤ (ℕᵒᵖ ⥤ C)) [G.Additive]
  (P : B ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  (H : (ℕᵒᵖ ⥤ B) ⥤ (ℕᵒᵖ ⥤ C)) [H.Additive]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (e : F ⋙ H ≅ P ⋙ G)
  (LF : DerivedCategory B ⥤ DerivedCategory (ℕᵒᵖ ⥤ B))
  (LG : DerivedCategory C ⥤ DerivedCategory (ℕᵒᵖ ⥤ C))
  (εF : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  (εG : DerivedCategory.Qh ⋙ LG ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)

/-- The ordinary-complex normalization equation for a derived pullback comparison.
The equation is stated generically so its specialization reuses the checked categorical types.
Source: blueprint tower compatibility, steps 1--3; Stacks 06YY and 0D6D
(blueprint: prop-weil-pbc-direct-image-limits). -/
def IsDerivedReductionPullbackComparison
    (M : CochainComplex B ℤ → Prop)
    (η : LF ⋙ H.mapDerivedCategory ≅ P.mapDerivedCategory ⋙ LG) : Prop :=
  ∀ K : CochainComplex B ℤ, M K →
        η.hom.app (DerivedCategory.Q.obj K) ≫
          LG.map (P.mapDerivedCategoryFactors.hom.app K) ≫
            reductionComplexCounit G LG εG
              ((P.mapHomologicalComplex (.up ℤ)).obj K) =
        H.mapDerivedCategory.map (reductionComplexCounit F LF εF K) ≫
          H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K)

end GenericComparisonPredicate

set_option linter.defProp false in
/-- Reuse the strict quotient-unit normalized representative formula.
The ordinary comparison agrees with this module's by `ordinaryReduction_eq_stratum`.
Source: blueprint tower compatibility, steps 1--3; Stacks 06YY and 0D6D
(blueprint: prop-weil-pbc-direct-image-limits). -/
def IsCompletedReductionPullbackComparison
    (τ : completedReductionTower V d ⋙ d.towerPull f ≅
        d.pull f ⋙ completedReductionTower U d) : Prop :=
  StratumReductionFormula d f τ

attribute [local semireducible] completedReductionCoefficient

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryReduction_augmentation
    (M : reductionModules V (d.completedRing V)) :
    (d.towerModulePull f).map ((completedReductionModuleUnit d V).app M) ≫
        (completedReductionOrdinaryPullbackIso d f).hom.app M =
      (d.constantPullbackIso f).hom.app M ≫
        (completedReductionModuleUnit d U).app
          ((proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
            (d.integralRingIso f)).obj M) := by
  apply NatTrans.ext
  funext n
  let adj := proEtaleRingModuleAdjunction f (d.completedRing V) (d.completedRing U)
    (d.integralRingIso f)
  apply (adj.homEquiv _ _).injective
  ext W x
  have h := congrArg (fun k ↦ k.val.app W x)
    (adj.unit.naturality (((completedReductionModuleUnit d V).app M).app n))
  change (adj.unit.app ((completedReductionLevel V d n.unop).obj M)).val.app W
      ((((completedReductionModuleUnit d V).app M).app n).val.app W x) =
    ((proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f)).map (((completedReductionModuleUnit d V).app M).app n)).val.app
        ((proEtaleBaseChange f).op.obj W) ((adj.unit.app M).val.app W x) at h
  change ((completedReductionLevelPullbackIso d f n.unop).hom.app M).val.app
      ((proEtaleBaseChange f).op.obj W)
      (((proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
        (d.integralRingIso f)).map
          (((completedReductionModuleUnit d V).app M).app n)).val.app
            ((proEtaleBaseChange f).op.obj W) ((adj.unit.app M).val.app W x)) = _
  rw [← h]
  erw [(completedReductionModuleUnit_exists d V).exists.choose_spec M n.unop W x]
  erw [levelPullIso_one]
  change _ = (((completedReductionModuleUnit d U).app
    ((proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f)).obj M)).app n).val.app
        ((proEtaleBaseChange f).op.obj W) ((adj.unit.app M).val.app W x)
  exact ((completedReductionModuleUnit_exists d U).exists.choose_spec _ n.unop _ _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryReduction_eq_stratum :
    completedReductionOrdinaryPullbackIso d f = stratumModuleReductionIso d f := by
  apply (stratumModuleReductionIso_exists d f).unique
  · intro M
    exact ordinaryReduction_augmentation d f M
  · exact (stratumModuleReductionIso_exists d f).exists.choose_spec

private theorem reductionFormula_iff
    (τ : completedReductionTower V d ⋙ d.towerPull f ≅
      d.pull f ⋙ completedReductionTower U d) :
    IsCompletedReductionPullbackComparison d f τ ↔ StratumReductionFormula d f τ := Iff.rfl

/-- The universal normalization of the ordinary reduction comparison determines its derived lift.
Source: Stacks Tags 06YY and 03EL
(blueprint: prop-weil-pbc-direct-image-limits).
Proof: the quotient-unit normalization identifies the ordinary comparison with the strict
stratum comparison. Their representative formulas are identical. Existence and uniqueness
therefore follow from the normalized strict reduction comparison. -/
theorem completedReductionPullbackIso_existsUnique :
    ∃! τ : completedReductionTower V d ⋙ d.towerPull f ≅
        d.pull f ⋙ completedReductionTower U d,
      IsCompletedReductionPullbackComparison d f τ := by
  obtain ⟨τ, hτ, hu⟩ := stratumReductionIso_exists d f
  exact ⟨τ, (reductionFormula_iff d f τ).mpr hτ,
    fun η hη ↦ hu η ((reductionFormula_iff d f η).mp hη)⟩


/-- The normalized reduction-tower/pullback isomorphism, rather than an arbitrary lift
of levelwise maps. Source: blueprint tower compatibility
(blueprint: prop-weil-pbc-direct-image-limits). -/
def AdicCoefficientDatum.reductionTowerPullbackIso :
    completedReductionTower V d ⋙ d.towerPull f ≅
      d.pull f ⋙ completedReductionTower U d :=
  (completedReductionPullbackIso_existsUnique d f).choose

/-- The strict derived projection map is the adjunct of tower chi followed by the
reduction of the ambient counit. Its evaluation is the specified finite projection.
Source: blueprint tower compatibility (blueprint: prop-weil-pbc-direct-image-limits). -/
def AdicCoefficientDatum.towerProjection (K : d.derived U) :
    (completedReductionTower V d).obj ((d.push f).obj K) ⟶
      (d.towerPush f).obj ((completedReductionTower U d).obj K) :=
  (d.towerAdjunction f).homEquiv _ _
    ((d.reductionTowerPullbackIso f).hom.app ((d.push f).obj K) ≫
      (completedReductionTower U d).map
        ((proEtaleRingDerivedAdjunction f (d.completedRing V) (d.completedRing U)
          (d.integralRingIso f)).counit.app K))


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem towerProjection_natural (K H : d.derived U) (a : K ⟶ H) :
    (completedReductionTower V d).map ((d.push f).map a) ≫ d.towerProjection f H =
      d.towerProjection f K ≫ (d.towerPush f).map
        ((completedReductionTower U d).map a) := by
  let adj := proEtaleRingDerivedAdjunction f (d.completedRing V)
    (d.completedRing U) (d.integralRingIso f)
  unfold AdicCoefficientDatum.towerProjection
  apply (d.towerAdjunction f).homEquiv_naturality_left_square
  have hn := (d.reductionTowerPullbackIso f).hom.naturality_assoc
    ((d.push f).map a) ((completedReductionTower U d).map (adj.counit.app H))
  change (d.towerPull f).map
      ((completedReductionTower V d).map ((d.push f).map a)) ≫
        (d.reductionTowerPullbackIso f).hom.app ((d.push f).obj H) ≫
          (completedReductionTower U d).map (adj.counit.app H) =
    (d.reductionTowerPullbackIso f).hom.app ((d.push f).obj K) ≫
      (completedReductionTower U d).map ((d.pull f).map ((d.push f).map a)) ≫
        (completedReductionTower U d).map (adj.counit.app H) at hn
  rw [Category.assoc, hn]
  simp only [← Functor.map_comp]
  erw [← adj.counit.naturality]
  rfl


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem reduction_eq_stratum :
    d.reductionTowerPullbackIso f = stratumReductionIso d f := by
  apply (completedReductionPullbackIso_existsUnique d f).unique
  · exact (completedReductionPullbackIso_existsUnique d f).choose_spec.1
  · exact (reductionFormula_iff d f _).mpr
      (stratumReductionIso_exists d f).exists.choose_spec


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem reduction_augmentation (K : d.derived V) :
    (d.towerPull f).map ((completedReductionAugmentation d V).app K) ≫
        (d.reductionTowerPullbackIso f).hom.app K =
      (d.derivedConstantPullbackIso f).hom.app K ≫
        (completedReductionAugmentation d U).app ((d.pull f).obj K) := by
  rw [reduction_eq_stratum]
  exact stratumReduction_augmentation d f K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem towerProjection_completion (K : d.derived U) :
    d.completionUnit V ((d.push f).obj K) ≫
        (completedRlim V (d.completedRing V)).map (d.towerProjection f K) =
      (d.push f).map (d.completionUnit U K) ≫
        (d.directImageRlimIso f).hom.app ((completedReductionTower U d).obj K) := by
  let a := proEtaleRingDerivedAdjunction f (d.completedRing V)
    (d.completedRing U) (d.integralRingIso f)
  let b := d.towerAdjunction f
  let ax := d.constantRlimAdjunction U
  let ay := d.constantRlimAdjunction V
  let e := TwoSquare.mk _ _ _ _ (d.derivedConstantPullbackIso f).hom
  let chi := mateEquiv a b e
  have hm := AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.mates_naturality
    a b (completedReductionAugmentation d V) (completedReductionAugmentation d U)
    (d.derivedConstantPullbackIso f).hom (d.reductionTowerPullbackIso f).hom
    (reduction_augmentation d f) K
  have hp : (mateEquiv a b
      (TwoSquare.mk _ _ _ _ (d.reductionTowerPullbackIso f).hom)).app K =
      d.towerProjection f K := by
    simp only [mateEquiv_apply, TwoSquare.mk, TwoSquare.natTrans,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app, Category.id_comp]
    change _ = b.unit.app _ ≫ (d.towerPush f).map (_ ≫ _)
    simp only [Functor.map_comp]
    repeat first | erw [Category.id_comp] | erw [Category.comp_id]
    rfl
  rw [hp] at hm
  have hu := unit_mateEquiv ax ay chi K
  have hi := iterated_mateEquiv_conjugateEquiv a b ay ax e
  change (mateEquiv ax ay chi).natTrans = (d.directImageRlimIso f).hom at hi
  change (d.push f).map (ax.unit.app K) ≫
      (mateEquiv ax ay chi).natTrans.app ((d.derivedConstantTower U).obj K) =
    ay.unit.app ((d.push f).obj K) ≫
      (completedRlim V (d.completedRing V)).map (chi.natTrans.app K) at hu
  rw [hi] at hu
  dsimp only [AdicCoefficientDatum.completionUnit]
  rw [Category.assoc, ← Functor.map_comp, hm, Functor.map_comp,
    ← Category.assoc, ← hu]
  simp only [Category.assoc]
  have hn := (d.directImageRlimIso f).hom.naturality
    ((completedReductionAugmentation d U).app K)
  change (d.push f).map ((completedRlim U (d.completedRing U)).map
      ((completedReductionAugmentation d U).app K)) ≫
        (d.directImageRlimIso f).hom.app ((completedReductionTower U d).obj K) =
    (d.directImageRlimIso f).hom.app ((d.derivedConstantTower U).obj K) ≫
      (completedRlim V (d.completedRing V)).map
        ((d.towerPush f).map ((completedReductionAugmentation d U).app K)) at hn
  erw [← hn]
  simp only [Functor.map_comp, Category.assoc]
  rfl

/-- Evaluate the pushed reduction tower using its canonical K-injective evaluation
comparison, the normalized reduction counit, and the specified scalar-restriction
comparison. Source: blueprint direct image and limits, projection-formula clause
(blueprint: prop-weil-pbc-direct-image-limits). -/
def AdicCoefficientDatum.towerPushReductionEvaluation
    (K : d.derived U) (n : ℕ) :
    (reductionTowerDerivedEvaluation V
        (reductionModuleRing V (d.completedRing V)) n).obj
        ((d.towerPush f).obj ((completedReductionTower U d).obj K)) ⟶
      (reductionDerivedRestrict V (d.projection V n)).obj
        ((d.finitePush f n).obj ((d.reduction U n).obj K)) :=
  (d.towerPushEvaluation f n).hom.app ((completedReductionTower U d).obj K) ≫
    (d.push f).map ((completedReductionEvaluation U d n).app K) ≫
      (proEtaleRingRestrictionDerivedDirectImage f
        (d.completedRing V) (d.finiteRing V n) (d.completedRing U) (d.finiteRing U n)
        (d.projection V n) (d.projection U n) (d.integralRingIso f)
        (d.finiteRingIso f n) (d.projection_comm f n)).inv.app ((d.reduction U n).obj K)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem towerProjection_evaluation (K : d.derived U) (n : ℕ) :
    (reductionTowerDerivedEvaluation V
        (reductionModuleRing V (d.completedRing V)) n).map (d.towerProjection f K) ≫
        d.towerPushReductionEvaluation f K n =
      (completedReductionEvaluation V d n).app ((d.push f).obj K) ≫
        (reductionDerivedRestrict V (d.projection V n)).map (d.finiteProjection f K n) := by
  let a := proEtaleRingDerivedAdjunction f (d.completedRing V) (d.completedRing U)
    (d.integralRingIso f)
  let EU := reductionTowerDerivedEvaluation U
    (reductionModuleRing U (d.completedRing U)) n
  let EV := reductionTowerDerivedEvaluation V
    (reductionModuleRing V (d.completedRing V)) n
  let RU := (proEtaleRingRestrictScalars (d.projection U n)).mapDerivedCategory
  let RV := (proEtaleRingRestrictScalars (d.projection V n)).mapDerivedCategory
  let u : completedReductionTower U d ⋙ EU ⟶
      d.reduction U n ⋙ RU :=
    completedReductionEvaluation U d n
  let v : completedReductionTower V d ⋙ EV ⟶
      d.reduction V n ⋙ RV :=
    completedReductionEvaluation V d n
  let δ := proEtaleRingRestrictionDerivedDirectImage f
    (d.completedRing V) (d.finiteRing V n) (d.completedRing U) (d.finiteRing U n)
    (d.projection V n) (d.projection U n) (d.integralRingIso f)
    (d.finiteRingIso f n) (d.projection_comm f n)
  let r := proEtaleRingRestrictionDerivedPullback f
    (d.completedRing V) (d.finiteRing V n) (d.completedRing U) (d.finiteRing U n)
    (d.projection V n) (d.projection U n) (d.integralRingIso f)
    (d.finiteRingIso f n) (d.projection_comm f n)
  let t := (d.chi f n).hom.app ((d.push f).obj K) ≫
    (d.reduction U n).map (a.counit.app K)
  have ht : (stratumTowerEvaluationIso d f n).inv.app
        ((completedReductionTower V d).obj ((d.push f).obj K)) ≫
      EU.map ((d.reductionTowerPullbackIso f).hom.app ((d.push f).obj K) ≫
        (completedReductionTower U d).map (a.counit.app K)) ≫ u.app K =
    (d.pull f).map (v.app ((d.push f).obj K)) ≫
      r.inv.app ((d.reduction V n).obj ((d.push f).obj K)) ≫
        (RU).map t := by
    have he := stratumReduction_evaluation d f n ((d.push f).obj K)
    rw [← reduction_eq_stratum] at he
    change EU.map ((d.reductionTowerPullbackIso f).hom.app ((d.push f).obj K)) ≫
        u.app ((d.pull f).obj ((d.push f).obj K)) =
      (stratumTowerEvaluationIso d f n).hom.app
          ((completedReductionTower V d).obj ((d.push f).obj K)) ≫
        (d.pull f).map (v.app ((d.push f).obj K)) ≫
          r.inv.app ((d.reduction V n).obj ((d.push f).obj K)) ≫
            (RU).map
              ((d.chi f n).hom.app ((d.push f).obj K)) at he
    have hn := u.naturality (a.counit.app K)
    change EU.map ((completedReductionTower U d).map (a.counit.app K)) ≫ u.app K =
      u.app ((d.pull f).obj ((d.push f).obj K)) ≫
        RU.map ((d.reduction U n).map (a.counit.app K)) at hn
    simp only [Functor.map_comp, Category.assoc]
    rw [hn]
    rw [← Category.assoc
      (EU.map ((d.reductionTowerPullbackIso f).hom.app ((d.push f).obj K)))
      (u.app ((d.pull f).obj ((d.push f).obj K)))
      (RU.map ((d.reduction U n).map (a.counit.app K))), he]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← RU.map_comp]
    rfl
  have hm := _root_.mate_adjunct (d.towerAdjunction f) a
    (TwoSquare.mk _ _ _ _ (stratumTowerEvaluationIso d f n).inv)
    ((completedReductionTower V d).obj ((d.push f).obj K))
    ((completedReductionTower U d).obj K)
    ((d.reductionTowerPullbackIso f).hom.app ((d.push f).obj K) ≫
      (completedReductionTower U d).map (a.counit.app K))
  change a.homEquiv _ _
    ((stratumTowerEvaluationIso d f n).inv.app
        ((completedReductionTower V d).obj ((d.push f).obj K)) ≫
      EU.map ((d.reductionTowerPullbackIso f).hom.app ((d.push f).obj K) ≫
        (completedReductionTower U d).map (a.counit.app K))) =
    EV.map (d.towerProjection f K) ≫
      (mateEquiv (d.towerAdjunction f) a
        (TwoSquare.mk _ _ _ _ (stratumTowerEvaluationIso d f n).inv)).natTrans.app _ at hm
  rw [← towerPushEvaluation_mate] at hm
  apply (cancel_mono (δ.hom.app ((d.reduction U n).obj K))).mp
  dsimp only [AdicCoefficientDatum.towerPushReductionEvaluation]
  change (EV.map (d.towerProjection f K) ≫
      ((d.towerPushEvaluation f n).hom.app ((completedReductionTower U d).obj K) ≫
        (d.push f).map (u.app K) ≫ δ.inv.app ((d.reduction U n).obj K))) ≫
      δ.hom.app ((d.reduction U n).obj K) =
    (v.app ((d.push f).obj K) ≫ RV.map (d.finiteProjection f K n)) ≫
      δ.hom.app ((d.reduction U n).obj K)
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  rw [← Category.assoc, ← hm]
  erw [← a.homEquiv_naturality_right]
  rw [Category.assoc, ht]
  erw [a.homEquiv_naturality_left]
  have hs := (proEtaleRingSheafChangeAdjunction f
    (d.completedRing V) (d.finiteRing V n) (d.completedRing U) (d.finiteRing U n)
    (d.projection V n) (d.projection U n) (d.integralRingIso f)
    (d.finiteRingIso f n) (d.projection_comm f n)).2.2
      ((d.reduction V n).obj ((d.push f).obj K)) ((d.reduction U n).obj K) t
  erw [hs]
  rfl


/-- The specified tower projection evaluates to the finite projection formula, is
natural in arbitrary morphisms, and identifies the two completion units. The map
is one morphism of derived strict towers, retaining every quotient transition.
Source: blueprint direct image and limits, projection and completeness clauses;
Stacks Tags 0944 and 099N (blueprint: prop-weil-pbc-direct-image-limits).
Proof: on flat-term K-flat models the scalar/pullback mate is tensor balancing.
Transposition of its composite with the counit is exactly finiteProjection, by the
normalized scalar-change adjunction comparison. The same tensor maps commute with
quotient transitions and chain maps, giving the strict tower map and naturality.
The constant-to-reduction augmentation has the same quotient-unit formula. Apply
adjunction transposition and the constant/pullback comparison: the resulting
completion map is direct image of the original unit followed by directImageRlimIso.
This is the last displayed equality. Perfectness makes the tower projection
invertible, by conservativity of evaluation for isomorphisms. -/
theorem AdicCoefficientDatum.towerProjection_properties (K : d.derived U) :
    (∀ n : ℕ,
      (reductionTowerDerivedEvaluation V
          (reductionModuleRing V (d.completedRing V)) n).map (d.towerProjection f K) ≫
          d.towerPushReductionEvaluation f K n =
        (completedReductionEvaluation V d n).app ((d.push f).obj K) ≫
          (reductionDerivedRestrict V (d.projection V n)).map (d.finiteProjection f K n)) ∧
      (∀ (H : d.derived U) (a : K ⟶ H),
        (completedReductionTower V d).map ((d.push f).map a) ≫ d.towerProjection f H =
          d.towerProjection f K ≫
            (d.towerPush f).map ((completedReductionTower U d).map a)) ∧
      d.completionUnit V ((d.push f).obj K) ≫
          (completedRlim V (d.completedRing V)).map (d.towerProjection f K) =
        (d.push f).map (d.completionUnit U K) ≫
          (d.directImageRlimIso f).hom.app ((completedReductionTower U d).obj K) := by
  exact ⟨towerProjection_evaluation d f K, towerProjection_natural d f K,
    towerProjection_completion d f K⟩

private theorem derivedTowerIsIso
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
    {X Y : DerivedCategory (ℕᵒᵖ ⥤ B)} (a : X ⟶ Y)
    (h : ∀ n : ℕᵒᵖ,
      IsIso ((((CategoryTheory.evaluation ℕᵒᵖ B).obj n).mapDerivedCategory).map a)) :
    IsIso a := by
  rw [DerivedCategory.isIso_iff]
  intro i
  have (n : ℕᵒᵖ) : IsIso
      (((DerivedCategory.homologyFunctor (ℕᵒᵖ ⥤ B) i).map a).app n) := by
    let E := (CategoryTheory.evaluation ℕᵒᵖ B).obj n
    have : IsIso ((E.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor B i).map a) := by
      change IsIso ((DerivedCategory.homologyFunctor B i).map (E.mapDerivedCategory.map a))
      let := h n
      infer_instance
    exact (NatIso.isIso_map_iff (E.mapDerivedCategoryHomologyFunctorIso i) a).2 inferInstance
  exact NatIso.isIso_of_isIso_app _

/-- Perfect quotient coefficients make the specified strict projection invertible.
Source: blueprint tower compatibility; Stacks Tags 0944 and 015F
(blueprint: prop-weil-pbc-direct-image-limits).
Proof: evaluate the tower adjunction mate. The coefficient restriction/pullback
comparisons identify its evaluation with the restriction of the finite projection.
The latter is invertible by the perfect projection formula. The cone of the tower map
therefore has zero cohomology at every index. Tower cohomology is levelwise, hence its
cone is acyclic and the original strict derived tower map is invertible. This uses
conservativity for isomorphisms, without claiming faithfulness of derived evaluations. -/
theorem AdicCoefficientDatum.towerProjection_isIso {U V : Scheme.{t}} (f : U ⟶ V)
    (K : d.derived U) : IsIso (d.towerProjection f K) := by
  have he (n : ℕ) : IsIso
      ((reductionTowerDerivedEvaluation V
        (reductionModuleRing V (d.completedRing V)) n).map (d.towerProjection f K)) := by
    have h := (d.towerProjection_properties f K).1 n
    have : IsIso ((reductionTowerDerivedEvaluation V
        (reductionModuleRing V (d.completedRing V)) n).map (d.towerProjection f K) ≫
        d.towerPushReductionEvaluation f K n) := by
      rw [h]
      infer_instance
    have : IsIso (d.towerPushReductionEvaluation f K n) := by
      unfold AdicCoefficientDatum.towerPushReductionEvaluation
      infer_instance
    exact IsIso.of_isIso_comp_right _ (d.towerPushReductionEvaluation f K n)
  exact derivedTowerIsIso (B := ringedSiteModules.{t + 1}
    (reductionModuleRing V (d.completedRing V))) (d.towerProjection f K)
    (fun n ↦ he n.unop)

attribute [instance] AdicCoefficientDatum.towerProjection_isIso

/-- Direct image preserves quotient-tower completeness, with the specified completion unit.
Source: blueprint direct image and limits; Stacks Tag 099N (3), (4)
(blueprint: prop-weil-pbc-direct-image-limits).
Proof: the perfect projection-formula maps identify the strict reduction tower of Rf_*K
with derived tower pushforward of K's strict reduction tower. Their quotient compatibility
is the tensor-unit normalization. The canonical completion unit of Rf_*K
then equals Rf_* of K's completion unit followed by the canonical direct-image/Rlim
comparison. Both maps are invertible, the first by hK and the second by its construction
as a conjugate of the constant/pullback identity square. Thus the completion unit is
invertible, which is exactly quotient-tower completeness at V.
No faithfulness of derived evaluations is invoked. -/
theorem AdicCoefficientDatum.push_complete (K : d.derived U)
    (hK : d.TowerComplete U K) : d.TowerComplete V ((d.push f).obj K) := by
  let : IsIso (d.completionUnit U K) := hK
  change IsIso (d.completionUnit V ((d.push f).obj K))
  have h := (d.towerProjection_properties f K).2.2
  have : IsIso (d.completionUnit V ((d.push f).obj K) ≫
      (completedRlim V (d.completedRing V)).map (d.towerProjection f K)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((completedRlim V (d.completedRing V)).map (d.towerProjection f K))

end AlgebraicGeometry.Scheme
