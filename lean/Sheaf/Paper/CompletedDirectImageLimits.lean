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
import all Sheaf.Paper.AdicCoefficientDatum
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all Sheaf.Paper.ConstantTowerDirectImageNormalization
import all Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.RightFractionDenseSubcategory
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Sheaf.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

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
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] completedAdicChangeData completedReductionCoefficient
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
  sorry

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
/-- The strict ordinary comparison and universal counits fix the derived comparison.
Source: blueprint tower compatibility, steps 1--3; Stacks 06YY and 0D6D
(blueprint: prop-weil-pbc-direct-image-limits). -/
def IsCompletedReductionPullbackComparison
    (τ : completedReductionTower V d ⋙ d.towerPull f ≅
        d.pull f ⋙ completedReductionTower U d) : Prop :=
  IsDerivedReductionPullbackComparison
    (completedReductionModuleTowerFunctor V d) (completedReductionModuleTowerFunctor U d)
    (proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f)) (d.towerModulePull f) (completedReductionOrdinaryPullbackIso d f)
    (completedReductionTower V d) (completedReductionTower U d)
    (coherenceReductionTowerCounit V d) (coherenceReductionTowerCounit U d)
    (CochainComplex.IsKFlatIndependentCoefficients (R := d.completedRing V)) τ

section DerivedPullComparison
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048

set_option backward.isDefEq.respectTransparency false in
private theorem restrictionLocalization
    {A : Type*} [Category A] {D : Type*} [Category D]
    (W : MorphismProperty A) [W.HasRightCalculusOfFractions]
    (L : A ⥤ D) [L.IsLocalization W] (P : ObjectProperty A)
    (res : ∀ X : A, ∃ (Y : P.FullSubcategory) (s : Y.obj ⟶ X), W s) :
    (P.ι ⋙ L).IsLocalization (W.inverseImage P.ι) := by
  let V := W.inverseImage P.ι
  obtain ⟨_, F, hF, ⟨e⟩⟩ :=
    rightFractionDenseSubcategory W inferInstance P res L V.Q
  have : F.IsEquivalence := hF
  have : (V.Q ⋙ F).IsLocalization V := inferInstance
  exact Functor.IsLocalization.of_iso V e

private theorem descendUnit
    {C D E : Type*} [Category C] [Category D] [Category E]
    (P : ObjectProperty C) (L : C ⥤ D) (W : MorphismProperty C)
    [(P.ι ⋙ L).IsLocalization (W.inverseImage P.ι)]
    (F G : D ⥤ E) (R : C ⥤ E) (α : L ⋙ F ⟶ R) (γ : L ⋙ G ⟶ R)
    (hγ : ∀ X : P.FullSubcategory, IsIso (γ.app X.obj)) :
    ∃! η : F ⟶ G, ∀ X : P.FullSubcategory,
      η.app (L.obj X.obj) = α.app X.obj ≫ inv (γ.app X.obj) := by
  let S := P.ι ⋙ L
  let V := W.inverseImage P.ι
  let τ : S ⋙ F ⟶ S ⋙ G :=
    { app := fun X ↦ α.app X.obj ≫ inv (γ.app X.obj)
      naturality := by
        intro X Y f
        change (L ⋙ F).map f.hom ≫ α.app Y.obj ≫ inv (γ.app Y.obj) =
          (α.app X.obj ≫ inv (γ.app X.obj)) ≫ (L ⋙ G).map f.hom
        rw [← Category.assoc, α.naturality, Category.assoc, Category.assoc]
        apply congrArg (α.app X.obj ≫ ·)
        apply (cancel_mono (γ.app Y.obj)).1
        simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
        rw [γ.naturality f.hom]
        simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp] }
  let E' := (Functor.whiskeringLeft P.FullSubcategory D E).obj S
  have : E'.Full := Localization.full_whiskeringLeft S V E
  refine ⟨E'.preimage τ, ?_, ?_⟩
  · intro X
    exact congrArg (fun k ↦ k.app X) (E'.map_preimage τ)
  · intro θ hθ
    apply Localization.natTrans_ext S V
    intro X
    exact (hθ X).trans (congrArg (fun k ↦ k.app X) (E'.map_preimage τ)).symm


private theorem descendIso
    {C D E : Type*} [Category C] [Category D] [Category E]
    (P : ObjectProperty C) (L : C ⥤ D) (W : MorphismProperty C)
    [(P.ι ⋙ L).IsLocalization (W.inverseImage P.ι)]
    (F G : D ⥤ E) (R : C ⥤ E) (α : L ⋙ F ⟶ R) (γ : L ⋙ G ⟶ R)
    (hα : ∀ X : P.FullSubcategory, IsIso (α.app X.obj))
    (hγ : ∀ X : P.FullSubcategory, IsIso (γ.app X.obj)) :
    ∃! η : F ≅ G, ∀ X : P.FullSubcategory,
      η.hom.app (L.obj X.obj) ≫ γ.app X.obj = α.app X.obj := by
  let S := P.ι ⋙ L
  let V := W.inverseImage P.ι
  obtain ⟨η, hη, hu⟩ := descendUnit P L W F G R α γ hγ
  let T := (Functor.whiskeringLeft P.FullSubcategory D E).obj S
  let : T.Full := Localization.full_whiskeringLeft S V E
  let : T.Faithful := Localization.faithful_whiskeringLeft S V E
  have happ (X : P.FullSubcategory) : IsIso ((T.map η).app X) := by
    change IsIso (η.app (L.obj X.obj))
    rw [hη X]
    let := hα X
    let := hγ X
    infer_instance
  have hT : IsIso (T.map η) := NatIso.isIso_of_isIso_app _
  let : IsIso η := isIso_of_reflects_iso η T
  refine ⟨asIso η, ?_, ?_⟩
  · intro X
    change η.app (L.obj X.obj) ≫ γ.app X.obj = _
    rw [hη X]
    let := hγ X
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  · intro η' hη'
    apply Iso.ext
    apply hu η'.hom
    intro X
    let := hγ X
    apply (cancel_mono (γ.app X.obj)).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact hη' X

private theorem descendIso_from_resolving
    {C D E : Type*} [Category C] [Category D] [Category E]
    (P P₀ : ObjectProperty C) (L : C ⥤ D) (W : MorphismProperty C)
    [W.HasRightCalculusOfFractions] [L.IsLocalization W]
    (res : ∀ X : C, ∃ (Y : P₀.FullSubcategory) (s : Y.obj ⟶ X), W s)
    (hP : ∀ X, P₀ X → P X)
    (F G : D ⥤ E) (R : C ⥤ E) (α : L ⋙ F ⟶ R) (γ : L ⋙ G ⟶ R)
    (hα : ∀ X : P.FullSubcategory, IsIso (α.app X.obj))
    (hγ : ∀ X : P₀.FullSubcategory, IsIso (γ.app X.obj)) :
    ∃! η : F ≅ G, ∀ X : P.FullSubcategory,
      η.hom.app (L.obj X.obj) ≫ γ.app X.obj = α.app X.obj := by
  have hres (X : C) : ∃ (Y : P.FullSubcategory) (s : Y.obj ⟶ X), W s := by
    obtain ⟨Y, s, hs⟩ := res X
    exact ⟨⟨Y.obj, hP Y.obj Y.property⟩, s, hs⟩
  let : (P.ι ⋙ L).IsLocalization (W.inverseImage P.ι) :=
    restrictionLocalization W L P hres
  have hγ' (X : P.FullSubcategory) : IsIso (γ.app X.obj) := by
    obtain ⟨Y, s, hs⟩ := res X.obj
    let : IsIso (L.map s) := Localization.inverts L W s hs
    let : IsIso (α.app X.obj) := hα X
    let : IsIso (α.app Y.obj) := hα ⟨Y.obj, hP Y.obj Y.property⟩
    have hi : IsIso (α.app Y.obj ≫ R.map s) := by
      rw [← α.naturality s]
      change IsIso (F.map (L.map s) ≫ α.app X.obj)
      infer_instance
    let : IsIso (R.map s) := IsIso.of_isIso_comp_left (α.app Y.obj) (R.map s)
    let : IsIso (γ.app Y.obj) := hγ Y
    have hi' : IsIso ((L ⋙ G).map s ≫ γ.app X.obj) := by
      rw [γ.naturality s]
      infer_instance
    have : IsIso ((L ⋙ G).map s) := by
      change IsIso (G.map (L.map s))
      infer_instance
    exact IsIso.of_isIso_comp_left ((L ⋙ G).map s) (γ.app X.obj)
  exact descendIso P L W F G R α γ hα hγ'

private theorem factorh_eq_factor
    {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    (F : B ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex B ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient B (.up ℤ)).obj K) =
      F.mapDerivedCategoryFactors.hom.app K := by
  rw [F.mapDerivedCategoryFactorsh_hom_app]
  simp only [quotientHomId, quotientInvId, homotopyFactorsInvId]
  erw [F.mapDerivedCategory.map_id, (DerivedCategory.Qh (C := C)).map_id]
  repeat' first | erw [Category.id_comp] | erw [Category.comp_id]

private theorem reductionCounit_eq
    {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    (F : B ⥤ C) [F.Additive] (L : DerivedCategory B ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (K : CochainComplex B ℤ) :
    reductionComplexCounit F L ε K =
      ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj K) := by
  have hid : (F.mapHomotopyCategoryFactors (.up ℤ)).hom.app K = 𝟙 _ := rfl
  simp only [reductionComplexCounit, quotientHomId, quotientInvId, hid]
  erw [L.map_id, (DerivedCategory.Qh (C := C)).map_id]
  repeat' first | erw [Category.id_comp] | erw [Category.comp_id]

section ModelPull
variable {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasDerivedCategory (ℕᵒᵖ ⥤ C)]
  (F : B ⥤ (ℕᵒᵖ ⥤ B)) [F.Additive] (G : C ⥤ (ℕᵒᵖ ⥤ C)) [G.Additive]
  (P : B ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  (H : (ℕᵒᵖ ⥤ B) ⥤ (ℕᵒᵖ ⥤ C)) [H.Additive]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  {M : CochainComplex B ℤ → Prop} {N : CochainComplex C ℤ → Prop}
  (e : F ⋙ H ≅ P ⋙ G)
  (LF : DerivedCategory B ⥤ DerivedCategory (ℕᵒᵖ ⥤ B))
  (LG : DerivedCategory C ⥤ DerivedCategory (ℕᵒᵖ ⥤ C))
  (εF : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  (εG : DerivedCategory.Qh ⋙ LG ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  (hiF : ∀ K : CochainComplex B ℤ, M K →
    IsIso (εF.app ((HomotopyCategory.quotient B (.up ℤ)).obj K)))
  (hiG : ∀ K : CochainComplex C ℤ, N K →
    IsIso (εG.app ((HomotopyCategory.quotient C (.up ℤ)).obj K)))

private abbrev modelPullCommon :=
  P.mapHomotopyCategory (.up ℤ) ⋙ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh

private abbrev modelPullSourceCounit :
    DerivedCategory.Qh ⋙ (LF ⋙ H.mapDerivedCategory) ⟶
      modelPullCommon G P :=
  (Functor.associator _ _ _).inv ≫ Functor.whiskerRight εF H.mapDerivedCategory ≫
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (F.mapHomotopyCategory (.up ℤ)) H.mapDerivedCategoryFactorsh.hom ≫
        (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight
            ((Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom ≫
              (Functor.mapHomotopyCategoryCompIso (Iso.refl (P ⋙ G)) (.up ℤ)).inv)
            DerivedCategory.Qh

private abbrev modelPullTargetCounit :
    DerivedCategory.Qh ⋙ (P.mapDerivedCategory ⋙ LG) ⟶
      modelPullCommon G P :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight P.mapDerivedCategoryFactorsh.hom LG ≫
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (P.mapHomotopyCategory (.up ℤ)) εG ≫
          (Functor.associator _ _ _).inv

include hiF hiG in
private theorem modelPullHomotopy_existsUnique
    (M₀ : CochainComplex B ℤ → Prop)
    (h₀ : ∀ K, M₀ K → M K)
    (res : ∀ K : CochainComplex B ℤ, ∃ (L : CochainComplex B ℤ) (s : L ⟶ K),
      M₀ L ∧ QuasiIso s)
    (hmap : ∀ K, M₀ K → N ((P.mapHomologicalComplex (.up ℤ)).obj K)) :
    ∃! η : LF ⋙ H.mapDerivedCategory ≅ P.mapDerivedCategory ⋙ LG,
      ∀ K : CochainComplex B ℤ, M K →
        η.hom.app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient B (.up ℤ)).obj K)) ≫
          (modelPullTargetCounit G P LG εG).app
            ((HomotopyCategory.quotient B (.up ℤ)).obj K) =
          (modelPullSourceCounit F G P H e LF εF).app
            ((HomotopyCategory.quotient B (.up ℤ)).obj K) := by
  let Q := HomotopyCategory.quotient B (.up ℤ)
  let S : ObjectProperty (HomotopyCategory B (.up ℤ)) :=
    fun K ↦ ∃ L : CochainComplex B ℤ, M L ∧ Q.obj L = K
  let S₀ : ObjectProperty (HomotopyCategory B (.up ℤ)) :=
    fun K ↦ ∃ L : CochainComplex B ℤ, M₀ L ∧ Q.obj L = K
  have hS (K) (hK : S₀ K) : S K := by
    obtain ⟨L, hL, rfl⟩ := hK
    exact ⟨L, h₀ L hL, rfl⟩
  have hr (K : HomotopyCategory B (.up ℤ)) :
      ∃ (L : S₀.FullSubcategory) (s : L.obj ⟶ K),
        HomotopyCategory.quasiIso B (.up ℤ) s := by
    obtain ⟨K, rfl⟩ := K.quotient_obj_surjective
    obtain ⟨L, s, hL, hs⟩ := res K
    exact ⟨⟨Q.obj L, L, hL, rfl⟩, Q.map s,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hα (K : S.FullSubcategory) :
      IsIso ((modelPullSourceCounit F G P H e LF εF).app K.obj) := by
    obtain ⟨L, hL, hLK⟩ := K.property
    let := hiF L hL
    rw [← hLK]
    simp only [modelPullSourceCounit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp]
    infer_instance
  have hγ (K : S₀.FullSubcategory) :
      IsIso ((modelPullTargetCounit G P LG εG).app K.obj) := by
    obtain ⟨L, hL, hLK⟩ := K.property
    rw [← hLK]
    have : IsIso (εG.app ((P.mapHomotopyCategory (.up ℤ)).obj (Q.obj L))) := by
      change IsIso (εG.app ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((P.mapHomologicalComplex (.up ℤ)).obj L)))
      exact hiG _ (hmap L hL)
    simp only [modelPullTargetCounit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id]
    infer_instance
  obtain ⟨η, hη, hu⟩ := descendIso_from_resolving S S₀ DerivedCategory.Qh
    (HomotopyCategory.quasiIso B (.up ℤ)) hr hS
    (LF ⋙ H.mapDerivedCategory) (P.mapDerivedCategory ⋙ LG)
    (modelPullCommon G P) (modelPullSourceCounit F G P H e LF εF)
    (modelPullTargetCounit G P LG εG) hα hγ
  refine ⟨η, ?_, ?_⟩
  · intro K hK
    exact hη ⟨Q.obj K, K, hK, rfl⟩
  · intro η' hη'
    apply hu η'
    intro K
    obtain ⟨L, hL, hLK⟩ := K.property
    rw [← hLK]
    exact hη' L hL

private theorem modelPull_normalized_iff
    (η : LF ⋙ H.mapDerivedCategory ≅ P.mapDerivedCategory ⋙ LG)
    (K : CochainComplex B ℤ) :
    (η.hom.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient B (.up ℤ)).obj K)) ≫
        (modelPullTargetCounit G P LG εG).app
          ((HomotopyCategory.quotient B (.up ℤ)).obj K) =
      (modelPullSourceCounit F G P H e LF εF).app
        ((HomotopyCategory.quotient B (.up ℤ)).obj K)) ↔
    (η.hom.app (DerivedCategory.Q.obj K) ≫
        LG.map (P.mapDerivedCategoryFactors.hom.app K) ≫
          reductionComplexCounit G LG εG ((P.mapHomologicalComplex (.up ℤ)).obj K) =
      H.mapDerivedCategory.map (reductionComplexCounit F LF εF K) ≫
        H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K)) := by
  simp only [modelPullSourceCounit, modelPullTargetCounit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  rw [factorh_eq_factor P K]
  erw [factorh_eq_factor H ((F.mapHomologicalComplex (.up ℤ)).obj K)]
  rw [reductionCounit_eq F LF εF K,
    reductionCounit_eq G LG εG ((P.mapHomologicalComplex (.up ℤ)).obj K)]
  have he : DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom.app
          ((HomotopyCategory.quotient B (.up ℤ)).obj K) ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (P ⋙ G)) (.up ℤ)).inv.app
          ((HomotopyCategory.quotient B (.up ℤ)).obj K)) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K) := by
    change DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (ℕᵒᵖ ⥤ C) (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app K) ≫
       (HomotopyCategory.quotient (ℕᵒᵖ ⥤ C) (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (P ⋙ G)) (.up ℤ)).inv.app K)) = _
    rw [← Functor.map_comp]
    have hv : (Functor.mapHomologicalComplexCompIso (Iso.refl (P ⋙ G)) (.up ℤ)).inv.app K =
        𝟙 (((P ⋙ G).mapHomologicalComplex (.up ℤ)).obj K) := rfl
    rw [hv, Category.comp_id]
    rfl
  rw [he]
  rfl


include hiF hiG in
private theorem modelPull_existsUnique
    (M₀ : CochainComplex B ℤ → Prop)
    (h₀ : ∀ K, M₀ K → M K)
    (res : ∀ K : CochainComplex B ℤ, ∃ (L : CochainComplex B ℤ) (s : L ⟶ K),
      M₀ L ∧ QuasiIso s)
    (hmap : ∀ K, M₀ K → N ((P.mapHomologicalComplex (.up ℤ)).obj K)) :
    ∃! η : LF ⋙ H.mapDerivedCategory ≅ P.mapDerivedCategory ⋙ LG,
      IsDerivedReductionPullbackComparison F G P H e LF LG εF εG M η := by
  obtain ⟨η, hη, hu⟩ := modelPullHomotopy_existsUnique F G P H e LF LG εF εG hiF hiG M₀ h₀ res hmap
  refine ⟨η, ?_, ?_⟩
  · intro K hK
    simpa only [reductionComplexCounit] using
      (modelPull_normalized_iff F G P H e LF LG εF εG η K).mp (hη K hK)
  · intro η' hη'
    apply hu η'
    intro K hK
    apply (modelPull_normalized_iff F G P H e LF LG εF εG η' K).mpr
    simpa only [reductionComplexCounit] using
      hη' K hK

end ModelPull

private theorem flatKFlatResolution (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (K : CochainComplex (proEtaleRingModules T R) ℤ) :
    ∃ (L : CochainComplex (proEtaleRingModules T R) ℤ) (s : L ⟶ K),
      (CochainComplex.IsKFlatIndependentCoefficients (R := R) L ∧ ∀ n : ℤ,
        SheafOfModules.IsFlatOnSite (J := ProEt.topology T) (R := R) (L.X n)) ∧
        QuasiIso s := by
  obtain ⟨L, s, hL, hflat, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) K
  refine ⟨L, s, ⟨hL, ?_⟩, hs⟩
  intro n
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (L.X n)).symm (hflat n)

private theorem pullback_kFlat {U V : Scheme.{t}} (f : U ⟶ V)
    (R : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj R ≅ S)
    (P : CochainComplex (proEtaleRingModules V R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hflat : ∀ n : ℤ,
      SheafOfModules.IsFlatOnSite (J := ProEt.topology V) (R := R) (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := S)
      (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P) := by
  obtain ⟨I, hI⟩ := proEtaleAlgebraicInverseImage_exists f R
  have : PreservesFiniteLimits (proEtaleSheafInverseImage f (Type (t + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage f (𝟙 V)).2.2.2.1
  let C := proEtaleRingModules V R
  let D := proEtaleRingModules U ((proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj R)
  have hmap' (F : C ⥤ D) (h : I.modules = F) {N N' : C} (a : N ⟶ N') :
      SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1} c.hom (F.obj N) (F.map a) =
        eqToHom (congrArg (fun G : C ⥤ D ↦
          SheafOfModules.changeOfRings.{t, t + 1, t + 1} c.hom (G.obj N)) h.symm) ≫
        SheafOfModules.changeOfRingsHom.{t, t + 1, t + 1} c.hom
          (I.modules.obj N) (I.modules.map a) ≫
        eqToHom (congrArg (fun G : C ⥤ D ↦
          SheafOfModules.changeOfRings.{t, t + 1, t + 1} c.hom (G.obj N')) h.symm).symm := by
    subst F
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (SheafOfModules.isKFlat_ringedToposPullback
    (proEtaleSheafInverseImage f (Type (t + 1)))
    (proEtaleSheafDirectImage f (Type (t + 1)))
    (proEtaleSheafAdjunction f (Type (t + 1))) I c.hom
    (proEtaleRingModulePullback f R S c)
    (fun N ↦ congrArg (fun F : C ⥤ D ↦
      SheafOfModules.changeOfRings.{t, t + 1, t + 1} c.hom (F.obj N)) hI.symm)
    (fun a ↦ hmap' _ hI a) P hP hflat).1


private theorem reductionCounitIso (T : Scheme.{t})
    (K : CochainComplex (reductionModules T (d.completedRing T)) ℤ)
    (hK : CochainComplex.IsKFlatIndependentCoefficients (R := d.completedRing T) K) :
    IsIso ((coherenceReductionTowerCounit T d).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) :=
  (completedReductionTower_properties T d).2.2 K hK

private theorem completedKFlatPullback
    (K : CochainComplex (reductionModules V (d.completedRing V)) ℤ)
    (hK : CochainComplex.IsKFlatIndependentCoefficients (R := d.completedRing V) K)
    (hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite
      (J := ProEt.topology V) (R := d.completedRing V) (K.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := d.completedRing U)
      (((proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
        (d.integralRingIso f)).mapHomologicalComplex (.up ℤ)).obj K) :=
  pullback_kFlat f _ _ _ K hK hflat

/-- The canonical derived comparison is uniquely fixed on K-flat representatives by the
strict ordinary comparison and the two universal derived counits.
Source: blueprint tower compatibility, steps 1--3; Stacks 06YY and 0D6D
(blueprint: prop-weil-pbc-direct-image-limits).
Proof: choose a K-flat flat-term representative P. Its pullback remains K-flat with flat
terms. The two reduction-tower counits are invertible there, so the displayed equation
uniquely defines the component by the ordinary strict tower isomorphism above. Naturality
for chain maps, compatible homotopies, and inverse quasi-isomorphisms descends this to
all derived objects. Every object has a K-flat representative; hence the natural
isomorphism is unique. Its evaluation is chi, since both have the same ordinary tensor
normalization, and the transition compatibility is retained from the strict comparison. -/
theorem completedReductionPullbackIso_existsUnique :
    ∃! τ : completedReductionTower V d ⋙ d.towerPull f ≅
        d.pull f ⋙ completedReductionTower U d,
      IsCompletedReductionPullbackComparison d f τ := by
  exact modelPull_existsUnique
    (completedReductionModuleTowerFunctor V d) (completedReductionModuleTowerFunctor U d)
    (proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f)) (d.towerModulePull f) (completedReductionOrdinaryPullbackIso d f)
    (completedReductionTower V d) (completedReductionTower U d)
    (coherenceReductionTowerCounit V d) (coherenceReductionTowerCounit U d)
    (reductionCounitIso d V) (reductionCounitIso d U)
    (fun K : CochainComplex (reductionModules V (d.completedRing V)) ℤ ↦
      CochainComplex.IsKFlatIndependentCoefficients (R := d.completedRing V) K ∧
        ∀ n : ℤ, SheafOfModules.IsFlatOnSite
          (J := ProEt.topology V) (R := d.completedRing V) (K.X n))
    (fun _ h ↦ h.1) (flatKFlatResolution V (d.completedRing V))
    (fun K h ↦ completedKFlatPullback d f K h.1 h.2)

end DerivedPullComparison

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
  sorry

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
