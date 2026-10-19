/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q96
-/
module

public import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Sheaf.Paper.SmoothPurityTowerEvaluationAdjoint
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology

/-!
# Acyclic components of injective coefficient towers

Source: blueprint main-20261015, sec-smooth-purity, sk-lem-sp-tower-levels,
`sk-lem-sp-tower-levels-acyclic.md` and its proof; Stacks Tags 03FD, 015E and 05TH
(blueprint: det-sp-tower-injective-components).

Index n denotes the positive level n+1. The tower direct image is the actual
product-site module pushforward. Its scalar map is the existing constant-section
map, so both coefficients and transitions are fixed, including for the identity map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Enough injectives for the recorded tower category, from its Grothendieck structure.
Source: Stacks 079H; blueprint proof, step 1
(blueprint: det-sp-tower-injective-components). -/
instance spTowerEnoughInjectives (T : Scheme.{t}) :
    EnoughInjectives (spCoefficientTowers l E T) :=
  letI := (Classical.choice (sp_coefficient_towers_abelian l E T)).grothendieck
  inferInstance

/-- The standard ordinary localization of the actual tower category.
Source: blueprint proof, step 1 (blueprint: det-sp-tower-injective-components). -/
instance spTowerHasDerived (T : Scheme.{t}) :
    HasDerivedCategory (spCoefficientTowers l E T) := HasDerivedCategory.standard _

/-- Enough injectives for ring-sheaf modules in the common larger universe.
Source: Stacks 079H; blueprint proof, step 1
(blueprint: det-sp-tower-injective-components). -/
instance spRingModulesEnoughInjectives (T : Scheme.{t})
    (R : Sheaf (Scheme.ProEt.topology T) RingCat.{max u (t + 1)}) :
    EnoughInjectives (ringedSiteModules.{max u (t + 1)} R) :=
  letI := SheafOfModules.isGrothendieckAbelianOfUniverses.{t + 1, t, max u (t + 1), 0}
    (Scheme.ProEt.topology T) R
  inferInstance

/-- Standard derived localization at a coefficient level.
Source: blueprint proof, step 1 (blueprint: det-sp-tower-injective-components). -/
instance spRingModulesHasDerived (T : Scheme.{t})
    (R : Sheaf (Scheme.ProEt.topology T) RingCat.{max u (t + 1)}) :
    HasDerivedCategory (ringedSiteModules.{max u (t + 1)} R) := HasDerivedCategory.standard _

/-- Sections of module sheaves form an additive functor.
Source: blueprint proof, step 3 (blueprint: det-sp-tower-injective-components). -/
instance spModuleEvaluationAdditive (T : Scheme.{t})
    (R : Sheaf (Scheme.ProEt.topology T) RingCat.{max u (t + 1)}) (U : T.ProEtᵒᵖ) :
    (SheafOfModules.evaluation.{max u (t + 1)} R U).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Evaluation uses the published, sectionwise normalized uncurrying equivalence.
Source: blueprint proof, exact evaluation (blueprint: det-sp-tower-injective-components). -/
instance spTowerEvaluationAdditive (T : Scheme.{t})
    (d : SpCoefficientTowersAbelian l E T) (n : ℕ) :
    (spCoefficientEvaluation l E T d.equivalence n).Additive :=
  letI := d.equivalenceAdditive
  inferInstance

/-- Exact evaluation preserves finite limits, by the recorded coefficient-tower theorem.
Source: blueprint proof, exact evaluation (blueprint: det-sp-tower-injective-components). -/
instance spTowerEvaluationLimits (T : Scheme.{t})
    (d : SpCoefficientTowersAbelian l E T) (n : ℕ) :
    PreservesFiniteLimits (spCoefficientEvaluation l E T d.equivalence n) :=
  d.evaluationLimits n

/-- Exact evaluation preserves finite colimits, by the recorded coefficient-tower theorem.
Source: blueprint proof, exact evaluation (blueprint: det-sp-tower-injective-components). -/
instance spTowerEvaluationColimits (T : Scheme.{t})
    (d : SpCoefficientTowersAbelian l E T) (n : ℕ) :
    PreservesFiniteColimits (spCoefficientEvaluation l E T d.equivalence n) :=
  d.evaluationColimits n

variable {T S : Scheme.{t}} (g : T ⟶ S)

/-- Base change on the level/site product, fixing the level.
Source: blueprint, levelwise direct image (blueprint: det-sp-tower-injective-components). -/
def spTowerBaseChange : ℕ × S.ProEt ⥤ ℕ × T.ProEt :=
  (𝟭 ℕ).prod (Scheme.proEtaleBaseChange g)

/-- The canonical constant-section scalar map at a product-site object.
Source: Stacks 0H7J; blueprint, coefficient identification
(blueprint: det-sp-tower-injective-components). -/
def spTowerRingMapApp (X : (ℕ × S.ProEt)ᵒᵖ) :
    (spCoefficientPresheaf l E S).obj X ⟶
      (spCoefficientPresheaf l E T).obj ((spTowerBaseChange g).op.obj X) :=
  (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map
    ((Scheme.coefficientProEtaleDirectRingMap g
      (CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (X.unop.1 + 1))))).hom.app
          (op X.unop.2))

private theorem coefficientRingMap_naturality
    {A B : CommRingCat.{max u (t + 1)}} (f : A ⟶ B) :
    (constantSheaf (Scheme.ProEt.topology S) CommRingCat.{max u (t + 1)}).map f ≫
        Scheme.coefficientProEtaleDirectRingMap g B =
      Scheme.coefficientProEtaleDirectRingMap g A ≫
        ((Scheme.proEtaleBaseChange g).sheafPushforwardContinuous
          CommRingCat.{max u (t + 1)} (Scheme.ProEt.topology S)
          (Scheme.ProEt.topology T)).map
            ((constantSheaf (Scheme.ProEt.topology T)
              CommRingCat.{max u (t + 1)}).map f) := by
  apply (sheafificationAdjunction (Scheme.ProEt.topology S)
    CommRingCat.{max u (t + 1)}).homEquiv _ _ |>.injective
  dsimp only [constantSheaf, Functor.comp_map]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [Scheme.coefficientProEtaleDirectRingMap, constantSheaf,
    Functor.comp_obj, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  exact congr_app ((sheafificationAdjunction (Scheme.ProEt.topology T)
    CommRingCat.{max u (t + 1)}).unit.naturality
      ((Functor.const T.ProEtᵒᵖ).map f)) ((Scheme.proEtaleBaseChange g).op.obj U)

/-- Constant-section coefficient maps commute with restrictions and quotient reductions.
Source: blueprint, levelwise direct image (blueprint: det-sp-tower-injective-components).
Proof: site naturality is naturality of the published constant-section map. For level
maps both composites send an integer to its reduction as a constant section; uniqueness
of the extension through sheafification makes them equal. A product arrow factors as
its level arrow and site arrow, giving the displayed naturality for every arrow. -/
theorem spTowerRingMap_naturality {X Y : (ℕ × S.ProEt)ᵒᵖ} (f : X ⟶ Y) :
    (spCoefficientPresheaf l E S).map f ≫ spTowerRingMapApp l E g Y =
      spTowerRingMapApp l E g X ≫
        (spCoefficientPresheaf l E T).map ((spTowerBaseChange g).op.map f) := by
  let P := (Scheme.proEtaleBaseChange g).sheafPushforwardContinuous
    RingCat.{max u (t + 1)} (Scheme.ProEt.topology S) (Scheme.ProEt.topology T)
  let φ : spCoefficientRings l E S ⟶ spCoefficientRings l E T ⋙ P :=
    NatTrans.ofOpSequence
      (fun n ↦ ⟨Functor.whiskerRight
        (Scheme.coefficientProEtaleDirectRingMap g
          (CommRingCat.of (ULift.{t + 1}
            (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))))).hom
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩)
      (fun n ↦ by
        simp only [spCoefficientRings, Functor.ofOpSequence_map_homOfLE_succ,
          Functor.comp_map]
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext U
        have h := coefficientRingMap_naturality.{t, u} (g := g)
          (CommRingCat.ofHom
            (ULift.ringEquiv.{u, t + 1}.symm.toRingHom.comp
              ((Ideal.Quotient.factorPowSucc (spEllIdeal l E) (n + 1)).comp
                ULift.ringEquiv.{u, t + 1}.toRingHom)))
        exact congrArg
          ((forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map)
          (congrArg (fun q ↦ q.hom.app U) h))
  let ψ := Functor.uncurry.map
    (Functor.whiskerRight φ (sheafToPresheaf (Scheme.ProEt.topology S)
      RingCat.{max u (t + 1)}))
  exact ψ.naturality ((prodOpEquiv (C := ℕ) (D := S.ProEt)).functor.map f)

/-- The structural ring map on the product site, with the actual coefficient reductions.
Source: blueprint, levelwise direct image (blueprint: det-sp-tower-injective-components). -/
def spTowerRingMap : spCoefficientPresheaf l E S ⟶
    (spTowerBaseChange g).op ⋙ spCoefficientPresheaf l E T where
  app := spTowerRingMapApp l E g
  naturality := fun {_ _} f ↦ spTowerRingMap_naturality l E g f

/-- Product-site module pushforward preserves the levelwise sheaf condition.
Source: blueprint, definition of g_(star,bullet)
(blueprint: det-sp-tower-injective-components).
Proof: at level n the underlying abelian presheaf is precomposition with base change.
That site functor is continuous, so it sends a sheaf to a sheaf by ordinary direct
image. Restricting the scalar action does not change this underlying abelian sheaf. -/
theorem spTowerPush_sheaf (M : spCoefficientTowers l E T) :
    spCoefficientTowerSheafCondition l E S
      ((PresheafOfModules.pushforward (spTowerRingMap l E g)).obj M.obj) := by
  intro n
  exact ((Scheme.proEtaleBaseChange g).sheafPushforwardContinuous
    AddCommGrpCat.{max u (t + 1)} (Scheme.ProEt.topology S) (Scheme.ProEt.topology T)).obj
      ⟨_, M.property n⟩ |>.property

/-- Ordinary direct image of coefficient towers, defined on actual product-site modules.
Every section, restriction, transition and morphism is pushed forward componentwise.
Source: blueprint, definition of g_(star,bullet)
(blueprint: det-sp-tower-injective-components). -/
def spTowerPush : spCoefficientTowers l E T ⥤ spCoefficientTowers l E S where
  obj M := ⟨(PresheafOfModules.pushforward (spTowerRingMap l E g)).obj M.obj,
    spTowerPush_sheaf l E g M⟩
  map f := ObjectProperty.homMk
    ((PresheafOfModules.pushforward (spTowerRingMap l E g)).map f.hom)

/-- Ordinary module direct image at the positive level n+1, using the canonical
constant-section coefficient map in the common coefficient universe.
Source: blueprint, finite-level direct image (blueprint: det-sp-tower-injective-components). -/
abbrev spLevelPush (n : ℕ) :=
  Scheme.coefficientProEtaleModuleDirectImage.{t, u} g
    (CommRingCat.of (ULift.{t + 1}
      (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))))

/-- The componentwise tower direct image is additive and left exact.
Source: blueprint proof, step 7 (blueprint: det-sp-tower-injective-components).
Proof: addition is componentwise. Kernels and finite limits are levelwise in the tower
category. Each ordinary module direct image is a right adjoint and preserves finite
limits; their universal factorizations respect transitions, giving the tower limits. -/
theorem spTowerPush_properties :
    (spTowerPush l E g).Additive ∧ PreservesFiniteLimits (spTowerPush l E g) := by
  have inclusionLimits (X : Scheme.{t}) :
      PreservesFiniteLimits (spCoefficientTowerSheafCondition l E X).ι := by
    have (J : Type) [SmallCategory J] [FinCategory J] :
        (spCoefficientTowerSheafCondition l E X).IsClosedUnderLimitsOfShape J := by
      constructor
      rintro M ⟨c⟩ n
      let V :=
        PresheafOfModules.toPresheaf.{max u (t + 1)} (spCoefficientPresheaf l E X) ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{max u (t + 1)}).obj
          (Prod.sectR n X.ProEt).op
      exact ObjectProperty.prop_of_isLimit (P := Presheaf.IsSheaf (Scheme.ProEt.topology X))
        (isLimitOfPreserves V c.isLimit) (fun j ↦ c.prop_diag_obj j n)
    exact ⟨fun J _ _ ↦ inferInstance⟩
  let P := PresheafOfModules.pushforward.{max u (t + 1)} (spTowerRingMap l E g)
  have : PreservesFiniteLimits P := by
    constructor
    intro J _ _
    constructor
    intro K
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦
      isLimitOfPreserves
        (PresheafOfModules.evaluation (spCoefficientPresheaf l E T)
          ((spTowerBaseChange g).op.obj X) ⋙
            ModuleCat.restrictScalars ((spTowerRingMap l E g).app X).hom) hc)⟩
  have := inclusionLimits T
  have : PreservesFiniteLimits
      (spTowerPush l E g ⋙ (spCoefficientTowerSheafCondition l E S).ι) :=
    inferInstanceAs (PreservesFiniteLimits
      ((spCoefficientTowerSheafCondition l E T).ι ⋙ P))
  have := preservesFiniteLimits_of_reflects_of_preserves
    (spTowerPush l E g) (spCoefficientTowerSheafCondition l E S).ι
  exact ⟨Functor.additive_of_preserves_binary_products _, inferInstance⟩

/-- Componentwise additivity of tower direct image.
Source: blueprint proof, step 7 (blueprint: det-sp-tower-injective-components). -/
instance spTowerPushAdditive : (spTowerPush l E g).Additive :=
  (spTowerPush_properties l E g).1

/-- Left exactness of tower direct image.
Source: blueprint proof, step 7 (blueprint: det-sp-tower-injective-components). -/
instance spTowerPushLimits : PreservesFiniteLimits (spTowerPush l E g) :=
  (spTowerPush_properties l E g).2

/-- The published ordinary module direct image is additive.
Source: blueprint, finite-level direct image (blueprint: det-sp-tower-injective-components). -/
instance spCoefficientModulePushAdditive (A : CommRingCat.{max u (t + 1)}) :
    (Scheme.coefficientProEtaleModuleDirectImage.{t, u} g A).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The published ordinary module direct image is left exact, being a right adjoint.
Source: blueprint, finite-level direct image (blueprint: det-sp-tower-injective-components). -/
instance spLevelPushLimits (n : ℕ) : PreservesFiniteLimits (spLevelPush l E g n) :=
  inferInstance

private theorem moduleHom_fun_heq.{v, w} {R : Type w} [Ring R]
    {M M' N N' : ModuleCat.{v} R} (hM : M = M') (hN : N = N')
    {f : M ⟶ N} {f' : M' ⟶ N'} (h : HEq f f') :
    HEq (fun x ↦ f x) (fun x ↦ f' x) := by
  subst M'
  subst N'
  cases h
  rfl

private theorem evaluationRestriction_fun_heq (X : Scheme.{t})
    (d : SpCoefficientTowersAbelian l E X) (M : spCoefficientTowers l E X)
    (n : ℕ) {U V : X.ProEtᵒᵖ} (f : U ⟶ V) :
    HEq (fun x ↦ ((spCoefficientEvaluation l E X d.equivalence n).obj M).val.map f x)
      (fun x ↦ M.obj.map (Prod.mkHom (𝟙 n) f.unop).op x) := by
  refine moduleHom_fun_heq
    (f := ((spCoefficientEvaluation l E X d.equivalence n).obj M).val.map f)
    (f' := M.obj.map (Prod.mkHom (𝟙 n) f.unop).op)
    (eq_of_heq (d.sections M n U)) ?_ (d.restrictions M n f)
  convert congrArg (ModuleCat.restrictScalars
    (((spCoefficientRing l E X n).obj).map f).hom).obj
      (eq_of_heq (d.sections M n V)) using 1 <;>
    simp [spCoefficientPresheaf, spCoefficientRings, spCoefficientRing,
      spCoefficientCommRings, derivedChangeRingIndependentCoefficients, systemEvaluation,
      Functor.ofOpSequence, Functor.ofSequence, Functor.OfSequence.map_id]

private theorem moduleRestriction_naturality.{v, w} {R S : Type w} [Ring R] [Ring S]
    (φ : R →+* S) {M M' : ModuleCat.{v} R} {N N' : ModuleCat.{v} S}
    (hM : M = M') (hN : N = N')
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N)
    (f' : M' ⟶ (ModuleCat.restrictScalars φ).obj N')
    (h : HEq (fun x ↦ f x) (fun x ↦ f' x)) :
    f ≫ (ModuleCat.restrictScalars φ).map (eqToHom hN) = eqToHom hM ≫ f' := by
  subst M'
  subst N'
  ext x
  exact congrFun (eq_of_heq h) x

private theorem moduleHom_naturality.{v, w} {R : Type w} [Ring R]
    {M M' N N' : ModuleCat.{v} R} (hM : M = M') (hN : N = N')
    (f : M ⟶ N) (f' : M' ⟶ N')
    (h : HEq (fun x ↦ f x) (fun x ↦ f' x)) :
    f ≫ eqToHom hN = eqToHom hM ≫ f' := by
  subst M'
  subst N'
  ext x
  exact congrFun (eq_of_heq h) x

private theorem moduleEqToHom_apply_heq.{v, w} {R : Type w} [Ring R]
    {M N : ModuleCat.{v} R} (h : M = N) (x : M) : HEq (eqToHom h x) x := by
  subst N
  rfl

variable (dT : SpCoefficientTowersAbelian l E T) (dS : SpCoefficientTowersAbelian l E S)

private theorem towerEvaluation_sections (n : ℕ) (M : spCoefficientTowers l E T)
    (U : S.ProEtᵒᵖ) :
    ((spCoefficientEvaluation l E S dS.equivalence n).obj
        ((spTowerPush l E g).obj M)).val.obj U =
      ((spLevelPush l E g n).obj
        ((spCoefficientEvaluation l E T dT.equivalence n).obj M)).val.obj U := by
  exact (eq_of_heq (dS.sections ((spTowerPush l E g).obj M) n U)).trans
    (congrArg (ModuleCat.restrictScalars
      ((spTowerRingMap l E g).app (op (n, U.unop))).hom).obj
        (eq_of_heq (dT.sections M n ((Scheme.proEtaleBaseChange g).op.obj U)))).symm

/-- Evaluation commutes with the actual tower direct image, by the identity on sections.
Source: blueprint, levelwise direct image (blueprint: det-sp-tower-injective-components).
Proof: both composites have sections M_(n+1)(T times_S U), with the action through the
same constant-section coefficient map. The four normalization fields of dT and dS
identify their restrictions and linear maps. The identity of these sections is a
natural linear isomorphism. Sectionwise faithfulness proves its uniqueness. -/
theorem spTowerEvaluationIso_existsUnique (n : ℕ) :
    ∃! e : spTowerPush l E g ⋙ spCoefficientEvaluation l E S dS.equivalence n ≅
        spCoefficientEvaluation l E T dT.equivalence n ⋙ spLevelPush l E g n,
      ∀ (M : spCoefficientTowers l E T) (U : S.ProEtᵒᵖ)
        (x : ((spCoefficientEvaluation l E S dS.equivalence n).obj
          ((spTowerPush l E g).obj M)).val.obj U),
        HEq ((e.hom.app M).val.app U x) x := by
  let F := spTowerPush l E g ⋙ spCoefficientEvaluation l E S dS.equivalence n
  let G := spCoefficientEvaluation l E T dT.equivalence n ⋙ spLevelPush l E g n
  let e : F ≅ G := NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget (spCoefficientRing l E S n)).preimageIso
      (PresheafOfModules.isoMk
        (fun U ↦ eqToIso (towerEvaluation_sections l E g dT dS n M U))
        (fun {U V} f ↦ by
          apply moduleRestriction_naturality _
            (towerEvaluation_sections l E g dT dS n M U)
            (towerEvaluation_sections l E g dT dS n M V)
          exact (evaluationRestriction_fun_heq l E S dS
            ((spTowerPush l E g).obj M) n f).trans
              (evaluationRestriction_fun_heq l E T dT M n
                ((Scheme.proEtaleBaseChange g).op.map f)).symm))) (by
    intro M N f
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply moduleHom_naturality
      (towerEvaluation_sections l E g dT dS n M U)
      (towerEvaluation_sections l E g dT dS n N U)
    have hS := moduleHom_fun_heq
      (eq_of_heq (dS.sections ((spTowerPush l E g).obj M) n U))
      (eq_of_heq (dS.sections ((spTowerPush l E g).obj N) n U))
      (dS.morphisms ((spTowerPush l E g).map f) n U)
    have hT := moduleHom_fun_heq
      (eq_of_heq (dT.sections M n ((Scheme.proEtaleBaseChange g).op.obj U)))
      (eq_of_heq (dT.sections N n ((Scheme.proEtaleBaseChange g).op.obj U)))
      (dT.morphisms f n ((Scheme.proEtaleBaseChange g).op.obj U))
    exact hS.trans hT.symm)
  have he : ∀ (M : spCoefficientTowers l E T) (U : S.ProEtᵒᵖ)
      (x : ((spCoefficientEvaluation l E S dS.equivalence n).obj
        ((spTowerPush l E g).obj M)).val.obj U),
      HEq ((e.hom.app M).val.app U x) x := by
    intro M U x
    exact moduleEqToHom_apply_heq (towerEvaluation_sections l E g dT dS n M U) x
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  ext M U x
  exact eq_of_heq ((he' M U x).trans (he M U x).symm)

/-- The canonical underived evaluation identity, fixed by the identity on sections.
Source: blueprint, levelwise direct image (blueprint: det-sp-tower-injective-components). -/
def spTowerEvaluationIso (n : ℕ) :
    spTowerPush l E g ⋙ spCoefficientEvaluation l E S dS.equivalence n ≅
      spCoefficientEvaluation l E T dT.equivalence n ⋙ spLevelPush l E g n :=
  (spTowerEvaluationIso_existsUnique l E g dT dS n).exists.choose

/-- The same evaluation identity on bounded below homotopy categories.
Source: blueprint proof, step 7 (blueprint: det-sp-tower-injective-components). -/
def spTowerEvaluationHomotopyIso (n : ℕ) :
    (spTowerPush l E g).mapHomotopyCategoryPlus ⋙
        (spCoefficientEvaluation l E S dS.equivalence n).mapHomotopyCategoryPlus ≅
      (spCoefficientEvaluation l E T dT.equivalence n).mapHomotopyCategoryPlus ⋙
        (spLevelPush l E g n).mapHomotopyCategoryPlus :=
  letI : (spLevelPush l E g n).Additive :=
    spCoefficientModulePushAdditive g (CommRingCat.of (ULift.{t + 1}
      (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))))
  letI : (spCoefficientEvaluation l E T dT.equivalence n ⋙ spLevelPush l E g n).Additive :=
    inferInstance
  Functor.mapHomotopyCategoryPlusCompIso
      (F := spTowerPush l E g)
      (G := spCoefficientEvaluation l E S dS.equivalence n)
      (H := spCoefficientEvaluation l E T dT.equivalence n ⋙ spLevelPush l E g n)
      (spTowerEvaluationIso l E g dT dS n) ≪≫
    (Functor.mapHomotopyCategoryPlusCompIso
      (F := spCoefficientEvaluation l E T dT.equivalence n)
      (G := spLevelPush l E g n)
      (H := spCoefficientEvaluation l E T dT.equivalence n ⋙ spLevelPush l E g n)
      (Iso.refl (spCoefficientEvaluation l E T dT.equivalence n ⋙ spLevelPush l E g n))).symm

/-- The finite-product retract and both acyclicity conclusions for injective towers.
Source: blueprint main-20261015, tower-level acyclicity lemma, paragraphs 1--2;
Stacks 03FD (blueprint: det-sp-tower-injective-components).

Proof:
1. Work in the common larger universe on the small pro-etale site. The ringed-site
Grothendieck theorem and Stacks 079H give enough injectives at every level; the tower
Grothendieck theorem does the same for towers.
2. By det-sp-tower-evaluation-adjoint embed I in the product of the right-adjoint
systems r_n J_n with J_n injective. Extend the identity of I across this monomorphism
by injectivity to split it. Products of towers are levelwise. At level r+1 only the
indices n+1 <= r+1 contribute, giving exactly the displayed finite product of actual
scalar restrictions. Evaluating the splitting gives the retract.
3. By lem-sc-injective-module-abelian-acyclic-zariski (Stacks 03FD), every J_n has
vanishing positive abelian-sheaf cohomology on every object. Scalar restriction leaves
that abelian sheaf unchanged. The module/abelian evaluation comparison transports
this vanishing to the R_(r+1)-module section functor.
4. Resolve the finitely many restricted J_n by injective R_(r+1)-module resolutions.
Their finite product is an injective resolution: maps extend coordinatewise and
kernels and images are coordinatewise in finite sums. Sections and cohomology commute
with these finite products. Apply the higher section functors to the retract; its
identity factors through zero, so all positive section functors vanish on I_(r+1).
5. For an injective resolution L of I_(r+1), g_* L has sections L(T times_S V).
Their positive cohomology vanishes by step 4. Kernels are sectionwise and cokernels
are sheafified sectionwise, so the positive cohomology sheaves of g_* L vanish.
This is precisely g_*-acyclicity. No infinite-product exactness or injectivity after
restriction of scalars is asserted. -/
theorem sp_tower_injective_components (I : spCoefficientTowers l E T) [Injective I] :
    (∀ r : ℕ, ∃ J : (n : Fin (r + 1)) →
        systemLevel.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T) n.val,
      (∀ n : Fin (r + 1), Injective (J n)) ∧
      Nonempty (Retract ((spCoefficientEvaluation l E T dT.equivalence r).obj I)
        (∏ᶜ fun n : Fin (r + 1) ↦
          (systemRestriction.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T)
            (Nat.le_of_lt_succ n.isLt)).obj (J n)))) ∧
    (∀ (r : ℕ) (U : T.ProEt),
      (SheafOfModules.evaluation.{max u (t + 1)} (spCoefficientRing l E T r) (op U)).rightAcyclic
        ((spCoefficientEvaluation l E T dT.equivalence r).obj I)) ∧
    (∀ r : ℕ, (spLevelPush l E g r).rightAcyclic
      ((spCoefficientEvaluation l E T dT.equivalence r).obj I)) := by
  sorry

/-- Evaluating any bounded below injective tower complex gives a complex computing
finite-level derived direct image: its canonical right-derived unit is invertible.
Source: blueprint, last paragraph; Stacks 015E and 05TH
(blueprint: det-sp-tower-injective-components).

Proof: evaluation is exact by det-sp-coefficient-towers-abelian, hence sends any
quasi-isomorphism into the tower complex to a quasi-isomorphism into its component.
It preserves the lower bound. The preceding component theorem gives termwise
g_*-acyclicity. Apply src-right-derived-functor-plus-acyclic-unit (Stacks 015E) to
obtain exactly the displayed invertible unit. An evaluated injective tower resolution
therefore computes the finite-level derived image of its source. Bounded below
injective resolutions are K-injective by lem-weil-pbc-bounded-below-injectives-kinjective,
so the D+ computation agrees with the ordinary unbounded derived direct image. -/
theorem sp_tower_injective_complex_computes (n : ℕ)
    (I : CochainComplex.Plus (spCoefficientTowers l E T))
    (hI : ∀ k : ℤ, Injective (I.obj.X k)) :
    IsIso ((spLevelPush l E g n).rightDerivedFunctorPlusUnit.app
      ((spCoefficientEvaluation l E T dT.equivalence n).mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient (spCoefficientTowers l E T)).obj I))) := by
  let F := spCoefficientEvaluation l E T dT.equivalence n
  let L := F.mapCochainComplexPlus.obj I
  apply (spLevelPush l E g n).isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic L
  intro k
  have : Injective (I.obj.X k) := hI k
  exact (sp_tower_injective_components l E g dT (I.obj.X k)).2.2 n

/-- The explicitly supplied bounded below injective resolution computes the finite-level
image of its source C. The equation specifies the isomorphism by the derived units
and the resolution isomorphism C to Q(I), rather than by an arbitrary identification.
Source: blueprint, last paragraph; Stacks 015E and 05TH
(blueprint: det-sp-tower-injective-components).
Proof: exact evaluation makes its derived unit invertible on every complex and sends
the resolution isomorphism to the evaluated resolution isomorphism. The preceding
acyclic-complex theorem makes the finite-level direct-image derived unit invertible
on the evaluated I. Compose these two invertible units and the inverse image of the
resolution isomorphism, exactly in the order displayed below. Thus g_* I_n represents
Rg_* C_n for the given resolution and not just for a selected resolution. -/
theorem sp_tower_injective_resolution_computes (n : ℕ)
    (C : DerivedCategory.Plus (spCoefficientTowers l E T))
    (I : CochainComplex.Plus (spCoefficientTowers l E T))
    (ρ : C ≅ DerivedCategory.Plus.Qh.obj
      ((HomotopyCategory.Plus.quotient (spCoefficientTowers l E T)).obj I))
    (hI : ∀ k : ℤ, Injective (I.obj.X k)) :
    ∃ e : DerivedCategory.Plus.Qh.obj
        ((spLevelPush l E g n).mapHomotopyCategoryPlus.obj
          ((spCoefficientEvaluation l E T dT.equivalence n).mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.quotient (spCoefficientTowers l E T)).obj I))) ≅
      ((spLevelPush l E g n).rightDerivedFunctorPlus.obj
        ((spCoefficientEvaluation l E T dT.equivalence n).rightDerivedFunctorPlus.obj C)),
      e.hom = (spLevelPush l E g n).rightDerivedFunctorPlusUnit.app
          ((spCoefficientEvaluation l E T dT.equivalence n).mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.quotient (spCoefficientTowers l E T)).obj I)) ≫
        (spLevelPush l E g n).rightDerivedFunctorPlus.map
          ((spCoefficientEvaluation l E T dT.equivalence n).rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.quotient (spCoefficientTowers l E T)).obj I)) ≫
        (spLevelPush l E g n).rightDerivedFunctorPlus.map
          ((spCoefficientEvaluation l E T dT.equivalence n).rightDerivedFunctorPlus.map ρ.inv) :=
  by
    have := sp_tower_injective_complex_computes l E g dT n I hI
    have := Functor.isIso_rightDerivedFunctorPlusUnit
      (spCoefficientEvaluation l E T dT.equivalence n)
    refine ⟨asIso ((spLevelPush l E g n).rightDerivedFunctorPlusUnit.app
        ((spCoefficientEvaluation l E T dT.equivalence n).mapHomotopyCategoryPlus.obj
          ((HomotopyCategory.Plus.quotient (spCoefficientTowers l E T)).obj I)) ≫
      (spLevelPush l E g n).rightDerivedFunctorPlus.map
        ((spCoefficientEvaluation l E T dT.equivalence n).rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.quotient (spCoefficientTowers l E T)).obj I)) ≫
      (spLevelPush l E g n).rightDerivedFunctorPlus.map
        ((spCoefficientEvaluation l E T dT.equivalence n).rightDerivedFunctorPlus.map ρ.inv)),
      rfl⟩

/-- Exact evaluation on D+ is termwise evaluation: its derived unit is always invertible.
This identifies the evaluation functors in the final comparison with C maps to C_n,
as defined by the coefficient-tower abelian theorem, including arbitrary lower bounds.
Source: blueprint, meaning of C_n and last paragraph
(blueprint: det-sp-tower-injective-components).
Proof: evaluation preserves kernels and cokernels by det-sp-coefficient-towers-abelian,
so it preserves quasi-isomorphisms of complexes and descends termwise to the ordinary
derived category. On D+ the same descent has invertible localization unit on every
bounded below complex. Uniqueness for right derived functors identifies this descent
and its unit with the published rightDerivedFunctorPlus construction. -/
theorem sp_tower_evaluation_derived_unit (n : ℕ)
    (L : HomotopyCategory.Plus (spCoefficientTowers l E T)) :
    IsIso ((spCoefficientEvaluation l E T dT.equivalence n).rightDerivedFunctorPlusUnit.app L) :=
  by
    have := Functor.isIso_rightDerivedFunctorPlusUnit
      (spCoefficientEvaluation l E T dT.equivalence n)
    exact NatIso.isIso_app_of_isIso
      (spCoefficientEvaluation l E T dT.equivalence n).rightDerivedFunctorPlusUnit L

private theorem derivedEvaluation_existsUnique
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (K : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [K.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] [PreservesFiniteLimits K]
    (c : F.mapHomotopyCategoryPlus ⋙ G.mapHomotopyCategoryPlus ≅
      H.mapHomotopyCategoryPlus ⋙ K.mapHomotopyCategoryPlus)
    (h : ∀ (J : A) [Injective J], K.rightAcyclic (H.obj J)) :
    ∃! e : F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ≅
        H.rightDerivedFunctorPlus ⋙ K.rightDerivedFunctorPlus,
      ∀ L : HomotopyCategory.Plus A,
        G.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj L) ≫
          G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app L) ≫
          e.hom.app (DerivedCategory.Plus.Qh.obj L) =
        DerivedCategory.Plus.Qh.map (c.hom.app L) ≫
          K.rightDerivedFunctorPlusUnit.app (H.mapHomotopyCategoryPlus.obj L) ≫
          K.rightDerivedFunctorPlus.map (H.rightDerivedFunctorPlusUnit.app L) := by
    let α := Functor.rightDerivedFunctorPlusCompUnit F G
    let β := Functor.rightDerivedFunctorPlusCompUnit H K
    let τ := Functor.isoWhiskerRight
      ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).symm ≪≫
        c ≪≫
        Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (H ⋙ K)))
      DerivedCategory.Plus.Qh
    have hG := Functor.isIso_rightDerivedFunctorPlusUnit G
    have hleft : (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor
        α (HomotopyCategory.Plus.quasiIso A) := by
      refine (HomotopyCategory.Plus.localizerMorphism_derives
        ((F ⋙ G).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)).isRightDerivedFunctor_of_isIso
          α (fun X ↦ ?_)
      rw [Functor.rightDerivedFunctorPlusCompUnit_app]
      have : IsIso (F.rightDerivedFunctorPlusUnit.app
          ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj X)) :=
        inferInstance
      have := NatIso.isIso_app_of_isIso G.rightDerivedFunctorPlusUnit
        (F.mapHomotopyCategoryPlus.obj
          ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj X))
      infer_instance
    have hright := H.isRightDerivedFunctor_rightDerivedFunctorPlus_comp_of_rightAcyclic K
      h
    let e := Functor.rightDerivedNatIso
      (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus)
      (H.rightDerivedFunctorPlus ⋙ K.rightDerivedFunctorPlus)
      α β (HomotopyCategory.Plus.quasiIso A) τ
    have hfac (L : HomotopyCategory.Plus A) :=
      Functor.rightDerivedNatTrans_app
        (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus)
        (H.rightDerivedFunctorPlus ⋙ K.rightDerivedFunctorPlus)
        α β (HomotopyCategory.Plus.quasiIso A) τ.hom L
    have he (L : HomotopyCategory.Plus A) :
        G.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj L) ≫
          G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app L) ≫
          e.hom.app (DerivedCategory.Plus.Qh.obj L) =
        DerivedCategory.Plus.Qh.map
            (c.hom.app L) ≫
          K.rightDerivedFunctorPlusUnit.app (H.mapHomotopyCategoryPlus.obj L) ≫
          K.rightDerivedFunctorPlus.map (H.rightDerivedFunctorPlusUnit.app L) := by
      have h := hfac L
      have hτ : τ.hom.app L = DerivedCategory.Plus.Qh.map
          (c.hom.app L) := by
        dsimp only [τ, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
          Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
        rw [Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app,
          Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app]
        rw [Category.id_comp]
        exact congrArg DerivedCategory.Plus.Qh.map
          (Category.comp_id (c.hom.app L))
      simpa only [e, α, β, Functor.rightDerivedNatIso_hom,
        Functor.rightDerivedFunctorPlusCompUnit_app, hτ, Category.assoc] using h
    refine ⟨e, he, ?_⟩
    intro e' he'
    apply Iso.ext
    apply Functor.rightDerived_ext
      (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus) α
      (HomotopyCategory.Plus.quasiIso A)
    ext L : 2
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, α,
      Functor.rightDerivedFunctorPlusCompUnit_app, Category.assoc] using
      (he' L).trans (he L).symm

/-- Derived tower direct image commutes naturally with evaluation. The compatibility
with both derived units fixes the comparison induced by the underived evaluation
identity; it is independent of every injective resolution.
Source: blueprint, last paragraph; Stacks 05TI and 05TH
(blueprint: det-sp-tower-injective-components).

Proof:
1. The tower direct image is additive and left exact, checked levelwise above, and
its source has enough injectives. The right-derived-plus theorem supplies its total
right derived functor and its unit, invertible on bounded below injective complexes.
2. Exact evaluation identifies its evaluated representative with g_* I_n. By
sp_tower_injective_complex_computes this same representative computes Rg_* C_n.
Exact evaluation itself is its own derived functor, identified by its derived unit.
3. The underived evaluation identity and these derived units give a comparison on
the bounded below homotopy category. The universal property of the right derived
functor descends it to D+. The preceding injective computation proves it is invertible.
4. Uniqueness for right derived functors proves independence of the resolution and
naturality in C. It also gives the displayed compatibility with the two units on
every bounded below complex, which uniquely characterizes the natural isomorphism. -/
theorem sp_tower_derived_direct_image_evaluation (n : ℕ) :
    ∃! e : (spTowerPush l E g).rightDerivedFunctorPlus ⋙
        (spCoefficientEvaluation l E S dS.equivalence n).rightDerivedFunctorPlus ≅
      (spCoefficientEvaluation l E T dT.equivalence n).rightDerivedFunctorPlus ⋙
        (spLevelPush l E g n).rightDerivedFunctorPlus,
      ∀ L : HomotopyCategory.Plus (spCoefficientTowers l E T),
        (spCoefficientEvaluation l E S dS.equivalence n).rightDerivedFunctorPlusUnit.app
            ((spTowerPush l E g).mapHomotopyCategoryPlus.obj L) ≫
          (spCoefficientEvaluation l E S dS.equivalence n).rightDerivedFunctorPlus.map
            ((spTowerPush l E g).rightDerivedFunctorPlusUnit.app L) ≫
          e.hom.app (DerivedCategory.Plus.Qh.obj L) =
        DerivedCategory.Plus.Qh.map
            ((spTowerEvaluationHomotopyIso l E g dT dS n).hom.app L) ≫
          (spLevelPush l E g n).rightDerivedFunctorPlusUnit.app
            ((spCoefficientEvaluation l E T dT.equivalence n).mapHomotopyCategoryPlus.obj L) ≫
          (spLevelPush l E g n).rightDerivedFunctorPlus.map
            ((spCoefficientEvaluation l E T dT.equivalence n).rightDerivedFunctorPlusUnit.app L) :=
  by
    have : (spLevelPush l E g n).Additive := spCoefficientModulePushAdditive g _
    have : PreservesFiniteLimits (spLevelPush l E g n) := spLevelPushLimits l E g n
    exact derivedEvaluation_existsUnique
      (spTowerPush l E g) (spCoefficientEvaluation l E S dS.equivalence n)
      (spCoefficientEvaluation l E T dT.equivalence n) (spLevelPush l E g n)
      (spTowerEvaluationHomotopyIso l E g dT dS n)
      (fun J _ ↦ (sp_tower_injective_components l E g dT J).2.2 n)

end AlgebraicGeometry.ProEtale

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
