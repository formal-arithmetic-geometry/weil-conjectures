/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import all WeilConjectures.Algebra.Homology.Site.SitePerfectModelRestrictionSupplement
import all WeilConjectures.DeligneLaumon.RoosIntrinsicUnitComparison.RoosIntrinsicUnitComparison
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import Mathlib.Data.Nat.Prime.Infinite

/-! # Open restriction and the actual completed quotient tower

Source: Stacks Tags 00XZ, 08TC and 0941; the finite-clopen expansion of
blueprint def-pur-section-invariant, retained step 5
(blueprint: lem-pur-open-completed-restriction-identification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [local irreducible] HasDerivedCategory.standard
-- Expose only the global branch of the existing slice presentation for elaboration.
set_option allowUnsafeReducibility true
attribute [local reducible] WeilConjectures.IntegralOnSlice.Site
  WeilConjectures.IntegralOnSlice.topology WeilConjectures.IntegralOnSlice.restrict
  WeilConjectures.IntegralOnSlice.ring WeilConjectures.IntegralOnSlice.finite
  WeilConjectures.IntegralOnSlice.projection
universe t u a b
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.OpenCompletedRestriction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The unchanged standard derived localization in the global slice presentation.
Source: Stacks 05RU (blueprint: lem-pur-open-completed-restriction-identification). -/
instance globalHasDerived (W : Scheme.{t}) :
    HasDerivedCategory (IntegralOnSlice.Mod l E W none) :=
  IntegralOnSlice.hasDerived l E W none

/-- The actual site inclusion, composition with the open immersion.
Source: Stacks 00XZ (blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev inclusion : U.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)

/-- Continuity of the actual site inclusion.
Source: Stacks 00XZ (blueprint: lem-pur-open-completed-restriction-identification). -/
instance inclusionContinuous : (inclusion j).IsContinuous
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) :=
  Scheme.ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)

/-- The ordinary precomposition of commutative ring sheaves.
Source: Stacks 00XZ (blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev ringRestriction :=
  (inclusion j).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)




private local instance (priority := 4000) ringSheafify (W : Scheme.{t}) :
    HasSheafify (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)} :=
  integralCoefficientRingSheafify.{t, u} W

private local instance (priority := 5000) weakRingSheafify (W : Scheme.{t}) :
    HasWeakSheafify (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)} :=
  (integralCoefficientRingSheafify.{t, u} W).isRightAdjoint

attribute [local irreducible] Padic

/-- Coefficient comparisons with their determining constant-section and projection equations.
These are assertion data, not an assumed existence of a comparison.
Source: Stacks 00XZ, 03CO (blueprint: lem-pur-open-completed-restriction-identification). -/
structure Coefficients where
  finite : ∀ n : ℕ, integralCoefficientCommRingSheaf l E U n ≅
    (ringRestriction.{t, u} j).obj (integralCoefficientCommRingSheaf l E X n)
  constants : ∀ (n : ℕ) (V : U.ProEt),
    (toSheafify (Scheme.ProEt.topology U)
      ((Functor.const U.ProEtᵒᵖ).obj (CommRingCat.of
        (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app (op V) ≫
      (finite n).hom.hom.app (op V) =
    (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of
        (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app
          (op ((inclusion j).obj V))
  completed : completedIntegralCommRingSheafUnrestricted l E U ≅
    (ringRestriction.{t, u} j).obj (completedIntegralCommRingSheafUnrestricted l E X)
  projections : ∀ n : ℕ, completed.hom ≫ (ringRestriction.{t, u} j).map
      (completedIntegralCommRingProjectionUnrestricted l E X n) =
    completedIntegralCommRingProjectionUnrestricted l E U n ≫ (finite n).hom

attribute [local irreducible] CategoryTheory.constantSheaf Padic

variable (c : Coefficients l E j)

/-- Ordinary site restriction with scalar action transported through the inverse
of the canonical restriction-to-local coefficient isomorphism.
Source: Stacks 00XZ (blueprint: lem-pur-open-completed-restriction-identification). -/
def restriction : IntegralOnSlice.Mod l E X none ⥤ IntegralOnSlice.Mod l E U none :=
  SheafOfModules.pushforward (F := inclusion j)
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      c.completed.hom)

/-- Finite ordinary restriction with the same constant-section normalization.
Source: Stacks 00XZ (blueprint: lem-pur-open-completed-restriction-identification). -/
def finiteRestriction (n : ℕ) : integralOperationsFiniteModules l E X n ⥤
    integralOperationsFiniteModules l E U n :=
  SheafOfModules.pushforward (F := inclusion j)
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (c.finite n).hom)

attribute [local reducible] CategoryTheory.constantSheaf

set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] SheafOfModules.instAbelian
  CategoryTheory.abelianOfAdjunction CategoryTheory.Abelian.ofCoimageImageComparisonIsIso
  IntegralOnSlice.Good integralOperationsGoodComplex

private instance inclusionCocontinuous : (inclusion j).IsCocontinuous
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) :=
  Scheme.ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)

private def coefficientIso (A : CommRingCat.{max u (t + 1)}) :
    (constantSheaf (Scheme.ProEt.topology U) CommRingCat.{max u (t + 1)}).obj A ≅
      (ringRestriction j).obj
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A) :=
  ((inclusion j).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{max u (t + 1)}
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)).app
      ((Functor.const X.ProEtᵒᵖ).obj A)

private theorem coefficientIso_constants (A : CommRingCat.{max u (t + 1)})
    (V : U.ProEt) :
    (toSheafify (Scheme.ProEt.topology U) ((Functor.const U.ProEtᵒᵖ).obj A)).app (op V) ≫
        (coefficientIso j A).hom.hom.app (op V) =
      (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
        (op ((inclusion j).obj V)) := by
  exact congrArg (fun f ↦ f.app (op V))
    ((inclusion j).toSheafify_pullbackSheafificationCompatibility
      CommRingCat.{max u (t + 1)} (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj A))

private theorem coefficientIso_natural {A B : CommRingCat.{max u (t + 1)}}
    (a : A ⟶ B) :
    (constantSheaf (Scheme.ProEt.topology U) CommRingCat.{max u (t + 1)}).map a ≫
        (coefficientIso j B).hom =
      (coefficientIso j A).hom ≫ (ringRestriction j).map
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)}).map a) := by
  exact ((inclusion j).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{max u (t + 1)}
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)).hom.naturality
      ((Functor.const X.ProEtᵒᵖ).map a)

private def coefficientTowerIso : integralCoefficientSheafSystem l E U ≅
    integralCoefficientSheafSystem l E X ⋙
      (inclusion j).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) := by
  let H := sheafCompose (Scheme.ProEt.topology U)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let α : integralCoefficientSheafSystem l E U ⟶
      integralCoefficientSheafSystem l E X ⋙
        (inclusion j).sheafPushforwardContinuous RingCat.{max u (t + 1)}
          (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) :=
    NatTrans.ofOpSequence (fun n ↦ H.map (coefficientIso j
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom)
      (fun n ↦ by
        have h := coefficientIso_natural j
          (CommRingCat.ofHom
            ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
              ((Padic.coefficientExtensionTransition l E (n + 1)).comp
                (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom)))
        simp only [integralCoefficientSheafSystem, Functor.comp_map,
          Functor.ofOpSequence_map_homOfLE_succ]
        ext V x
        exact congrArg (fun f ↦ (f.hom.app V).hom x) h)
  letI : ∀ n, IsIso (α.app n) := by
    intro n
    change IsIso (H.map (coefficientIso j
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n.unop + 1))))).hom)
    infer_instance
  letI : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

attribute [local reducible] completedIntegralCommRingSheafUnrestricted
  completedIntegralCoefficientSheafUnrestricted CategoryTheory.Limits.limit

private def forgetCompletedIso (W : Scheme.{t}) :
    (sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        (completedIntegralCommRingSheafUnrestricted l E W) ≅
      limit (integralCoefficientSheafSystem l E W) :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun V ↦
    @RingEquiv.toRingCatIso _ _ (RingCat.ring _) (RingCat.ring _)
      { toEquiv := Equiv.refl _
        map_add' := fun _ _ ↦ rfl
        map_mul' := fun _ _ ↦ rfl }) (fun f ↦ by ext x; rfl))

private def completedRingIso :
    (sheafCompose (Scheme.ProEt.topology U)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        (completedIntegralCommRingSheafUnrestricted l E U) ≅
      (sheafCompose (Scheme.ProEt.topology U)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          ((ringRestriction j).obj (completedIntegralCommRingSheafUnrestricted l E X)) := by
  let F := (inclusion j).sheafPushforwardContinuous RingCat.{max u (t + 1)}
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)
  exact (forgetCompletedIso l E U ≪≫
    HasLimit.isoOfNatIso (coefficientTowerIso l E j) ≪≫
    (preservesLimitIso F (integralCoefficientSheafSystem l E X)).symm) ≪≫
    F.mapIso (forgetCompletedIso l E X).symm

private def completedCoefficientIso : completedIntegralCommRingSheafUnrestricted l E U ≅
    (ringRestriction j).obj (completedIntegralCommRingSheafUnrestricted l E X) :=
  (sheafCompose (Scheme.ProEt.topology U)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).preimageIso
      (completedRingIso l E j)

private theorem forgetCompletedIso_projection (W : Scheme.{t}) (n : ℕ) :
    (forgetCompletedIso l E W).hom ≫
        limit.π (integralCoefficientSheafSystem l E W) (op n) =
      (sheafCompose (Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (completedIntegralCommRingProjectionUnrestricted l E W n) := by
  ext V x
  simp only [forgetCompletedIso, ObjectProperty.isoMk_hom,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    completedIntegralCommRingProjectionUnrestricted]
  rfl

attribute [local irreducible] CategoryTheory.Limits.limit
  completedIntegralCoefficientSheafUnrestricted
  completedRingIso completedCoefficientIso coefficientIso coefficientTowerIso
  completedIntegralCommRingSheafUnrestricted

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  completedIntegralCoefficientSheafUnrestricted

private theorem completedCoefficientIso_projection (n : ℕ) :
    (completedCoefficientIso l E j).hom ≫ (ringRestriction j).map
        (completedIntegralCommRingProjectionUnrestricted l E X n) =
      completedIntegralCommRingProjectionUnrestricted l E U n ≫
        (coefficientIso j (CommRingCat.of
          (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom := by
  let F := (inclusion j).sheafPushforwardContinuous RingCat.{max u (t + 1)}
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)
  let H := sheafCompose (Scheme.ProEt.topology U)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  apply H.map_injective
  simp only [Functor.map_comp]
  change H.map (completedCoefficientIso l E j).hom ≫
      F.map ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (completedIntegralCommRingProjectionUnrestricted l E X n)) = _
  have hm : H.map (completedCoefficientIso l E j).hom =
      ((forgetCompletedIso l E U ≪≫
        HasLimit.isoOfNatIso (coefficientTowerIso l E j) ≪≫
        (preservesLimitIso F (integralCoefficientSheafSystem l E X)).symm) ≪≫
        F.mapIso (forgetCompletedIso l E X).symm).hom := by
    unfold completedCoefficientIso
    change H.map (H.preimage (completedRingIso l E j).hom) = _
    rw [Functor.map_preimage]
    unfold completedRingIso
    rfl
  rw [hm]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [← forgetCompletedIso_projection l E X n]
  simp only [Functor.map_comp, ← F.map_comp_assoc,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [preservesLimitIso_inv_π, HasLimit.isoOfNatIso_hom_π]
  rw [← Category.assoc, forgetCompletedIso_projection]
  unfold coefficientTowerIso
  rfl

attribute [local irreducible] completedCoefficientIso

private def normalizedCoefficients : Coefficients l E j where
  finite n := coefficientIso j (CommRingCat.of
    (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
  constants _n V := coefficientIso_constants j _ V
  completed := completedCoefficientIso l E j
  projections := completedCoefficientIso_projection l E j

attribute [local semireducible] CategoryTheory.Limits.limit

private theorem coefficients_subsingleton (c d : Coefficients l E j) : c = d := by
  have hf : c.finite = d.finite := by
    funext n
    apply Iso.ext
    apply Sheaf.hom_ext
    unfold integralCoefficientCommRingSheaf constantSheaf
    apply sheafify_hom_ext (D := CommRingCat.{max u (t + 1)})
      (Scheme.ProEt.topology U) _ _
      ((ringRestriction j).obj (integralCoefficientCommRingSheaf l E X n)).property
    apply NatTrans.ext
    funext V
    exact (c.constants n V.unop).trans (d.constants n V.unop).symm
  have hc : c.completed = d.completed := by
    apply Iso.ext
    let F := (inclusion j).sheafPushforwardContinuous RingCat.{max u (t + 1)}
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)
    let H := sheafCompose (Scheme.ProEt.topology U)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
    apply H.map_injective
    apply (cancel_mono (F.map (forgetCompletedIso l E X).hom)).1
    apply (isLimitOfPreserves F (limit.isLimit
      (integralCoefficientSheafSystem l E X))).hom_ext
    intro n
    change (H.map c.completed.hom ≫ F.map (forgetCompletedIso l E X).hom) ≫
        F.map (limit.π _ n) =
      (H.map d.completed.hom ≫ F.map (forgetCompletedIso l E X).hom) ≫
        F.map (limit.π _ n)
    simp only [Category.assoc, ← Functor.map_comp]
    rw [show n = op n.unop from rfl, forgetCompletedIso_projection]
    have he : c.completed.hom ≫ (ringRestriction j).map
        (completedIntegralCommRingProjectionUnrestricted l E X n.unop) =
      d.completed.hom ≫ (ringRestriction j).map
        (completedIntegralCommRingProjectionUnrestricted l E X n.unop) := by
      rw [c.projections, d.projections, hf]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    ext x
    exact congrArg (fun f ↦ (f.hom.app V).hom x) he
  cases c
  cases d
  cases hf
  cases hc
  rfl

attribute [local irreducible] CategoryTheory.Limits.limit

private theorem normalizedRestrictionExact
    {R : Sheaf (Scheme.ProEt.topology X) RingCat.{max u (t + 1)}}
    {S : Sheaf (Scheme.ProEt.topology U) RingCat.{max u (t + 1)}}
    (a : S ≅ ((inclusion j).sheafPushforwardContinuous RingCat
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)).obj R) :
    (SheafOfModules.pushforward.{max u (t + 1)} a.hom).Additive ∧
      PreservesFiniteLimits (SheafOfModules.pushforward.{max u (t + 1)} a.hom) ∧
      PreservesFiniteColimits (SheafOfModules.pushforward.{max u (t + 1)} a.hom) := by
  let : (inclusion j).IsLeftAdjoint :=
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
      (inferInstance : WeaklyEtale j) trivial).isLeftAdjoint
  let : (SheafOfModules.pushforward.{max u (t + 1)} a.hom).IsLeftAdjoint :=
    SheafOfModules.isLeftAdjoint_pushforward_of_isIso a.hom
  refine ⟨?_, SheafOfModules.pushforward_finiteLimits a.hom, inferInstance⟩
  constructor
  intro M N f g
  ext V x
  rfl

attribute [local irreducible] normalizedCoefficients CategoryTheory.constantSheaf


/-- Existence of the uniquely normalized coefficients and exactness of their restrictions.
Source: Stacks 00XZ, 03CO (blueprint: lem-pur-open-completed-restriction-identification).
Proof: constant sheafification commutes with localization. Its comparison is fixed by
constants, so it commutes with every coefficient reduction. Sectionwise inverse limits
supply the completed comparison and its projection equations. Restriction is exact;
scalar transport through each ring isomorphism is an exact equivalence. -/
theorem coefficients_exact :
    ∃! c : Coefficients l E j,
      (restriction l E j c).Additive ∧
      PreservesFiniteLimits (restriction l E j c) ∧
      PreservesFiniteColimits (restriction l E j c) ∧
      ∀ n : ℕ, (finiteRestriction l E j c n).Additive ∧
        PreservesFiniteLimits (finiteRestriction l E j c n) ∧
        PreservesFiniteColimits (finiteRestriction l E j c n) := by
  refine ⟨normalizedCoefficients l E j, ?_, fun c _ ↦ coefficients_subsingleton l E j c _⟩
  let H := sheafCompose (Scheme.ProEt.topology U)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  have hc := normalizedRestrictionExact j
    (R := (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        (completedIntegralCommRingSheafUnrestricted l E X))
    (S := H.obj (completedIntegralCommRingSheafUnrestricted l E U))
    (H.mapIso (normalizedCoefficients l E j).completed)
  refine ⟨hc.1, hc.2.1, hc.2.2, ?_⟩
  intro n
  exact normalizedRestrictionExact j
    (R := integralCoefficientSheaf l E X n)
    (S := integralCoefficientSheaf l E U n)
    (H.mapIso ((normalizedCoefficients l E j).finite n))

/-- The coefficient data determined by constants and limit projections.
Source: Stacks 00XZ, 03CO (blueprint: lem-pur-open-completed-restriction-identification). -/
def coefficients : Coefficients l E j := (coefficients_exact l E j).exists.choose

/-- Ordinary exact restriction with the uniquely normalized coefficient data.
Source: Stacks 00XZ (blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev ordinary := restriction l E j (coefficients l E j)

/-- Additivity of ordinary restriction.
Source: Stacks 00XZ (blueprint: lem-pur-open-completed-restriction-identification). -/
instance ordinaryAdditive : (ordinary l E j).Additive :=
  (coefficients_exact l E j).exists.choose_spec.1

/-- Finite limits of ordinary restriction.
Source: Stacks 00XZ (blueprint: lem-pur-open-completed-restriction-identification). -/
instance ordinaryLimits : PreservesFiniteLimits (ordinary l E j) :=
  (coefficients_exact l E j).exists.choose_spec.2.1

/-- Finite colimits of ordinary restriction.
Source: Stacks 00XZ (blueprint: lem-pur-open-completed-restriction-identification). -/
instance ordinaryColimits : PreservesFiniteColimits (ordinary l E j) :=
  (coefficients_exact l E j).exists.choose_spec.2.2.1

/-- Termwise ordinary restriction, before localization.
Source: Stacks 015F (blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev complexRestriction : IntegralOnSlice.Cx l E X none ⥤
    IntegralOnSlice.Cx l E U none := (ordinary l E j).mapHomologicalComplex (.up ℤ)

/-- The exact functor on ordinary unbounded derived categories.
Source: Stacks 015F (blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev derivedRestriction : IntegralOnSlice.D l E X none ⥤
    IntegralOnSlice.D l E U none := (ordinary l E j).mapDerivedCategory

/-- Canonical graph-coordinate image of a section under finite inverse image.
Source: Stacks 00XZ, 03D2
(blueprint: lem-pur-open-completed-restriction-identification). -/
def graphSection (n : ℕ) (M : integralOperationsFiniteModules l E X n) (V : U.ProEt)
    (x : M.val.obj (op ((inclusion j).obj V))) :
    ((integralOperationsLevelPullback l E j n).obj M).val.obj (op V) :=
  ((integralOperationsLevelPullback l E j n).obj M).val.map
    ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
      (inferInstance : WeaklyEtale j) trivial).unit.app V).op
    (integralOperationsPullbackGenerator l E j n M ((inclusion j).obj V) x)

/-- The source's actual strict quotient tower, on one common representative.
Source: Bhatt--Scholze 3.5.2
(blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev sourceTower (P : IntegralOnSlice.Cx l E X none) :=
  (IntegralOnSlice.tower l E X none).obj P

/-- The target's actual strict finite-pullback tower.
Source: Bhatt--Scholze 6.5.9(4)
(blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev targetTower (P : IntegralOnSlice.Cx l E X none) :
    ℕᵒᵖ ⥤ IntegralOnSlice.Cx l E U none :=
  (integralOperationsPullbackTowerFunctor l E j).obj P

/-- The actual first Roos projection, in the strict model used by integral operations.
Source: Stacks 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
def roosProjection {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    integralOperationsRoos T ⟶ ∏ᶜ fun n : ℕ ↦ T.obj (op n) :=
  CochainComplex.mappingCocone.fst
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ T.obj (op n))
      (integralOperationsTowerStep T))

/-- The actual second Roos coordinate, retaining Mathlib's shifted-cone sign.
Source: Stacks 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
def roosSecond {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) (q : ℤ) :
    (integralOperationsRoos T).X q ⟶ (∏ᶜ fun n : ℕ ↦ T.obj (op n)).X (q - 1) :=
  (CochainComplex.mappingCocone.snd
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ T.obj (op n))
      (integralOperationsTowerStep T))).v q (q - 1) (by rfl)

attribute [local irreducible] roosProjection roosSecond

attribute [local irreducible] coefficients IntegralOnSlice.reductionWitness
  unrestrictedIntegralReductionExistence IntegralOnSlice.completion
  IntegralOnSlice.completionComparison IntegralOnSlice.completionUnit
  integralDerivedPullback integralDerivedPullbackComparison

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  completedIntegralCoefficientSheafUnrestricted CategoryTheory.Limits.limit
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- One of the original tower normalization equations.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
def FiniteSectionNormalization
    (finite : ∀ n : ℕ, finiteRestriction l E j (coefficients l E j) n ≅
    integralOperationsLevelPullback l E j n)
    (_levels : IntegralOnSlice.tower l E X none ⋙
      (Functor.whiskeringRight ℕᵒᵖ
        (IntegralOnSlice.Cx l E X none) (IntegralOnSlice.Cx l E U none)).obj
          (complexRestriction l E j) ≅
    integralOperationsPullbackTowerFunctor l E j)
    (_product : ∀ P : IntegralOnSlice.Cx l E X none,
    (complexRestriction l E j).obj (∏ᶜ fun n : ℕ ↦ (sourceTower l E P).obj (op n)) ≅
      ∏ᶜ fun n : ℕ ↦ (targetTower l E j P).obj (op n))
    (_roos : IntegralOnSlice.roos l E X none ⋙ complexRestriction l E j ≅
    integralOperationsPullbackComplexFunctor l E j) : Prop :=
  ∀ (n : ℕ) (M : integralOperationsFiniteModules l E X n)
      (V : U.ProEt) (x : M.val.obj (op ((inclusion j).obj V))),
    ((finite n).hom.app M).val.app (op V) x = graphSection l E j n M V x

/-- One of the original tower normalization equations.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
def LevelSectionNormalization
    (_finite : ∀ n : ℕ, finiteRestriction l E j (coefficients l E j) n ≅
    integralOperationsLevelPullback l E j n)
    (levels : IntegralOnSlice.tower l E X none ⋙
      (Functor.whiskeringRight ℕᵒᵖ
        (IntegralOnSlice.Cx l E X none) (IntegralOnSlice.Cx l E U none)).obj
          (complexRestriction l E j) ≅
    integralOperationsPullbackTowerFunctor l E j)
    (_product : ∀ P : IntegralOnSlice.Cx l E X none,
    (complexRestriction l E j).obj (∏ᶜ fun n : ℕ ↦ (sourceTower l E P).obj (op n)) ≅
      ∏ᶜ fun n : ℕ ↦ (targetTower l E j P).obj (op n))
    (_roos : IntegralOnSlice.roos l E X none ⋙ complexRestriction l E j ≅
    integralOperationsPullbackComplexFunctor l E j) : Prop :=
  ∀ (P : IntegralOnSlice.Cx l E X none) (n : ℕ) (i : ℤ)
      (V : U.ProEt) (x : (P.X i).val.obj (op ((inclusion j).obj V))),
    HEq
      (((((levels.hom.app P).app (op n)).f i).val.app (op V))
        (IntegralOnSlice.generator l E X none n (P.X i)
          (op ((inclusion j).obj V)) 1 x))
      (graphSection l E j n
        (((unrestrictedIntegralFiniteComplex l E X n).obj P).X i) V
        (unrestrictedIntegralTensorSection l E X n (P.X i)
          (op ((inclusion j).obj V)) 1 x))

/-- One of the original tower normalization equations.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
def ProductNormalization
    (_finite : ∀ n : ℕ, finiteRestriction l E j (coefficients l E j) n ≅
    integralOperationsLevelPullback l E j n)
    (levels : IntegralOnSlice.tower l E X none ⋙
      (Functor.whiskeringRight ℕᵒᵖ
        (IntegralOnSlice.Cx l E X none) (IntegralOnSlice.Cx l E U none)).obj
          (complexRestriction l E j) ≅
    integralOperationsPullbackTowerFunctor l E j)
    (product : ∀ P : IntegralOnSlice.Cx l E X none,
    (complexRestriction l E j).obj (∏ᶜ fun n : ℕ ↦ (sourceTower l E P).obj (op n)) ≅
      ∏ᶜ fun n : ℕ ↦ (targetTower l E j P).obj (op n))
    (_roos : IntegralOnSlice.roos l E X none ⋙ complexRestriction l E j ≅
    integralOperationsPullbackComplexFunctor l E j) : Prop :=
  ∀ (P : IntegralOnSlice.Cx l E X none) (n : ℕ),
    (product P).hom ≫ Pi.π (fun k : ℕ ↦ (targetTower l E j P).obj (op k)) n =
      (complexRestriction l E j).map
        (Pi.π (fun k : ℕ ↦ (sourceTower l E P).obj (op k)) n) ≫
          (levels.hom.app P).app (op n)

/-- One of the original tower normalization equations.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
def RoosFirstNormalization
    (_finite : ∀ n : ℕ, finiteRestriction l E j (coefficients l E j) n ≅
    integralOperationsLevelPullback l E j n)
    (_levels : IntegralOnSlice.tower l E X none ⋙
      (Functor.whiskeringRight ℕᵒᵖ
        (IntegralOnSlice.Cx l E X none) (IntegralOnSlice.Cx l E U none)).obj
          (complexRestriction l E j) ≅
    integralOperationsPullbackTowerFunctor l E j)
    (product : ∀ P : IntegralOnSlice.Cx l E X none,
    (complexRestriction l E j).obj (∏ᶜ fun n : ℕ ↦ (sourceTower l E P).obj (op n)) ≅
      ∏ᶜ fun n : ℕ ↦ (targetTower l E j P).obj (op n))
    (roos : IntegralOnSlice.roos l E X none ⋙ complexRestriction l E j ≅
    integralOperationsPullbackComplexFunctor l E j) : Prop :=
  ∀ P : IntegralOnSlice.Cx l E X none,
    roos.hom.app P ≫ roosProjection (A := IntegralOnSlice.Mod l E U none) (targetTower l E j P) =
      (complexRestriction l E j).map
        (roosProjection (A := IntegralOnSlice.Mod l E X none) (sourceTower l E P)) ≫
          (product P).hom

/-- One of the original tower normalization equations.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
def RoosSecondNormalization
    (_finite : ∀ n : ℕ, finiteRestriction l E j (coefficients l E j) n ≅
    integralOperationsLevelPullback l E j n)
    (_levels : IntegralOnSlice.tower l E X none ⋙
      (Functor.whiskeringRight ℕᵒᵖ
        (IntegralOnSlice.Cx l E X none) (IntegralOnSlice.Cx l E U none)).obj
          (complexRestriction l E j) ≅
    integralOperationsPullbackTowerFunctor l E j)
    (product : ∀ P : IntegralOnSlice.Cx l E X none,
    (complexRestriction l E j).obj (∏ᶜ fun n : ℕ ↦ (sourceTower l E P).obj (op n)) ≅
      ∏ᶜ fun n : ℕ ↦ (targetTower l E j P).obj (op n))
    (roos : IntegralOnSlice.roos l E X none ⋙ complexRestriction l E j ≅
    integralOperationsPullbackComplexFunctor l E j) : Prop :=
  ∀ (P : IntegralOnSlice.Cx l E X none) (q : ℤ),
    (roos.hom.app P).f q ≫
        roosSecond (A := IntegralOnSlice.Mod l E U none) (targetTower l E j P) q =
      (ordinary l E j).map
        (roosSecond (A := IntegralOnSlice.Mod l E X none) (sourceTower l E P) q) ≫
          (product P).hom.f (q - 1)

/-- The conjunction of the five original normalization equations.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
def TowerNormalization
    (finite : ∀ n : ℕ, finiteRestriction l E j (coefficients l E j) n ≅
    integralOperationsLevelPullback l E j n)
    (levels : IntegralOnSlice.tower l E X none ⋙
      (Functor.whiskeringRight ℕᵒᵖ
        (IntegralOnSlice.Cx l E X none) (IntegralOnSlice.Cx l E U none)).obj
          (complexRestriction l E j) ≅
    integralOperationsPullbackTowerFunctor l E j)
    (product : ∀ P : IntegralOnSlice.Cx l E X none,
    (complexRestriction l E j).obj (∏ᶜ fun n : ℕ ↦ (sourceTower l E P).obj (op n)) ≅
      ∏ᶜ fun n : ℕ ↦ (targetTower l E j P).obj (op n))
    (roos : IntegralOnSlice.roos l E X none ⋙ complexRestriction l E j ≅
    integralOperationsPullbackComplexFunctor l E j) : Prop :=
  FiniteSectionNormalization l E j finite levels product roos ∧
  LevelSectionNormalization l E j finite levels product roos ∧
  ProductNormalization l E j finite levels product roos ∧
  RoosFirstNormalization l E j finite levels product roos ∧
  RoosSecondNormalization l E j finite levels product roos

/-- Normalization data for the single natural comparison. The finite sections fix
its levels; the two shifted-cone coordinates fix the actual chain map. The final
factorization fixes its descent on every derived morphism, including roofs.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
def TowerComparison :=
  { d : (∀ n : ℕ, finiteRestriction l E j (coefficients l E j) n ≅
    integralOperationsLevelPullback l E j n) ×
    (IntegralOnSlice.tower l E X none ⋙
      (Functor.whiskeringRight ℕᵒᵖ
        (IntegralOnSlice.Cx l E X none) (IntegralOnSlice.Cx l E U none)).obj
          (complexRestriction l E j) ≅
    integralOperationsPullbackTowerFunctor l E j) ×
    (∀ P : IntegralOnSlice.Cx l E X none,
    (complexRestriction l E j).obj (∏ᶜ fun n : ℕ ↦ (sourceTower l E P).obj (op n)) ≅
      ∏ᶜ fun n : ℕ ↦ (targetTower l E j P).obj (op n)) ×
    (IntegralOnSlice.roos l E X none ⋙ complexRestriction l E j ≅
    integralOperationsPullbackComplexFunctor l E j) //
      TowerNormalization l E j d.1 d.2.1 d.2.2.1 d.2.2.2 }

variable {l E j} in
/-- The original finite comparison data.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev TowerComparison.finite (d : TowerComparison l E j) :
    ∀ n : ℕ, finiteRestriction l E j (coefficients l E j) n ≅
    integralOperationsLevelPullback l E j n :=
  d.val.1

variable {l E j} in
/-- The original levels comparison data.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev TowerComparison.levels (d : TowerComparison l E j) :
    IntegralOnSlice.tower l E X none ⋙
      (Functor.whiskeringRight ℕᵒᵖ
        (IntegralOnSlice.Cx l E X none) (IntegralOnSlice.Cx l E U none)).obj
          (complexRestriction l E j) ≅
    integralOperationsPullbackTowerFunctor l E j :=
  d.val.2.1

variable {l E j} in
/-- The original product comparison data.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev TowerComparison.product (d : TowerComparison l E j) :
    ∀ P : IntegralOnSlice.Cx l E X none,
    (complexRestriction l E j).obj (∏ᶜ fun n : ℕ ↦ (sourceTower l E P).obj (op n)) ≅
      ∏ᶜ fun n : ℕ ↦ (targetTower l E j P).obj (op n) :=
  d.val.2.2.1

variable {l E j} in
/-- The original roos comparison data.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev TowerComparison.roos (d : TowerComparison l E j) :
    IntegralOnSlice.roos l E X none ⋙ complexRestriction l E j ≅
    integralOperationsPullbackComplexFunctor l E j :=
  d.val.2.2.2

private theorem tower_normalized (d : TowerComparison l E j) :
    TowerNormalization l E j d.finite d.levels d.product d.roos := d.property

variable {l E j} in
/-- The original finite_sections equation, projected from normalization.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
theorem TowerComparison.finite_sections (d : TowerComparison l E j) :
    FiniteSectionNormalization l E j d.finite d.levels d.product d.roos :=
  (tower_normalized l E j d).1

variable {l E j} in
/-- The original level_sections equation, projected from normalization.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
theorem TowerComparison.level_sections (d : TowerComparison l E j) :
    LevelSectionNormalization l E j d.finite d.levels d.product d.roos :=
  (tower_normalized l E j d).2.1

variable {l E j} in
/-- The original product_projections equation, projected from normalization.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
theorem TowerComparison.product_projections (d : TowerComparison l E j) :
    ProductNormalization l E j d.finite d.levels d.product d.roos :=
  (tower_normalized l E j d).2.2.1

variable {l E j} in
/-- The original roos_first equation, projected from normalization.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
theorem TowerComparison.roos_first (d : TowerComparison l E j) :
    RoosFirstNormalization l E j d.finite d.levels d.product d.roos :=
  (tower_normalized l E j d).2.2.2.1

variable {l E j} in
/-- The original roos_second equation, projected from normalization.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
theorem TowerComparison.roos_second (d : TowerComparison l E j) :
    RoosSecondNormalization l E j d.finite d.levels d.product d.roos :=
  (tower_normalized l E j d).2.2.2.2


attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors

/-- The exact localization normalization as a proposition, keeping data-record recursors small.
Source: Stacks 015F, 08TC
(blueprint: lem-pur-open-completed-restriction-identification). -/
def ComparisonLocalization
    (roos : IntegralOnSlice.roos l E X none ⋙ complexRestriction l E j ≅
      integralOperationsPullbackComplexFunctor l E j)
    (derived : IntegralOnSlice.completion l E X none ⋙ derivedRestriction l E j ≅
      integralDerivedPullback l E j) : Prop :=
    ∀ P : (IntegralOnSlice.Good l E X none).FullSubcategory,
    derived.hom.app ((IntegralOnSlice.qGood l E X none).obj P) ≫
        (integralDerivedPullbackComparison l E j).hom.app P =
      (derivedRestriction l E j).map
        ((IntegralOnSlice.completionComparison l E X none).hom.app P) ≫
      (ordinary l E j).mapDerivedCategoryFactors.hom.app
        ((IntegralOnSlice.roos l E X none).obj P.obj) ≫
      DerivedCategory.Q.map (roos.hom.app P.obj)


/-- The descent of the normalized tower and Roos comparisons.
Source: Stacks 015F, 08TC
(blueprint: lem-pur-open-completed-restriction-identification). -/
def Comparison :=
  { d : TowerComparison l E j ×
      (IntegralOnSlice.completion l E X none ⋙ derivedRestriction l E j ≅
        integralDerivedPullback l E j) //
    ComparisonLocalization l E j d.1.roos d.2 }

variable {l E j} in
/-- The representative-level comparison data.
Source: Stacks 015F, 08TC
(blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev Comparison.toTowerComparison (d : Comparison l E j) : TowerComparison l E j := d.val.1

variable {l E j} in
/-- The inherited finite comparison.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev Comparison.finite (d : Comparison l E j) := d.toTowerComparison.finite

variable {l E j} in
/-- The inherited levels comparison.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev Comparison.levels (d : Comparison l E j) := d.toTowerComparison.levels

variable {l E j} in
/-- The inherited product comparison.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev Comparison.product (d : Comparison l E j) := d.toTowerComparison.product

variable {l E j} in
/-- The inherited roos comparison.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev Comparison.roos (d : Comparison l E j) := d.toTowerComparison.roos

variable {l E j} in
/-- The inherited finite_sections normalization equation.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
theorem Comparison.finite_sections (d : Comparison l E j) :
    FiniteSectionNormalization l E j d.finite d.levels d.product d.roos :=
  d.toTowerComparison.finite_sections

variable {l E j} in
/-- The inherited level_sections normalization equation.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
theorem Comparison.level_sections (d : Comparison l E j) :
    LevelSectionNormalization l E j d.finite d.levels d.product d.roos :=
  d.toTowerComparison.level_sections

variable {l E j} in
/-- The inherited product_projections normalization equation.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
theorem Comparison.product_projections (d : Comparison l E j) :
    ProductNormalization l E j d.finite d.levels d.product d.roos :=
  d.toTowerComparison.product_projections

variable {l E j} in
/-- The inherited roos_first normalization equation.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
theorem Comparison.roos_first (d : Comparison l E j) :
    RoosFirstNormalization l E j d.finite d.levels d.product d.roos :=
  d.toTowerComparison.roos_first

variable {l E j} in
/-- The inherited roos_second normalization equation.
Source: Stacks 00XZ, 08TC, 0941
(blueprint: lem-pur-open-completed-restriction-identification). -/
theorem Comparison.roos_second (d : Comparison l E j) :
    RoosSecondNormalization l E j d.finite d.levels d.product d.roos :=
  d.toTowerComparison.roos_second

variable {l E j} in
/-- The original derived comparison isomorphism.
Source: Stacks 015F, 08TC
(blueprint: lem-pur-open-completed-restriction-identification). -/
abbrev Comparison.derived (d : Comparison l E j) :
    IntegralOnSlice.completion l E X none ⋙ derivedRestriction l E j ≅
      integralDerivedPullback l E j := d.val.2

variable {l E j} in
/-- The original localization equation, projected from its proof record.
Source: Stacks 015F, 08TC
(blueprint: lem-pur-open-completed-restriction-identification). -/
theorem Comparison.localization (d : Comparison l E j) :
    ComparisonLocalization l E j d.roos d.derived := d.property


/-- Existence of the representative-normalized comparison, with no completeness
hypothesis on its unbounded source. In particular its source is restriction of
completion, and not ordinary restriction of an arbitrary uncompleted input.
Source: Stacks 00XZ, 08TC, 0941; blueprint def-pur-section-invariant, retained step 5
(blueprint: lem-pur-open-completed-restriction-identification).

Proof: (1) localize the site and use the constant-section-preserving finite ring
comparisons; sectionwise limits give the completed comparison. (2) The graph
coprojections identify finite inverse image with ordinary restriction, naturally
also for semilinear quotient maps. (3) On one flat-term K-flat representative use
P_n = P tensor B_n, with the actual 1 tensor rho transitions and p tensor 1 units.
The finite comparisons identify these strict towers, not just their derived levels.
(4) Restriction preserves sectionwise exact countable products. Apply the canonical
product comparison on both shifted-Roos coordinates; it preserves every projection
and the zero-second-coordinate augmentation. (5) Descend through the resolving
localization, whose universal property gives naturality for every derived roof
and the displayed Q factorization. (6) On complete inputs the canonical quotient
completion unit is invertible; compose its restriction with this same comparison.
The coordinate equations give every finite reduction and augmentation equation. -/
theorem open_completed_restriction
    (_hlX : ∀ x : X, Invertible (l : X.residueField x))
    (_hlU : ∀ x : U, Invertible (l : U.residueField x)) :
    Nonempty (Comparison l E j) := by
  sorry

/-- The canonical open comparison is restriction of the actual quotient completion
unit followed by the representative-normalized comparison. Its naturality includes
all derived roofs because both factors are natural transformations on D(R_X).
Source: Stacks 00XZ, 08TC, 0941; retained step 5 of def-pur-section-invariant
(blueprint: lem-pur-open-completed-restriction-identification). -/
def kappa (d : Comparison l E j) :
    derivedRestriction l E j ⟶ integralDerivedPullback l E j :=
  Functor.whiskerRight (IntegralOnSlice.completionUnit l E X none)
    (derivedRestriction l E j) ≫ d.derived.hom

private theorem kappa_isIso (d : Comparison l E j)
    (K : IntegralOnSlice.D l E X none)
    [IsIso ((IntegralOnSlice.completionUnit l E X none).app K)] :
    IsIso ((kappa l E j d).app K) := by
  change IsIso ((derivedRestriction l E j).map
    ((IntegralOnSlice.completionUnit l E X none).app K) ≫ d.derived.hom.app K)
  infer_instance

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem completeUnit
    (X : Scheme.{u}) (K : IntegralOnSlice.D.{u, u} l E X none)
    (hK : sfIntegralConstructible l E X K) :
    IsIso ((IntegralOnSlice.completionUnit.{u, u} l E X none).app K) := by
  classical
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  let D : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hprime
      exponent_pos := by decide
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl : l ≠ D.p := by change l ≠ p; omega
  have hcomplete : IsDerivedCompleteUnrestricted.{u, u} l E X K :=
    ⟨D, hl, (sfDerivedComplete_iff_legacy.{u, 0} l E X D hl K).mp hK.1⟩
  exact (show IsIso ((IntegralOnSlice.completionUnit.{u, u} l E X none).app K) from
    RoosIntrinsicUnitComparison.complete_unit_isIso.{u, u} l E X K hcomplete)


/-- On the recorded integral constructible full subcategory the specified canonical
map is invertible. The common ambient universe here is exactly that of the recorded
sfIntegralConstructible predicate; the unbounded comparison above retains independent
site and coefficient universes.
Source: Stacks 00XZ, 08TC, 0941, 0A0E; retained step 5 of def-pur-section-invariant
(blueprint: lem-pur-open-completed-restriction-identification).

Proof: use the constant-section-normalized coefficient isomorphisms and exact
restriction. On one flat-term K-flat representative, identify the actual finite
quotient towers through the graph coprojections, including their semilinear
transitions and reduction units. Restriction preserves sectionwise products, and
the comparison on both Roos coordinates preserves the projections and augmentation.
Descend the comparison through the resolving localization, with the specified Q
factorization, obtaining naturality on every derived roof. For a constructible
integral input, its derived completeness makes the canonical quotient completion
unit invertible by the completed-reduction augmentation theorem (identity tower
comparison and canonical reduction augmentation). Apply exact derived restriction
and then the first comparison isomorphism. This is precisely kappa, and its finite
projections are exactly the normalized reductions, by the first and second
Roos coordinate equations. Empty U, j = id and K = 0 use the
same constructions; no equivalence of ambient categories is required. -/
theorem open_completed_restriction_complete
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (_hlX : ∀ x : X, Invertible (l : X.residueField x))
    (_hlU : ∀ x : U, Invertible (l : U.residueField x)) :
    ∃ d : Comparison l E j,
      ∀ K : DerivedCategory (integralTowerModules l E X),
        sfIntegralConstructible l E X K → IsIso ((kappa l E j d).app K) := by
  classical
  let d : Comparison.{u, u} l E j :=
    Classical.choice (open_completed_restriction.{u, u} l E j _hlX _hlU)
  refine ⟨d, ?_⟩
  intro K hK
  let : IsIso ((IntegralOnSlice.completionUnit.{u, u} l E X none).app K) :=
    completeUnit l E X K hK
  exact kappa_isIso.{u, u} l E j d K

end WeilConjectures.OpenCompletedRestriction
