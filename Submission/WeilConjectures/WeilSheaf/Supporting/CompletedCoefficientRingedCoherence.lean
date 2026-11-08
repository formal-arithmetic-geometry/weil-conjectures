/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.Pullback

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Composition and slice localization of completed coefficient ring maps

Source: Stacks Project, Tag 04J0; Bhatt--Scholze, Proposition 6.6.11 and Remark 6.8.15
(blueprint: lem-tw-completed-coefficient-ringed-coherence).

The small pro-etale site keeps object universe t+1 and morphism universe t.
Coefficient values live in max u (t+1); the two input universes are independent.
Index n denotes the positive exponent n+1. All coefficient maps are fixed by
projections, and all geometric comparisons by their adjunction mates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe t u
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The recorded Kan-extension/sheafification inverse image at the coefficient size.
Source: Stacks 00VC, 09A5 (blueprint: lem-tw-completed-coefficient-ringed-coherence). -/
abbrev completedRingPull {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  letI : HasColimitsOfSize.{t, t + 1} CommRingCat.{max u (t + 1)} :=
    hasColimitsOfSizeShrink.{t, t + 1, max u (t + 1), max u (t + 1)} _
  Functor.sheafPullbackConstruction.sheafPullback (proEtaleBaseChange f)
    CommRingCat.{max u (t + 1)} (ProEt.topology Y) (ProEt.topology X)

/-- Its specified Kan-extension/sheafification adjunction.
Source: Stacks 00VC, 09A5 (blueprint: lem-tw-completed-coefficient-ringed-coherence). -/
abbrev completedRingAdj {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  letI : HasColimitsOfSize.{t, t + 1} CommRingCat.{max u (t + 1)} :=
    hasColimitsOfSizeShrink.{t, t + 1, max u (t + 1), max u (t + 1)} _
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (proEtaleBaseChange f)
    CommRingCat.{max u (t + 1)} (ProEt.topology Y) (ProEt.topology X)

/-- Constant-section structural map, using the recorded constant-section adjunct.
Source: Stacks 0H7J (blueprint: lem-tw-completed-coefficient-ringed-coherence). -/
def completedRingConstantMap {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : CommRingCat.{max u (t + 1)}) :
    (completedRingPull.{t, u} f).obj
        ((constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).obj A) ⟶
      (constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A :=
  ((completedRingAdj.{t, u} f).homEquiv _ _).symm
    (coefficientProEtaleDirectRingMap.{t, u} f A)

private instance completedWeakSheafify (W : Scheme.{t}) :
    (sheafToPresheaf (ProEt.topology W) CommRingCat.{max u (t + 1)}).IsRightAdjoint :=
  (integralCoefficientRingSheafify.{t, u} W).isRightAdjoint

private theorem completedDirect_unit {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : CommRingCat.{max u (t + 1)}) (H : Y.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app H ≫
        (coefficientProEtaleDirectRingMap f A).hom.app H =
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
        ((proEtaleBaseChange f).op.obj H) := by
  have h := ((sheafificationAdjunction (ProEt.topology Y)
    CommRingCat.{max u (t + 1)}).homEquiv
      ((Functor.const Y.ProEtᵒᵖ).obj A)
      (((proEtaleBaseChange f).sheafPushforwardContinuous
        CommRingCat.{max u (t + 1)} (ProEt.topology Y) (ProEt.topology X)).obj
          ((constantSheaf (ProEt.topology X) _).obj A))).apply_symm_apply
            (Functor.whiskerLeft (proEtaleBaseChange f).op
              (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))
  exact congrArg (fun a ↦ a.app H) h

private theorem completedConstant_naturality {X Y : Scheme.{t}} (f : X ⟶ Y)
    {A B : CommRingCat.{max u (t + 1)}} (a : A ⟶ B) :
    (completedRingPull.{t, u} f).map
        ((constantSheaf (ProEt.topology Y) _).map a) ≫ completedRingConstantMap f B =
      completedRingConstantMap f A ≫ (constantSheaf (ProEt.topology X) _).map a := by
  apply ((completedRingAdj.{t, u} f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [completedRingConstantMap, Equiv.apply_symm_apply]
  apply ((sheafificationAdjunction (ProEt.topology Y) _).homEquiv _ _).injective
  apply NatTrans.ext
  funext H
  change _ ≫ _ ≫ _ = _ ≫ _ ≫ _
  rw [← Category.assoc, ← Category.assoc]
  have h := congrArg (fun a ↦ a.app H)
    (toSheafify_naturality (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).map a))
  change a ≫ _ = _ ≫ _ at h
  erw [← h, Category.assoc, completedDirect_unit, completedDirect_unit]
  exact congrArg (fun a ↦ a.app ((proEtaleBaseChange f).op.obj H))
    (toSheafify_naturality (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map a))

attribute [-instance] completedWeakSheafify

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The projection equations determine exactly one structural ring map.
Source: Stacks 03CO, 04J0; Bhatt--Scholze 6.6.11
(blueprint: lem-tw-completed-coefficient-ringed-coherence).
Proof: the constant-section adjuncts commute with reductions, since their two
extensions agree on every constant. Compose the pulled-back projections with
these maps to obtain a cone in the target site. The sectionwise limit universal
property supplies the map and proves its uniqueness. No infinite-limit
preservation by inverse image is used. -/
theorem completedRingMap_existsUnique {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ∃! c : (completedRingPull.{t, u} f).obj
        (completedIntegralCommRingSheafUnrestricted l E Y) ⟶
          completedIntegralCommRingSheafUnrestricted l E X,
      ∀ n : ℕ, c ≫ completedIntegralCommRingProjectionUnrestricted l E X n =
        (completedRingPull.{t, u} f).map
          (completedIntegralCommRingProjectionUnrestricted l E Y n) ≫
            completedRingConstantMap f
              (CommRingCat.of (ULift.{t + 1}
                (Padic.coefficientExtensionRing l E (n + 1)))) := by
  let F := sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let d (n : ℕ) := (completedRingPull.{t, u} f).map
    (completedIntegralCommRingProjectionUnrestricted l E Y n) ≫
      completedRingConstantMap f
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))
  let c : Cone (integralCoefficientSheafSystem l E X) :=
    { pt := F.obj ((completedRingPull.{t, u} f).obj
        (completedIntegralCommRingSheafUnrestricted l E Y))
      π := NatTrans.ofOpSequence (fun n ↦ F.map (d n)) (by
        intro n
        simp only [Functor.const_obj_map, integralCoefficientSheafSystem,
          Functor.ofOpSequence_map_homOfLE_succ]
        change F.map (d n) = F.map (d (n + 1)) ≫ _
        change _ = F.map (d (n + 1)) ≫ F.map
          ((constantSheaf (ProEt.topology X) _).map _)
        rw [← F.map_comp]
        congr 1
        dsimp only [d]
        rw [Category.assoc, ← completedConstant_naturality, ← Category.assoc,
          ← Functor.map_comp]
        congr 2
        apply (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat RingCat)).map_injective
        change limit.π (integralCoefficientSheafSystem l E Y) (op n) =
          limit.π _ (op (n + 1)) ≫ integralCoefficientSheafTransition l E Y n
        simpa only [integralCoefficientSheafSystem,
          Functor.ofOpSequence_map_homOfLE_succ] using
          (limit.w (integralCoefficientSheafSystem l E Y)
            (homOfLE (Nat.le_succ n)).op).symm) }
  let m : (completedRingPull.{t, u} f).obj
      (completedIntegralCommRingSheafUnrestricted l E Y) ⟶
        completedIntegralCommRingSheafUnrestricted l E X := F.preimage (limit.lift _ c)
  have hm (n : ℕ) : m ≫ completedIntegralCommRingProjectionUnrestricted l E X n = d n := by
    apply F.map_injective
    change F.map m ≫ limit.π _ (op n) = _
    simp only [m, Functor.map_preimage]
    exact limit.lift_π c (op n)
  refine ⟨m, hm, ?_⟩
  intro m' hm'
  apply F.map_injective
  apply limit.hom_ext
  intro n
  change F.map m' ≫ limit.π _ n = F.map m ≫ limit.π _ n
  change F.map m' ≫ F.map (completedIntegralCommRingProjectionUnrestricted l E X n.unop) =
    F.map m ≫ F.map (completedIntegralCommRingProjectionUnrestricted l E X n.unop)
  rw [← F.map_comp, ← F.map_comp, hm', hm]

/-- The unique projection-defined completed coefficient map, with no extra choices.
Source: Stacks 04J0 (blueprint: lem-tw-completed-coefficient-ringed-coherence). -/
def completedRingMap {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (completedRingPull.{t, u} f).obj (completedIntegralCommRingSheafUnrestricted l E Y) ⟶
      completedIntegralCommRingSheafUnrestricted l E X :=
  (completedRingMap_existsUnique l E f).exists.choose

/-- The base-changed object's morphism to the original object.
Source: Stacks 04J0 (blueprint: lem-tw-completed-coefficient-ringed-coherence). -/
abbrev completedRingSliceArrow {T W : Scheme.{t}} (g : T ⟶ W) (U : W.ProEt) :
    ((proEtaleBaseChange g).obj U).left ⟶ U.left :=
  pullback.fst U.hom g

/-- The actual geometric identification H ×_U (U ×_W T) ≅ H ×_W T over T.
Source: Stacks 04J0 (blueprint: lem-tw-completed-coefficient-ringed-coherence). -/
def completedRingSlicePointIso {T W : Scheme.{t}} (g : T ⟶ W) (U : W.ProEt)
    (H : U.left.ProEt) :
    (MorphismProperty.Over.map ⊤ ((proEtaleBaseChange g).obj U).prop).obj
        ((proEtaleBaseChange (completedRingSliceArrow g U)).obj H) ≅
      (proEtaleBaseChange g).obj ((MorphismProperty.Over.map ⊤ U.prop).obj H) :=
  MorphismProperty.Over.isoMk (pullbackRightPullbackFstIso U.hom g H.hom) (by
    change (pullbackRightPullbackFstIso U.hom g H.hom).hom ≫
      pullback.snd (H.hom ≫ U.hom) g =
        pullback.snd H.hom (pullback.fst U.hom g) ≫ pullback.snd U.hom g
    exact pullbackRightPullbackFstIso_hom_snd U.hom g H.hom)

section SliceProof

set_option backward.defeqAttrib.useBackward true

private theorem completed_inverseMate_app
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D} (a : L ⊣ R) (b : L' ⊣ R')
    (β : R ⋙ G ⟶ H ⋙ R') (X : A) :
    (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ β)).natTrans).app X =
      L'.map (G.map (a.unit.app X)) ≫ L'.map (β.app (L.obj X)) ≫
        b.counit.app (H.obj (L.obj X)) := by
  simp [mateEquiv]

private theorem completed_iteratedInverseMate_isIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : F₁ ⊣ U₁) (d : F₂ ⊣ U₂)
    (α : TwoSquare U₂ R₂ R₁ U₁) [IsIso α.natTrans] :
    IsIso (((mateEquiv a b).symm ((mateEquiv d c).symm α)).natTrans) := by
  rw [iterated_mateEquiv_conjugateEquiv_symm]
  change IsIso ((conjugateEquiv (a.comp d) (c.comp b)).symm α.natTrans)
  infer_instance

private abbrev completedRestrictFunctor {W : Scheme.{t}} (U : W.ProEt) :=
  MorphismProperty.Over.map ⊤ U.prop

private instance completedRestrictContinuous {W : Scheme.{t}} (U : W.ProEt) :
    (completedRestrictFunctor U).IsContinuous (ProEt.topology U.left) (ProEt.topology W) :=
  ProEt.isContinuous_overMap U.prop

private instance completedRestrictCocontinuous {W : Scheme.{t}} (U : W.ProEt) :
    (completedRestrictFunctor U).IsCocontinuous (ProEt.topology U.left) (ProEt.topology W) :=
  ProEt.isCocontinuous_overMap U.prop

private abbrev completedRestrict {W : Scheme.{t}} (U : W.ProEt) :=
  (completedRestrictFunctor U).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
    (ProEt.topology U.left) (ProEt.topology W)

section ConstantRestriction

variable {C D A : Type*} [Category C] [Category D] [Category A]
  (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K] [G.IsCocontinuous J K]
  [∀ (F : Cᵒᵖ ⥤ A), G.op.HasPointwiseRightKanExtension F]
  [HasWeakSheafify J A] [HasWeakSheafify K A]

private def completedConstantRestrictionIso (a : A) :
    (G.sheafPushforwardContinuous A J K).obj ((constantSheaf K A).obj a) ≅
      (constantSheaf J A).obj a :=
  ((G.pushforwardContinuousSheafificationCompatibility A J K).app
    ((Functor.const Dᵒᵖ).obj a)).symm

private theorem completedConstantRestrictionIso_naturality {a b : A} (f : a ⟶ b) :
    (G.sheafPushforwardContinuous A J K).map ((constantSheaf K A).map f) ≫
      (completedConstantRestrictionIso G J K b).hom =
    (completedConstantRestrictionIso G J K a).hom ≫ (constantSheaf J A).map f := by
  exact (G.pushforwardContinuousSheafificationCompatibility A J K).inv.naturality
    ((Functor.const Dᵒᵖ).map f)

end ConstantRestriction

private def completedRestrictConstant {W : Scheme.{t}} (U : W.ProEt)
    (A : CommRingCat.{max u (t + 1)}) :
    (completedRestrict.{t, u} U).obj ((constantSheaf (ProEt.topology W) _).obj A) ≅
      (constantSheaf (ProEt.topology U.left) _).obj A := by
  let : HasWeakSheafify (ProEt.topology W) CommRingCat.{max u (t + 1)} :=
    (integralCoefficientRingSheafify.{t, u} W).isRightAdjoint
  let : HasWeakSheafify (ProEt.topology U.left) CommRingCat.{max u (t + 1)} :=
    (integralCoefficientRingSheafify.{t, u} U.left).isRightAdjoint
  let : HasLimitsOfSize.{t + 1, t + 1} CommRingCat.{max u (t + 1)} :=
    hasLimitsOfSizeShrink _
  exact completedConstantRestrictionIso (A := CommRingCat.{max u (t + 1)})
    (completedRestrictFunctor U)
    (ProEt.topology U.left) (ProEt.topology W) A

private theorem completedRestrictConstant_naturality {W : Scheme.{t}} (U : W.ProEt)
    {A B : CommRingCat.{max u (t + 1)}} (a : A ⟶ B) :
    (completedRestrict.{t, u} U).map ((constantSheaf (ProEt.topology W) _).map a) ≫
      (completedRestrictConstant.{t, u} U B).hom =
    (completedRestrictConstant.{t, u} U A).hom ≫
      (constantSheaf (ProEt.topology U.left) _).map a := by
  let : HasWeakSheafify (ProEt.topology W) CommRingCat.{max u (t + 1)} :=
    (integralCoefficientRingSheafify.{t, u} W).isRightAdjoint
  let : HasWeakSheafify (ProEt.topology U.left) CommRingCat.{max u (t + 1)} :=
    (integralCoefficientRingSheafify.{t, u} U.left).isRightAdjoint
  let : HasLimitsOfSize.{t + 1, t + 1} CommRingCat.{max u (t + 1)} :=
    hasLimitsOfSizeShrink _
  exact completedConstantRestrictionIso_naturality (A := CommRingCat.{max u (t + 1)})
    (completedRestrictFunctor U)
    (ProEt.topology U.left) (ProEt.topology W) a

attribute [irreducible] completedRestrictConstant

private abbrev completedRestrictRings {W : Scheme.{t}} (U : W.ProEt) :=
  (completedRestrictFunctor U).sheafPushforwardContinuous RingCat.{max u (t + 1)}
    (ProEt.topology U.left) (ProEt.topology W)

private instance completedRestrictRings_limits {W : Scheme.{t}} (U : W.ProEt) :
    PreservesLimitsOfShape ℕᵒᵖ (completedRestrictRings.{t, u} U) := by
  apply preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf (ProEt.topology U.left) RingCat.{max u (t + 1)})

private def completedRestrictDiagram {W : Scheme.{t}} (U : W.ProEt) :
    integralCoefficientSheafSystem l E W ⋙ completedRestrictRings.{t, u} U ≅
      integralCoefficientSheafSystem l E U.left := by
  let F := sheafCompose (ProEt.topology U.left)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let a : integralCoefficientSheafSystem l E W ⋙ completedRestrictRings.{t, u} U ⟶
      integralCoefficientSheafSystem l E U.left :=
    NatTrans.ofOpSequence
      (F := integralCoefficientSheafSystem l E W ⋙ completedRestrictRings.{t, u} U)
      (G := integralCoefficientSheafSystem l E U.left) (fun n ↦ F.map
      (completedRestrictConstant.{t, u} U (CommRingCat.of
        (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom) (by
      intro n
      simp only [Functor.comp_map, integralCoefficientSheafSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      have h := congrArg F.map (completedRestrictConstant_naturality.{t, u} U
        (CommRingCat.ofHom
          ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
            ((Padic.coefficientExtensionTransition l E (n + 1)).comp
              (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))))
      simp only [Functor.map_comp] at h
      exact h)
  have : IsIso a := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    change IsIso (F.map (completedRestrictConstant.{t, u} U (CommRingCat.of
      (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n.unop + 1))))).hom)
    infer_instance
  exact asIso a

private def completedRestrictCompletion {W : Scheme.{t}} (U : W.ProEt) :
    (completedRestrict.{t, u} U).obj
        (completedIntegralCommRingSheafUnrestricted l E W) ≅
      completedIntegralCommRingSheafUnrestricted l E U.left := by
  let F := sheafCompose (ProEt.topology U.left)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  exact F.preimageIso
    (preservesLimitIso (completedRestrictRings.{t, u} U)
      (integralCoefficientSheafSystem l E W) ≪≫
        HasLimit.isoOfNatIso (completedRestrictDiagram.{t, u} l E U))

attribute [irreducible] completedRestrictCompletion

private instance completedObjectBaseContinuous {W : Scheme.{t}} (U : W.ProEt) :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology W) (ProEt.topology U.left) :=
  ProEt.isContinuous_overPullback U.hom

private abbrev completedObjectPush {W : Scheme.{t}} (U : W.ProEt) :=
  letI : (proEtaleBaseChange U.hom).IsContinuous
      (ProEt.topology W) (ProEt.topology U.left) :=
    ProEt.isContinuous_overPullback U.hom
  (proEtaleBaseChange U.hom).sheafPushforwardContinuous
    CommRingCat.{max u (t + 1)} (ProEt.topology W) (ProEt.topology U.left)

private def completedRestrictionAdj {W : Scheme.{t}} (U : W.ProEt) :
    completedRestrict.{t, u} U ⊣
      completedObjectPush.{t, u} U :=
  Adjunction.sheafPushforwardContinuous (E := CommRingCat.{max u (t + 1)})
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ U.hom U.prop trivial)
    (ProEt.topology U.left) (ProEt.topology W)

private def completedSliceRightIso {T W : Scheme.{t}} (g : T ⟶ W) (U : W.ProEt) :
    proEtaleBaseChange U.hom ⋙ proEtaleBaseChange (completedRingSliceArrow g U) ≅
      proEtaleBaseChange g ⋙ proEtaleBaseChange ((proEtaleBaseChange g).obj U).hom :=
  (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
    (completedRingSliceArrow g U) U.hom).symm ≪≫
  MorphismProperty.Over.pullbackCongr (pullback.condition (f := U.hom) (g := g)) ≪≫
  MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
    ((proEtaleBaseChange g).obj U).hom g

private def completedSliceGamma {T W : Scheme.{t}} (g : T ⟶ W) (U : W.ProEt) :
    completedObjectPush.{t, u} ((proEtaleBaseChange g).obj U) ⋙
      (proEtaleBaseChange g).sheafPushforwardContinuous
        CommRingCat.{max u (t + 1)} (ProEt.topology W) (ProEt.topology T) ≅
    (proEtaleBaseChange (completedRingSliceArrow g U)).sheafPushforwardContinuous
        CommRingCat.{max u (t + 1)} (ProEt.topology U.left)
          (ProEt.topology ((proEtaleBaseChange g).obj U).left) ⋙
      completedObjectPush.{t, u} U :=
  letI : (proEtaleBaseChange U.hom).IsContinuous
      (ProEt.topology W) (ProEt.topology U.left) :=
    ProEt.isContinuous_overPullback U.hom
  letI : (proEtaleBaseChange ((proEtaleBaseChange g).obj U).hom).IsContinuous
      (ProEt.topology T) (ProEt.topology ((proEtaleBaseChange g).obj U).left) :=
    ProEt.isContinuous_overPullback ((proEtaleBaseChange g).obj U).hom
  letI : (proEtaleBaseChange (completedRingSliceArrow g U)).IsContinuous
      (ProEt.topology U.left) (ProEt.topology ((proEtaleBaseChange g).obj U).left) :=
    ProEt.isContinuous_overPullback (completedRingSliceArrow g U)
  letI := Functor.isContinuous_comp (proEtaleBaseChange g)
    (proEtaleBaseChange ((proEtaleBaseChange g).obj U).hom)
    (ProEt.topology W) (ProEt.topology T)
    (ProEt.topology ((proEtaleBaseChange g).obj U).left)
  letI := Functor.isContinuous_comp (proEtaleBaseChange U.hom)
    (proEtaleBaseChange (completedRingSliceArrow g U))
    (ProEt.topology W) (ProEt.topology U.left)
    (ProEt.topology ((proEtaleBaseChange g).obj U).left)
  Functor.sheafPushforwardContinuousComp _ _ CommRingCat.{max u (t + 1)}
    (ProEt.topology W) (ProEt.topology T)
      (ProEt.topology ((proEtaleBaseChange g).obj U).left) ≪≫
  Functor.sheafPushforwardContinuousIso (completedSliceRightIso g U).symm
    CommRingCat.{max u (t + 1)} (ProEt.topology W)
      (ProEt.topology ((proEtaleBaseChange g).obj U).left) ≪≫
  (Functor.sheafPushforwardContinuousComp _ _ CommRingCat.{max u (t + 1)}
    (ProEt.topology W) (ProEt.topology U.left)
      (ProEt.topology ((proEtaleBaseChange g).obj U).left)).symm

private def completedSliceBeta {T W : Scheme.{t}} (g : T ⟶ W) (U : W.ProEt) :=
  ((mateEquiv (completedRestrictionAdj.{t, u} ((proEtaleBaseChange g).obj U))
    (completedRestrictionAdj.{t, u} U)).symm
      (TwoSquare.mk _ _ _ _ (completedSliceGamma.{t, u} g U).hom)).natTrans

private def completedSliceLambda {T W : Scheme.{t}} (g : T ⟶ W) (U : W.ProEt) :=
  ((mateEquiv (completedRingAdj.{t, u} g)
    (completedRingAdj.{t, u} (completedRingSliceArrow g U))).symm
      (TwoSquare.mk _ _ _ _ (completedSliceBeta.{t, u} g U))).natTrans

private theorem completedProEt_comp_left {W : Scheme.{t}} {A B C : W.ProEt}
    (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).left = f.left ≫ g.left := rfl

private theorem completedSliceBeta_app {T W : Scheme.{t}} (g : T ⟶ W) (U : W.ProEt)
    (F : Sheaf (ProEt.topology T) CommRingCat.{max u (t + 1)}) (H : U.left.ProEt) :
    ((completedSliceBeta.{t, u} g U).app F).hom.app (op H) =
      F.obj.map (completedRingSlicePointIso g U H).hom.op := by
  dsimp only [completedSliceBeta]
  rw [completed_inverseMate_app]
  change F.obj.map _ ≫ (𝟙 _ ≫ F.obj.map _ ≫ 𝟙 _) ≫ F.obj.map _ = _
  simp only [Category.id_comp, Category.comp_id]
  rw [← F.obj.map_comp, ← F.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  simp only [unop_comp, completedProEt_comp_left]
  apply pullback.hom_ext <;>
    simp [completedSliceRightIso, completedRingSlicePointIso,
      completedRestrictFunctor, MorphismProperty.Over.mapPullbackAdj,
      MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackCongr,
      proEtaleBaseChange, completedRingSliceArrow, completedProEt_comp_left]

private instance completedSliceBeta_isIso {T W : Scheme.{t}} (g : T ⟶ W)
    (U : W.ProEt) : IsIso (completedSliceBeta.{t, u} g U) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _),
    NatTrans.isIso_iff_isIso_app]
  intro H
  change IsIso (((completedSliceBeta.{t, u} g U).app F).hom.app H)
  rw [completedSliceBeta_app g U F H.unop]
  infer_instance

attribute [irreducible] completedRestrictionAdj completedSliceGamma

private instance completedSliceLambda_isIso {T W : Scheme.{t}} (g : T ⟶ W)
    (U : W.ProEt) : IsIso (completedSliceLambda.{t, u} g U) := by
  exact completed_iteratedInverseMate_isIso (completedRingAdj.{t, u} g)
    (completedRingAdj.{t, u} (completedRingSliceArrow g U))
    (completedRestrictionAdj.{t, u} U)
    (completedRestrictionAdj.{t, u} ((proEtaleBaseChange g).obj U))
    (TwoSquare.mk _ _ _ _ (completedSliceGamma.{t, u} g U).hom)

attribute [irreducible] completedSliceBeta completedSliceLambda

section ConstantCompatibility

attribute [local implicit_reducible] MorphismProperty

end ConstantCompatibility

attribute [local implicit_reducible] MorphismProperty Scheme.ProEt
  Scheme.instCategoryProEt

end SliceProof

end WeilConjectures
