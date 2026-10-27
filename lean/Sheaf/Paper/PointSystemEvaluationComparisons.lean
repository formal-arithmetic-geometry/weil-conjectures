/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G9
-/
module

public import Sheaf.Paper.PointRestrictionSystemChainMap
import all Sheaf.Paper.PointRestrictionSystemChainMap
import all Sheaf.Paper.PointAutomorphismRestrictionNatural

/-! # Ordinary evaluation comparisons for point-system transport

The comparisons hold for every point automorphism, with the specified inverse
coefficient action. This isolates the ordinary evaluation construction from derived
transport. Source: sk-prop-tf-transport-integral proof, scalar comparisons and pullback
compatibility; agent-formulated ordinary-system refinement
(blueprint: lem-trf-point-system-ordinary-evaluation-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
universe t u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointSystemEvaluation
variable (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g]

private def quotient (n : ℕ) : pointRestrictionScalars.{t, u} l E none →+*
    pointRestrictionScalars.{t, u} l E (some n) :=
  RingHom.ulift (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))

section

attribute [local irreducible] quotient

private abbrev finiteRSections (n : ℕ) :=
  pointRestrictionSections l E D.k (some n) ⋙
    ModuleCat.restrictScalars.{max u (t + 1)} (quotient.{t, u} l E n)

private abbrev towerEvaluation (n : ℕ) :=
  (evaluation ℕᵒᵖ (ModuleCat.{max u (t + 1)}
    (pointRestrictionScalars.{t, u} l E none))).obj (op n)

private def moduleIso {R : Type*} [Ring R] (M N : ModuleCat R)
    (e : M ≃ₗ[R] N) : M ≅ N := LinearEquiv.toModuleIso e

private theorem coefficient_app (n : ℕ) (U : (Spec (.of D.k)).ProEt) :
      (PointRestrictionSystem.coefficient D l E g).hom.app (op (n, U)) =
        (inv (inverseImageFiniteCoefficientMap l E g n)).hom.app
          (op U) :=
    eq_of_heq ((PointRestrictionSystem.coefficient_existsUnique D l E g).exists.choose_spec n U)
private theorem evaluationRing_app (n : ℕ) (U : (Spec (.of D.k)).ProEtᵒᵖ) :
      (eqToHom (coefficientSequenceEvaluationRing_eq l E
        (Spec (.of D.k)) n).symm).hom.app U = 𝟙 _ := by
    rw [ObjectProperty.eqToHom_hom, eqToHom_app]
    rfl

attribute [local irreducible] PointRestrictionSystem.coefficient
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  CategoryTheory.sheafCompose

private abbrev levelCast (n : ℕ) :=
  eqToHom (coefficientSequenceEvaluationRing_eq l E (Spec (.of D.k)) n).symm

private theorem finiteLevelSquare (n : ℕ) :
    levelCast D l E n ≫
      ((Prod.sectR n (Spec (.of D.k)).ProEt).sheafPushforwardContinuous RingCat
        (ProEt.topology (Spec (.of D.k)))
        (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k))))).map
          (PointRestrictionSystem.coefficient D l E g) =
    inv (inverseImageFiniteCoefficientMap l E g n) ≫
      ((proEtaleIsoPostcompose g).sheafPushforwardContinuous RingCat
        (ProEt.topology (Spec (.of D.k))) (ProEt.topology (Spec (.of D.k)))).map
        (levelCast D l E n) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change (levelCast D l E n).hom.app U ≫
    (PointRestrictionSystem.coefficient D l E g).hom.app (op (n, U.unop)) =
      (inv (inverseImageFiniteCoefficientMap l E g n)).hom.app U ≫
        (levelCast D l E n).hom.app
          (op ((proEtaleIsoPostcompose g).obj U.unop))
  have he (V : (Spec (.of D.k)).ProEtᵒᵖ) : (levelCast D l E n).hom.app V = 𝟙 _ :=
    evaluationRing_app D l E n V
  have hc : (PointRestrictionSystem.coefficient D l E g).hom.app (op (n, U.unop)) =
      (inv (inverseImageFiniteCoefficientMap l E g n)).hom.app U := by
    exact coefficient_app D l E g n U.unop
  exact ((congrArg (fun f ↦ f ≫
      (PointRestrictionSystem.coefficient D l E g).hom.app (op (n, U.unop))) (he U)).trans
        (Category.id_comp _)).trans
    (hc.trans ((congrArg (fun f ↦
      (inv (inverseImageFiniteCoefficientMap l E g n)).hom.app U ≫ f)
      (he (op ((proEtaleIsoPostcompose g).obj U.unop)))).trans
        (Category.comp_id _)).symm)

private def finiteLevelIso (n : ℕ) :
    PointRestrictionSystem.pull D l E g ⋙ coefficientSequenceEvaluation l E (Spec (.of D.k)) n ≅
      coefficientSequenceEvaluation l E (Spec (.of D.k)) n ⋙
        inverseImageFiniteModules l E g n := by
  letI := Functor.isContinuous_comp (Prod.sectR n (Spec (.of D.k)).ProEt)
    (PointRestrictionSystem.reindex D g)
    (ProEt.topology (Spec (.of D.k)))
    (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k))))
    (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k))))
  unfold PointRestrictionSystem.pull coefficientSequenceEvaluation inverseImageFiniteModules
    isoSectionwiseModuleInverseImage
  exact SheafOfModules.pushforwardComp
    (F := Prod.sectR n (Spec (.of D.k)).ProEt) (G := PointRestrictionSystem.reindex D g)
    (levelCast D l E n) (PointRestrictionSystem.coefficient D l E g) ≪≫
    SheafOfModules.pushforwardCongr
      (F := Prod.sectR n (Spec (.of D.k)).ProEt ⋙ PointRestrictionSystem.reindex D g)
      (finiteLevelSquare D l E g n) ≪≫
    (SheafOfModules.pushforwardComp
      (F := proEtaleIsoPostcompose g)
      (G := Prod.sectR n (Spec (.of D.k)).ProEt)
      (inv (inverseImageFiniteCoefficientMap l E g n))
      (levelCast D l E n)).symm

private abbrev projection (n : ℕ) :=
  (sheafCompose (ProEt.topology (Spec (.of D.k)))
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (completedIntegralCommRingProjectionUnrestricted l E (Spec (.of D.k)) n)

private theorem projection_app (n : ℕ) (U : (Spec (.of D.k)).ProEtᵒᵖ) :
    (projection D l E n).hom.app U =
      (limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n)).hom.app U := by
  rfl

private theorem projection_scalar (n : ℕ) (U : (Spec (.of D.k)).ProEt)
    (b : pointRestrictionScalars.{t, u} l E none) :
    (projection D l E n).hom.app (op U)
      (pointRestrictionScalarAt l E (Spec (.of D.k)) none U b) =
    pointRestrictionScalarAt l E (Spec (.of D.k)) (some n) U (quotient l E n b) := by
  have h := ConcreteCategory.congr_hom (C := RingCat) (projection_app D l E n (op U))
    (pointRestrictionScalarAt l E (Spec (.of D.k)) none U b)
  refine h.trans ((integral_projection l E _ n U b).trans ?_)
  have hq : quotient l E n b =
      (⟨Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) b.down⟩ :
        ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))) := by
    unfold quotient
    rfl
  rw [hq]
  exact quotient_constant l E _ n U b

private def finiteSectionsRestrictionIso (n : ℕ) :
    scalarReductionRestriction l E (Spec (.of D.k)) n ⋙
      pointRestrictionSections l E D.k none ≅ finiteRSections D l E n := by
  refine NatIso.ofComponents (fun N ↦ ?_) ?_
  · refine moduleIso
      ((scalarReductionRestriction l E (Spec (.of D.k)) n ⋙
        pointRestrictionSections l E D.k none).obj N)
      ((finiteRSections D l E n).obj N)
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := ?_ }
    intro b x
    exact congrArg
      (fun a : (integralCoefficientSheaf l E (Spec (.of D.k)) n).obj.obj
        (op (ProEt.mk (𝟙 _))) ↦ a • (show N.val.obj (op (ProEt.mk (𝟙 _))) from x))
      (projection_scalar D l E n (ProEt.mk (𝟙 _)) b)
  · intro M N f
    ext x
    rfl

private def pushforwardRestrictIso
    {C B : Type*} [Category* C] [Category* B]
    {J : GrothendieckTopology C} {K : GrothendieckTopology B}
    (F : C ⥤ B) [F.IsContinuous J K]
    {A A' : Sheaf J RingCat.{v}} {R : Sheaf K RingCat.{v}}
    (p : A ⟶ A') (φ : A' ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R) :
    SheafOfModules.pushforward.{v} (p ≫ φ) ≅
      SheafOfModules.pushforward.{v} φ ⋙ SheafOfModules.restrictScalars.{v} p :=
  Iso.refl _

private def levelRestrictionIso (n : ℕ) :
    PointRestrictionSystem.concreteRestriction D l E ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E (Spec (.of D.k)))).obj (op n) ≅
      coefficientSequenceEvaluation l E (Spec (.of D.k)) n ⋙
        scalarReductionRestriction l E (Spec (.of D.k)) n := by
  change SheafOfModules.pushforward (PointRestrictionSystem.scalarLeg D l E n) ≅ _
  dsimp only [coefficientSequenceEvaluation, scalarReductionRestriction]
  exact pushforwardRestrictIso (Prod.sectR n (Spec (.of D.k)).ProEt)
    (projection D l E n)
    (eqToHom (coefficientSequenceEvaluationRing_eq l E (Spec (.of D.k)) n).symm)

private def evaluationWhiskeringIso
    {C A B I : Type*} [Category* C] [Category* A] [Category* B] [Category* I]
    (H : C ⥤ I ⥤ A) (F : A ⥤ B) (i : I) :
    (H ⋙ (Functor.whiskeringRight I A B).obj F) ⋙ (evaluation I B).obj i ≅
      (H ⋙ (evaluation I A).obj i) ⋙ F := Iso.refl _

private def ordinarySourceEvaluation (n : ℕ) :
    (PointRestrictionSystem.concreteSections D l E ⋙ towerEvaluation l E n) ≅
      coefficientSequenceEvaluation l E (Spec (.of D.k)) n ⋙ finiteRSections D l E n :=
  evaluationWhiskeringIso (PointRestrictionSystem.concreteRestriction D l E)
    (pointRestrictionSections l E D.k none) (op n) ≪≫
  Functor.isoWhiskerRight (levelRestrictionIso D l E n)
    (pointRestrictionSections l E D.k none) ≪≫
  Functor.associator (coefficientSequenceEvaluation l E (Spec (.of D.k)) n)
    (scalarReductionRestriction l E (Spec (.of D.k)) n)
    (pointRestrictionSections l E D.k none) ≪≫
  Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E (Spec (.of D.k)) n)
    (finiteSectionsRestrictionIso D l E n)

private def ordinaryTargetEvaluation (n : ℕ) :
    ((PointRestrictionSystem.pull D l E g ⋙ PointRestrictionSystem.concreteSections D l E) ⋙
      towerEvaluation l E n) ≅
    coefficientSequenceEvaluation l E (Spec (.of D.k)) n ⋙
      (inverseImageFiniteModules l E g n ⋙ finiteRSections D l E n) :=
  Functor.associator (PointRestrictionSystem.pull D l E g)
    (PointRestrictionSystem.concreteSections D l E)
    (towerEvaluation l E n) ≪≫
  Functor.isoWhiskerLeft (PointRestrictionSystem.pull D l E g) (ordinarySourceEvaluation D l E n) ≪≫
  (Functor.associator (PointRestrictionSystem.pull D l E g)
    (coefficientSequenceEvaluation l E (Spec (.of D.k)) n)
    (finiteRSections D l E n)).symm ≪≫
  Functor.isoWhiskerRight (finiteLevelIso D l E g n) (finiteRSections D l E n) ≪≫
  Functor.associator (coefficientSequenceEvaluation l E (Spec (.of D.k)) n)
    (inverseImageFiniteModules l E g n) (finiteRSections D l E n)

private theorem moduleNatIso_ext
    {C : Type*} [Category* C] {R : Type*} [Ring R]
    {F G : C ⥤ ModuleCat R} (e f : F ≅ G)
    (h : ∀ M, HEq (fun x ↦ e.hom.app M x) (fun x ↦ f.hom.app M x)) : e = f := by
  apply Iso.ext
  ext M x
  exact congrFun (eq_of_heq (h M)) x

private theorem ordinarySourceEvaluation_normalization (n : ℕ)
    (M : coefficientSequenceModules l E (Spec (.of D.k))) :
    HEq (fun x : ((PointRestrictionSystem.concreteSections D l E).obj M).obj (op n) ↦
      (ordinarySourceEvaluation D l E n).hom.app M x)
    (fun x : M.val.obj (op (n, ProEt.mk (𝟙 (Spec (.of D.k))))) ↦ x) := HEq.rfl

private theorem ordinaryTargetEvaluation_normalization (n : ℕ)
    (M : coefficientSequenceModules l E (Spec (.of D.k))) :
    HEq (fun x : ((PointRestrictionSystem.concreteSections D l E).obj
        ((PointRestrictionSystem.pull D l E g).obj M)).obj (op n) ↦
      (ordinaryTargetEvaluation D l E g n).hom.app M x)
    (fun x : M.val.obj (op (n,
      (proEtaleIsoPostcompose g).obj
        (ProEt.mk (𝟙 (Spec (.of D.k)))))) ↦ x) := HEq.rfl

end

attribute [local irreducible] ordinarySourceEvaluation ordinaryTargetEvaluation

/-- Canonical evaluation comparisons are identity on all underlying sections.
Source: sk-prop-tf-transport-integral proof, scalar comparisons and pullback
compatibility; agent-formulated ordinary-system refinement
(blueprint: lem-trf-point-system-ordinary-evaluation-comparisons).
Proof: restricting through the completion and then through R has the quotient
R→A_n action, by the completed projection equation. The sequence reindexing is
(n,U)↦(n,g U), with action c_n inverse, exactly the finite inverse image. Thus
identity on the section carriers is linear, natural and inverse to itself on both
sides. Equality on every section proves uniqueness of the pair of comparisons. -/
theorem evaluation_existsUnique (n : ℕ) :
    ∃! e :
      (PointRestrictionSystem.sections D l E ⋙ (evaluation ℕᵒᵖ (ModuleCat.{max u (t + 1)}
          (pointRestrictionScalars.{t, u} l E none))).obj (op n) ≅
        coefficientSequenceEvaluation l E (Spec (.of D.k)) n ⋙
          (pointRestrictionSections l E D.k (some n) ⋙
          ModuleCat.restrictScalars.{max u (t + 1)}
            (show pointRestrictionScalars.{t, u} l E none →+*
              pointRestrictionScalars.{t, u} l E (some n) from
            RingHom.ulift (Ideal.Quotient.mk
              (Padic.coefficientExtensionIdeal l E (n + 1)))))) ×
      ((PointRestrictionSystem.pull D l E g ⋙ PointRestrictionSystem.sections D l E) ⋙
        (evaluation ℕᵒᵖ (ModuleCat.{max u (t + 1)}
          (pointRestrictionScalars.{t, u} l E none))).obj (op n) ≅
        coefficientSequenceEvaluation l E (Spec (.of D.k)) n ⋙
          (inverseImageFiniteModules.{t, u} l E g n ⋙ (pointRestrictionSections l E D.k (some n) ⋙
          ModuleCat.restrictScalars.{max u (t + 1)}
            (show pointRestrictionScalars.{t, u} l E none →+*
              pointRestrictionScalars.{t, u} l E (some n) from
            RingHom.ulift (Ideal.Quotient.mk
              (Padic.coefficientExtensionIdeal l E (n + 1))))))),
      ∀ M : coefficientSequenceModules l E (Spec (.of D.k)),
        HEq (fun x : ((PointRestrictionSystem.sections D l E).obj M).obj (op n) ↦ e.1.hom.app M x)
          (fun x : M.val.obj (op (n, ProEt.mk (𝟙 (Spec (.of D.k))))) ↦ x) ∧
        HEq (fun x : ((PointRestrictionSystem.sections D l E).obj
            ((PointRestrictionSystem.pull D l E g).obj M)).obj (op n) ↦
            e.2.hom.app M x)
          (fun x : M.val.obj (op (n,
            (proEtaleIsoPostcompose g).obj
              (ProEt.mk (𝟙 (Spec (.of D.k)))))) ↦ x) := by
  unfold PointRestrictionSystem.sections
  rw [PointRestrictionSystem.restriction_eq]
  refine ⟨(ordinarySourceEvaluation D l E n, ordinaryTargetEvaluation D l E g n),
    fun M ↦ ⟨ordinarySourceEvaluation_normalization D l E n M,
      ordinaryTargetEvaluation_normalization D l E g n M⟩, ?_⟩
  intro e heq
  apply Prod.ext
  · apply moduleNatIso_ext
    intro M
    exact (heq M).1.trans (ordinarySourceEvaluation_normalization D l E n M).symm
  · apply moduleNatIso_ext
    intro M
    exact (heq M).2.trans (ordinaryTargetEvaluation_normalization D l E g n M).symm

end WeilConjectures.PointSystemEvaluation
