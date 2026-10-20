/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.SixFunctors.IntegralLisseReductionConstruction
import Sheaf.SixFunctors.IntegralLisseCoefficientLimit
import Sheaf.SixFunctors.IntegralLisseCoefficientQuotients
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Sites.LocalProperties

/-!
# IntegralLisseReductionComplete

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.4(1).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

private abbrev finiteUnit (n : ℕ) :=
  (integralLisseFiniteRestriction l E X n).obj
    (SheafOfModules.unit ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (integralLisseFiniteRing l E X n)))

private def finiteUnitTower : ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (integralLisseRing l E X) where
  obj n := finiteUnit l E X n.unop
  map {i j} f :=
    ⟨{ app := fun U ↦ ModuleCat.ofHom
         (X := (finiteUnit l E X i.unop).val.obj U)
         (Y := (finiteUnit l E X j.unop).val.obj U)
         { toFun := (integralLisseFiniteDiagram l E X).map f |>.hom.app U
           map_add' := map_add _
           map_smul' := fun r s ↦ by
             change (integralLisseFiniteRing l E X i.unop).obj.obj U at s
             change ((integralLisseFiniteDiagram l E X).map f).hom.app U
                 ((integralLisseReduction l E X i.unop).hom.app U r * s) =
               (integralLisseReduction l E X j.unop).hom.app U r *
                 (show (integralLisseFiniteRing l E X j.unop).obj.obj U from
                   ((integralLisseFiniteDiagram l E X).map f).hom.app U s)
             rw [map_mul]
             congr 1
             have h := congrArg (fun q ↦ q.hom.app U r)
               ((integralLisseCoefficientCone l E X).naturality f)
             exact h.symm }
       naturality := fun g ↦ by
         ext s
         exact congrArg (fun q ↦ q s)
           (((integralLisseFiniteDiagram l E X).map f).hom.naturality g) }⟩
  map_id i := by
    ext U s
    change (integralLisseFiniteRing l E X i.unop).obj.obj U at s
    change ((integralLisseFiniteDiagram l E X).map (𝟙 i)).hom.app U s = s
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    ext U s
    change (integralLisseFiniteRing l E X _).obj.obj U at s
    change ((integralLisseFiniteDiagram l E X).map (f ≫ g)).hom.app U s = _
    rw [CategoryTheory.Functor.map_comp]
    rfl

private def finiteUnitCone : Cone (finiteUnitTower l E X) where
  pt := SheafOfModules.unit (integralLisseRing l E X)
  π :=
    { app n := integralLisseRingMap l E X
        ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (integralLisseReduction l E X n.unop))
      naturality {i j} f := by
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro U
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        change (integralLisseReduction l E X j.unop).hom.app U s * 1 =
          ((integralLisseFiniteDiagram l E X).map f).hom.app U
            (show (integralLisseFiniteRing l E X i.unop).obj.obj U from
              (integralLisseReduction l E X i.unop).hom.app U s * 1)
        rw [map_mul, map_one]
        have h := congrArg (fun q ↦ q.hom.app U s)
          ((integralLisseCoefficientCone l E X).naturality f)
        exact congrArg (fun x ↦ x * 1) h }

private theorem finiteUnitCone_isLimit : Nonempty (IsLimit (finiteUnitCone l E X)) := by
  have hc := (integralLisseCoefficient_isLimit l E X).some
  refine ⟨isLimitOfReflects (SheafOfModules.forget _) ?_⟩
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro U
  apply isLimitOfReflects (forget (ModuleCat _))
  let V := sheafToPresheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} ⋙
    (evaluation X.ProEtᵒᵖ CommRingCat.{u + 1}).obj U ⋙ forget CommRingCat.{u + 1}
  have hV := isLimitOfPreserves V hc
  apply Classical.choice
  apply (Types.isLimit_iff _).mpr
  intro f hf
  obtain ⟨a, ha, hu⟩ := (Types.isLimit_iff _).mp ⟨hV⟩ f hf
  refine ⟨a, ?_, ?_⟩
  · intro n
    change (integralLisseReduction l E X n.unop).hom.app U a * 1 = _
    rw [mul_one]
    exact ha n
  · intro a' ha'
    apply hu a'
    intro n
    have h := ha' n
    change (integralLisseReduction l E X n.unop).hom.app U a' * 1 = _ at h
    change (integralLisseReduction l E X n.unop).hom.app U a' = _
    simpa only [mul_one] using h

/-- The coefficient unit has a normalized complete scalar-cokernel tower.
Source: Bhatt--Scholze, Lemma 6.8.2(1) and Proposition 6.8.4(1)
(blueprint: lem-sfb-integral-lisse-module-complete).
Proof: the coefficient quotient calculation identifies each actual cokernel with
the finite coefficient unit. Cokernel uniqueness makes these identifications
compatible with transitions and projections. The coefficient limit is limiting
after evaluation and forgetting to sets, hence also as a module cone. Transport
this universal property through the quotient-tower isomorphism. Normalization
of transitions follows from the cokernel calculation for arbitrary modules. -/
theorem integralLisseUnitCokernel_complete :
    IsIntegralReductionTower l E X
        (integralLisseCokernelTower l E X (SheafOfModules.unit (integralLisseRing l E X))) ∧
      Nonempty (IsLimit (Cone.mk _
        (integralLisseCokernelCone l E X (SheafOfModules.unit (integralLisseRing l E X))))) := by
  let M := SheafOfModules.unit (integralLisseRing l E X)
  let q := finiteUnitCone l E X
  have hq (n : ℕ) : IsIntegralLisseQuotient l E X
      (Padic.coefficientExtensionUniformizer l E ^ (n + 1)) (q.π.app (op n)) :=
    integralLisseCoefficient_quotients l E X n
  let α : integralLisseCokernelTower l E X M ⟶ finiteUnitTower l E X :=
    NatTrans.ofOpSequence
      (fun n ↦ cokernel.desc _ (q.π.app (op n)) (hq n).choose)
      (fun n ↦ by
        apply (cancel_epi (cokernel.π _)).1
        simp only [integralLisseCokernelTower, Functor.ofOpSequence_map_homOfLE_succ,
          integralLisseCokernelTransition, cokernel.π_desc_assoc, cokernel.π_desc]
        exact (q.w (homOfLE (Nat.le_succ n)).op).symm)
  have hi (n : ℕᵒᵖ) : IsIso (α.app n) :=
    isIso_integralLisseQuotient_desc l E X _ _ (hq n.unop)
  have : IsIso α := (NatTrans.isIso_iff_isIso_app α).mpr hi
  constructor
  · constructor
    · intro n
      refine ⟨SheafOfModules.unit _, inferInstance, ⟨(asIso (α.app (op n))).symm⟩⟩
    · intro n
      simpa only [integralLisseCokernelTower,
        Functor.ofOpSequence_map_homOfLE_succ] using
        integralLisseCokernelTransition_quotient l E X M n
  · let c := Cone.mk M (integralLisseCokernelCone l E X M)
    refine ⟨(IsLimit.postcomposeHomEquiv (asIso α) c) ?_⟩
    apply IsLimit.ofIsoLimit (finiteUnitCone_isLimit l E X).some
    refine Cone.ext (Iso.refl M) ?_
    intro n
    change q.π.app n ≫ 𝟙 _ =
      (integralLisseCokernelCone l E X M).app n ≫ α.app n
    simp only [Category.comp_id, α, integralLisseCokernelCone, NatTrans.ofOpSequence_app,
      cokernel.π_desc]

private def integralLisseCompletionUnit :
    𝟭 (ringedSiteModules.{u + 1} (integralLisseRing l E X)) ⟶
      integralLisseCokernelFunctor l E X ⋙ lim where
  app M := limit.lift _ (Cone.mk M (integralLisseCokernelCone l E X M))
  naturality {M N} f := by
    apply limit.hom_ext
    intro n
    change f ≫ limit.lift _ (Cone.mk N (integralLisseCokernelCone l E X N)) ≫
        limit.π (integralLisseCokernelTower l E X N) n =
      limit.lift _ (Cone.mk M (integralLisseCokernelCone l E X M)) ≫
        limMap (integralLisseCokernelMap l E X f) ≫
        limit.π (integralLisseCokernelTower l E X N) n
    rw [limMap_π, limit.lift_π, limit.lift_π_assoc]
    exact integralLisseCokernelCone_natural l E X f n.unop

private instance completionLim_additive :
    (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (integralLisseRing l E X)) ⥤ _).Additive :=
  ⟨by
    intro M N f g
    apply limit.hom_ext
    intro n
    simp only [lim_map, limMap_π, Preadditive.add_comp, Preadditive.comp_add,
      NatTrans.app_add]
  ⟩
private theorem freeComplete (I : Type (u + 1)) [Finite I] :
    Nonempty (IsLimit (Cone.mk (SheafOfModules.free (R := integralLisseRing l E X) I)
      (integralLisseCokernelCone l E X _))) := by
  classical
  have : IsIso ((integralLisseCompletionUnit l E X).app
      (SheafOfModules.unit (integralLisseRing l E X))) :=
    (limit.isLimit _).nonempty_isLimit_iff_isIso_lift.mp
      (integralLisseUnitCokernel_complete l E X).2
  let K := Discrete.functor (fun _ : I ↦ SheafOfModules.unit (integralLisseRing l E X))
  have : IsIso (whiskerLeft K (integralLisseCompletionUnit l E X)) :=
    (NatTrans.isIso_iff_isIso_app _).mpr (fun _ ↦
      inferInstanceAs (IsIso ((integralLisseCompletionUnit l E X).app
        (SheafOfModules.unit (integralLisseRing l E X)))))
  have := isIso_app_coconePt_of_preservesColimit K (integralLisseCompletionUnit l E X)
    (SheafOfModules.freeCofan I) (SheafOfModules.isColimitFreeCofan I)
  exact (limit.isLimit _).nonempty_isLimit_iff_isIso_lift.mpr this
/-- Restriction to a slice preserves inverse limits of module sheaves. -/
theorem integralLisseOver_preserves_limits (U : X.ProEt) :
    PreservesLimitsOfShape ℕᵒᵖ
      (SheafOfModules.overFunctor.{u + 1} (integralLisseRing l E X) U) := by
  constructor
  intro K
  apply preservesLimit_of_preserves_limit_cone (limit.isLimit K)
  apply isLimitOfReflects (SheafOfModules.forget _)
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro V
  exact isLimitOfPreserves (SheafOfModules.evaluation _ (op V.unop.left)) (limit.isLimit K)

private theorem localScalar_comm (U : X.ProEt)
    (M N : ringedSiteModules.{u + 1} (integralLisseRing l E X))
    (e : M.over U ≅ N.over U) (n : ℕ) :
    (SheafOfModules.overFunctor (integralLisseRing l E X) U).map
        (integralLisseScalar l E X M (Padic.coefficientExtensionUniformizer l E ^ (n + 1))) ≫
      e.hom = e.hom ≫
        (SheafOfModules.overFunctor (integralLisseRing l E X) U).map
          (integralLisseScalar l E X N
            (Padic.coefficientExtensionUniformizer l E ^ (n + 1))) := by
  ext V x
  exact (e.hom.val.app V).hom.map_smul _ x

private theorem localComplete_of_iso (U : X.ProEt)
    (M N : ringedSiteModules.{u + 1} (integralLisseRing l E X))
    (e : M.over U ≅ N.over U)
    (hc : Nonempty (IsLimit (Cone.mk N (integralLisseCokernelCone l E X N)))) :
    Nonempty (IsLimit ((SheafOfModules.overFunctor (integralLisseRing l E X) U).mapCone
      (Cone.mk M (integralLisseCokernelCone l E X M)))) := by
  let F := SheafOfModules.overFunctor.{u + 1} (integralLisseRing l E X) U
  have : HasWeakSheafify ((Scheme.ProEt.topology X).over U) AddCommGrpCat.{u + 1} :=
    inferInstance
  have : ((Scheme.ProEt.topology X).over U).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := inferInstance
  have := (ringedOverFunctor_exactGeneral (integralLisseRing l E X) U).1
  have := (ringedOverFunctor_exactGeneral (integralLisseRing l E X) U).2.2
  have := integralLisseOver_preserves_limits l E X U
  let a := fun P n ↦ integralLisseScalar l E X P
    (Padic.coefficientExtensionUniformizer l E ^ (n + 1))
  let eQ (n : ℕ) : F.obj (integralLisseCokernel l E X M n) ≅
      F.obj (integralLisseCokernel l E X N n) :=
    PreservesCokernel.iso F (a M n) ≪≫
      cokernel.mapIso _ (F.map (a N n)) e e (localScalar_comm l E X U M N e n) ≪≫
      (PreservesCokernel.iso F (a N n)).symm
  have heQ (n : ℕ) : F.map (cokernel.π (a M n)) ≫ (eQ n).hom =
      e.hom ≫ F.map (cokernel.π (a N n)) := by
    simp [eQ, Category.assoc]
  let α : integralLisseCokernelTower l E X M ⋙ F ⟶
      integralLisseCokernelTower l E X N ⋙ F :=
    NatTrans.ofOpSequence (fun n ↦ (eQ n).hom) (fun n ↦ by
      apply (cancel_epi (F.map (cokernel.π (a M (n + 1))))).1
      simp only [Functor.comp_map, integralLisseCokernelTower,
        Functor.ofOpSequence_map_homOfLE_succ]
      simp only [← Category.assoc]
      rw [← F.map_comp, integralLisseCokernelTransition, cokernel.π_desc,
        heQ, heQ, Category.assoc, ← F.map_comp, integralLisseCokernelTransition,
        cokernel.π_desc])
  have : IsIso α := (NatTrans.isIso_iff_isIso_app _).mpr (fun n ↦
    inferInstanceAs (IsIso ((eQ n.unop).hom)))
  let cM := F.mapCone (Cone.mk M (integralLisseCokernelCone l E X M))
  let cN := F.mapCone (Cone.mk N (integralLisseCokernelCone l E X N))
  refine ⟨(IsLimit.postcomposeHomEquiv (asIso α) cM) ?_⟩
  apply IsLimit.ofIsoLimit (isLimitOfPreserves F hc.some)
  refine Cone.ext e.symm ?_
  intro n
  change F.map ((integralLisseCokernelCone l E X N).app n) =
    e.inv ≫ (F.map ((integralLisseCokernelCone l E X M).app n) ≫ α.app n)
  apply (cancel_epi e.hom).1
  simp only [← Category.assoc, e.hom_inv_id, Category.id_comp]
  exact (heQ n.unop).symm

/-- A finite locally free integral module is the limit of its actual scalar quotients.
Source: Bhatt--Scholze, Proposition 6.8.4(1)
(blueprint: lem-sfb-integral-lisse-module-complete).
Proof: finite sums preserve completeness of the coefficient unit. Restriction preserves
limits and cokernels, and the completion map is invertible on a trivializing cover.
The local inverse maps descend because they invert the same map on overlaps. -/
theorem integralLisseCokernel_isLimit (M : IntegralLisseModule l E X) :
    Nonempty (IsLimit (Cone.mk M.obj (integralLisseCokernelCone l E X M.obj))) := by
  have hM : M.obj.IsFiniteLocallyFree := M.property
  obtain ⟨q, hq, hf⟩ := hM.exists_localGeneratorsData
  let a := (integralLisseCompletionUnit l E X).app M.obj
  have hlocal (i : q.I) :
      IsIso ((SheafOfModules.overFunctor (integralLisseRing l E X) (q.X i)).map a) := by
    let F := SheafOfModules.overFunctor.{u + 1} (integralLisseRing l E X) (q.X i)
    have : HasWeakSheafify ((Scheme.ProEt.topology X).over (q.X i)) AddCommGrpCat.{u + 1} :=
      inferInstance
    have : ((Scheme.ProEt.topology X).over (q.X i)).WEqualsLocallyBijective
        AddCommGrpCat.{u + 1} := inferInstance
    have := integralLisseOver_preserves_limits l E X (q.X i)
    have := (ringedOverFunctor_exactGeneral (integralLisseRing l E X) (q.X i)).1
    have := hf.isFiniteType i
    have := hq.isIso i
    let I := (q.generators i).I
    let e : M.obj.over (q.X i) ≅
        (SheafOfModules.free (R := integralLisseRing l E X) I).over (q.X i) :=
      (asIso (q.generators i).π).symm ≪≫
        SheafOfModules.mapFreeIso F I (Iso.refl _)
    have hc := localComplete_of_iso l E X (q.X i) M.obj
      (SheafOfModules.free I) e (freeComplete l E X I)
    let hL := isLimitOfPreserves F
      (limit.isLimit (integralLisseCokernelTower l E X M.obj))
    have he : hL.lift (F.mapCone (Cone.mk M.obj
        (integralLisseCokernelCone l E X M.obj))) = F.map a := by
      apply hL.hom_ext
      intro n
      rw [hL.fac]
      change F.map ((integralLisseCokernelCone l E X M.obj).app n) =
        F.map a ≫ F.map (limit.π (integralLisseCokernelTower l E X M.obj) n)
      rw [← F.map_comp]
      change _ = F.map
        (limit.lift _ (Cone.mk M.obj (integralLisseCokernelCone l E X M.obj)) ≫ limit.π _ n)
      rw [limit.lift_π]
    have hi := hL.nonempty_isLimit_iff_isIso_lift.mp hc
    rwa [he] at hi
  have hi : IsIso ((SheafOfModules.toSheaf (integralLisseRing l E X)).map a) := by
    apply CategoryTheory.Sheaf.isIso_of_coversTop q.coversTop
    intro i
    change IsIso ((SheafOfModules.toSheaf ((integralLisseRing l E X).over (q.X i))).map
      ((SheafOfModules.overFunctor (integralLisseRing l E X) (q.X i)).map a))
    infer_instance
  have : IsIso a := isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)
  exact (limit.isLimit _).nonempty_isLimit_iff_isIso_lift.mpr this

end AlgebraicGeometry.ProEtale
