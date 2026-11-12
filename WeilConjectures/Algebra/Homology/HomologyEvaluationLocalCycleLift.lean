/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomologyEvaluationDefinitions
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
set_option profiler true in
set_option maxHeartbeats 1000000 in
-- The differential formula unfolds localized Hom and evaluated kernel structures.
/-- Every pair of local cycle representatives has a representative in the target cycles.
Source: Stacks Project, Tag 0A8X, Hom differential formula.
(blueprint: new-b2-homology-evaluation-local-cycle-lift).

Apply the differential projection formula in degree n to the Hom cocycle, at source
index -n and target index 1. Evaluation on the given T-cycle kills the precomposition
term, while the Hom cycle equation kills the differential term. Thus the evaluation
in J-degree zero has differential zero. Evaluation of sheaves of modules at U preserves
kernels. Applying this to the cycle inclusion identifies its image with the kernel
of the evaluated J-differential, and supplies the required b. The argument also works
on the empty open and when either cycle representative is zero.
-/
theorem homologyEvaluation_local_cycle_lift (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ) :
    ∀ (U : X.Opens)
      (φ : ((homComplex (R := X.sheaf) T J).cycles n).val.obj (op U))
      (z : (T.cycles (-n)).val.obj (op U)),
      ∃ b : (J.cycles 0).val.obj (op U),
        (J.iCycles 0).val.app (op U) b =
          ((homologyEvaluationProjection X T J n).val.app (op U)
            (((homComplex (R := X.sheaf) T J).iCycles n).val.app (op U) φ)).app
              (op (Over.mk (𝟙 U)))
            (((T.iCycles (-n)).val.app (op U)) z) := by
  intro U φ z
  let P := homComplex (R := X.sheaf) T J
  let π := Classical.choose (homComplex_projections_exists (R := X.sheaf))
  let x := ((π T J n (-n) 0 (by omega)).val.app (op U)
    ((P.iCycles n).val.app (op U) φ)).app
      (op (Over.mk (𝟙 U))) ((T.iCycles (-n)).val.app (op U) z)
  have hd : (J.d 0 1).val.app (op U) x = 0 := by
    have hformula := (Classical.choose_spec
      (homComplex_projections_exists (R := X.sheaf))).2.1
      T J n (n + 1) (-n) 1 0 (1 - n) rfl (by omega) (by omega) (by omega)
    have h := congrArg
      (fun k : P.X n ⟶ SheafOfModules.homObj (R := X.sheaf) (T.X (-n)) (J.X 1) ↦
        (k.val.app (op U) ((P.iCycles n).val.app (op U) φ)).app
          (op (Over.mk (𝟙 U))) ((T.iCycles (-n)).val.app (op U) z)) hformula
    have hP := congrArg
      (fun k ↦ k.val.app (op U) φ) (P.iCycles_d n (n + 1))
    have hT := congrArg
      (fun k ↦ k.val.app (op U) z) (T.iCycles_d (-n) (1 - n))
    change (P.d n (n + 1)).val.app (op U)
      ((P.iCycles n).val.app (op U) φ) = 0 at hP
    change (T.d (-n) (1 - n)).val.app (op U)
      ((T.iCycles (-n)).val.app (op U) z) = 0 at hT
    let ev : (SheafOfModules.homObj (R := X.sheaf) (T.X (-n)) (J.X 1)).val.obj
        (op U) →+ (J.X 1).val.obj (op U) :=
      { toFun f := f.app (op (Over.mk (𝟙 U))) ((T.iCycles (-n)).val.app (op U) z)
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    let R₀ := (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf
    let F := SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U)
    change ev ((F.map (P.d n (n + 1) ≫ π T J (n + 1) (-n) 1 (by omega))).hom
        ((P.iCycles n).val.app (op U) φ)) =
      ev ((F.map (π T J n (-n) 0 (by omega) ≫
        SheafOfModules.homObjMap (R := X.sheaf) (𝟙 (T.X (-n))) (J.d 0 1) -
          n.negOnePow • (π T J n (1 - n) 1 (by omega) ≫
            SheafOfModules.homObjMap (R := X.sheaf) (T.d (-n) (1 - n)) (𝟙 (J.X 1))))).hom
              ((P.iCycles n).val.app (op U) φ)) at h
    rw [Functor.map_sub] at h
    simp only [Units.smul_def, Functor.map_zsmul, ModuleCat.hom_sub,
      ModuleCat.hom_zsmul, LinearMap.sub_apply, LinearMap.smul_apply,
      map_sub, map_zsmul] at h
    change ((π T J (n + 1) (-n) 1 (by omega)).val.app (op U)
      ((P.d n (n + 1)).val.app (op U) ((P.iCycles n).val.app (op U) φ))).app
        (op (Over.mk (𝟙 U))) ((T.iCycles (-n)).val.app (op U) z) =
      (J.d 0 1).val.app (op U) x - (n.negOnePow : ℤ) •
        (show (J.X 1).val.obj (op U) from (((π T J n (1 - n) 1 (by omega)).val.app (op U)
          ((P.iCycles n).val.app (op U) φ)).app (op (Over.mk (𝟙 U))))
            ((T.d (-n) (1 - n)).val.app (op U) ((T.iCycles (-n)).val.app (op U) z))) at h
    rw [hP, hT, map_zero, map_zero] at h
    change 0 = (J.d 0 1).val.app (op U) x -
      (n.negOnePow : ℤ) • (0 : (J.X 1).val.obj (op U)) at h
    simpa only [smul_zero, sub_zero] using h.symm
  let E := SheafOfModules.evaluation X.ringCatSheaf (op U)
  let S := ShortComplex.mk (E.map (J.iCycles 0)) (E.map (J.d 0 1))
    (by rw [← E.map_comp, J.iCycles_d, E.map_zero])
  have hk : IsLimit (KernelFork.ofι S.f S.zero) :=
    isLimitForkMapOfIsLimit' E _ (J.cyclesIsKernel 0 1 (by simp :
      (ComplexShape.up ℤ).next 0 = 1))
  have hs : S.Exact := S.exact_of_f_is_kernel hk
  exact (S.moduleCat_exact_iff.mp hs) x hd

end CategoryTheory
