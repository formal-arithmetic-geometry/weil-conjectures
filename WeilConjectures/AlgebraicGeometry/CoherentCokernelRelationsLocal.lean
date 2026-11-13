/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.CokernelTuplePullbackLocalFreeCover
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Mathlib.CategoryTheory.Abelian.CommSq

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

set_option backward.isDefEq.respectTransparency false in
private theorem overMap_preserves_kernel (X : RingedSpace.{u})
    (U V : Opens X) (hVU : V ≤ U)
    {A B : SheafOfModules.{u} ((moduleRings X).over U)} (g : A ⟶ B) :
    PreservesLimit (parallelPair g 0)
      (SheafOfModules.overMap.{u} (moduleRings X) (homOfLE hVU)) := by
  apply preservesLimit_of_preserves_limit_cone (kernelIsKernel g)
  apply isLimitOfReflects (SheafOfModules.forget ((moduleRings X).over V))
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro W
  let E := SheafOfModules.evaluation ((moduleRings X).over U)
    (Opposite.op ((Over.map (homOfLE hVU)).obj W.unop))
  let T := ModuleCat.restrictScalars
    (RingCat.Hom.hom (𝟙 ((moduleRings X).obj.obj (Opposite.op W.unop.left))))
  exact isLimitOfPreserves (E ⋙ T) (kernelIsKernel g)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 500000 in
-- Unfold the slice restriction functor in the kernel and pullback comparisons.
/-- Finite-free replacement for cokernel relations on a neighbourhood of each point
(Stacks, Tag 01BY). -/
theorem coherent_cokernel_relations_local (X : RingedSpace.{u})
    (F G : SheafOfModules.{u} (moduleRings X)) (f : F ⟶ G)
    (hF : F.IsFiniteType) (hG : IsCoherent X G)
    (U : Opens X) (n : ℕ)
    (g : SheafOfModules.free (R := (moduleRings X).over U) (ULift.{u} (Fin n)) ⟶
      (cokernel f).over U) :
    ∀ x : X, x ∈ U →
      ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
        ∃ (m : ℕ)
          (ψ : SheafOfModules.free (R := (moduleRings X).over V)
            (ULift.{u} (Fin m)) ⟶ G.over V),
          ∃ e : kernel ψ ⟶
            (SheafOfModules.overMap (moduleRings X) (homOfLE hVU)).obj (kernel g),
            Epi e := by
  intro x hx
  have _ := hG
  obtain ⟨V, hVU, hxV, m, p, hp⟩ :=
    cokernel_tuple_pullback_local_free_cover X F G f hF U n g x hx
  let D := SheafOfModules.overMap.{u} (moduleRings X) (homOfLE hVU)
  let gV := D.map g
  let q := D.map ((cokernel.π f).over U)
  let ψ := p ≫ pullback.snd gV q
  have : Epi p := hp
  let a := kernel.map ψ (pullback.snd gV q) p (𝟙 _) (by simp [ψ])
  let b := kernel.map (pullback.snd gV q) gV (pullback.fst gV q) q
    pullback.condition.symm
  have sq : IsPushout ψ p (𝟙 _) (pullback.snd gV q) := by
    refine IsPushout.of_isColimit
      (PushoutCocone.IsColimit.mk (by simp [ψ]) (fun s ↦ s.inl)
        (fun s ↦ by simp) (fun s ↦ ?_) (fun s t ht _ ↦ by simpa using ht))
    apply (cancel_epi p).mp
    simpa only [ψ, pullback.snd, limit.π, Category.assoc] using s.condition
  have : Epi a := Abelian.epi_kernel_map_of_isPushout sq
  have : IsIso b :=
    isIso_kernel_map_of_isPullback (IsPullback.of_hasPullback gV q).flip
  have := overMap_preserves_kernel X U V hVU g
  have : Epi b := by infer_instance
  have : Epi (PreservesKernel.iso D g).inv := by infer_instance
  let e : kernel ψ ⟶ D.obj (kernel g) :=
    a ≫ b ≫ (PreservesKernel.iso D g).inv
  refine ⟨V, hVU, hxV, m, ψ, e, ?_⟩
  constructor
  intro Z t₁ t₂ ht
  apply (cancel_epi (PreservesKernel.iso D g).inv).mp
  apply (cancel_epi b).mp
  apply (cancel_epi a).mp
  simpa only [e, Category.assoc] using ht

end AlgebraicGeometry.RingedSpace
