/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import all WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! # The unit-coefficient criterion for a tensor pullback

Source: Stacks Project, Constructions, Tags 01NK and 01O9, the description of the
open where a map to an invertible module is surjective.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A surjection to a trivialized line module is detected by one global section of
the original module on any fixed affine base chart.

Source: Stacks Project, Constructions, Tags 01NK and 01O9, the generator-open
criterion; Sheaves, Tag 0098, affine tensor pullback.
(blueprint: lem-trf-affine-tensor-generator-locus).

Proof: The affine tensor-section comparison identifies sections of the pullback on
an affine neighborhood with finite sums of multiples of pulled-back sections from V.
If the stalk map is surjective, lift the germ of the frame, represent the lift on
a neighborhood, and shrink to an affine neighborhood inside B. Its image has unit
coefficient. The germ of this coefficient is a finite sum of multiples of the germs
of the coefficients of the sections a from V. In a local ring all nonunits belong
to its maximal ideal, so at least one of these coefficients is a unit. Conversely,
a unit coefficient makes the corresponding image a basis of the target stalk,
which proves surjectivity. The membership criterion for basic opens identifies
unit germs with points of D(alpha). No finiteness assumption on M is used. -/
theorem affine_tensor_generator_locus {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) [M.IsQuasicoherent] (N : X.Modules)
    (φ : (tensorPullback f).obj M ⟶ N)
    (V : Y.affineOpens) (B : X.affineOpens) (hB : B.1 ≤ f ⁻¹ᵁ V.1)
    (e : Γ(N, B.1)) (he : IsFreeGenerator e) (x : X) (hx : x ∈ B.1) :
    Function.Surjective
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ.mapPresheaf) ↔
      ∃ (a : Γ(M, V.1)) (α : Γ(X, B.1)),
        φ.app B.1 (((tensorPullback f).obj M).presheaf.map (homOfLE hB).op
          (tensorPullbackSection f M V.1 a)) = α • e ∧ x ∈ X.basicOpen α := by
  classical
  let P := (tensorPullback f).obj M
  let ex := N.presheaf.germ B.1 x hx e
  let E : X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] N.presheaf.stalk x :=
    LinearEquiv.ofBijective
      { toFun := fun r ↦ r • ex
        map_add' := fun r s ↦ add_smul r s ex
        map_smul' := fun r s ↦ mul_smul r s ex }
      (stalk_generator_bijective he x hx)
  let q : P.presheaf.stalk x →ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
    E.symm.toLinearMap.comp (φ.stalkLinearMap x)
  have hq (U : X.Opens) (hxU : x ∈ U) (s : Γ(P, U)) :
      q (P.presheaf.germ U x hxU s) =
        E.symm (N.presheaf.germ U x hxU (φ.app U s)) := by
    change E.symm (φ.stalkLinearMap x _) = _
    rw [Hom.stalkLinearMap_germ]
  have hqa (a : Γ(M, V.1)) (α : Γ(X, B.1))
      (ha : φ.app B.1 (P.presheaf.map (homOfLE hB).op
        (tensorPullbackSection f M V.1 a)) = α • e) :
      q (P.presheaf.germ B.1 x hx (P.presheaf.map (homOfLE hB).op
        (tensorPullbackSection f M V.1 a))) = X.presheaf.germ B.1 x hx α := by
    rw [hq, ha, germ_smul N]
    exact E.symm_apply_apply _
  have hsurj : Function.Surjective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ.mapPresheaf) ↔
      Function.Surjective q := by
    change Function.Surjective (φ.stalkLinearMap x) ↔ _
    exact ⟨fun h ↦ E.symm.surjective.comp h, fun h y ↦ by
      obtain ⟨z, hz⟩ := h (E.symm y)
      exact ⟨z, E.symm.injective hz⟩⟩
  rw [hsurj]
  constructor
  · intro h
    by_contra hn
    have hnon (a : Γ(M, V.1)) (α : Γ(X, B.1))
        (ha : φ.app B.1 (P.presheaf.map (homOfLE hB).op
          (tensorPullbackSection f M V.1 a)) = α • e) :
        X.presheaf.germ B.1 x hx α ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
      rw [IsLocalRing.mem_maximalIdeal]
      intro hu
      exact hn ⟨a, α, ha, (X.mem_basicOpen α x hx).mpr hu⟩
    obtain ⟨z, hz⟩ := h 1
    obtain ⟨U, hUB, hxU, s, hs⟩ := P.presheaf.exists_le_germ_eq z hx
    obtain ⟨C, hC, hxC, hCU⟩ := exists_isAffineOpen_mem_and_subset hxU
    change C ≤ U at hCU
    let C' : X.affineOpens := ⟨C, hC⟩
    let hCV : C ≤ f ⁻¹ᵁ V.1 := hCU.trans (hUB.trans hB)
    let : Algebra Γ(Y, V.1) Γ(X, C) := (f.appLE V.1 C hCV).hom.toAlgebra
    let : ∀ G : Y.Modules, Module Γ(Y, V.1) Γ((tensorPullback f).obj G, C) :=
      fun G ↦ Module.compHom _ (f.appLE V.1 C hCV).hom
    obtain ⟨c, hc, _, hpure, _⟩ := exists_tensorPullback_affine_sections f V C' hCV
    obtain ⟨t, ht⟩ := (hc M inferInstance).surjective
      (P.presheaf.map (homOfLE hCU).op s)
    have hunit (a : Γ(M, V.1)) :
        ((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app M).val.app
          (op V.1) a = tensorPullbackSection f M V.1 a := by
      exact Classical.choose_spec (exists_tensorPullbackAdjunction f) M (op V.1) a
    have hmem (t : Γ(M, V.1) ⊗[Γ(Y, V.1)] Γ(X, C)) :
        q (P.presheaf.germ C x hxC (c M inferInstance t)) ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
      induction t using TensorProduct.induction_on with
      | zero => simp only [map_zero]; exact Ideal.zero_mem _
      | tmul a b =>
        rw [hpure, hunit, germ_smul P, LinearMap.map_smul]
        obtain ⟨α, hα⟩ := he.exists_smul_eq
          (φ.app B.1 (P.presheaf.map (homOfLE hB).op
            (tensorPullbackSection f M V.1 a)))
        have hr : P.presheaf.germ C x hxC
            (P.presheaf.map (homOfLE hCV).op (tensorPullbackSection f M V.1 a)) =
            P.presheaf.germ B.1 x hx
              (P.presheaf.map (homOfLE hB).op (tensorPullbackSection f M V.1 a)) := by
          erw [← P.presheaf.germ_res_apply (homOfLE (hCU.trans hUB)) x hxC]
          rw [presheaf_map_map_apply]
          rfl
        rw [hr, hqa a α hα.symm]
        exact Ideal.mul_mem_left _ _ (hnon a α hα.symm)
      | add t u ht hu =>
        rw [map_add, map_add, map_add]
        exact Ideal.add_mem _ ht hu
    have h1 := hmem t
    rw [ht] at h1
    erw [P.presheaf.germ_res_apply, hs, hz] at h1
    exact (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk x)).ne_top
      (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  · rintro ⟨a, α, ha, hα⟩
    apply LinearMap.range_eq_top.mp
    apply Ideal.eq_top_of_isUnit_mem (LinearMap.range q)
      ⟨P.presheaf.germ B.1 x hx (P.presheaf.map (homOfLE hB).op
        (tensorPullbackSection f M V.1 a)), hqa a α ha⟩
    exact (X.mem_basicOpen α x hx).mp hα

end AlgebraicGeometry.Scheme.Modules
