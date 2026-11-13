/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

public import Mathlib.Algebra.Category.ModuleCat.Limits

import WeilConjectures.AlgebraicGeometry.FormalComparisonCompletedAffineModel
import WeilConjectures.AlgebraicGeometry.CoherentAffineMapSupportRadical
import WeilConjectures.RingTheory.AdicCompletionNoetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Affine annihilation of the canonical formal push-pull comparison

## References

* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem annihilator_ker_of_square
    {B : Type u} [CommRing B] {M N P Q : ModuleCat.{u} B}
    (v : M ⟶ N) (w : P ⟶ Q) (eM : M ≅ P) (eN : N ≅ Q)
    (hs : v ≫ eN.hom = eM.hom ≫ w) {a : B}
    (ha : a ∈ Module.annihilator B (LinearMap.ker w.hom)) :
    a ∈ Module.annihilator B (LinearMap.ker v.hom) := by
  rw [Module.mem_annihilator] at ha ⊢
  intro x
  apply Subtype.ext
  change a • (x : M) = 0
  apply eM.toLinearEquiv.injective
  rw [map_smul, map_zero]
  have hx : eM.hom (x : M) ∈ LinearMap.ker w.hom := by
    rw [LinearMap.mem_ker]
    have he := congrArg (fun k : M ⟶ Q ↦ k (x : M)) hs
    change eN.hom (v.hom x) = w.hom (eM.hom x) at he
    rw [x.property, map_zero] at he
    exact he.symm
  exact congrArg Subtype.val (ha ⟨eM.hom x, hx⟩)

private theorem annihilator_coker_of_square
    {B : Type u} [CommRing B] {M N P Q : ModuleCat.{u} B}
    (v : M ⟶ N) (w : P ⟶ Q) (eM : M ≅ P) (eN : N ≅ Q)
    (hs : v ≫ eN.hom = eM.hom ≫ w) {a : B}
    (ha : a ∈ Module.annihilator B (Q ⧸ LinearMap.range w.hom)) :
    a ∈ Module.annihilator B (N ⧸ LinearMap.range v.hom) := by
  rw [Module.mem_annihilator] at ha ⊢
  intro x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range v.hom) x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  have hy : a • eN.hom y ∈ LinearMap.range w.hom := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    rw [Submodule.Quotient.mk_smul]
    exact ha (Submodule.Quotient.mk (eN.hom y))
  obtain ⟨z, hz⟩ := hy
  obtain ⟨x, hx⟩ := eM.toLinearEquiv.surjective z
  refine ⟨x, eN.toLinearEquiv.injective ?_⟩
  have he := congrArg (fun k : M ⟶ Q ↦ k x) hs
  change eN.hom (v.hom x) = w.hom (eM.hom x) at he
  change eM.hom x = z at hx
  change eN.hom (v.hom x) = eN.hom (a • y)
  rw [map_smul, he, hx]
  exact hz

set_option maxHeartbeats 500000 in
-- Identifying kernels and quotient carriers after restricting scalars needs extra heartbeats.
/-- The canonical comparison, specified by its quotient and adjunction equations,
has affine limit kernel and cokernel killed by a positive power of K
(Stacks, Lemma 088B; Remark 0888; Tag 01Y9). -/
theorem formalSystemsPushPull_affine_annihilation
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (J K : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f]
    (hV : IsIso (pullback.snd f (Scheme.Opens.ι K.support.compl)))
    (adj : Scheme.Modules.tensorPullback f ⊣ Scheme.Modules.pushforward f)
    (G : CoherentFormalModule Y J) (F : CoherentModules X)
    (β : G.obj ⋙ Scheme.Modules.tensorPullback f ≅
      formalCompletionSystem (J.comap f) F.obj)
    (h : RingedSpace.IsCoherent Y.toRingedSpace
      ((Scheme.Modules.pushforward f).obj F.obj))
    (κ : formalCompletionSystem J ((Scheme.Modules.pushforward f).obj F.obj) ⟶
      formalCompletionSystem (J.comap f) F.obj ⋙ Scheme.Modules.pushforward f)
    (α : G ⟶ (completion Y J).obj ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩)
    (hκ : ∀ n : ℕ,
      formalModuleQuotientπ J (n + 1) ((Scheme.Modules.pushforward f).obj F.obj) ≫
        κ.app (op n) =
      (Scheme.Modules.pushforward f).map
        (formalModuleQuotientπ (J.comap f) (n + 1) F.obj))
    (hα : ∀ n : ℕ, α.hom.app (op n) ≫ κ.app (op n) =
      adj.unit.app (G.obj.obj (op n)) ≫
        (Scheme.Modules.pushforward f).map (β.hom.app (op n))) :
    ∀ U : Y.affineOpens, ∃ t : ℕ, 1 ≤ t ∧
      K.ideal U ^ t ≤ Module.annihilator Γ(Y, U.1) (LinearMap.ker
        (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation Y.ringCatSheaf (op U.1)))).hom) ∧
      K.ideal U ^ t ≤ Module.annihilator Γ(Y, U.1)
        (↥(limit (((completion Y J).obj
          ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩).obj ⋙
          SheafOfModules.evaluation Y.ringCatSheaf (op U.1)) :
          ModuleCat Γ(Y, U.1)) ⧸ LinearMap.range
          (lim.map (Functor.whiskerRight α.hom
            (SheafOfModules.evaluation Y.ringCatSheaf (op U.1)))).hom) := by
  intro U
  let B := Γ(Y, U.1)
  let R := AdicCompletion (J.ideal U) B
  let L := (K.ideal U).map (algebraMap B R)
  have : IsNoetherianRing B := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing R := AdicCompletion.isNoetherianRing (J.ideal U)
  obtain ⟨A, D, c, hc, eA, eD, hs⟩ :=
    formalComparison_completed_affine_model J K f hV adj G F β h κ α hκ hα U
  obtain ⟨hk, hq⟩ := coherentAffineMap_support_radical R L A D c hc
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hk
    (Ideal.fg_of_isNoetherianRing L)
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hq
    (Ideal.fg_of_isNoetherianRing L)
  let t := max n m + 1
  have hnt : n ≤ t := (le_max_left n m).trans (Nat.le_succ _)
  have hmt : m ≤ t := (le_max_right n m).trans (Nat.le_succ _)
  have hker := (Ideal.pow_le_pow_right hnt).trans hn
  have hcoker := (Ideal.pow_le_pow_right hmt).trans hm
  refine ⟨t, Nat.succ_le_succ (Nat.zero_le _), ?_, ?_⟩
  · intro a ha
    have haR : algebraMap B R a ∈ L ^ t := by
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ha
    apply annihilator_ker_of_square (B := B) _ _ eA eD hs
    rw [Module.mem_annihilator]
    intro x
    have hx := Module.mem_annihilator.mp (hker haR) x
    exact hx
  · intro a ha
    have haR : algebraMap B R a ∈ L ^ t := by
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ha
    apply annihilator_coker_of_square (B := B) _ _ eA eD hs
    rw [Module.mem_annihilator]
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    have hy := Module.mem_annihilator.mp (hcoker haR) (Submodule.Quotient.mk y)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hy
    exact hy

end AlgebraicGeometry
