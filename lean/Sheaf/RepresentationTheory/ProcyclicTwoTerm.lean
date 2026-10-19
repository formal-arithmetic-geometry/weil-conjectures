/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker Q33
-/
module

public import Sheaf.RepresentationTheory.DiscreteContinuousCohomology
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.Additive
import Mathlib.Data.Nat.Periodic
import Mathlib.Algebra.BigOperators.Intervals
import WeilConjectures.Topology.ContinuousOpenNormalStabilizer
import Sheaf.RepresentationTheory.CoinducedDiscreteEmbedding
import WeilConjectures.CategoryTheory.EffaceableDeltaFunctorUniversal
import Sheaf.RepresentationTheory.ContinuousCochainsInvariantsZero
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor

/-!
# Two-term continuous cohomology of the additive l-adic integers

Source: blueprint, sec-smooth-purity/sk-prop-a1-kummer/lem-exc-procyclic-two-term,
statement and proof (blueprint: lem-exc-procyclic-two-term).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

section

open ZeroObject

set_option linter.style.haveILetI false

open scoped BigOperators
open Topology

private noncomputable def pcReduction (l : ℕ) [Fact l.Prime] (r : ℕ) :
    LocallyConstant ℤ_[l] (ZMod (l ^ r)) where
  toFun := PadicInt.toZModPow r
  isLocallyConstant := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨Metric.ball x ((l : ℝ) ^ (-(r : ℤ))), Metric.isOpen_ball, ?_, ?_⟩
    · exact Metric.mem_ball_self (zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _)
    · intro y hy
      apply sub_eq_zero.mp
      rw [← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
        ← PadicInt.norm_le_pow_iff_mem_span_pow]
      exact (show ‖y - x‖ < (l : ℝ) ^ (-(r : ℤ)) from hy).le

private theorem sum_periods {V : Type*} [AddCommGroup V] (f : ℕ → V)
    (L : ℕ) (hf : Function.Periodic f L) (k : ℕ) :
    ∑ i ∈ Finset.range (k * L), f i = k • ∑ i ∈ Finset.range L, f i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simpa [Nat.add_comm] using (hf.nat_mul k) i

private theorem cyclic_primitive {V : Type*} [AddCommGroup V]
    (N : ℕ) [NeZero N] (f : ZMod N → V) (hf : ∑ i ∈ Finset.range N, f i = 0) :
    ∃ h : ZMod N → V, ∀ x, h (x + 1) - h x = f x := by
  let P (n : ℕ) : V := ∑ i ∈ Finset.range n, f i
  have hP : P N = 0 := hf
  have hsucc (n : ℕ) : P (n + 1) = P n + f n := Finset.sum_range_succ _ _
  refine ⟨fun x ↦ P x.val, ?_⟩
  intro x
  change P (x + 1).val - P x.val = f x
  have hx := x.val_lt
  by_cases h : x.val + 1 < N
  · have hv : (x + 1).val = x.val + 1 := by
      calc
        (x + 1).val = ((x.val + 1 : ℕ) : ZMod N).val := by
          congr 1
          simp
        _ = x.val + 1 := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt h]
    rw [hv, hsucc, add_sub_cancel_left, ZMod.natCast_zmod_val]
  · have he : x.val + 1 = N := by omega
    have hv : (x + 1).val = 0 := by
      rw [← ZMod.natCast_zmod_val x, ← Nat.cast_one, ← Nat.cast_add, he]
      simp
    have hz : P x.val + f x = 0 := by
      have hh := hsucc x.val
      rw [he, ZMod.natCast_zmod_val, hP] at hh
      exact hh.symm
    rw [hv, show P 0 = 0 by simp [P], zero_sub]
    exact (eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using hz)).symm

private theorem padic_primitive (l : ℕ) [Fact l.Prime] (s : ℕ)
    {V : Type*} [AddCommGroup V] (hk : ∀ v : V, (l ^ s) • v = 0)
    (f : LocallyConstant ℤ_[l] V) :
    ∃ h : LocallyConstant ℤ_[l] V, ∀ x, h (x + 1) - h x = f x := by
  classical
  letI : TopologicalSpace V := ⊥
  letI : DiscreteTopology V := ⟨rfl⟩
  obtain ⟨U, hU⟩ := ProfiniteGrp.exists_openNormalSubgroup_right_invariant
    (ProfiniteGrp.of (Multiplicative ℤ_[l])) V (fun x ↦ f x.toAdd) f.continuous
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp U.isOpen
    (1 : Multiplicative ℤ_[l]) U.one_mem
  obtain ⟨r, hr⟩ := PadicInt.exists_pow_neg_lt l hε
  have hsmall (x : ℤ_[l]) (hx : PadicInt.toZModPow r x = 0) :
      Multiplicative.ofAdd x ∈ U := by
    apply hball
    change ‖x - 0‖ < ε
    rw [sub_zero]
    apply lt_of_le_of_lt _ hr
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
      RingHom.mem_ker]
    exact hx
  have hf (x y : ℤ_[l]) (hxy : PadicInt.toZModPow r x = PadicInt.toZModPow r y) :
      f x = f y := by
    have hu := hU (Multiplicative.ofAdd y) (Multiplicative.ofAdd (x - y))
      (hsmall (x - y) (by rw [map_sub, hxy, sub_self]))
    change f (y + (x - y)) = f y at hu
    simpa [add_sub_cancel_left] using hu
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : NeZero (l ^ (r + s)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let g : ZMod (l ^ r) → V := fun a ↦ f (a.val : ℤ_[l])
  have hfg (x : ℤ_[l]) : f x = g (PadicInt.toZModPow r x) := by
    apply hf
    simp
  let fn : ZMod (l ^ (r + s)) → V := fun a ↦ g (a.val : ZMod (l ^ r))
  have hnat (n : ℕ) : fn n = g (n : ZMod (l ^ r)) := by
    dsimp [fn]
    rw [ZMod.val_natCast]
    exact congrArg g (by
      apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
      exact Nat.mod_mod_of_dvd n (pow_dvd_pow l (Nat.le_add_right r s)))
  have hp : Function.Periodic (fun n : ℕ ↦ g (n : ZMod (l ^ r))) (l ^ r) := by
    intro n
    simp
  have hsum : ∑ i ∈ Finset.range (l ^ (r + s)), fn i = 0 := by
    simp_rw [hnat]
    rw [pow_add, Nat.mul_comm (l ^ r), sum_periods _ _ hp, hk]
  obtain ⟨H, hH⟩ := cyclic_primitive (l ^ (r + s)) fn hsum
  let h : LocallyConstant ℤ_[l] V :=
    ⟨fun x ↦ H (PadicInt.toZModPow (r + s) x),
      (pcReduction l (r + s)).isLocallyConstant.comp H⟩
  refine ⟨h, ?_⟩
  intro x
  change H (PadicInt.toZModPow (r + s) (x + 1)) -
    H (PadicInt.toZModPow (r + s) x) = f x
  rw [map_add, map_one, hH, hfg]
  dsimp [fn]
  congr 1
  rw [← PadicInt.cast_toZModPow r (r + s) (Nat.le_add_right r s) x]
  exact ZMod.natCast_val _

namespace Rep

private theorem universalDeltaFunctor_iso
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    (T R : CohomologicalDeltaFunctor C D) (hT : T.IsUniversal) (hR : R.IsUniversal)
    (e : T.F 0 ≅ R.F 0) (q : ℕ) : Nonempty (T.F q ≅ R.F q) := by
  obtain ⟨α, hα, _⟩ := hT R e.hom
  obtain ⟨β, hβ, _⟩ := hR T e.inv
  let idT : CohomologicalDeltaFunctor.Hom T T :=
    ⟨fun n ↦ 𝟙 (T.F n), by intros; simp⟩
  let idR : CohomologicalDeltaFunctor.Hom R R :=
    ⟨fun n ↦ 𝟙 (R.F n), by intros; simp⟩
  let αβ : CohomologicalDeltaFunctor.Hom T T :=
    ⟨fun n ↦ α.app n ≫ β.app n, by
      intro S hS n
      simp only [NatTrans.comp_app, ← Category.assoc]
      rw [α.naturality S hS n]
      simp only [Category.assoc]
      rw [β.naturality S hS n]⟩
  let βα : CohomologicalDeltaFunctor.Hom R R :=
    ⟨fun n ↦ β.app n ≫ α.app n, by
      intro S hS n
      simp only [NatTrans.comp_app, ← Category.assoc]
      rw [β.naturality S hS n]
      simp only [Category.assoc]
      rw [α.naturality S hS n]⟩
  have hαβ : αβ = idT := (hT T (𝟙 (T.F 0))).unique
    (by change α.app 0 ≫ β.app 0 = _; rw [hα, hβ]; exact e.hom_inv_id)
    rfl
  have hβα : βα = idR := (hR R (𝟙 (R.F 0))).unique
    (by change β.app 0 ≫ α.app 0 = _; rw [hβ, hα]; exact e.inv_hom_id)
    rfl
  refine ⟨⟨α.app q, β.app q, ?_, ?_⟩⟩
  · exact congrArg (fun f : CohomologicalDeltaFunctor.Hom T T ↦ f.app q) hαβ
  · exact congrArg (fun f : CohomologicalDeltaFunctor.Hom R R ↦ f.app q) hβα

variable {A : Type u} [Ring A] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
private noncomputable abbrev ttX (M : DiscreteContinuousRep.{u, 0, w} A G) : ℕ → ModuleCat.{w} A
  | 0 => ModuleCat.of A M.obj.V
  | 1 => ModuleCat.of A M.obj.V
  | _ + 2 => 0
private noncomputable abbrev ttD (τ : G) (M : DiscreteContinuousRep.{u, 0, w} A G) :
    ∀ n, ttX M n ⟶ ttX M (n + 1)
  | 0 => ModuleCat.ofHom (M.obj.ρ τ - LinearMap.id)
  | 1 => 0
  | _ + 2 => 0
private noncomputable abbrev ttComplex (τ : G) (M : DiscreteContinuousRep.{u, 0, w} A G) :
    CochainComplex (ModuleCat.{w} A) ℕ :=
  CochainComplex.of (ttX M) (ttD τ M) (by
    intro n
    cases n with
    | zero => exact comp_zero
    | succ n => cases n <;> exact zero_comp)
private noncomputable def ttMap (τ : G) {M N : DiscreteContinuousRep.{u, 0, w} A G} (f : M ⟶ N) :
    ttComplex τ M ⟶ ttComplex τ N :=
  CochainComplex.ofHom (fun n ↦ match n with
    | 0 => ModuleCat.ofHom f.hom.hom
    | 1 => ModuleCat.ofHom f.hom.hom
    | _ + 2 => 0) (by
      intro n
      cases n with
      | zero =>
        simp only [ttComplex, CochainComplex.of_d]
        ext x
        change N.obj.ρ τ (f.hom.hom x) - f.hom.hom x =
          f.hom.hom (M.obj.ρ τ x - x)
        rw [map_sub, Rep.hom_comm_apply]
      | succ n => cases n <;> simp only [ttComplex, CochainComplex.of_d, ttD,
          comp_zero])
private noncomputable def ttFunctor (τ : G) : DiscreteContinuousRep.{u, 0, w} A G ⥤
    CochainComplex (ModuleCat.{w} A) ℕ where
  obj := ttComplex τ
  map := ttMap τ
  map_id M := by
    apply HomologicalComplex.hom_ext
    intro n
    match n with
    | 0 => rfl
    | 1 => rfl
    | n + 2 => exact (isZero_zero _).eq_of_src _ _
  map_comp f g := by
    apply HomologicalComplex.hom_ext
    intro n
    match n with
    | 0 => rfl
    | 1 => rfl
    | n + 2 => exact (isZero_zero _).eq_of_src _ _

private noncomputable abbrev ttForget : DiscreteContinuousRep.{u, 0, w} A G ⥤
    ModuleCat.{w} A :=
  ObjectProperty.ι (fun X : Rep.{w} A G ↦ ∀ m : X.V, IsOpen {g | X.ρ g m = m}) ⋙
    forget₂ (Rep.{w} A G) (ModuleCat.{w} A)

private local instance ttPreadditive
    [h : Abelian (DiscreteContinuousRep.{u, 0, w} A G)] :
    Preadditive (DiscreteContinuousRep.{u, 0, w} A G) := h.toPreadditive

private local instance ttModulePreadditive : Preadditive (ModuleCat.{w} A) :=
  (inferInstance : Abelian (ModuleCat.{w} A)).toPreadditive

attribute [local instance 4000] Preadditive.preadditiveHasZeroMorphisms

attribute [local instance 3000] ttPreadditive ttModulePreadditive

private local instance ttAdditive
    [Abelian (DiscreteContinuousRep.{u, 0, w} A G)]
    [PreservesFiniteLimits (ttForget.{u, w} (A := A) (G := G))] (τ : G) :
    (ttFunctor (A := A) τ).Additive := by
  haveI : (ttForget.{u, w} (A := A) (G := G)).Additive :=
    Functor.additive_of_preserves_binary_products _
  constructor
  intro M N f g
  apply HomologicalComplex.hom_ext
  intro n
  match n with
  | 0 => exact Functor.map_add (ttForget.{u, w} (A := A) (G := G))
  | 1 => exact Functor.map_add (ttForget.{u, w} (A := A) (G := G))
  | n + 2 => exact (isZero_zero _).eq_of_src _ _

private theorem ttDegreewise [Abelian (DiscreteContinuousRep.{u, 0, w} A G)]
    [PreservesFiniteLimits (ttForget.{u, w} (A := A) (G := G))]
    [PreservesFiniteColimits (ttForget.{u, w} (A := A) (G := G))]
    (τ : G) (S : ShortComplex (DiscreteContinuousRep.{u, 0, w} A G))
    (hS : S.ShortExact) (n : ℕ) :
    ((S.map (ttFunctor τ)).map (HomologicalComplex.eval
      (ModuleCat.{w} A) (ComplexShape.up ℕ) n)).ShortExact := by
  haveI : (ttForget.{u, w} (A := A) (G := G)).Additive :=
    Functor.additive_of_preserves_binary_products _
  have h := hS.map_of_exact (ttForget.{u, w} (A := A) (G := G))
  match n with
  | 0 => exact h
  | 1 => exact h
  | n + 2 =>
    have hz : IsZero ((S.map (ttFunctor τ)).map
        (HomologicalComplex.eval (ModuleCat.{w} A) (ComplexShape.up ℕ) (n + 2))).X₂ :=
      isZero_zero _
    constructor
    · exact ShortComplex.exact_of_isZero_X₂ _ hz

private noncomputable def ttDelta [Abelian (DiscreteContinuousRep.{u, 0, w} A G)]
    [PreservesFiniteLimits (ttForget.{u, w} (A := A) (G := G))]
    [PreservesFiniteColimits (ttForget.{u, w} (A := A) (G := G))] (τ : G) :
    CohomologicalDeltaFunctor (DiscreteContinuousRep.{u, 0, w} A G) (ModuleCat.{w} A) := by
  haveI : (ttForget.{u, w} (A := A) (G := G)).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hs (S : ShortComplex (DiscreteContinuousRep.{u, 0, w} A G))
      (hS : S.ShortExact) : (S.map (ttFunctor τ)).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ (ttDegreewise τ S hS)
  exact
    { F := fun q ↦ ttFunctor τ ⋙ HomologicalComplex.homologyFunctor _ _ q
      additive := fun _ ↦ inferInstance
      delta := fun S hS n ↦ (hs S hS).δ n (n + 1) rfl
      mono_zero := by
        intro S hS
        haveI : Mono (((ttFunctor τ).map S.f).f 0) := (ttDegreewise τ S hS 0).mono_f
        exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
          ((ttFunctor τ).map S.f) 0 (by intro i hi; change i + 1 = 0 at hi; omega)
      exact_middle := by
        intro S hS n
        exact ⟨_, (hs S hS).homology_exact₂ n⟩
      exact_right := by
        intro S hS n
        exact ⟨_, (hs S hS).homology_exact₃ n (n + 1) rfl⟩
      exact_left := by
        intro S hS n
        exact ⟨_, (hs S hS).homology_exact₁ n (n + 1) rfl⟩
      naturality := by
        intro S R hS hR φ n
        exact HomologicalComplex.HomologySequence.δ_naturality
          ((ttFunctor τ).mapShortComplex.map φ) (hs S hS) (hs R hR) n (n + 1) rfl }

private theorem ttHighZero (τ : G) (M : DiscreteContinuousRep.{u, 0, w} A G)
    (q : ℕ) (hq : 2 ≤ q) : IsZero ((ttComplex τ M).homology q) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  rw [HomologicalComplex.exactAt_iff]
  apply ShortComplex.exact_of_isZero_X₂
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hq
  simpa [ttComplex, ttX, Nat.add_comm] using isZero_zero (ModuleCat.{w} A)

private theorem ttOneZero (τ : G) (M : DiscreteContinuousRep.{u, 0, w} A G)
    (h : Function.Surjective (M.obj.ρ τ - (LinearMap.id : M.obj.V →ₗ[A] M.obj.V))) :
    IsZero ((ttComplex τ M).homology 1) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  exact h x

private theorem ttCoinducedSurjective (l : ℕ) [Fact l.Prime] (s : ℕ)
    (hA : (l ^ s : ℕ) • (1 : A) = 0)
    (M N : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]))
    (e : N.obj.V ≃ₗ[A] LocallyConstant (Multiplicative ℤ_[l]) M.obj.V)
    (he : ∀ (g : Multiplicative ℤ_[l]) (f : N.obj.V) (x : Multiplicative ℤ_[l]),
      e (N.obj.ρ g f) x = e f (x * g)) :
    Function.Surjective (N.obj.ρ (Multiplicative.ofAdd (1 : ℤ_[l])) -
      (LinearMap.id : N.obj.V →ₗ[A] N.obj.V)) := by
  intro f
  let f' : LocallyConstant ℤ_[l] M.obj.V :=
    ⟨fun x ↦ e f (Multiplicative.ofAdd x),
      (e f).isLocallyConstant.comp_continuous continuous_ofAdd⟩
  have hk (m : M.obj.V) : (l ^ s) • m = 0 := by
    calc
      (l ^ s) • m = ((l ^ s) • (1 : A)) • m := by rw [smul_assoc, one_smul]
      _ = 0 := by rw [hA, zero_smul]
  obtain ⟨h, hh⟩ := padic_primitive l s hk f'
  let H : LocallyConstant (Multiplicative ℤ_[l]) M.obj.V :=
    ⟨fun x ↦ h x.toAdd, h.isLocallyConstant.comp_continuous continuous_toAdd⟩
  refine ⟨e.symm H, e.injective ?_⟩
  ext x
  simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, LocallyConstant.sub_apply]
  rw [he]
  simp only [LinearEquiv.apply_symm_apply]
  exact hh x.toAdd
private theorem ttFixed (l : ℕ) [Fact l.Prime]
    (M : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]))
    (m : M.obj.V) (hm : M.obj.ρ (Multiplicative.ofAdd (1 : ℤ_[l])) m = m) :
    ∀ g, M.obj.ρ g m = m := by
  letI : TopologicalSpace M.obj.V := ⊥
  letI : DiscreteTopology M.obj.V := ⟨rfl⟩
  letI : MulAction (Multiplicative ℤ_[l]) M.obj.V :=
    { smul := fun a x ↦ M.obj.ρ a x
      one_smul := by intro x; change M.obj.ρ 1 x = x; rw [map_one]; rfl
      mul_smul := by
        intro a b x
        change M.obj.ρ (a * b) x = M.obj.ρ a (M.obj.ρ b x)
        rw [map_mul]
        rfl }
  haveI : ContinuousSMul (Multiplicative ℤ_[l]) M.obj.V :=
    continuousSMul_iff_stabilizer_isOpen.mpr M.property
  have hc' : Continuous (fun g : Multiplicative ℤ_[l] ↦ M.obj.ρ g m) := by
    change Continuous (fun g : Multiplicative ℤ_[l] ↦ g • m)
    exact continuous_smul.comp (continuous_id.prodMk continuous_const)
  have hc : Continuous (fun x : ℤ_[l] ↦ M.obj.ρ (Multiplicative.ofAdd x) m) :=
    hc'.comp continuous_ofAdd
  have hn (n : ℕ) : M.obj.ρ (Multiplicative.ofAdd (n : ℤ_[l])) m = m := by
    induction n with
    | zero => change M.obj.ρ 1 m = m; simp
    | succ n ih =>
      rw [Nat.cast_add_one, ofAdd_add, map_mul, Module.End.mul_apply, hm, ih]
  intro g
  exact PadicInt.denseRange_natCast.induction_on (p := fun x : ℤ_[l] ↦
      M.obj.ρ (Multiplicative.ofAdd x) m = m) g.toAdd
    (isClosed_eq hc continuous_const) hn

private noncomputable def ttKerEquiv (l : ℕ) [Fact l.Prime]
    (M : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l])) :
    LinearMap.ker (M.obj.ρ (Multiplicative.ofAdd (1 : ℤ_[l])) - LinearMap.id) ≃ₗ[A]
      (⨅ g, LinearMap.ker (M.obj.ρ g - LinearMap.id) : Submodule A M.obj.V) where
  toFun x := ⟨x.val, by
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    exact ttFixed l M x.val (sub_eq_zero.mp x.property)⟩
  invFun x := ⟨x.val, by
    have h := x.property
    simp only [Submodule.mem_iInf] at h
    exact h (Multiplicative.ofAdd (1 : ℤ_[l]))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def ttZeroKerIso (τ : G)
    (M : DiscreteContinuousRep.{u, 0, w} A G) :
    (ttComplex τ M).homology 0 ≅
      ModuleCat.of A (LinearMap.ker (M.obj.ρ τ - LinearMap.id)) :=
  ((ttComplex τ M).isoHomologyπ 0 0 (by simp) (by
    exact (ttComplex τ M).shape _ _ (by simp))).symm ≪≫
    ((ttComplex τ M).cyclesIsKernel 0 1 (by simp)).conePointUniqueUpToIso
      (ModuleCat.kernelIsLimit ((ttComplex τ M).d 0 1))

private theorem ttZeroKerIso_π (τ : G) (M : DiscreteContinuousRep.{u, 0, w} A G) :
    (ttComplex τ M).homologyπ 0 ≫ (ttZeroKerIso τ M).hom ≫
      ModuleCat.ofHom (LinearMap.ker (M.obj.ρ τ - LinearMap.id)).subtype =
        (ttComplex τ M).iCycles 0 := by
  simp only [ttZeroKerIso, Iso.trans_hom, Iso.symm_hom, ← Category.assoc,
    HomologicalComplex.isoHomologyπ_hom_inv_id, Category.id_comp]
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

private theorem ttZeroKerIso_natural (τ : G)
    {M N : DiscreteContinuousRep.{u, 0, w} A G} (f : M ⟶ N) :
    HomologicalComplex.homologyMap (ttMap τ f) 0 ≫ (ttZeroKerIso τ N).hom ≫
        ModuleCat.ofHom (LinearMap.ker (N.obj.ρ τ - LinearMap.id)).subtype =
      (ttZeroKerIso τ M).hom ≫
        ModuleCat.ofHom (LinearMap.ker (M.obj.ρ τ - LinearMap.id)).subtype ≫
          ModuleCat.ofHom f.hom.hom := by
  apply (cancel_epi ((ttComplex τ M).homologyπ 0)).mp
  simp only [← Category.assoc, HomologicalComplex.homologyπ_naturality]
  have hm := ttZeroKerIso_π τ M
  have hn := ttZeroKerIso_π τ N
  simp only [Category.assoc] at hm hn ⊢
  rw [hn]
  simpa only [← hm, Category.assoc, ttMap, CochainComplex.ofHom] using
    HomologicalComplex.cyclesMap_i (ttMap τ f) 0

private noncomputable def ttZeroIso (l : ℕ) [Fact l.Prime]
    (V : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]) ⥤ ModuleCat.{w} A)
    (t : ∀ M : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]),
      V.obj M ≃ₗ[A] (⨅ g, LinearMap.ker (M.obj.ρ g - LinearMap.id) : Submodule A M.obj.V))
    (ht : ∀ (M N : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]))
      (f : M ⟶ N) (x : V.obj M),
      (t N ((V.map f).hom x)).val = f.hom.hom (t M x).val) :
    ttFunctor (Multiplicative.ofAdd (1 : ℤ_[l])) ⋙
      HomologicalComplex.homologyFunctor _ _ 0 ≅ V := by
  let e (M : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l])) :=
    ttZeroKerIso (Multiplicative.ofAdd (1 : ℤ_[l])) M ≪≫
      (ttKerEquiv l M).toModuleIso ≪≫ (t M).toModuleIso.symm
  refine NatIso.ofComponents e ?_
  intro M N f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (t N).injective
  apply Subtype.ext
  change (t N ((e N).hom.hom
      ((HomologicalComplex.homologyMap (ttMap _ f) 0).hom x))).val =
    (t N ((V.map f).hom ((e M).hom.hom x))).val
  rw [ht]
  simp only [e, Iso.trans_hom, Iso.symm_hom, ModuleCat.hom_comp, LinearMap.comp_apply,
    LinearEquiv.toModuleIso_hom, LinearEquiv.toModuleIso_inv,
    ModuleCat.hom_ofHom, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  exact congrArg (fun k ↦ k.hom x) (ttZeroKerIso_natural _ f)

private theorem ttComparison (l : ℕ) [Fact l.Prime] (s : ℕ) [Finite A]
    (hA : (l ^ s : ℕ) • (1 : A) = 0) :
    ∀ q : ℕ, Nonempty
      (discreteContinuousCohomologyFunctor.{0, u, w} (Multiplicative ℤ_[l]) A q ≅
        ttFunctor (Multiplicative.ofAdd (1 : ℤ_[l])) ⋙
          HomologicalComplex.homologyFunctor (ModuleCat.{w} A) (ComplexShape.up ℕ) q) := by
  classical
  let G := Multiplicative ℤ_[l]
  let h := Classical.choose (discreteModules_abelian.{0, u, w} G A)
  letI := h
  letI : Preadditive (DiscreteContinuousRep.{u, 0, w} A G) := h.toPreadditive
  letI : Preadditive (ModuleCat.{w} A) :=
    (inferInstance : Abelian (ModuleCat.{w} A)).toPreadditive
  let hp := Classical.choose_spec (discreteModules_abelian.{0, u, w} G A)
  letI := hp.choose
  letI := hp.choose_spec.1
  letI : PreservesFiniteLimits (ttForget (A := A) (G := G)) := hp.choose_spec.2.1
  letI : PreservesFiniteColimits (ttForget (A := A) (G := G)) := hp.choose_spec.2.2.1
  letI : ∀ M : DiscreteContinuousRep.{u, 0, w} A G, TopologicalSpace M.obj.V := fun _ ↦ ⊥
  letI : ∀ M : DiscreteContinuousRep.{u, 0, w} A G, DiscreteTopology M.obj.V :=
    fun _ ↦ ⟨rfl⟩
  letI : ∀ M : DiscreteContinuousRep.{u, 0, w} A G, ContinuousConstSMul A M.obj.V :=
    fun _ ↦ ⟨fun _ ↦ continuous_of_discreteTopology⟩
  let comp := continuousCochains_derived_invariants.{0, u, w} G A
  let V := Classical.choose comp
  let a := Classical.choose (Classical.choose_spec comp)
  letI : V.Additive := a
  let t := Classical.choose (Classical.choose_spec (Classical.choose_spec comp))
  have ht := (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec comp))).1
  obtain ⟨F, e, hmap, hd, _⟩ := (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec comp))).2
  obtain ⟨V', a', t', ht', hlim, _⟩ :=
    continuousCochains_invariants_zero.{0, u, w} G A F e hmap hd
  letI : PreservesFiniteLimits V' := hlim
  letI : PreservesFiniteLimits V := preservesFiniteLimits_of_natIso
    ((ttZeroIso l V' t' ht').symm ≪≫ ttZeroIso l V t ht)
  obtain ⟨R, hR, hRu, ⟨hRzero⟩⟩ := V.exists_universal_rightDerived_deltaFunctor
  let T := ttDelta (A := A) (Multiplicative.ofAdd (1 : ℤ_[l]))
  have hTu : T.IsUniversal := by
    apply effaceable_deltaFunctor_isUniversal
    intro q hq M
    obtain ⟨D, eD, ι, hD, _, _, hinj⟩ := exists_coinduced_discrete_embedding.{0, u, w} G A
    have hm : Mono (ι.app M) := by
      constructor
      intro Z f g hfg
      apply ObjectProperty.hom_ext
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      apply hinj M
      exact congrArg (fun k ↦ k.hom.hom x) hfg
    refine ⟨D.obj M, ι.app M, hm, ?_⟩
    have hz : IsZero ((ttComplex (Multiplicative.ofAdd (1 : ℤ_[l])) (D.obj M)).homology q) := by
      by_cases heq : q = 1
      · subst q
        exact ttOneZero _ _ (ttCoinducedSurjective l s hA M (D.obj M) (eD M) (hD M))
      · exact ttHighZero _ _ q (by omega)
    exact hz.eq_of_tgt _ _
  have e0 : T.F 0 ≅ R.F 0 := by
    rw [hR]
    exact ttZeroIso l V t ht ≪≫ hRzero.symm
  intro q
  obtain ⟨eqiso⟩ := universalDeltaFunctor_iso T R hTu hRu e0 q
  rw [hR] at eqiso
  exact ⟨eqiso.symm⟩

end Rep

end

namespace Rep

/-- Continuous cohomology of discrete modules over the additive group of l-adic integers
is computed, naturally in coefficients, by the two-term complex with differential `τ - 1`.
Here `Multiplicative` only converts the additive group to the convention of `Rep`;
`Multiplicative.ofAdd (1 : ℤ_[l])` is the specified additive generator, not the group identity.
The equivalences `e₀` and `e₁` identify the two nonzero terms with the coefficient module,
and their naturality equations specify the same coefficient map in both degrees.
The final natural isomorphisms identify the complex's cohomology with the recorded right
derived functors of invariants in every degree.

Proof:
1. Construct the complex functor with the same module in degrees zero and one,
   differential `τ - 1`, and zero above. Equivariance makes the coefficient maps commute
   with the differential. Density of the natural numbers in the l-adic integers identifies
   the kernel of `τ - 1` with invariants, naturally in coefficients.
2. Exactness of the underlying module functor makes this construction degreewise exact.
   The homology long exact sequence and its naturality give a cohomological delta-functor;
   its initial map is monic because there are no incoming differentials in degree zero.
3. Use the translation coinduced embedding. A locally constant function factors through
   reduction modulo `l^r`: choose an open normal translation stabilizer and a sufficiently
   small l-adic ball contained in it. Pull the function back to modulus `l^(r+s)`.
4. The total sum at the larger modulus is `l^s` times the sum at the smaller modulus,
   hence zero. Partial sums give a primitive on the larger cyclic quotient. The zero
   total sum verifies the wraparound equation as well as the ordinary successor equation.
   Pull back this primitive to the l-adic integers. It proves surjectivity of `τ - 1`
   on the coinduced module, and hence vanishing of its degree-one cohomology.
5. Degrees at least two already vanish. The coinduced embedding therefore effaces every
   positive degree, and the effaceable delta-functor is universal.
6. Use the particular invariant functor chosen in `discreteContinuousCohomologyFunctor`.
   Its invariant-submodule equivalences identify it naturally with degree-zero two-term
   cohomology. The degree-zero continuous-cochain comparison supplies a left exact invariant
   functor; transport its finite-limit preservation to the particular chosen functor.
   Its right derived functors form a universal delta-functor.
7. The two universal delta-functors have naturally isomorphic degree-zero terms.
   Extend that isomorphism and its inverse by universality. Uniqueness makes their
   composites identities in every degree, giving the required natural isomorphisms.

Source: blueprint, sec-smooth-purity/sk-prop-a1-kummer/lem-exc-procyclic-two-term,
statement and all three proof paragraphs (blueprint: lem-exc-procyclic-two-term). -/
theorem exists_procyclic_twoTerm_computation
    (l : ℕ) [Fact l.Prime] (s : ℕ) (A : Type u) [Ring A] [Finite A]
    (hA : (l ^ s : ℕ) • (1 : A) = 0) :
    ∃ K : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]) ⥤
        CochainComplex (ModuleCat.{w} A) ℕ,
      ∃ (e₀ : ∀ M : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]),
          (K.obj M).X 0 ≃ₗ[A] M.obj.V)
        (e₁ : ∀ M : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]),
          (K.obj M).X 1 ≃ₗ[A] M.obj.V),
        (∀ (M N : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]))
          (f : M ⟶ N) (x : (K.obj M).X 0),
          e₀ N (((K.map f).f 0).hom x) = f.hom.hom (e₀ M x)) ∧
        (∀ (M N : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]))
          (f : M ⟶ N) (x : (K.obj M).X 1),
          e₁ N (((K.map f).f 1).hom x) = f.hom.hom (e₁ M x)) ∧
        (∀ (M : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]))
          (x : (K.obj M).X 0),
          e₁ M (((K.obj M).d 0 1).hom x) =
            M.obj.ρ (Multiplicative.ofAdd (1 : ℤ_[l])) (e₀ M x) - e₀ M x) ∧
        (∀ (M : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]))
          (n : ℕ), 2 ≤ n → IsZero ((K.obj M).X n)) ∧
        ∀ q : ℕ, Nonempty
          (discreteContinuousCohomologyFunctor.{0, u, w} (Multiplicative ℤ_[l]) A q ≅
            K ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{w} A) (ComplexShape.up ℕ) q) := by
  let K := ttFunctor (A := A) (G := Multiplicative ℤ_[l]) (Multiplicative.ofAdd 1)
  let e₀ : ∀ M : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]),
      (K.obj M).X 0 ≃ₗ[A] M.obj.V := fun M ↦ LinearEquiv.refl A M.obj.V
  let e₁ : ∀ M : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]),
      (K.obj M).X 1 ≃ₗ[A] M.obj.V := fun M ↦ LinearEquiv.refl A M.obj.V
  have hn₀ : ∀ (M N : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]))
      (f : M ⟶ N) (x : (K.obj M).X 0),
      e₀ N (((K.map f).f 0).hom x) = f.hom.hom (e₀ M x) := by intros; rfl
  have hn₁ : ∀ (M N : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]))
      (f : M ⟶ N) (x : (K.obj M).X 1),
      e₁ N (((K.map f).f 1).hom x) = f.hom.hom (e₁ M x) := by intros; rfl
  have hd : ∀ (M : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]))
      (x : (K.obj M).X 0), e₁ M (((K.obj M).d 0 1).hom x) =
      M.obj.ρ (Multiplicative.ofAdd (1 : ℤ_[l])) (e₀ M x) - e₀ M x := by
    intros; rfl
  have hz : ∀ (M : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]))
      (n : ℕ), 2 ≤ n → IsZero ((K.obj M).X n) := by
    intro M n hn
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn
    simpa [K, ttFunctor, ttComplex, ttX, Nat.add_comm] using
      (isZero_zero (ModuleCat.{w} A))
  exact ⟨K, e₀, e₁, hn₀, hn₁, hd, hz,
    ttComparison l s hA⟩

end Rep
