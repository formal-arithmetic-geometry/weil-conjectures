/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.RingTheory.LocalEssentiallyFinitePresentationModInjective
import Sheaf.RingTheory.RegularSequenceGradedPolynomial
import Sheaf.RingTheory.QuasiRegularFlatQuotientBaseChange
import Sheaf.RingTheory.QuasiRegularNoetherianLocal
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Relative regular equations after arbitrary base change

Source: Stacks Project, Divisors, Tags 0FUD and 063U, and More on Algebra, Tag 0CEP
(blueprint: lem-pur-relative-regular-equations-base-change).

The primes in the conclusion contain the specified equations, so regularity includes
nonvanishing of the final quotient. No flatness of the changing algebra is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace RingTheory.Sequence

open scoped Pointwise in
private theorem flat_quotSMulTop_of_residue_injective
    {P : Type*} [CommRing P] {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M] [Module.FinitePresentation S M] [Module.Flat R M]
    [Algebra R P] [Algebra P S] [IsScalarTower R P S]
    [Algebra.FinitePresentation R P] (W : Submonoid P) [IsLocalization W S]
    (x : S)
    (h : Function.Injective
      ((IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)).mapQ
        (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M))
        ((LinearMap.lsmul S M x).restrictScalars R)
        (Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal R)
          ((LinearMap.lsmul S M x).restrictScalars R)))) :
    IsSMulRegular M x ∧ Module.Flat R (QuotSMulTop x M) := by
  let u := (LinearMap.lsmul S M x).restrictScalars R
  obtain ⟨hinj, hflat⟩ :=
    Algebra.local_essentially_finite_presentation_mod_injective (P := P) W (LinearMap.lsmul S M x) h
  have hrange : LinearMap.range u = (x • (⊤ : Submodule S M)).restrictScalars R := by
    ext y
    change (∃ z, x • z = y) ↔ y ∈ x • (⊤ : Submodule S M)
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
  refine ⟨hinj, ?_⟩
  have : Module.Flat R (M ⧸ LinearMap.range u) := hflat
  exact Module.Flat.of_linearEquiv
    ((Submodule.Quotient.restrictScalarsEquiv R (x • (⊤ : Submodule S M))).symm.trans
      (Submodule.quotEquivOfEq _ _ hrange.symm))

open scoped Pointwise in
/-- The closed-fibre multiplication criterion makes the next prefix quotient flat.
This is the induction step of Stacks Tag 00MG, using Tag 046Y for an essentially
finitely presented local algebra. The double-quotient interchange identifies the
closed fibre of the prefix with the prefix in the closed fibre. -/
private theorem closedFiber_regular_step
    {P : Type*} [CommRing P] {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra R P] [Algebra P S] [IsScalarTower R P S]
    [Algebra.FinitePresentation R P] (W : Submonoid P) [IsLocalization W S]
    (fs : List S) (i : ℕ) (hi : i < fs.length) :
    let I : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
    IsRegular (S ⧸ I) (fs.map (Ideal.Quotient.mk I)) →
    Module.Flat R (S ⧸ Ideal.ofList (fs.take i)) →
    IsSMulRegular
        (S ⧸ (Ideal.ofList (fs.take i) • (⊤ : Submodule S S))) fs[i] ∧
      Module.Flat R (S ⧸ Ideal.ofList (fs.take (i + 1))) := by
  dsimp only
  intro hreg hflat
  let I : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  let J : Ideal S := Ideal.ofList (fs.take i)
  let Q := S ⧸ J
  have : Module.Flat R Q := hflat
  have : Module.FinitePresentation S Q :=
    Module.finitePresentation_of_surjective J.mkQ (Submodule.mkQ_surjective J)
      (by rw [Submodule.ker_mkQ]; exact Submodule.fg_span (fs.take i).finite_toSet)
  have hlen : i < (fs.map (Ideal.Quotient.mk I)).length := by simpa using hi
  have hbar := hreg.regular_mod_prev i (by simpa using hi)
  have hJ : Ideal.ofList ((fs.map (Ideal.Quotient.mk I)).take i) =
      J.map (Ideal.Quotient.mk I) := by
    rw [← List.map_take, ← Ideal.map_ofList]
  have hsmul : (Ideal.ofList ((fs.map (Ideal.Quotient.mk I)).take i) •
      (⊤ : Submodule (S ⧸ I) (S ⧸ I))) = J.map (Ideal.Quotient.mk I) := by
    rw [hJ, Ideal.smul_eq_mul, Ideal.mul_top]
  rw [hsmul] at hbar
  have hbar' : IsSMulRegular ((S ⧸ I) ⧸ J.map (Ideal.Quotient.mk I))
      (fs.map (Ideal.Quotient.mk I))[i] := hbar
  let e := DoubleQuot.quotQuotEquivCommₐ S I J
  have hQ : IsSMulRegular (Q ⧸ I.map (Ideal.Quotient.mk J)) fs[i] := by
    have hb : IsSMulRegular ((S ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) fs[i] := by
      rw [List.getElem_map] at hbar'
      exact (isSMulRegular_algebraMap_iff (A := S ⧸ I)).mp hbar'
    exact (e.toLinearEquiv.isSMulRegular_congr fs[i]).mp hb
  have hI : IsLocalRing.maximalIdeal R • (⊤ : Submodule R Q) =
      (I.map (Ideal.Quotient.mk J)).restrictScalars R := by
    rw [Ideal.smul_top_eq_map, Ideal.map_map]
    rfl
  let eR : (Q ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R Q))) ≃ₗ[R]
      Q ⧸ I.map (Ideal.Quotient.mk J) :=
    (Submodule.quotEquivOfEq _ _ hI).trans
      (Submodule.Quotient.restrictScalarsEquiv R _)
  have hmod : Function.Injective
      ((IsLocalRing.maximalIdeal R • (⊤ : Submodule R Q)).mapQ
        (IsLocalRing.maximalIdeal R • (⊤ : Submodule R Q))
        ((LinearMap.lsmul S Q fs[i]).restrictScalars R)
        (Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal R)
          ((LinearMap.lsmul S Q fs[i]).restrictScalars R))) := by
    intro a b hab
    apply eR.injective
    apply hQ
    have hcomm (a : Q ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R Q))) :
        eR (((IsLocalRing.maximalIdeal R • (⊤ : Submodule R Q)).mapQ
          (IsLocalRing.maximalIdeal R • (⊤ : Submodule R Q))
          ((LinearMap.lsmul S Q fs[i]).restrictScalars R)
          (Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal R)
            ((LinearMap.lsmul S Q fs[i]).restrictScalars R))) a) = fs[i] • eR a := by
      induction a using Submodule.Quotient.induction_on with
      | H a => rfl
    change fs[i] • eR a = fs[i] • eR b
    rw [← hcomm, ← hcomm, hab]
  have hstep := flat_quotSMulTop_of_residue_injective (R := R) (P := P) W fs[i] hmod
  have hregular : IsSMulRegular
      (S ⧸ (Ideal.ofList (fs.take i) • (⊤ : Submodule S S))) fs[i] := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact hstep.1
  refine ⟨hregular, ?_⟩
  have : Module.Flat R (QuotSMulTop fs[i] Q) := hstep.2
  let eNext := Submodule.quotOfListConsSMulTopEquivQuotSMulTopOuter S fs[i] (fs.take i)
  have heq : Ideal.ofList (fs.take (i + 1)) • (⊤ : Submodule S S) =
      Ideal.ofList (fs[i] :: fs.take i) • (⊤ : Submodule S S) := by
    congr 1
    rw [List.take_succ_eq_append_getElem hi, Ideal.ofList_append]
    simp only [Ideal.ofList_cons, Ideal.ofList_nil, sup_comm]
    rw [bot_sup_eq]
  let e₁ := Submodule.quotEquivOfEq _ _ heq
  have heqJ : Ideal.ofList (fs.take i) • (⊤ : Submodule S S) = J := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  let e₂ := QuotSMulTop.congr fs[i] (Submodule.quotEquivOfEq _ _ heqJ)
  have heqNext : Ideal.ofList (fs.take (i + 1)) • (⊤ : Submodule S S) =
      Ideal.ofList (fs.take (i + 1)) := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  let e₀ := (Submodule.quotEquivOfEq _ _ heqNext).symm
  exact Module.Flat.of_linearEquiv
    ((e₀.trans (e₁.trans (eNext.trans e₂))).restrictScalars R)


private theorem flat_prefix_of_closedFiber
    {R S P : Type*} [CommRing R] [CommRing S] [CommRing P]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Algebra R P] [Algebra P S]
    [IsScalarTower R P S] [Algebra.FinitePresentation R P]
    (W : Submonoid P) [IsLocalization W S] [Module.Flat R S]
    (fs : List S)
    (hreg : IsRegular (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
      (fs.map (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal R).map (algebraMap R S))))) :
    ∀ i : ℕ, i ≤ fs.length → Module.Flat R (S ⧸ Ideal.ofList (fs.take i)) := by
  intro i hi
  induction i with
  | zero =>
    rw [List.take_zero, Ideal.ofList_nil]
    exact Module.Flat.of_linearEquiv
      ((Submodule.quotEquivOfEqBot (⊥ : Submodule S S) rfl).restrictScalars R)
  | succ i ih =>
    exact (closedFiber_regular_step (P := P) W fs i
      (Nat.lt_of_succ_le hi) hreg (ih (Nat.le_of_succ_le hi))).2

open scoped TensorProduct in
private theorem flat_prefix_atPrime
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    {b : ℕ} (f : Fin b → A) (hreg : IsRegular A (List.ofFn f))
    [Module.Flat R (A ⧸ Ideal.span (Set.range f))]
    (p : Ideal A) [p.IsPrime] (hmem : ∀ j : Fin b, f j ∈ p) :
    ∀ i : ℕ, i ≤ b → Module.Flat R (Localization.AtPrime p ⧸
      (Ideal.ofList ((List.ofFn f).take i)).map (algebraMap A (Localization.AtPrime p))) := by
  let S := Localization.AtPrime p
  let r := p.comap (algebraMap R A)
  let Rl := Localization.AtPrime r
  let K := IsLocalRing.ResidueField Rl
  let : Algebra Rl S := (Localization.localRingHom r p (algebraMap R A) rfl).toAlgebra
  have : IsLocalHom (algebraMap Rl S) := Localization.isLocalHom_localRingHom _ _ _ _
  have : IsScalarTower R Rl S := .of_algebraMap_eq' (by
    ext x
    exact (Localization.localRingHom_to_map r p (algebraMap R A) rfl x).symm)
  let P := Localization (Algebra.algebraMapSubmonoid A r.primeCompl)
  let : Algebra Rl P := (IsLocalization.map (M := r.primeCompl) (S := Rl)
    (T := Algebra.algebraMapSubmonoid A r.primeCompl) P (algebraMap R A)
    (by intro x hx; exact ⟨x, hx, rfl⟩)).toAlgebra
  have : IsScalarTower R Rl P := .of_algebraMap_eq' (by
    ext x
    change algebraMap A P (algebraMap R A x) =
      IsLocalization.map (M := r.primeCompl) (S := Rl)
        (T := Algebra.algebraMapSubmonoid A r.primeCompl) P (algebraMap R A)
        (by intro y hy; exact ⟨y, hy, rfl⟩) (algebraMap R Rl x)
    exact (IsLocalization.map_eq _ x).symm)
  have hle : Algebra.algebraMapSubmonoid A r.primeCompl ≤ p.primeCompl := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  let : Algebra P S := IsLocalization.localizationAlgebraOfSubmonoidLe P S
    (Algebra.algebraMapSubmonoid A r.primeCompl) p.primeCompl hle
  have : IsScalarTower A P S := IsLocalization.localization_isScalarTower_of_submonoid_le
    P S (Algebra.algebraMapSubmonoid A r.primeCompl) p.primeCompl hle
  have : IsScalarTower Rl P S := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext r.primeCompl
    ext x
    change algebraMap Rl S (algebraMap R Rl x) =
      algebraMap P S (algebraMap Rl P (algebraMap R Rl x))
    rw [← IsScalarTower.algebraMap_apply R Rl S,
      ← IsScalarTower.algebraMap_apply R Rl P,
      IsScalarTower.algebraMap_apply R A P,
      ← IsScalarTower.algebraMap_apply A P S,
      ← IsScalarTower.algebraMap_apply R A S]
  have : Algebra.IsPushout R A Rl P :=
    Algebra.isPushout_of_isLocalization r.primeCompl Rl A P
  have : Algebra.IsPushout R Rl A P := (Algebra.IsPushout.comm R A Rl P).mp inferInstance
  have : Algebra.FinitePresentation Rl P :=
    Algebra.FinitePresentation.equiv (Algebra.IsPushout.equiv R Rl A P)
  have : IsLocalization (p.primeCompl.map (algebraMap A P)) S :=
    IsLocalization.isLocalization_of_submonoid_le P S
      (Algebra.algebraMapSubmonoid A r.primeCompl) p.primeCompl hle
  have : Module.Flat R S := inferInstance
  have : Module.Flat Rl S := (Module.flat_iff_of_isLocalization Rl r.primeCompl S).mpr
    (inferInstance : Module.Flat R S)
  let g := fun j ↦ algebraMap A S (f j)
  have hregS : IsRegular S (List.ofFn g) := by
    have hw := hreg.toIsWeaklyRegular.of_isLocalization S p.primeCompl
    rw [List.map_ofFn] at hw
    apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal ?_).mpr hw
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff S p _).mpr (hmem j)
  let J := Ideal.span (Set.range f)
  have hJ : Ideal.span (Set.range g) = J.map (algebraMap A S) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have : Module.Flat R (S ⧸ Ideal.span (Set.range g)) := by
    rw [hJ]
    have : Module.Flat (A ⧸ J) (S ⧸ J.map (algebraMap A S)) :=
      IsLocalization.flat _ (Algebra.algebraMapSubmonoid (A ⧸ J) p.primeCompl)
    have : IsScalarTower R (A ⧸ J) (S ⧸ J.map (algebraMap A S)) :=
      .of_algebraMap_eq' rfl
    exact Module.Flat.trans R (A ⧸ J) _
  have hgraded := Ideal.quasiRegular_flatQuotient_baseChange (R := R) (R' := K) g
    (Ideal.regularSequence_gradedPolynomial g hregS).1
  let F := S ⊗[R] K
  let e : S ⊗[Rl] K ≃ₐ[Rl] F := IsLocalization.algebraTensorEquiv r.primeCompl Rl S K
  have : IsLocalRing F := by
    have : IsLocalRing (S ⊗[Rl] K) :=
      (Algebra.TensorProduct.comm Rl K S).toRingEquiv.isLocalRing
    exact e.toRingEquiv.isLocalRing
  have : IsNoetherianRing F := by
    let B := A ⊗[R] K
    have : IsNoetherianRing (K ⊗[R] A) :=
      Algebra.FiniteType.isNoetherianRing K (K ⊗[R] A)
    have : IsNoetherianRing B := isNoetherianRing_of_ringEquiv (K ⊗[R] A)
      (Algebra.TensorProduct.comm R K A).toRingEquiv
    let : Algebra B F := (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom R A S) (AlgHom.id R K)).toAlgebra
    have : IsScalarTower A B F := .of_algebraMap_eq' (by ext x; rfl)
    have : IsLocalization (Algebra.algebraMapSubmonoid B p.primeCompl) F :=
      IsLocalization.tensorProduct_tensorProduct R K p.primeCompl S (by
        apply RingHom.ext
        intro x
        change Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A S)
          (AlgHom.id R K) (1 ⊗ₜ[R] x) = 1 ⊗ₜ[R] x
        simp only [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply])
    exact IsLocalization.isNoetherianRing
      (Algebra.algebraMapSubmonoid B p.primeCompl) F inferInstance
  let I := (IsLocalRing.maximalIdeal Rl).map (algebraMap Rl S)
  let eQ : (S ⧸ I) ≃ₐ[Rl] F :=
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S
      (IsLocalRing.maximalIdeal Rl)).restrictScalars Rl).trans e
  have heQ (x : S) : eQ (Ideal.Quotient.mk I x) = x ⊗ₜ[R] (1 : K) := by
    change e ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S
      (IsLocalRing.maximalIdeal Rl)) (Ideal.Quotient.mk I x)) = _
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
    rfl
  have : IsLocalRing (S ⧸ I) := eQ.symm.toRingEquiv.isLocalRing
  have hregF : IsRegular F (List.ofFn fun j ↦ g j ⊗ₜ[R] (1 : K)) :=
    quasiRegularNoetherianLocal b _ (by
      intro j
      rw [← heQ]
      have : IsLocalHom eQ.toRingHom := eQ.surjective.isLocalHom
      have : IsLocalHom (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective.isLocalHom
      exact map_nonunit eQ.toRingHom _
        (map_nonunit (Ideal.Quotient.mk I) _
          ((IsLocalization.AtPrime.to_map_mem_maximal_iff S p _).mpr (hmem j)))) hgraded
  have hregQ : IsRegular (S ⧸ I)
      ((List.ofFn g).map (Ideal.Quotient.mk I)) := by
    apply (eQ.toRingEquiv.toAddEquiv.isRegular_congr ?_).mpr hregF
    rw [show (List.ofFn fun j ↦ g j ⊗ₜ[R] (1 : K)) =
      (List.ofFn g).map (fun x ↦ x ⊗ₜ[R] (1 : K)) by
        rw [List.map_ofFn]; rfl]
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro a _ x
    change eQ (Ideal.Quotient.mk I a * x) = (a ⊗ₜ[R] (1 : K)) * eQ x
    rw [map_mul, heQ]
  have hprefix := flat_prefix_of_closedFiber (R := Rl) (S := S) (P := P)
    (p.primeCompl.map (algebraMap A P)) (List.ofFn g) hregQ
  intro i hi
  have : Module.Flat Rl (S ⧸ Ideal.ofList ((List.ofFn g).take i)) :=
    hprefix i (by simpa only [List.length_ofFn] using hi)
  have hf := (Module.flat_iff_of_isLocalization Rl r.primeCompl
    (S ⧸ Ideal.ofList ((List.ofFn g).take i))).mp inferInstance
  have hlist : List.ofFn g = (List.ofFn f).map (algebraMap A S) := by
    simp only [List.map_ofFn, Function.comp_def, g]
  rw [hlist, ← List.map_take, ← Ideal.map_ofList] at hf
  exact hf

open scoped Pointwise in
private theorem smul_regular_tensor_of_flat_quotient
    {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [AddCommGroup N] [Module R N] (x : A) (hx : IsSMulRegular M x)
    [Module.Flat R (QuotSMulTop x M)] :
    IsSMulRegular (M ⊗[R] N) x := by
  let g := (LinearMap.lsmul A M x).restrictScalars R
  have hrange : LinearMap.range g = (x • (⊤ : Submodule A M)).restrictScalars R := by
    ext y
    change (∃ z, x • z = y) ↔ y ∈ x • (⊤ : Submodule A M)
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
  have : Module.Flat R (M ⧸ LinearMap.range g) :=
    Module.Flat.of_linearEquiv
      ((Submodule.Quotient.restrictScalarsEquiv R (x • (⊤ : Submodule A M))).symm.trans
        (Submodule.quotEquivOfEq _ _ hrange.symm)).symm
  have hinj := LinearMap.lTensor_injective_of_exact_of_flat
    (LinearMap.range g).mkQ (Submodule.mkQ_surjective _) g hx
    (by rw [LinearMap.exact_iff, Submodule.ker_mkQ]) N
  have hinj' : Function.Injective (g.rTensor N) :=
    (LinearMap.lTensor_inj_iff_rTensor_inj N g).mp hinj
  have hmap (z : M ⊗[R] N) : (g.rTensor N) z = x • z := by
    induction z with
    | zero => simp
    | add z t hz ht => simp [hz, ht, smul_add]
    | tmul m n => rfl
  intro z t h
  apply hinj'
  simpa only [hmap] using h

private theorem weaklyRegular_tensor_of_flat_prefix
    {R D R' : Type*} [CommRing R] [CommRing D] [CommRing R']
    [Algebra R D] [Algebra R R'] (fs : List D) (hreg : IsWeaklyRegular D fs)
    (hflat : ∀ i : ℕ, i ≤ fs.length → Module.Flat R (D ⧸ Ideal.ofList (fs.take i))) :
    IsWeaklyRegular (D ⊗[R] R') (fs.map (algebraMap D (D ⊗[R] R'))) := by
  constructor
  intro i hi
  have hi' : i < fs.length := by simpa only [List.length_map] using hi
  let J := Ideal.ofList (fs.take i)
  let Q := D ⧸ J
  have hJ : (J • (⊤ : Submodule D D)) = J := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have hregQ : IsSMulRegular Q fs[i] := by
    let eQ := Submodule.quotEquivOfEq _ _ hJ
    exact (eQ.isSMulRegular_congr fs[i]).mp (hreg.regular_mod_prev i hi')
  have hnext : Module.Flat R (QuotSMulTop fs[i] Q) := by
    have := hflat (i + 1) (Nat.succ_le_iff.mpr hi')
    have heq : Ideal.ofList (fs.take (i + 1)) • (⊤ : Submodule D D) =
        Ideal.ofList (fs[i] :: fs.take i) • (⊤ : Submodule D D) := by
      congr 1
      rw [List.take_succ_eq_append_getElem hi', Ideal.ofList_append]
      simp only [Ideal.ofList_cons, Ideal.ofList_nil, sup_comm, bot_sup_eq]
    let e₀ := (Submodule.quotEquivOfEq _ _
      (show Ideal.ofList (fs.take (i + 1)) • (⊤ : Submodule D D) =
        Ideal.ofList (fs.take (i + 1)) by rw [Ideal.smul_eq_mul, Ideal.mul_top])).symm
    let e₁ := Submodule.quotEquivOfEq _ _ heq
    let e₂ := Submodule.quotOfListConsSMulTopEquivQuotSMulTopOuter D fs[i] (fs.take i)
    let e₃ := QuotSMulTop.congr fs[i] (Submodule.quotEquivOfEq _ _
      (show Ideal.ofList (fs.take i) • (⊤ : Submodule D D) = J by
        rw [Ideal.smul_eq_mul, Ideal.mul_top]))
    exact Module.Flat.of_linearEquiv
      ((e₀.trans (e₁.trans (e₂.trans e₃))).restrictScalars R).symm
  have ht : IsSMulRegular (Q ⊗[R] R') fs[i] :=
    smul_regular_tensor_of_flat_quotient (R := R) fs[i] hregQ
  let e := Algebra.TensorProduct.quotientTensorEquiv (R := R) D R' D J
  have ht' : IsSMulRegular ((D ⊗[R] R') ⧸ J.map (algebraMap D (D ⊗[R] R'))) fs[i] :=
    (e.toLinearEquiv.isSMulRegular_congr fs[i]).mp ht
  rw [List.getElem_map, ← List.map_take, ← Ideal.map_ofList,
    Ideal.smul_eq_mul, Ideal.mul_top]
  exact (isSMulRegular_algebraMap_iff (A := D ⊗[R] R')).mpr ht'

/-- A regular sequence in a flat finitely presented algebra with flat final quotient
remains regular at every prime containing its images after arbitrary base change.
Source: Stacks Project, Divisors, Tag 0FUD, remark-relative-regular-immersion-elements,
and Tag 063U, lemma-relative-regular-immersion-flat-in-neighbourhood; More on Algebra,
Tag 0CEP (blueprint: lem-pur-relative-regular-equations-base-change).

Proof:
1. Contract the chosen prime to p in A and then to r in R. Put S = A_p and
   Rl = R_r. The natural local map Rl → S is essentially finitely presented:
   first form P = (R \ r)⁻¹A = Rl ⊗[R] A, then localize P further.
   Localization preserves the original regular sequence and flat final quotient.
2. Regularity in S gives the polynomial associated-graded isomorphism. Apply
   quasi-regular flat-quotient base change to the residue field k of Rl. The ring
   F = S ⊗[R] k is local, because it identifies with S/(maximalIdeal Rl)S.
   It is Noetherian, being a localization of the finite type k-algebra A ⊗[R] k.
   The Noetherian local quasi-regularity criterion gives regularity in F.
3. Induct on the prefix length. For the quotient Q by a prefix, finite generation
   of the prefix ideal gives finite presentation as an S-module. Closed-fibre
   regularity makes multiplication by the next equation injective modulo the
   maximal ideal of Rl. Apply Stacks Tag 046Y, the essentially finitely presented
   local module criterion, to Q → Q. Its cokernel is the next prefix quotient,
   hence flat over Rl and therefore over R. The empty prefix is S itself.
4. Tensor the successive multiplication injections with R'. Their cokernels are
   flat by step 3, so tensoring preserves injectivity. The tensor-quotient
   equivalence identifies these maps with the multiplication maps on the prefix
   quotients of E = S ⊗[R] R'. Thus the sequence is weakly regular in E.
5. E is the localization of B = A ⊗[R] R' at the image of A \ p. This image
   avoids the given prime q, so B_q is a further localization of E. Weak
   regularity persists there. Every equation lies in its maximal ideal, giving
   regularity including the nonzero final quotient. This also covers b = 0.
-/
theorem isRegular_localizationAtPrime_tensorProduct_of_flat_quotient
    {R : Type u} {A : Type v} {R' : Type w}
    [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    {b : ℕ} (f : Fin b → A) (hreg : IsRegular A (List.ofFn f))
    [Module.Flat R (A ⧸ Ideal.span (Set.range f))]
    (q : Ideal (A ⊗[R] R')) [q.IsPrime]
    (hmem : ∀ j : Fin b, f j ⊗ₜ[R] (1 : R') ∈ q) :
    IsRegular (Localization.AtPrime q)
      (List.ofFn fun j : Fin b ↦
        algebraMap (A ⊗[R] R') (Localization.AtPrime q) (f j ⊗ₜ[R] (1 : R'))) := by
  let B := A ⊗[R] R'
  let L := Localization.AtPrime q
  let p := q.comap (algebraMap A B)
  have hflat := flat_prefix_atPrime (R := R) f hreg p hmem
  let D := Localization.AtPrime p
  let E := D ⊗[R] R'
  let fs := (List.ofFn f).map (algebraMap A D)
  have hwD : IsWeaklyRegular D fs :=
    hreg.toIsWeaklyRegular.of_isLocalization D p.primeCompl
  have hflatD : ∀ i : ℕ, i ≤ fs.length → Module.Flat R (D ⧸ Ideal.ofList (fs.take i)) := by
    intro i hi
    have hf := hflat i (by simpa only [fs, List.length_map, List.length_ofFn] using hi)
    have heq : Ideal.ofList (fs.take i) =
        (Ideal.ofList ((List.ofFn f).take i)).map (algebraMap A D) := by
      rw [Ideal.map_ofList, List.map_take]
    rw [heq]
    exact hf
  have hwE : IsWeaklyRegular E (fs.map (algebraMap D E)) :=
    weaklyRegular_tensor_of_flat_prefix fs hwD hflatD
  let : Algebra B E :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A D) (AlgHom.id R R')).toAlgebra
  have : IsScalarTower A B E := .of_algebraMap_eq' (by ext a; rfl)
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid B p.primeCompl) E :=
    IsLocalization.tensorProduct_tensorProduct R R' p.primeCompl D (by
      ext t
      change Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A D)
        (AlgHom.id R R') (1 ⊗ₜ[R] t) = 1 ⊗ₜ[R] t
      simp only [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply])
  have : IsLocalization (Algebra.algebraMapSubmonoid B p.primeCompl) E := hloc
  have hle : Algebra.algebraMapSubmonoid B p.primeCompl ≤ q.primeCompl := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  let : Algebra E L := IsLocalization.localizationAlgebraOfSubmonoidLe E L
    (Algebra.algebraMapSubmonoid B p.primeCompl) q.primeCompl hle
  have : IsScalarTower B E L := IsLocalization.localization_isScalarTower_of_submonoid_le
    E L (Algebra.algebraMapSubmonoid B p.primeCompl) q.primeCompl hle
  have : IsLocalization (q.primeCompl.map (algebraMap B E)) L :=
    IsLocalization.isLocalization_of_submonoid_le E L
      (Algebra.algebraMapSubmonoid B p.primeCompl) q.primeCompl hle
  have : Module.Flat E L := IsLocalization.flat L (q.primeCompl.map (algebraMap B E))
  have hwL := hwE.of_flat (S := L)
  have heq : ((fs.map (algebraMap D E)).map (algebraMap E L)) =
      List.ofFn (fun j : Fin b ↦ algebraMap B L (f j ⊗ₜ[R] (1 : R'))) := by
    simp only [fs, List.map_ofFn, Function.comp_def]
    congr 1
    funext j
    change algebraMap E L (algebraMap B E (f j ⊗ₜ[R] (1 : R'))) = _
    exact (IsScalarTower.algebraMap_apply B E L _).symm
  rw [heq] at hwL
  apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal ?_).mpr hwL
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L q _).mpr (hmem j)

end RingTheory.Sequence
