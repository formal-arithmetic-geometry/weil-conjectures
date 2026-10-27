/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q136
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.RingTheory.Finiteness.Defs

import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Localization at the unique prime over a base prime

Source: Stacks Project, Algebra, Tags 00EA and 00DK
(blueprint: lem-trf-unique-prime-localization).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace IsLocalization

/-- The canonical `B`-algebra map `S⁻¹B → B_q`, with `S = A ∖ p`.
Source: Stacks, Tag 00EA (blueprint: lem-trf-unique-prime-localization). -/
noncomputable def uniquePrimeLocalizationMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]
    (hpq : Ideal.comap (algebraMap A B) q = p) :
    Localization (Submonoid.map (algebraMap A B) p.primeCompl) →ₐ[B]
      Localization.AtPrime q :=
  IsLocalization.liftAlgHom
    (M := Submonoid.map (algebraMap A B) p.primeCompl)
    (f := Algebra.ofId B (Localization.AtPrime q))
    (fun y ↦ by
      rcases y.property with ⟨a, ha, he⟩
      exact he ▸ IsLocalization.map_units (Localization.AtPrime q)
        (⟨algebraMap A B a, fun h ↦ ha
          ((congrArg (fun I : Ideal A ↦ a ∈ I) hpq).mp h)⟩ : q.primeCompl))

/-- The usual action of `A_p` on `M ⊗[A] A_p`, obtained by tensor symmetry.
Source: Stacks, Tag 00DK (blueprint: lem-trf-unique-prime-localization). -/
noncomputable abbrev uniquePrimeTensorModule
    {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]
    (M : Type w) [AddCommGroup M] [Module A M] :
    Module (Localization.AtPrime p) (M ⊗[A] Localization.AtPrime p) :=
  (TensorProduct.comm A M (Localization.AtPrime p)).toAddEquiv.module
    (Localization.AtPrime p)

/-- The canonical action of `A_p` on `M_q`, by the localized ring map `A_p → B_q`.
Source: Stacks, Tags 00EA and 00DK (blueprint: lem-trf-unique-prime-localization). -/
noncomputable abbrev uniquePrimeLocalizedModule
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]
    (hpq : Ideal.comap (algebraMap A B) q = p)
    (M : Type w) [AddCommGroup M] [Module B M] :
    Module (Localization.AtPrime p) (LocalizedModule.AtPrime q M) :=
  @Module.compHom (Localization.AtPrime q) (Localization.AtPrime p)
    (LocalizedModule.AtPrime q M) _ _
    (LocalizedModule.moduleOfIsLocalization (S := q.primeCompl)) _
    (Localization.localRingHom p q (algebraMap A B) hpq.symm)

/-- The type of `A_p`-linear equivalences with the canonical actions on both sides.
Source: Stacks, Tags 00EA and 00DK (blueprint: lem-trf-unique-prime-localization). -/
abbrev UniquePrimeModuleEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]
    (hpq : Ideal.comap (algebraMap A B) q = p)
    (M : Type w) [AddCommGroup M] [Module B M] [Module A M] :=
  @LinearEquiv (Localization.AtPrime p) (Localization.AtPrime p) _ _
    (RingHom.id _) (RingHom.id _) _ _
    (M ⊗[A] Localization.AtPrime p) (LocalizedModule.AtPrime q M) _ _
    (uniquePrimeTensorModule p M) (uniquePrimeLocalizedModule p q hpq M)

private theorem shrinkLocalizedModule
    {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (S T : Submonoid R) (hST : S ≤ T)
    (hcof : ∀ t : T, ∃ d : R, d * t ∈ S) (f : M →ₗ[R] N)
    [IsLocalizedModule T f] : IsLocalizedModule S f where
  map_units s := IsLocalizedModule.map_units f ⟨s, hST s.property⟩
  surj y := by
    obtain ⟨⟨m, t⟩, ht⟩ := IsLocalizedModule.surj T f y
    obtain ⟨d, hd⟩ := hcof t
    refine ⟨⟨d • m, ⟨d * t, hd⟩⟩, ?_⟩
    change (d * (t : R)) • y = f (d • m)
    rw [mul_smul, map_smul, ← ht]
    change d • ((t : R) • y) = _
    rfl
  exists_of_eq h := by
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := T) (f := f) h
    obtain ⟨d, hd⟩ := hcof t
    refine ⟨⟨d * t, hd⟩, ?_⟩
    simpa only [Submonoid.smul_def, mul_smul] using congrArg (d • ·) ht

private theorem uniquePrimeDenominators
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]
    (_hpq : Ideal.comap (algebraMap A B) q = p)
    (huniq : ∀ (q' : Ideal B), q'.IsPrime →
      Ideal.comap (algebraMap A B) q' = p → q' = q) :
    ∀ t : q.primeCompl, ∃ d : B,
      d * t ∈ Submonoid.map (algebraMap A B) p.primeCompl := by
  let S := Submonoid.map (algebraMap A B) p.primeCompl
  let C := Localization S
  have hunit (t : q.primeCompl) : IsUnit (algebraMap B C t) := by
    by_contra hn
    obtain ⟨m, hm, htm⟩ := exists_max_ideal_of_mem_nonunits hn
    have := hm
    let r := m.comap (algebraMap B C)
    have hrp : r.comap (algebraMap A B) ≤ p := by
      intro a ha
      by_contra hap
      have hu := IsLocalization.map_units C
        (⟨algebraMap A B a, ⟨a, hap, rfl⟩⟩ : S)
      exact hm.ne_top (m.eq_top_of_isUnit_mem ha hu)
    obtain ⟨r', hrr', hr', hr'p⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime p r hrp
    have hrq : r ≤ q := huniq r' hr' hr'p ▸ hrr'
    exact t.property (hrq htm)
  intro t
  obtain ⟨s, hs, d, hd⟩ := (IsLocalization.algebraMap_isUnit_iff (S := C) S).mp (hunit t)
  exact ⟨d, by simpa only [hd, mul_comm] using hs⟩

set_option backward.isDefEq.respectTransparency false in
private noncomputable def uniquePrimeEquivOfCofinal
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]
    (hpq : Ideal.comap (algebraMap A B) q = p)
    (hST : Submonoid.map (algebraMap A B) p.primeCompl ≤ q.primeCompl)
    (hcof : ∀ t : q.primeCompl, ∃ d : B,
      d * t ∈ Submonoid.map (algebraMap A B) p.primeCompl)
    (M : Type w) [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower A B M] : UniquePrimeModuleEquiv p q hpq M := by
  letI : Module (Localization.AtPrime q) (LocalizedModule.AtPrime q M) :=
    LocalizedModule.moduleOfIsLocalization (S := q.primeCompl)
  -- Override the default quotient action with the action fixed by the statement.
  letI : SMul (Localization.AtPrime q) (LocalizedModule.AtPrime q M) :=
    (LocalizedModule.moduleOfIsLocalization (S := q.primeCompl)).toSMul
  letI : Module (Localization.AtPrime p) (LocalizedModule.AtPrime q M) :=
    uniquePrimeLocalizedModule p q hpq M
  have htower : IsScalarTower A (Localization.AtPrime p) (LocalizedModule.AtPrime q M) :=
    IsScalarTower.of_algebraMap_smul (R := A) (A := Localization.AtPrime p)
      (fun a x ↦ by
        change @SMul.smul (Localization.AtPrime q) (LocalizedModule.AtPrime q M)
          (LocalizedModule.moduleOfIsLocalization (S := q.primeCompl)).toSMul
          (Localization.localRingHom p q (algebraMap A B) hpq.symm
            (algebraMap A (Localization.AtPrime p) a)) x = _
        change Localization.localRingHom p q (algebraMap A B) hpq.symm
          (algebraMap A (Localization.AtPrime p) a) • x = _
        rw [Localization.localRingHom_to_map, algebraMap_smul, algebraMap_smul])
  letI := htower
  have hshrink := shrinkLocalizedModule _ _ hST hcof
    (LocalizedModule.mkLinearMap q.primeCompl M)
  haveI : IsLocalizedModule (Algebra.algebraMapSubmonoid B p.primeCompl)
      (LocalizedModule.mkLinearMap q.primeCompl M) := hshrink
  haveI := IsLocalizedModule.restrictScalars p.primeCompl
    (LocalizedModule.mkLinearMap q.primeCompl M)
  exact ((TensorProduct.comm A M (Localization.AtPrime p)).toAddEquiv.linearEquiv
    (Localization.AtPrime p)).trans
      (IsLocalizedModule.isBaseChange p.primeCompl (Localization.AtPrime p)
        ((LocalizedModule.mkLinearMap q.primeCompl M).restrictScalars A)).equiv

set_option backward.isDefEq.respectTransparency false in
private theorem uniquePrimeEquivOfCofinal_tmul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]
    (hpq : Ideal.comap (algebraMap A B) q = p)
    (hST : Submonoid.map (algebraMap A B) p.primeCompl ≤ q.primeCompl)
    (hcof : ∀ t : q.primeCompl, ∃ d : B,
      d * t ∈ Submonoid.map (algebraMap A B) p.primeCompl)
    (M : Type w) [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower A B M] (m : M) (a : A) (s : p.primeCompl) :
    uniquePrimeEquivOfCofinal p q hpq hST hcof M
      (m ⊗ₜ[A] IsLocalization.mk' (Localization.AtPrime p) a s) =
        LocalizedModule.mk (algebraMap A B a • m)
          (⟨algebraMap A B s, fun h ↦ s.property
            ((congrArg (fun I : Ideal A ↦ (s : A) ∈ I) hpq).mp h)⟩ : q.primeCompl) := by
  let : SMul (Localization.AtPrime q) (LocalizedModule.AtPrime q M) :=
    (LocalizedModule.moduleOfIsLocalization (S := q.primeCompl)).toSMul
  simp only [uniquePrimeEquivOfCofinal, LinearEquiv.trans_apply,
    AddEquiv.linearEquiv_apply, LinearEquiv.coe_toAddEquiv, AddEquiv.toFun_eq_coe]
  change Localization.localRingHom p q (algebraMap A B) hpq.symm
    (IsLocalization.mk' (Localization.AtPrime p) a s) •
      (LocalizedModule.mk m (1 : q.primeCompl)) = _
  rw [Localization.localRingHom_mk', LocalizedModule.mk'_smul_mk]
  simp only [mul_one]

/-- The finite-algebra unique-prime localization isomorphism and its natural module form.
Source: Stacks, Tag 00EA, case (1)+(2)(a), and Tag 00DK
(blueprint: lem-trf-unique-prime-localization).

Proof:
1. A finite algebra is integral (`lem-weil-pbc-finite-algebra-is-integral`). Going up
   (`pqf-lem-going-up`) takes every prime contracting inside `p` to a prime over `p`,
   which is `q` by uniqueness. Thus every such prime is contained in `q`.
2. The prime correspondence (`lem-weil-pbc-localization-prime-residue-field-iso`)
   shows that every prime of `S⁻¹B` lies in the extension of `q`. A nonunit outside
   this extension would belong to a maximal ideal by
   `lem-weil-pbc-proper-ideal-contained-in-maximal`, a contradiction.
3. Localizing this local ring again at that prime changes nothing. The canonical
   localization comparison in `lem-weil-pbc-localization-prime-residue-field-iso`
   therefore identifies `S⁻¹B` with `B_q`, by the displayed canonical map.
4. `lem-weil-pbc-localization-tensor-over-base`, tensor symmetry and the tensor unit
   identify `M ⊗[A] A_p` with `S⁻¹M`. Every element outside `q` acts invertibly there
   by step 3. Send `m/b` to `(b/1)⁻¹(m/1)` to invert `S⁻¹M → M_q`.
   The fraction relation makes this well-defined: a denominator outside `q` killing
   `b'm-bm'` acts invertibly. The resulting maps are mutually inverse.
5. These maps are `A_p`-linear; their composite has the displayed pure-tensor formula.
   Applying a `B`-linear map to numerators commutes with both maps, giving naturality. -/
theorem uniquePrimeLocalization
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]
    (hpq : Ideal.comap (algebraMap A B) q = p)
    (huniq : ∀ (q' : Ideal B), q'.IsPrime →
      Ideal.comap (algebraMap A B) q' = p → q' = q) :
    Function.Bijective (uniquePrimeLocalizationMap p q hpq) ∧
      ∃ e : ∀ (M : Type w) [AddCommGroup M] [Module B M] [Module A M]
          [IsScalarTower A B M], UniquePrimeModuleEquiv p q hpq M,
        (∀ (M : Type w) [AddCommGroup M] [Module B M] [Module A M]
            [IsScalarTower A B M] (m : M) (a : A) (s : p.primeCompl),
          e M (m ⊗ₜ[A] IsLocalization.mk' (Localization.AtPrime p) a s) =
            LocalizedModule.mk (algebraMap A B a • m)
              (⟨algebraMap A B s, fun h ↦ s.property
                ((congrArg (fun I : Ideal A ↦ (s : A) ∈ I) hpq).mp h)⟩ : q.primeCompl)) ∧
        (∀ (M N : Type w) [AddCommGroup M] [AddCommGroup N]
            [Module B M] [Module B N] [Module A M] [Module A N]
            [IsScalarTower A B M] [IsScalarTower A B N]
            (f : M →ₗ[B] N) (x : M ⊗[A] Localization.AtPrime p),
          e N ((f.restrictScalars A).rTensor (Localization.AtPrime p) x) =
            LocalizedModule.map q.primeCompl f (e M x)) := by
  classical
  let S := Submonoid.map (algebraMap A B) p.primeCompl
  have hST : S ≤ q.primeCompl := by
    rintro b ⟨a, ha, rfl⟩ hb
    exact ha ((congrArg (fun I : Ideal A ↦ a ∈ I) hpq).mp hb)
  have hcof := uniquePrimeDenominators p q hpq huniq
  have hloc : IsLocalization q.primeCompl (Localization S) :=
    IsLocalization.of_le S q.primeCompl hST (fun t ht ↦ by
      obtain ⟨d, hd⟩ := hcof ⟨t, ht⟩
      exact isUnit_of_dvd_unit (map_dvd (algebraMap B (Localization S))
        ⟨d, mul_comm _ _⟩) (IsLocalization.map_units (Localization S) ⟨d * t, hd⟩))
  have := hloc
  refine ⟨?_, ?_⟩
  · exact IsLocalization.bijective q.primeCompl
      (uniquePrimeLocalizationMap p q hpq).toRingHom
      (uniquePrimeLocalizationMap p q hpq).comp_algebraMap
  · refine ⟨fun M _ _ _ _ ↦ uniquePrimeEquivOfCofinal p q hpq hST hcof M, ?_, ?_⟩
    · intro M _ _ _ _ m a s
      exact uniquePrimeEquivOfCofinal_tmul p q hpq hST hcof M m a s
    · intro M N _ _ _ _ _ _ _ _ f x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul m r =>
        obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl r
        simp only [LinearMap.rTensor_tmul, LinearMap.restrictScalars_apply,
          uniquePrimeEquivOfCofinal_tmul, LocalizedModule.map_mk, map_smul]

end IsLocalization
