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
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso

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
  sorry

end IsLocalization
