/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Flat.Stability
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.StdBasis

/-!
# Selecting generators as a basis of a localized direct summand

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07C6;
Algebra, Tags 00NX and 0GWM.
-/

@[expose] public section

universe u v

namespace Module

private theorem selected_basis_of_split
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    (n m : ℕ) (x : Fin m → M) (hx : Submodule.span A (Set.range x) = ⊤)
    (p : Ideal A) [p.IsPrime]
    (d : M →ₗ[A] (Fin n → A)) (l : (Fin n → A) →ₗ[A] M)
    (hld : l.comp d = LinearMap.id) :
    ∃ t : A, t ∉ p ∧ ∃ (V : Finset (Fin m)) (c : ℕ),
      V.card = c ∧ c ≤ min n m ∧
      ∃ e : Fin c ≃ V,
        ∃ bs : Module.Basis (Fin c) (Localization.Away t) (LocalizedModule.Away t M),
          ∀ j : Fin c, bs j =
            LocalizedModule.mkLinearMap (Submonoid.powers t) M (x (e j).1) := by
  classical
  have : Module.Finite A M := Module.Finite.of_fg_top
    (hx ▸ Submodule.fg_span (Set.finite_range x))
  have : Module.Projective A M := Module.Projective.of_split d l hld
  have : Module.FinitePresentation A M := Module.finitePresentation_of_projective A M
  let L := Localization.AtPrime p
  let N := LocalizedModule p.primeCompl M
  let loc : M →ₗ[A] N := LocalizedModule.mkLinearMap p.primeCompl M
  have hspan : Submodule.span L (Set.range (loc ∘ x)) = ⊤ := by
    rw [Set.range_comp]
    exact span_eq_top_of_isLocalizedModule L p.primeCompl loc hx
  obtain ⟨κ, a, bp, hbp⟩ := Module.exists_basis_of_span_of_flat (loc ∘ x) hspan
  have : Finite κ := Module.Finite.finite_basis bp
  let : Fintype κ := Fintype.ofFinite κ
  have ha : Function.Injective a := by
    intro i j h
    apply bp.injective
    rw [hbp, hbp, h]
  let c := Fintype.card κ
  let V : Finset (Fin m) := Finset.univ.image a
  let ek : Fin c ≃ κ := (Fintype.equivFin κ).symm
  let ea : κ ≃ V := Equiv.ofBijective
    (fun i ↦ ⟨a i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    ⟨fun i j h ↦ ha (congrArg Subtype.val h), by
      rintro ⟨j, hj⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
      exact ⟨i, rfl⟩⟩
  let e : Fin c ≃ V := ek.trans ea
  let bc : Module.Basis (Fin c) L N := bp.reindex ek.symm
  have hbc : ∀ j, bc j = loc (x (e j).1) := by
    intro j
    simp only [bc, Module.Basis.reindex_apply, Equiv.symm_symm, hbp]
    rfl
  have hcV : V.card = c := by
    simpa [V, c] using Finset.card_image_of_injective Finset.univ ha
  have hcm : c ≤ m := by
    simpa [c] using Fintype.card_le_of_injective a ha
  have hd : Function.Injective d := by
    intro z w h
    have hh := congrArg l h
    simpa only [← LinearMap.comp_apply, hld, LinearMap.id_apply] using hh
  have hcn : c ≤ n := by
    have hdim := LinearMap.finrank_le_finrank_of_injective
      (LocalizedModule.map_injective p.primeCompl d hd)
    let bq := (Pi.basisFun A (Fin n)).ofIsLocalizedModule L p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl (Fin n → A))
    change Module.finrank L N ≤
      Module.finrank L (LocalizedModule p.primeCompl (Fin n → A)) at hdim
    rw [Module.finrank_eq_card_basis bc, Module.finrank_eq_card_basis bq] at hdim
    simpa only [Fintype.card_fin] using hdim
  let y : Fin c → M := fun j ↦ x (e j).1
  let φ : (Fin c →₀ A) →ₗ[A] M := Finsupp.linearCombination A y
  let l₁ : (Fin c →₀ A) →ₗ[A] (Fin c →₀ L) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A L)
  let φp : (Fin c →₀ L) →ₗ[L] N :=
    IsLocalizedModule.mapExtendScalars p.primeCompl l₁ loc L φ
  have hφp : φp = bc.repr.symm.toLinearMap := by
    apply LinearMap.restrictScalars_injective A
    rw [show (φp.restrictScalars A) =
      IsLocalizedModule.map p.primeCompl l₁ loc φ from rfl]
    rw [IsLocalizedModule.map_linearCombination]
    ext j
    simp [y, ← hbc]
  have hbij : Function.Bijective φp := by
    rw [hφp]
    exact bc.repr.symm.bijective
  obtain ⟨t, ht, hφt⟩ := Module.FinitePresentation.exists_notMem_bijective φ p l₁ loc hbij
  let l₁t : (Fin c →₀ A) →ₗ[A] (Fin c →₀ Localization.Away t) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A (Localization.Away t))
  let loct : M →ₗ[A] LocalizedModule.Away t M :=
    LocalizedModule.mkLinearMap (Submonoid.powers t) M
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective l₁t loct] at hφt
  let φt : (Fin c →₀ Localization.Away t) →ₗ[Localization.Away t]
      LocalizedModule.Away t M :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers t) l₁t loct (Localization.Away t) φ
  let et := LinearEquiv.ofBijective φt hφt
  refine ⟨t, ht, V, c, hcV, le_min hcn hcm, e, Module.Basis.ofRepr et.symm, ?_⟩
  intro j
  change φt (Finsupp.single j 1) = loct (y j)
  change IsLocalizedModule.map (Submonoid.powers t) l₁t loct φ
    (Finsupp.single j 1) = loct (y j)
  rw [IsLocalizedModule.map_linearCombination]
  simp

/-- A finite spanning family of a module which is a direct summand of `A_b^n` contains
 a basis after a further principal localization near a specified prime.
Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07C6 (selection and shrinking);
Algebra, Tags 00NX and 0GWM.
(blueprint: lem-weil-pbc-selected-basis-of-localized-split)

Proof: The split injection exhibits `M_b` as a direct summand of the finite free
module `A_b^n`, so it is finite projective, hence finitely presented (00NX). The prime
`p`, which avoids `b`, extends to a prime of `A_b`. Localizing the split injection
at this prime makes `M_p` a finite projective module over the local ring `A_p`,
hence free. The given generators span its residue vector space. Select a subset
which is a residue basis and enumerate it by `Fin c`. Its cardinality is at most
`m`, and the split injection after residue base change makes it at most `n`.
Nakayama makes these prescribed lifts generate `M_p`. A surjective map between
finite free modules of the same rank is bijective, so these lifts are a basis
at `p`. Finite presentation of `M_b` spreads this isomorphism to a principal
neighbourhood of the extended prime (0GWM, in its prescribed-lifts form).
Write its localization element as `t / b^k`. Since it avoids the extended prime,
`t` avoids `p`. The iterated localization is the localization at `b * t`;
transport the basis along the localization equivalences. They send each original
`x i` divided by one to itself divided by one, giving the displayed basis values.
No global finite presentation of `M` is required. -/
theorem exists_selected_basis_away_mul_of_split
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    (n m : ℕ) (x : Fin m → M) (hx : Submodule.span A (Set.range x) = ⊤)
    (p : Ideal A) [p.IsPrime] (b : A) (hb : b ∉ p)
    (d : LocalizedModule.Away b M →ₗ[Localization.Away b] (Fin n → Localization.Away b))
    (l : (Fin n → Localization.Away b) →ₗ[Localization.Away b] LocalizedModule.Away b M)
    (hld : l.comp d = LinearMap.id) :
    ∃ t : A, t ∉ p ∧ ∃ (V : Finset (Fin m)) (c : ℕ),
      V.card = c ∧ c ≤ min n m ∧
      ∃ e : Fin c ≃ V,
        ∃ bs : Module.Basis (Fin c) (Localization.Away (b * t))
            (LocalizedModule.Away (b * t) M),
          ∀ j : Fin c, bs j =
            LocalizedModule.mkLinearMap (Submonoid.powers (b * t)) M (x (e j).1) := by
  sorry

end Module
