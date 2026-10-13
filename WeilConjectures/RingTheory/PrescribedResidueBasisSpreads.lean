/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.LocalRing.Module

/-!
# Spreading a prescribed residue basis

Source: Stacks Project, Algebra, proof of Tag 0GWM, with prescribed lifts;
Tags 00DV (8) and 05G8 establish the local isomorphism
(blueprint: lem-weil-pbc-prescribed-residue-basis-spreads).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Module.FinitePresentation

/-- A prescribed residue basis spreads when the prime localization is free of the same rank.
Source: Stacks Project, Algebra, proof of Tag 0GWM, adapted to prescribed lifts
(blueprint: lem-weil-pbc-prescribed-residue-basis-spreads).

Proof: (1) Define the map from `A^r` to `M` sending the standard vectors to `m i`.
Its localization has image the span of `m i / 1`
[def-weil-finitely-generated-module, def-weil-pbc-module-localization,
def-weil-pbc-free-module]. (2) Identify the residue base change with that of the localized
module [lem-weil-pbc-localization-tensor-product, def-weil-pbc-localization-at-prime,
def-weil-module-base-change]. Nakayama (Tag 00DV (8)) makes the localized map surjective
[lem-weil-pbc-nakayama-local-generators]. (3) A basis of the prime localization identifies
this map with a surjective endomorphism of a finite free module, hence an isomorphism by
Tag 05G8 [def-weil-pbc-free-module,
lem-weil-pbc-finite-module-surjective-endomorphism-bijective]. (4) Spread this isomorphism
to some `f` outside `p` using finite presentation of `M` and finiteness of `A^r`
[lem-weil-pbc-finite-to-finitely-presented-map-iso-at-prime-spreads]. (5) Identify the
localization of `A^r` at `f` with `A_f^r`; the resulting isomorphism sends each standard
vector to `m i / 1`, giving exactly the required basis
[def-weil-pbc-module-localization-away, def-weil-pbc-free-module]. -/
theorem exists_basis_away_of_prescribed_residue_basis
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    [Module.FinitePresentation A M] (p : Ideal A) [p.IsPrime] (r : ℕ) (m : Fin r → M)
    (hres : ∃ b : Module.Basis (Fin r) p.ResidueField (p.ResidueField ⊗[A] M),
      ∀ i : Fin r, b i = (1 : p.ResidueField) ⊗ₜ[A] m i)
    (hfree : Nonempty (Module.Basis (Fin r) (Localization.AtPrime p)
      (LocalizedModule p.primeCompl M))) :
    ∃ f : A, f ∉ p ∧
      ∃ b : Module.Basis (Fin r) (Localization.Away f) (LocalizedModule.Away f M),
        ∀ i : Fin r, b i = LocalizedModule.mkLinearMap (Submonoid.powers f) M (m i) := by
  classical
  let L := Localization.AtPrime p
  let N := LocalizedModule p.primeCompl M
  let K := p.ResidueField
  let loc : M →ₗ[A] N := LocalizedModule.mkLinearMap p.primeCompl M
  obtain ⟨bres, hbres⟩ := hres
  obtain ⟨bfree⟩ := hfree
  -- Identify the residue base change of the prime localization.
  let eK : (K ⊗[L] N) ≃ₗ[K] (K ⊗[A] M) :=
    (LinearEquiv.baseChange L K _ _
      (LocalizedModule.equivTensorProduct p.primeCompl M)).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A L K K M)
  let bk := bres.map eK.symm
  have hbk : ∀ i, (1 : K) ⊗ₜ[L] loc (m i) = bk i := by
    intro i
    apply eK.injective
    change eK ((1 : K) ⊗ₜ[L] loc (m i)) = eK (eK.symm (bres i))
    rw [eK.apply_symm_apply, hbres]
    simp only [eK, LinearEquiv.trans_apply]
    rw [LinearEquiv.baseChange_tmul]
    dsimp only [loc]
    rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.equivTensorProduct_apply_mk,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    simp only [Localization.mk_one, one_smul]
  -- Nakayama makes the localized prescribed family generate.
  have : Module.Finite L N := Module.Finite.of_basis bfree
  have hspan : Submodule.span L (Set.range (loc ∘ m)) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis (loc ∘ m) bk hbk
  let φ : (Fin r →₀ A) →ₗ[A] M := Finsupp.linearCombination A m
  let l₁ : (Fin r →₀ A) →ₗ[A] (Fin r →₀ L) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A L)
  let φp : (Fin r →₀ L) →ₗ[L] N :=
    IsLocalizedModule.mapExtendScalars p.primeCompl l₁ loc L φ
  have hφp : φp = Finsupp.linearCombination L (loc ∘ m) :=
    LinearMap.restrictScalars_injective A
      (IsLocalizedModule.map_linearCombination p.primeCompl L loc)
  have hsurj : Function.Surjective φp := by
    rw [hφp, ← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact hspan
  -- Equal ranks turn this surjection into an endomorphism of a finite free module.
  have hendo : Function.Bijective (bfree.repr.toLinearMap.comp φp) :=
    OrzechProperty.bijective_of_surjective_endomorphism _
      (bfree.repr.surjective.comp hsurj)
  have hbij : Function.Bijective φp :=
    ⟨fun x y h ↦ hendo.injective (congrArg bfree.repr h), hsurj⟩
  -- Spread the isomorphism defined by the original global elements.
  obtain ⟨f, hf, hφf⟩ := Module.FinitePresentation.exists_notMem_bijective φ p l₁ loc hbij
  let l₁f : (Fin r →₀ A) →ₗ[A] (Fin r →₀ Localization.Away f) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A (Localization.Away f))
  let locf : M →ₗ[A] LocalizedModule.Away f M :=
    LocalizedModule.mkLinearMap (Submonoid.powers f) M
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective l₁f locf] at hφf
  let φf : (Fin r →₀ Localization.Away f) →ₗ[Localization.Away f]
      LocalizedModule.Away f M :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers f) l₁f locf
      (Localization.Away f) φ
  -- Its images of the standard vectors are exactly the prescribed lifts.
  let ef := LinearEquiv.ofBijective φf hφf
  refine ⟨f, hf, Module.Basis.ofRepr ef.symm, ?_⟩
  intro i
  change φf (Finsupp.single i 1) = locf (m i)
  have heq := IsLocalizedModule.map_linearCombination (Submonoid.powers f)
    (Localization.Away f) locf (v := m)
  change IsLocalizedModule.map (Submonoid.powers f) l₁f locf φ
    (Finsupp.single i 1) = locf (m i)
  rw [heq]
  simp

end Module.FinitePresentation
