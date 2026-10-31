/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RepresentationTheory.Intertwining

/-! # A uniform denominator for localized intertwining maps

Source: Stanford Weil II seminar L19, Proposition 1.1.9, rational stage.
(blueprint: new-e7-localized-intertwining-lift).
-/

@[expose] public section
set_option autoImplicit false

namespace Representation

private theorem localized_kernel_killed
    {R : Type*} [CommRing R] (S : Submonoid R)
    {N N' : Type*} [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N'] [IsNoetherian R N]
    (g : N →ₗ[R] N') [IsLocalizedModule S g] :
    ∃ s : S, ∀ x : N, g x = 0 → (s : R) • x = 0 := by
  have hz : g.comp g.ker.subtype = g.comp (0 : g.ker →ₗ[R] N) := by
    ext x
    simp
  obtain ⟨s, hs⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
    S g g.ker.subtype 0 hz
  refine ⟨s, fun x hx ↦ ?_⟩
  simpa only [LinearMap.smul_apply, Submodule.subtype_apply,
    LinearMap.zero_apply, smul_zero, Submonoid.smul_def] using
      LinearMap.congr_fun hs ⟨x, hx⟩

/-- A single localization denominator makes a lifted linear map equivariant.
Source: Stanford Weil II seminar L19, Proposition 1.1.9, rational stage.
(blueprint: new-e7-localized-intertwining-lift).

Finite presentation lifts the localized map after multiplication by a denominator s.
Every commutator of this lift with a group element lies in the kernel of g, because
its localization is equivariant. This kernel is finite: it is a submodule of the
noetherian target N. Choose a single denominator t killing its finite generators.
Then t times the lifted map is equivariant for every group element, and its
localization equals ts times the original map. -/
theorem exists_localized_intertwining_lift
    {R : Type*} [CommRing R] (S : Submonoid R)
    {G : Type*} [Monoid G]
    {M N M' N' : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup M'] [Module R M']
    [AddCommGroup N'] [Module R N']
    [Module.FinitePresentation R M] [IsNoetherian R N]
    (f : M →ₗ[R] M') [IsLocalizedModule S f]
    (g : N →ₗ[R] N') [IsLocalizedModule S g]
    (ρ : Representation R G M) (σ : Representation R G N)
    (ρ' : Representation R G M') (σ' : Representation R G N')
    (hf : ∀ a x, f (ρ a x) = ρ' a (f x))
    (hg : ∀ a x, g (σ a x) = σ' a (g x))
    (ψ : ρ'.IntertwiningMap σ') :
    ∃ (s : S) (φ : ρ.IntertwiningMap σ),
      g.comp φ.toLinearMap = (s : R) • ψ.toLinearMap.comp f := by
  obtain ⟨φ, s, hφ⟩ :=
    Module.FinitePresentation.exists_lift_of_isLocalizedModule S g (ψ.toLinearMap.comp f)
  obtain ⟨t, ht⟩ := localized_kernel_killed S g
  have hφx (x : M) : g (φ x) = (s : R) • ψ (f x) :=
    LinearMap.congr_fun hφ x
  have he (a : G) (x : M) : g (φ (ρ a x) - σ a (φ x)) = 0 := by
    rw [map_sub, sub_eq_zero, hg]
    rw [hφx, hf, ψ.isIntertwining, hφx, map_smul]
  let Φ : ρ.IntertwiningMap σ :=
    { toLinearMap := (t : R) • φ
      isIntertwining' a := by
        ext x
        change (t : R) • φ (ρ a x) = σ a ((t : R) • φ x)
        rw [map_smul, ← sub_eq_zero, ← smul_sub]
        exact ht _ (he a x) }
  refine ⟨t * s, Φ, ?_⟩
  ext x
  change g ((t : R) • φ x) = ((t * s : S) : R) • ψ (f x)
  rw [map_smul, hφx, Submonoid.coe_mul, mul_smul]

end Representation
