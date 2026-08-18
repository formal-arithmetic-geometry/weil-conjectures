/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Localization.Defs

/-!

# Power torsion: the algebraic layer of strict transforms

This file collects the power-torsion algebra needed for strict transforms of blow-ups,
following the blueprint chapter "Nagata compactification", Section "Power torsion and
strict-transform charts".

For a ring `R`, an `R`-module `M` and an element `a : R`, the `a`-power-torsion
submodule `Γ_(a)(M)` consists of the elements killed by some power of `a`. The strict
transform of a module (and, via coordinate rings, of a scheme) along the blow-up of a
center with local equation `a` is the quotient of the ordinary pullback by this
submodule.

## Main definitions and results

- `Submodule.powTorsion`: the `a`-power-torsion submodule
  (blueprint: `def:nagata-power-torsion`; being a submodule is
  `lemma:nagata-power-torsion-submodule`, discharged by the definition);
- `Submodule.mem_powTorsion_iff`: the simp-normal membership criterion
  (`lemma:nagata-mem-power-torsion`);
- `Submodule.powTorsion_eq_ker_localization`: `Γ_(a)(M)` is the kernel of the
  localization map `M → M_a` (`lemma:nagata-power-torsion-kernel-localization`);
- `Submodule.localized'_powTorsion`: localization maps power torsion onto the power
  torsion of the localized module (`lemma:nagata-power-torsion-localization` and
  `lemma:nagata-module-power-torsion-localization`, stated for an arbitrary
  localization);
- `Submodule.powTorsion_quotient_torsionfree` and
  `Submodule.powTorsion_quotient_smul_injective`: the power-torsion quotient has no
  exceptional torsion (`lemma:nagata-power-torsion-quotient-torsionfree`);
- `Submodule.powTorsionQuotientMap`: the functorial map induced on power-torsion
  quotients by a linear map;
- `Submodule.powTorsionQuotientMap_injective`,
  `Submodule.powTorsionQuotientMap_surjective`,
  `Submodule.powTorsionQuotientMap_exact`: a universally exact short exact sequence of
  modules induces a short exact sequence of power-torsion quotients. This is the
  affine-chart content of `lemma:nagata-module-strict-transform-exact`
  (Stacks Project Tag 080W); the only input beyond exactness is injectivity of
  `M₁/a^nM₁ → M₂/a^nM₂` for all `n`, phrased elementwise as the hypothesis `H`.

-/

@[expose] public section

namespace Submodule

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- The `a`-power-torsion submodule `Γ_(a)(M)` of an `R`-module `M`: the elements
killed by some power of `a`. Being a submodule is part of the definition.
(Blueprint: `def:nagata-power-torsion`, `lemma:nagata-power-torsion-submodule`.) -/
def powTorsion (a : R) : Submodule R M where
  carrier := {m | ∃ n : ℕ, a ^ n • m = 0}
  zero_mem' := ⟨0, smul_zero _⟩
  add_mem' := by
    rintro x y ⟨nx, hx⟩ ⟨ny, hy⟩
    have h1 : a ^ (nx + ny) • x = 0 := by rw [add_comm, pow_add, mul_smul, hx, smul_zero]
    have h2 : a ^ (nx + ny) • y = 0 := by rw [pow_add, mul_smul, hy, smul_zero]
    exact ⟨nx + ny, by rw [smul_add, h1, h2, add_zero]⟩
  smul_mem' := by
    rintro r x ⟨n, hn⟩
    exact ⟨n, by rw [smul_comm, hn, smul_zero]⟩

variable {R M} {a : R}

/-- Membership in the power-torsion submodule, in simp-normal form.
(Blueprint: `lemma:nagata-mem-power-torsion`.) -/
@[simp]
lemma mem_powTorsion_iff {m : M} : m ∈ powTorsion R M a ↔ ∃ n : ℕ, a ^ n • m = 0 :=
  Iff.rfl

section Localization

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- The power-torsion submodule is the kernel of the localization map `M → M_a`,
stated for an arbitrary realization `f : M →ₗ[R] N` of the localization of `M` away
from the powers of `a`.
(Blueprint: `lemma:nagata-power-torsion-kernel-localization`.) -/
theorem powTorsion_eq_ker_localization (f : M →ₗ[R] N)
    [IsLocalizedModule (Submonoid.powers a) f] :
    powTorsion R M a = LinearMap.ker f := by
  ext m
  rw [LinearMap.mem_ker, IsLocalizedModule.eq_zero_iff (Submonoid.powers a),
    mem_powTorsion_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨⟨a ^ n, n, rfl⟩, hn⟩
  · rintro ⟨⟨s, n, rfl⟩, hs⟩
    exact ⟨n, hs⟩

variable (S' : Type*) [CommRing S'] [Algebra R S'] (p : Submonoid R) [IsLocalization p S']
variable [Module S' N] [IsScalarTower R S' N]

/-- Localization of power torsion: for a localization `f : M →ₗ[R] N` at `p` over
`S' = R_p`, the localization of `Γ_(a)(M)` is the power torsion of `N` at the image of
`a`. Applied to `p = Submonoid.powers s` this is the statement that power torsion, and
hence its quotient, localizes.
(Blueprint: `lemma:nagata-power-torsion-localization`,
`lemma:nagata-module-power-torsion-localization`.) -/
theorem localized'_powTorsion (f : M →ₗ[R] N) [IsLocalizedModule p f] :
    (powTorsion R M a).localized' S' p f = powTorsion S' N (algebraMap R S' a) := by
  ext x
  rw [mem_localized', mem_powTorsion_iff]
  constructor
  · rintro ⟨m, hm, s, rfl⟩
    obtain ⟨n, hn⟩ := hm
    refine ⟨n, ?_⟩
    rw [← map_pow, algebraMap_smul, ← IsLocalizedModule.mk'_smul, hn,
      IsLocalizedModule.mk'_zero]
  · rintro ⟨n, hn⟩
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f x
    simp only [Function.uncurry_apply_pair] at hn ⊢
    rw [← map_pow, algebraMap_smul, ← IsLocalizedModule.mk'_smul,
      IsLocalizedModule.mk'_eq_zero'] at hn
    obtain ⟨t, ht⟩ := hn
    refine ⟨t • m, ⟨n, ?_⟩, t * s, IsLocalizedModule.mk'_cancel_left f m t s⟩
    rw [smul_comm, ht]

end Localization

section Quotient

variable (R M a)

/-- The power-torsion quotient has no exceptional torsion: no nonzero class of
`M ⧸ Γ_(a)(M)` is killed by a power of `a`.
(Blueprint: `lemma:nagata-power-torsion-quotient-torsionfree`.) -/
theorem powTorsion_quotient_torsionfree :
    powTorsion R (M ⧸ powTorsion R M a) a = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨n, hn⟩
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hn
  obtain ⟨k, hk⟩ := hn
  rw [mem_bot, Submodule.Quotient.mk_eq_zero]
  exact ⟨k + n, by rw [pow_add, mul_smul, hk]⟩

/-- Multiplication by `a` is injective on the power-torsion quotient.
(Blueprint: `lemma:nagata-power-torsion-quotient-torsionfree`.) -/
theorem powTorsion_quotient_smul_injective :
    Function.Injective fun x : M ⧸ powTorsion R M a ↦ a • x := by
  intro x y hxy
  rw [← sub_eq_zero, ← smul_sub] at hxy
  have : x - y ∈ powTorsion R (M ⧸ powTorsion R M a) a := ⟨1, by rwa [pow_one]⟩
  rw [powTorsion_quotient_torsionfree, mem_bot, sub_eq_zero] at this
  exact this

end Quotient

section Functoriality

variable {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup M₃] [Module R M₃]

variable (a) in
/-- A linear map sends power torsion to power torsion; this is the induced map on the
power-torsion quotients, the affine-chart form of the strict transform of a module map. -/
def powTorsionQuotientMap (f : M₁ →ₗ[R] M₂) :
    M₁ ⧸ powTorsion R M₁ a →ₗ[R] M₂ ⧸ powTorsion R M₂ a :=
  Submodule.mapQ _ _ f <| by
    rintro x ⟨n, hn⟩
    exact ⟨n, by rw [← map_smul, hn, map_zero]⟩

@[simp]
lemma powTorsionQuotientMap_mk (f : M₁ →ₗ[R] M₂) (x : M₁) :
    powTorsionQuotientMap a f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) :=
  Submodule.mapQ_apply _ _ _ _

/-- The power-torsion quotient of an injective map is injective. This is the
left-exactness part of `lemma:nagata-module-strict-transform-exact`. -/
theorem powTorsionQuotientMap_injective {f : M₁ →ₗ[R] M₂} (hf : Function.Injective f) :
    Function.Injective (powTorsionQuotientMap a f) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  rintro x hx
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.mem_ker, powTorsionQuotientMap_mk, Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨n, hn⟩ := hx
  rw [mem_bot, Submodule.Quotient.mk_eq_zero]
  refine ⟨n, hf ?_⟩
  rw [map_smul, hn, map_zero]

/-- The power-torsion quotient of a surjective map is surjective. This is the
right-exactness part of `lemma:nagata-module-strict-transform-exact`. -/
theorem powTorsionQuotientMap_surjective {g : M₂ →ₗ[R] M₃} (hg : Function.Surjective g) :
    Function.Surjective (powTorsionQuotientMap a g) := by
  rintro x
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := hg m
  exact ⟨Submodule.Quotient.mk y, powTorsionQuotientMap_mk _ _⟩

/-- Strict transform preserves universally exact sequences, affine-chart form
(Stacks Project Tag 080W): if `0 → M₁ → M₂ → M₃ → 0` is exact and remains exact after
base change to `R/a^n` — only injectivity of `M₁/a^nM₁ → M₂/a^nM₂` is used, phrased
elementwise as the hypothesis `H` — then the sequence of `a`-power-torsion quotients is
exact in the middle. Together with `Submodule.powTorsionQuotientMap_injective` and
`Submodule.powTorsionQuotientMap_surjective` this proves exactness of the transformed
short exact sequence.
(Blueprint: `lemma:nagata-module-strict-transform-exact`.) -/
theorem powTorsionQuotientMap_exact {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃}
    (hfg : Function.Exact f g)
    (H : ∀ (n : ℕ) (y : M₁), (∃ x, f y = a ^ n • x) → ∃ z, y = a ^ n • z) :
    Function.Exact (powTorsionQuotientMap a f) (powTorsionQuotientMap a g) := by
  rintro x
  constructor
  · intro hx
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [powTorsionQuotientMap_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨n, hn⟩ := hx
    rw [← map_smul] at hn
    obtain ⟨w, hw⟩ := (hfg (a ^ n • m)).mp hn
    obtain ⟨z, rfl⟩ := H n w ⟨m, hw⟩
    have heq : a ^ n • f z = a ^ n • m := by rw [← map_smul, hw]
    refine ⟨Submodule.Quotient.mk z, ?_⟩
    rw [powTorsionQuotientMap_mk, ← sub_eq_zero, ← Submodule.Quotient.mk_sub,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨n, by rw [smul_sub, heq, sub_self]⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [powTorsionQuotientMap_mk, powTorsionQuotientMap_mk, Submodule.Quotient.mk_eq_zero]
    exact ⟨0, by rw [pow_zero, one_smul, hfg.apply_apply_eq_zero]⟩

end Functoriality

end Submodule
