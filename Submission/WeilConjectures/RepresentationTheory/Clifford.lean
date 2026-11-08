/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.SimpleModule.Isotypic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Geometric constituents after a finite-index extension

Let `ρ` be a finite-dimensional representation over an algebraically closed field `k` of a group
`W`, let `Π ⊴ W` be a normal subgroup and `F ∈ W`. In the application `W` is the Weil group of
a geometrically connected scheme `X₀` over a finite field, `Π = π₁(X̄)` is the geometric
fundamental group and `F` is a Frobenius lift, so that `Π` and `Fᵐ` generate the Weil group of
`X₀` after a constant extension of degree `m`.

After passing from `F` to a power `Fᵐ`, the representation has a finite filtration by subspaces
stable under `Π` and `Fᵐ` whose successive quotients are irreducible under `Π` alone. This is
Clifford theory: `Fᵐ` eventually fixes the `Π`-isotypic components of a quotient, and an
eigenvector of the operator induced by `Fᵐ` on the multiplicity space of an isotypic component
gives a `Π`-irreducible subspace stable under `Fᵐ`.

## Main statements

- `Representation.exists_filtration_isIrreducible_restrict`: blueprint
  `lem-zl-geometric-constituents-any-base`.
-/

@[expose] public section

section Twisted

/-! ### Operators twisting a module structure

Throughout, `Θ` is a `k`-linear operator on an `R`-module `M` which twists the `R`-action:
`Θ (a • m) = b • Θ m` for some `b` depending only on `a` (and conversely). -/

variable {k R M : Type*} [Field k] [Ring R] [AddCommGroup M] [Module R M] [Module k M]

/-- The image of an `R`-submodule under a `k`-linear map `Θ` such that every `a • Θ m` is of
the form `Θ (b • m)` for some `b` depending only on `a`. -/
def Submodule.twistedMap (Θ : M →ₗ[k] M) (h : ∀ a : R, ∃ b : R, ∀ m : M, Θ (b • m) = a • Θ m)
    (N : Submodule R M) : Submodule R M where
  carrier := Θ '' N
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, N.add_mem hx hy, map_add ..⟩
  zero_mem' := ⟨0, N.zero_mem, map_zero _⟩
  smul_mem' a := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨b, hb⟩ := h a
    exact ⟨b • x, N.smul_mem b hx, hb x⟩

theorem Submodule.mem_twistedMap {Θ : M →ₗ[k] M}
    {h : ∀ a : R, ∃ b : R, ∀ m : M, Θ (b • m) = a • Θ m} {N : Submodule R M} {x : M} :
    x ∈ N.twistedMap Θ h ↔ ∃ y ∈ N, Θ y = x :=
  Iff.rfl

/-- The preimage of an `R`-submodule under a `k`-linear map `Θ` such that every `Θ (a • m)` is
of the form `b • Θ m` for some `b` depending only on `a`. -/
def Submodule.twistedComap (Θ : M →ₗ[k] M) (h : ∀ a : R, ∃ b : R, ∀ m : M, Θ (a • m) = b • Θ m)
    (N : Submodule R M) : Submodule R M where
  carrier := Θ ⁻¹' N
  add_mem' {x y} hx hy := by
    simpa using N.add_mem hx hy
  zero_mem' := by simp
  smul_mem' a x hx := by
    obtain ⟨b, hb⟩ := h a
    simpa [hb] using N.smul_mem b hx

/-- Powers of an operator twisting the `R`-action again twist the `R`-action. -/
theorem Module.End.exists_pow_smul_eq (Θ : Module.End k M)
    (h : ∀ a : R, ∃ b : R, ∀ m : M, Θ (a • m) = b • Θ m) (n : ℕ) :
    ∀ a : R, ∃ b : R, ∀ m : M, (Θ ^ n) (a • m) = b • (Θ ^ n) m := by
  induction n with
  | zero => exact fun a ↦ ⟨a, fun m ↦ rfl⟩
  | succ n ih =>
    intro a
    obtain ⟨b, hb⟩ := ih a
    obtain ⟨c, hc⟩ := h b
    exact ⟨c, fun m ↦ by rw [pow_succ', Module.End.mul_apply, hb, hc, Module.End.mul_apply]⟩

/-- Powers of an operator twisting the `R`-action again twist the `R`-action. -/
theorem Module.End.exists_pow_smul_eq' (Θ : Module.End k M)
    (h : ∀ a : R, ∃ b : R, ∀ m : M, Θ (b • m) = a • Θ m) (n : ℕ) :
    ∀ a : R, ∃ b : R, ∀ m : M, (Θ ^ n) (b • m) = a • (Θ ^ n) m := by
  induction n with
  | zero => exact fun a ↦ ⟨a, fun m ↦ rfl⟩
  | succ n ih =>
    intro a
    obtain ⟨b, hb⟩ := ih a
    obtain ⟨c, hc⟩ := h b
    exact ⟨c, fun m ↦ by rw [pow_succ, Module.End.mul_apply, hc, hb, Module.End.mul_apply]⟩

/-- A bijective operator twisting the `R`-action maps simple submodules to simple submodules. -/
theorem Submodule.isSimpleModule_twistedMap {Θ : M →ₗ[k] M} (hΘ : Function.Bijective Θ)
    (h₁ : ∀ a : R, ∃ b : R, ∀ m : M, Θ (a • m) = b • Θ m)
    (h₂ : ∀ a : R, ∃ b : R, ∀ m : M, Θ (b • m) = a • Θ m) (N : Submodule R M)
    [IsSimpleModule R N] : IsSimpleModule R (N.twistedMap Θ h₂) := by
  rw [isSimpleModule_iff_isAtom] at *
  refine ⟨fun hbot ↦ ?_, fun U hU ↦ ?_⟩
  · obtain ⟨x, hx, hx0⟩ := N.exists_mem_ne_zero_of_ne_bot ‹IsAtom N›.1
    have : Θ x ∈ N.twistedMap Θ h₂ := ⟨x, hx, rfl⟩
    rw [hbot, Submodule.mem_bot, map_eq_zero_iff Θ hΘ.1] at this
    exact hx0 this
  · have hle : U.twistedComap Θ h₁ ≤ N := fun x hx ↦ by
      obtain ⟨y, hy, hxy⟩ := hU.le hx
      rwa [← hΘ.1 hxy]
    have hne : U.twistedComap Θ h₁ ≠ N := fun heq ↦ hU.not_ge fun x hx ↦ by
      obtain ⟨y, hy, rfl⟩ := hx
      rw [← heq] at hy
      exact hy
    have hbot := ‹IsAtom N›.2 _ (lt_of_le_of_ne hle hne)
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := hΘ.2 x
    have : y ∈ U.twistedComap Θ h₁ := hx
    rw [hbot, Submodule.mem_bot] at this
    simp [this]

variable [Algebra k R] [IsScalarTower k R M]

/-- Eigenvector step of Clifford theory: if an injective operator `Ψ` twisting the `R`-action
maps a simple submodule `S` onto a submodule isomorphic to `S`, then some simple submodule is
stable under `Ψ`. -/
theorem Submodule.exists_isSimpleModule_apply_mem [IsAlgClosed k] [FiniteDimensional k M]
    {Ψ : M →ₗ[k] M} (hΨ : Function.Injective Ψ)
    (h : ∀ a : R, ∃ b : R, ∀ m : M, Ψ (b • m) = a • Ψ m) (S : Submodule R M)
    [IsSimpleModule R S] (e : S ≃ₗ[R] S.twistedMap Ψ h) :
    ∃ C : Submodule R M, IsSimpleModule R C ∧ ∀ x ∈ C, Ψ x ∈ C := by
  have hex (s : S) : ∃ y ∈ S, Ψ y = e s := (e s).2
  choose ψ hψS hψ using hex
  have hadd (s t : S) : (⟨ψ (s + t), hψS _⟩ : S) = ⟨ψ s, hψS s⟩ + ⟨ψ t, hψS t⟩ :=
    Subtype.ext (hΨ (by simp [hψ]))
  have hsmul (a b : R) (hb : ∀ m : M, Ψ (b • m) = a • Ψ m) (s : S) :
      (⟨ψ (a • s), hψS _⟩ : S) = b • ⟨ψ s, hψS s⟩ :=
    Subtype.ext (hΨ (by simp [hψ, hb]))
  -- The operator `f ↦ Ψ ∘ f ∘ Ψ⁻¹ ∘ e` on `Hom_R(S, M)`.
  let 𝒯 : (S →ₗ[R] M) →ₗ[k] (S →ₗ[R] M) :=
    { toFun f :=
        { toFun s := Ψ (f ⟨ψ s, hψS s⟩)
          map_add' s t := by rw [hadd, map_add, map_add]
          map_smul' a s := by
            obtain ⟨b, hb⟩ := h a
            rw [hsmul a b hb, map_smul, hb, RingHom.id_apply] }
      map_add' f g := by
        ext s
        simp
      map_smul' c f := by
        ext s
        simp }
  have : FiniteDimensional k S :=
    Module.Finite.of_injective (S.subtype.restrictScalars k) Subtype.val_injective
  let ι : (S →ₗ[R] M) →ₗ[k] (S →ₗ[k] M) :=
    { toFun f := f.restrictScalars k
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have : FiniteDimensional k (S →ₗ[R] M) :=
    Module.Finite.of_injective ι (LinearMap.restrictScalars_injective k)
  have : Nontrivial (S →ₗ[R] M) := by
    have := IsSimpleModule.nontrivial R S
    refine nontrivial_of_ne S.subtype 0 fun h0 ↦ ?_
    obtain ⟨x, hx⟩ := exists_ne (0 : S)
    exact hx (Subtype.ext (LinearMap.congr_fun h0 x))
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue 𝒯
  obtain ⟨f, hf⟩ := hc.exists_hasEigenvector
  have hinj : Function.Injective f := f.injective_or_eq_zero.resolve_right hf.2
  refine ⟨LinearMap.range f, IsSimpleModule.congr (LinearEquiv.ofInjective f hinj).symm, ?_⟩
  rintro _ ⟨s', rfl⟩
  obtain ⟨s, hs⟩ := e.surjective ⟨Ψ s', s', s'.2, rfl⟩
  have hs' : (⟨ψ s, hψS s⟩ : S) = s' := Subtype.ext (hΨ (by rw [hψ, hs]))
  have h1 : Ψ (f ⟨ψ s, hψS s⟩) = c • f s := LinearMap.congr_fun hf.apply_eq_smul s
  rw [hs'] at h1
  rw [h1]
  exact (LinearMap.range f).smul_of_tower_mem c (LinearMap.mem_range_self f s)

/-- **Clifford theory, key step.** If a bijective `k`-linear operator `Θ` on a nonzero
finite-dimensional module twists the `R`-action in both directions, then some simple
submodule is stable under a positive power of `Θ`. -/
theorem Submodule.exists_isSimpleModule_pow_apply_mem [IsAlgClosed k] [FiniteDimensional k M]
    [Nontrivial M] {Θ : Module.End k M} (hΘ : Function.Bijective Θ)
    (h₁ : ∀ a : R, ∃ b : R, ∀ m : M, Θ (a • m) = b • Θ m)
    (h₂ : ∀ a : R, ∃ b : R, ∀ m : M, Θ (b • m) = a • Θ m) :
    ∃ j, 0 < j ∧ ∃ C : Submodule R M, IsSimpleModule R C ∧ ∀ x ∈ C, (Θ ^ j) x ∈ C := by
  have : IsArtinian R M := isArtinian_of_tower k inferInstance
  have : IsNoetherian R M := isNoetherian_of_tower k inferInstance
  obtain ⟨S, hS, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule R M)).resolve_left top_ne_bot
  have : IsSimpleModule R S := isSimpleModule_iff_isAtom.mpr hS
  have hbij (n : ℕ) : Function.Bijective ⇑(Θ ^ n) := by
    rw [Module.End.coe_pow]
    exact hΘ.iterate n
  let T (n : ℕ) := S.twistedMap (Θ ^ n) (Θ.exists_pow_smul_eq' h₂ n)
  have hT (n : ℕ) : IsSimpleModule R (T n) :=
    S.isSimpleModule_twistedMap (hbij n) (Θ.exists_pow_smul_eq h₁ n) _
  -- Pigeonhole: `Θ` permutes the finitely many isotypic components.
  let g (n : ℕ) : isotypicComponents R M := ⟨isotypicComponent R M (T n), T n, hT n, rfl⟩
  obtain ⟨a, b, hab, hg⟩ : ∃ a b, a < b ∧ g a = g b := by
    obtain ⟨a, b, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite g
    rcases hne.lt_or_gt with h' | h'
    · exact ⟨a, b, h', h⟩
    · exact ⟨b, a, h', h.symm⟩
  have hle : T b ≤ isotypicComponent R M (T a) := by
    have hg' : isotypicComponent R M (T a) = isotypicComponent R M (T b) :=
      congrArg Subtype.val hg
    rw [hg']
    exact (T b).le_isotypicComponent
  obtain ⟨e⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent R M (T a)) (T b) hle
  have hTb : T b = (T a).twistedMap (Θ ^ (b - a)) (Θ.exists_pow_smul_eq' h₂ _) := by
    ext x
    simp only [T, Submodule.mem_twistedMap]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(Θ ^ a) y, ⟨y, hy, rfl⟩, by rw [← Module.End.mul_apply, pow_sub_mul_pow Θ hab.le]⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, by rw [← Module.End.mul_apply, pow_sub_mul_pow Θ hab.le]⟩
  obtain ⟨C, hC, hCΘ⟩ := (T a).exists_isSimpleModule_apply_mem (hbij _).1 _
    (e.symm.trans (LinearEquiv.ofEq _ _ hTb))
  exact ⟨b - a, Nat.sub_pos_of_lt hab, C, hC, hCΘ⟩


end Twisted

namespace Representation

section Adjoin

variable {k W V : Type*} [Field k] [Group W] [AddCommGroup V] [Module k V]

/-- A subspace stable under `ρ g` for all `g ∈ P` is stable under every element of the
subalgebra generated by `ρ '' P`. -/
theorem le_comap_of_mem_adjoin_image (ρ : Representation k W V) (P : Subgroup W)
    {Q : Submodule k V} (hQ : ∀ g ∈ P, Q ≤ Q.comap (ρ g)) {a : Module.End k V}
    (ha : a ∈ Algebra.adjoin k (ρ '' P)) : Q ≤ Q.comap a := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact hQ g hg
  | algebraMap c =>
    intro x hx
    rw [Submodule.mem_comap, Module.algebraMap_end_apply]
    exact Q.smul_mem c hx
  | add x y _ _ hx hy => exact fun v hv ↦ Q.add_mem (hx hv) (hy hv)
  | mul x y _ _ hx hy => exact fun v hv ↦ hx (hy hv)


end Adjoin

variable {k W V : Type*} [Field k] [IsAlgClosed k] [Group W] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]


end Representation
