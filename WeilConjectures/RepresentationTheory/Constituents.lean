/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import WeilConjectures.RepresentationTheory.CompositionSeries

/-!
# Comparing the constituents of representations

A *constituent* of a representation `ρ` is an irreducible subquotient `S / U`. The relation
`Representation.ConstituentsLE ρ σ` says that every constituent of `ρ` is equivalent to a
constituent of `σ`. This file proves the standard closure properties of this relation: it passes
along injective and surjective intertwining maps, the constituents of the middle term of a short
exact sequence are constituents of its ends, those of a representation with a finite filtration
are constituents of its graded pieces, and it is compatible with tensor products.

## Main definitions

- `Subrepresentation.quotient`: the quotient representation `V ⧸ U`.
- `Representation.ConstituentsLE`: every constituent of `ρ` is a constituent of `σ`.

## Main results

- `Representation.ConstituentsLE.of_exact`: constituents of the middle of a short exact sequence.
- `Representation.ConstituentsLE.of_chain`: constituents of a representation with a finite
  filtration are constituents of the graded pieces.
- `Representation.ConstituentsLE.tprod`: `ρ ≤ ρ'` implies `ρ ⊗ σ ≤ ρ' ⊗ σ`.

## Blueprint

- `lem-mg-filtration-refinement`, `lem-mg-filtered-tensor-product`: the constituents of a filtered
  representation and of a tensor product.
-/

@[expose] public section

open TensorProduct

namespace Subrepresentation

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]
  {ρ : Representation k W V}

/-- The quotient representation `V ⧸ U` of a representation by a subrepresentation. -/
noncomputable abbrev quotient (U : Subrepresentation ρ) : Representation k W (V ⧸ U.toSubmodule) :=
  ρ.quotient U.toSubmodule fun g _ hx ↦ U.apply_mem_toSubmodule g hx

/-- The quotient map `V → V ⧸ U` as an intertwining map. -/
noncomputable def mkQ (U : Subrepresentation ρ) : ρ.IntertwiningMap U.quotient :=
  ⟨U.toSubmodule.mkQ, fun _ ↦ rfl⟩

theorem mkQ_surjective (U : Subrepresentation ρ) : Function.Surjective U.mkQ :=
  U.toSubmodule.mkQ_surjective

/-- The inclusion `U → V` as an intertwining map. -/
noncomputable def subtype (U : Subrepresentation ρ) : U.toRepresentation.IntertwiningMap ρ :=
  ⟨U.toSubmodule.subtype, fun _ ↦ rfl⟩

theorem subtype_injective (U : Subrepresentation ρ) : Function.Injective U.subtype :=
  U.toSubmodule.injective_subtype

theorem exact_subtype_mkQ (U : Subrepresentation ρ) : Function.Exact U.subtype U.mkQ := fun y ↦ by
  change U.toSubmodule.mkQ y = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨fun hy ↦ ⟨⟨y, hy⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩

end Subrepresentation

namespace Representation

variable {k : Type*} [Field k] {W : Type*} [Group W]
  {V V' V'' : Type*} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
  [AddCommGroup V''] [Module k V'']

/-- Every constituent (irreducible subquotient) of `ρ` is equivalent to a constituent of `σ`.
(blueprint: `lem-mg-filtration-refinement`) -/
def ConstituentsLE (ρ : Representation k W V) (σ : Representation k W V') : Prop :=
  ∀ U S : Subrepresentation ρ, (S.subquotient U).IsIrreducible →
    ∃ U' S' : Subrepresentation σ, (S'.subquotient U').IsIrreducible ∧
      Nonempty ((S.subquotient U).Equiv (S'.subquotient U'))

namespace ConstituentsLE

variable {ρ : Representation k W V} {σ : Representation k W V'} {τ : Representation k W V''}

theorem refl (ρ : Representation k W V) : ConstituentsLE ρ ρ := fun U S h ↦
  ⟨U, S, h, ⟨Equiv.refl _⟩⟩

theorem trans (h₁ : ConstituentsLE ρ σ) (h₂ : ConstituentsLE σ τ) : ConstituentsLE ρ τ :=
  fun U S h ↦ by
    obtain ⟨U', S', h', ⟨e⟩⟩ := h₁ U S h
    obtain ⟨U'', S'', h'', ⟨e'⟩⟩ := h₂ U' S' h'
    exact ⟨U'', S'', h'', ⟨e.trans e'⟩⟩

/-- The constituents of `ρ` are constituents of `σ` if `ρ` embeds into `σ`. -/
theorem of_injective (f : ρ.IntertwiningMap σ) (hf : Function.Injective f) :
    ConstituentsLE ρ σ := fun U S h ↦ by
  let e := Subrepresentation.subquotientEquivOfIntertwiningMap f (U := U) (S := S)
    (U' := Subrepresentation.map f U) (S' := Subrepresentation.map f S)
    (fun x hx ↦ ⟨x, hx, rfl⟩) (fun x _ hx ↦ ⟨x, hx, rfl⟩)
    (fun x _ hx ↦ by
      obtain ⟨y, hy, hyx⟩ := Subrepresentation.mem_map.1 hx
      exact hf hyx ▸ hy)
    fun y hy ↦ by
      obtain ⟨x, hx, rfl⟩ := Subrepresentation.mem_map.1 hy
      exact ⟨x, hx, by rw [sub_self]; exact Submodule.zero_mem _⟩
  exact ⟨_, _, e.isIrreducible_iff.1 h, ⟨e⟩⟩

/-- The constituents of `σ` are constituents of `ρ` if `σ` is a quotient of `ρ`. -/
theorem of_surjective (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) :
    ConstituentsLE σ ρ := fun U S h ↦ by
  let e := Subrepresentation.subquotientComapEquiv f hf U S
  exact ⟨_, _, e.isIrreducible_iff.2 h, ⟨e.symm⟩⟩

theorem of_equiv (e : ρ.Equiv σ) : ConstituentsLE ρ σ :=
  of_injective e.toIntertwiningMap e.injective

/-- **Constituents of a short exact sequence.** If `σ₁ → ρ → σ₂` is exact with `ρ → σ₂`
surjective, every constituent of `ρ` is a constituent of `σ₁` or of `σ₂`. -/
theorem of_exact {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
    {σ₁ : Representation k W V₁} {σ₂ : Representation k W V₂} (f : σ₁.IntertwiningMap ρ)
    (g : ρ.IntertwiningMap σ₂) (hexact : Function.Exact f g) (hg : Function.Surjective g)
    (h₁ : ConstituentsLE σ₁ τ) (h₂ : ConstituentsLE σ₂ τ) : ConstituentsLE ρ τ := by
  intro U S hirr
  by_cases h : f.range ⊓ S ≤ U
  · -- the constituent survives in `σ₂`
    have hinj (x) (hxS : x ∈ S) (hx : g x ∈ Subrepresentation.map g (U ⊓ S)) : x ∈ U := by
      obtain ⟨u, hu, hux⟩ := Subrepresentation.mem_map.1 hx
      have hxu : x - u ∈ f.range := (hexact (x - u)).1 (by rw [map_sub, hux, sub_self])
      have := h (Subrepresentation.mem_inf.2
        ⟨hxu, S.toSubmodule.sub_mem hxS (Subrepresentation.mem_inf.1 hu).2⟩)
      have hx := U.toSubmodule.add_mem this (Subrepresentation.mem_inf.1 hu).1
      rwa [sub_add_cancel] at hx
    let e := (Subrepresentation.subquotientEquivOfIntertwiningMap g
      (U' := Subrepresentation.map g (U ⊓ S)) (S' := Subrepresentation.map g S)
      (fun x hx ↦ Subrepresentation.mem_map.2 ⟨x, hx, rfl⟩)
      (fun x hxS hxU ↦ Subrepresentation.mem_map.2 ⟨x, Subrepresentation.mem_inf.2 ⟨hxU, hxS⟩,
        rfl⟩) hinj
      fun y hy ↦ by
        obtain ⟨x, hx, rfl⟩ := Subrepresentation.mem_map.1 hy
        exact ⟨x, hx, by rw [sub_self]; exact Submodule.zero_mem _⟩)
    obtain ⟨U', S', h', ⟨e'⟩⟩ := h₂ _ _ (e.isIrreducible_iff.1 hirr)
    exact ⟨U', S', h', ⟨e.trans e'⟩⟩
  · -- the constituent comes from `σ₁`
    let e := Subrepresentation.subquotientEquivOfIntertwiningMap f
      (U := Subrepresentation.comap f U) (S := Subrepresentation.comap f S)
      (U' := U) (S' := S) (fun _ hx ↦ hx) (fun _ _ hx ↦ hx) (fun _ _ hx ↦ hx) fun y hy ↦ by
        obtain ⟨x, hx, hxy⟩ := Subrepresentation.exists_mem_inf_sub_mem_of_isIrreducible hirr h hy
        obtain ⟨⟨x', rfl⟩, hxS⟩ := Subrepresentation.mem_inf.1 hx
        exact ⟨x', hxS, hxy⟩
    obtain ⟨U', S', h', ⟨e'⟩⟩ := h₁ _ _ (e.isIrreducible_iff.2 hirr)
    exact ⟨U', S', h', ⟨e.symm.trans e'⟩⟩

/-- The constituents of `ρ` are constituents of a subrepresentation `U` or of the quotient
`V ⧸ U`. -/
theorem of_subrepresentation (U : Subrepresentation ρ) (h₁ : ConstituentsLE U.toRepresentation τ)
    (h₂ : ConstituentsLE U.quotient τ) : ConstituentsLE ρ τ :=
  of_exact U.subtype U.mkQ U.exact_subtype_mkQ U.mkQ_surjective h₁ h₂

/-- The zero representation has no constituents. -/
theorem of_subsingleton [Subsingleton V] (ρ : Representation k W V) (σ : Representation k W V') :
    ConstituentsLE ρ σ := fun U S hirr ↦ by
  have := hirr.nontrivial
  obtain ⟨q₁, q₂, hq⟩ := exists_pair_ne (S.toSubmodule ⧸ U.toSubmodule.comap S.toSubmodule.subtype)
  induction q₁ using Submodule.Quotient.induction_on with | _ x
  induction q₂ using Submodule.Quotient.induction_on with | _ y
  exact (hq (congrArg _ (Subtype.ext (Subsingleton.elim (x : V) y)))).elim

/-- **Constituents of a filtered representation.** If `0 = F_m ≤ ⋯ ≤ F_1 ≤ F_0 = V` is a finite
decreasing filtration by subrepresentations, every constituent of `ρ` is a constituent of one of
the graded pieces `F_j ⧸ F_{j+1}`. (blueprint: `lem-mg-filtration-refinement`) -/
theorem of_chain (F : ℕ → Subrepresentation ρ) (hF : ∀ j, F (j + 1) ≤ F j) (h0 : F 0 = ⊤)
    {m : ℕ} (hm : F m = ⊥) (h : ∀ j < m, ConstituentsLE ((F j).subquotient (F (j + 1))) τ) :
    ConstituentsLE ρ τ := by
  -- the constituents of the subrepresentation `F j`, by downward induction on `j`
  have key (i : ℕ) (hi : i ≤ m) : ConstituentsLE (F (m - i)).toRepresentation τ := by
    induction i with
    | zero =>
      rw [Nat.sub_zero, hm]
      have : Subsingleton (⊥ : Subrepresentation ρ).toSubmodule :=
        Submodule.subsingleton_iff_eq_bot.2 rfl
      exact of_subsingleton _ τ
    | succ i ih =>
      set j := m - (i + 1)
      have hj : m - i = j + 1 := by omega
      have ih := ih (by omega)
      rw [hj] at ih
      -- the inclusion `F (j + 1) → F j` and the quotient `F j → F j / F (j + 1)`
      let incl : (F (j + 1)).toRepresentation.IntertwiningMap (F j).toRepresentation :=
        ⟨Submodule.inclusion (hF j), fun _ ↦ rfl⟩
      let quot : (F j).toRepresentation.IntertwiningMap ((F j).subquotient (F (j + 1))) :=
        ⟨Submodule.mkQ _, fun _ ↦ rfl⟩
      refine of_exact incl quot (fun y ↦ ?_) (Submodule.mkQ_surjective _) ih (h j (by omega))
      change Submodule.mkQ _ y = 0 ↔ _
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨fun hy ↦ ⟨⟨y, hy⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩
  have h := key m le_rfl
  rw [Nat.sub_self, h0] at h
  exact (of_equiv ((Subrepresentation.topSubquotientBotEquiv ρ).symm.trans
    (Subrepresentation.subquotientBotEquiv ⊤))).trans h

/-- An equivalence `ρ ≅ ρ'` induces `ρ ⊗ σ ≅ ρ' ⊗ σ`. -/
noncomputable def _root_.Representation.Equiv.rTensor {V₁ : Type*} [AddCommGroup V₁] [Module k V₁]
    {ρ₁ : Representation k W V₁} (e : ρ.Equiv ρ₁) (σ : Representation k W V'') :
    (ρ.tprod σ).Equiv (ρ₁.tprod σ) :=
  Equiv.mk (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl k V'')) fun w ↦ by
    refine TensorProduct.ext' fun x y ↦ ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, tprod_apply,
      TensorProduct.map_tmul, TensorProduct.congr_tmul, LinearEquiv.refl_apply]
    congr 1
    exact e.apply_apply w x

/-- **Constituents of a tensor product.** If every constituent of `ρ` is a constituent of `ρ'`,
then every constituent of `ρ ⊗ σ` is a constituent of `ρ' ⊗ σ`: a constituent of `ρ ⊗ σ` is a
subquotient of `A ⊗ σ` for a constituent `A` of `ρ`, and `A' ⊗ σ` is a subquotient of `ρ' ⊗ σ`
for a constituent `A'` of `ρ'`. (blueprint: `lem-mg-filtered-tensor-product`) -/
theorem tprod_left [FiniteDimensional k V] (h : ConstituentsLE ρ σ) (τ : Representation k W V'') :
    ConstituentsLE (ρ.tprod τ) (σ.tprod τ) := by
  intro U S hirr
  obtain ⟨UV, SV, -, hV, U₁, S₁, ⟨e₁⟩⟩ := Subrepresentation.exists_subquotient_tprod_left_equiv hirr
  obtain ⟨U₂, S₂, -, ⟨e₂⟩⟩ := h UV SV hV
  -- `A' ⊗ τ` is a subquotient of `σ ⊗ τ`, for the constituent `A' = S₂ / U₂` of `σ`
  let q : S₂.toRepresentation.IntertwiningMap (S₂.subquotient U₂) := ⟨Submodule.mkQ _, fun _ ↦ rfl⟩
  have hq : Function.Surjective (q.rTensor τ) :=
    LinearMap.rTensor_surjective V'' (Submodule.mkQ_surjective _)
  have hi : Function.Injective ((Subrepresentation.subtype S₂).rTensor τ) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (Subrepresentation.subtype_injective S₂)
  have hA : ConstituentsLE ((S₂.subquotient U₂).tprod τ) (σ.tprod τ) :=
    (of_surjective _ hq).trans (of_injective _ hi)
  have hB : ConstituentsLE (((SV.subquotient UV)).tprod τ) (σ.tprod τ) :=
    (of_equiv (e₂.rTensor τ)).trans hA
  obtain ⟨U₃, S₃, h₃, ⟨e₃⟩⟩ := hB U₁ S₁ (e₁.isIrreducible_iff.2 hirr)
  exact ⟨U₃, S₃, h₃, ⟨e₁.symm.trans e₃⟩⟩

/-- The symmetric version of `tprod_left`. -/
theorem tprod_right [FiniteDimensional k V] (h : ConstituentsLE ρ σ) (τ : Representation k W V'') :
    ConstituentsLE (τ.tprod ρ) (τ.tprod σ) :=
  ((of_equiv (Representation.TensorProduct.comm τ ρ)).trans (h.tprod_left τ)).trans
    (of_equiv (Representation.TensorProduct.comm σ τ))

end ConstituentsLE

end Representation
