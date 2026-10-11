/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.SeparableClosure

/-!
# A separable closure is the union of its finite separable subextensions

A separable closure of a field `k` is Mathlib's `IsSepClosure k ks`. Here we record that `ks` is
the directed union of its finite separable subextensions, so that `ks` is their filtered colimit.

## Main statements

- `IsSepClosure.exists_intermediateField_mem`: every element of a separable closure lies in a
  finite separable subextension (blueprint `def-pd-separable-closure`).
- `IsSepClosed.instInfinite`: a separably closed field is infinite.
-/

@[expose] public section

universe u v

open IntermediateField

/-- **A separable closure is the union of its finite separable subextensions.** Let `ks` be a
separable closure of `k`. Every `x ∈ ks` lies in a subextension `K` of `ks/k` that is finite and
separable over `k`, namely `k⟮x⟯`; hence `ks = colim K` over the finite separable subextensions.

The separable closure itself is Mathlib's `IsSepClosure`.

(blueprint: `def-pd-separable-closure`) -/
theorem IsSepClosure.exists_intermediateField_mem (k : Type u) {ks : Type v} [Field k] [Field ks]
    [Algebra k ks] [IsSepClosure k ks] (x : ks) :
    ∃ K : IntermediateField k ks, FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧ x ∈ K := by
  have := IsSepClosure.separable (k := k) (K := ks)
  have hx : IsSeparable k x := Algebra.IsSeparable.isSeparable k x
  exact ⟨k⟮x⟯, adjoin.finiteDimensional hx.isIntegral,
    (isSeparable_adjoin_simple_iff_isSeparable k ks).mpr hx, mem_adjoin_simple_self k x⟩

/-- A separably closed field is infinite: over a finite field `k` with `q` elements the
polynomial `X ^ q - X - 1` is separable (its derivative is `-1`) but has no root, since
`a ^ q = a` for every `a ∈ k`. -/
instance (priority := 100) IsSepClosed.instInfinite (k : Type u) [Field k] [IsSepClosed k] :
    Infinite k := by
  refine Infinite.of_not_fintype fun _ ↦ ?_
  obtain ⟨a, ha⟩ := IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C (1 : k) (-1) (-1)
    (FiniteField.cast_card_eq_zero k) (Fintype.one_lt_card (α := k)) (by simp)
  simp [FiniteField.pow_card] at ha

/-! ### Ported from the `proetale` package (`Proetale.Mathlib.FieldTheory.IsSepClosed`) -/

/-- `IsSepClosed` transfers along a ring isomorphism of fields. -/
theorem IsSepClosed.of_ringEquiv {k k' : Type*} [Field k] [Field k']
    (e : k ≃+* k') [IsSepClosed k] : IsSepClosed k' := by
  refine ⟨fun p hp => ?_⟩
  have hsplit : (p.map e.symm.toRingHom).Splits :=
    IsSepClosed.splits_of_separable _ hp.map
  have hpush := hsplit.map e.toRingHom
  rwa [Polynomial.map_map, e.toRingHom_comp_symm_toRingHom, Polynomial.map_id] at hpush

/-- **Separable elements land in a separably closed subfield.** Let `K / k` be a separable
extension, `γ : k →+* Ω₁` an embedding into a separably closed field and `φ : Ω₁ →+* Ω₂`.
Every embedding `χ : K →+* Ω₂` extending `φ ∘ γ` factors through `φ`: each `χ a` is a root of
the separable polynomial `(minpoly k a).map γ`, which splits in `Ω₁`. -/
theorem IsSepClosed.exists_comp_eq {k K Ω₁ Ω₂ : Type*} [Field k] [Field K] [Field Ω₁]
    [Field Ω₂] [Algebra k K] [Algebra.IsSeparable k K] [IsSepClosed Ω₁] (γ : k →+* Ω₁)
    (φ : Ω₁ →+* Ω₂) (χ : K →+* Ω₂) (h : χ.comp (algebraMap k K) = φ.comp γ) :
    ∃ ψ : K →+* Ω₁, φ.comp ψ = χ := by
  have hrange (a : K) : χ a ∈ φ.range := by
    have hsep := Algebra.IsSeparable.isSeparable k a
    have hsplit := IsSepClosed.splits_codomain (f := γ) _ hsep
    refine hsplit.mem_range_of_isRoot
      ((Polynomial.map_ne_zero_iff γ.injective).2 (minpoly.ne_zero hsep.isIntegral)) ?_
    rw [Polynomial.map_map, ← h, ← Polynomial.map_map, Polynomial.IsRoot,
      Polynomial.eval_map_apply, Polynomial.eval_map_algebraMap, minpoly.aeval, map_zero]
  let e : Ω₁ ≃+* φ.range := RingEquiv.ofBijective φ.rangeRestrict
    ⟨fun _ _ hxy ↦ φ.injective congr($hxy.1), φ.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (χ.codRestrict φ.range hrange), RingHom.ext fun a ↦ ?_⟩
  change φ (e.symm _) = χ a
  have : e (e.symm ⟨χ a, hrange a⟩) = ⟨χ a, hrange a⟩ := e.apply_symm_apply _
  exact congr($this.1)
