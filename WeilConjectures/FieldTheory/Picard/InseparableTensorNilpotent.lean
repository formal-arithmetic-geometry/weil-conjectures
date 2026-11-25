/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Inseparable elements and nilpotents after algebraic-closure base change

An element of a finite extension `K/k` with inseparable minimal polynomial produces a nonzero
nilpotent in `K ⊗[k] kbar`, where `kbar` is an algebraic closure of `k`.

## Implementation details

The quotient `AdjoinRoot (minpoly k α) ≅ k(α)` embeds into `K`, and flatness over `k` keeps
this injective after tensoring with `kbar`, where it becomes
`kbar[T]/(P.map (algebraMap k kbar))`. If `K ⊗[k] kbar` were reduced, this polynomial would be
radical, hence squarefree and thus separable over the perfect field `kbar`; separability then
descends to `k`, a contradiction.

## References

* Stacks Project, Algebra, Lemma Tags 030V and 030W
-/

@[expose] public section

open scoped TensorProduct

namespace FieldTheory

/-- An element of a finite extension `K/k` with inseparable minimal polynomial produces a
nonzero nilpotent in `K ⊗[k] kbar` for an algebraic closure `kbar` of `k`, so this tensor
product is not reduced. -/
theorem inseparable_tensorProduct_algebraicClosure_not_isReduced
    (k K kbar : Type*) [Field k] [Field K] [Field kbar] [Algebra k K] [Algebra k kbar]
    [FiniteDimensional k K] [IsAlgClosure k kbar]
    (α : K) (hαinseparable : ¬ IsSeparable k α) :
    (∃ x : K ⊗[k] kbar, x ≠ 0 ∧ IsNilpotent x) ∧ ¬ IsReduced (K ⊗[k] kbar) := by
  classical
  let : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have hα : IsIntegral k α := IsIntegral.of_finite k α
  let P := minpoly k α
  let Q := P.map (algebraMap k kbar)
  have hP : P.Monic := minpoly.monic hα
  have hQ : Q ≠ 0 := (hP.map _).ne_zero
  have hQsep : ¬ Q.Separable := by
    intro h
    exact hαinseparable ((Polynomial.separable_map (algebraMap k kbar)).mp h)
  let e₁ := IntermediateField.adjoinRootEquivAdjoin k hα
  let f : AdjoinRoot P →ₐ[k] K := (IntermediateField.adjoin k {α}).val.comp e₁.toAlgHom
  have hf : Function.Injective f := Subtype.val_injective.comp e₁.injective
  let g := Algebra.TensorProduct.map (AlgHom.id k kbar) f
  have hg : Function.Injective g :=
    Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hf
  let P' := P.map (Algebra.TensorProduct.includeRight : k →ₐ[k] kbar ⊗[k] k).toRingHom
  let e₂ := AdjoinRoot.tensorAlgEquiv (R := k) (T := kbar) P P' rfl
  let e₃ := AdjoinRoot.mapAlgEquiv (Algebra.TensorProduct.rid k kbar kbar) P' Q (by
    apply Associated.of_eq
    dsimp only [P', Q]
    rw [Polynomial.map_map]
    congr 1
    ext x
    simp [Algebra.smul_def])
  let e := e₂.trans e₃
  have hnred : ¬ IsReduced (K ⊗[k] kbar) := by
    intro hred
    let := hred
    let : IsReduced (kbar ⊗[k] K) :=
      isReduced_of_injective (Algebra.TensorProduct.comm k kbar K)
        (Algebra.TensorProduct.comm k kbar K).injective
    let : IsReduced (kbar ⊗[k] AdjoinRoot P) := isReduced_of_injective g hg
    let : IsReduced (AdjoinRoot Q) := isReduced_of_injective e.symm e.symm.injective
    have hrad : IsRadical Q := isRadical_iff_span_singleton.mpr
      ((Ideal.isRadical_iff_quotient_reduced (Ideal.span {Q})).mpr
        (show IsReduced (AdjoinRoot Q) from inferInstance))
    exact hQsep (PerfectField.separable_iff_squarefree.mpr (hrad.squarefree hQ))
  exact ⟨exists_isNilpotent_of_not_isReduced hnred, hnred⟩

end FieldTheory
