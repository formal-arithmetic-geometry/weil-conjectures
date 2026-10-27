/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups C1 and B4
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import WeilConjectures.FieldTheory.SeparableExtension
public import Sheaf.FieldTheory.FieldTower
import Sheaf.FieldTheory.SeparableQuotientProduct
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.Algebra.Algebra.Pi

/-!
# A finite separable field tensored with an algebraically closed field

Source: Stacks Project, Tag 0FD1, proof, residue-field base change; Tags 030U, 00U3,
030N, and 09GU for the polynomial presentation and splitting argument
(blueprint: lem-pc-separable-tensor-algebraic-closure).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

attribute [local instance] TensorProduct.rightAlgebra

private theorem separable_of_finite_separableExtension
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    [Module.Finite k K] (h : IsSeparableExtension k K) : Algebra.IsSeparable k K := by
  obtain ⟨s, hs, hsep⟩ := h ⊤ (IntermediateField.fg_top k K)
  have hsempty : s = ∅ := by
    have : IsEmpty s := hs.1.isEmpty_of_isAlgebraic
    exact Set.isEmpty_coe_sort.mp this
  subst s
  rw [IntermediateField.adjoin_empty] at hsep
  let := hsep
  have : Algebra.IsSeparable k (⊤ : IntermediateField k K) := by
    apply Algebra.IsSeparable.of_equiv_equiv
      (IntermediateField.botEquiv k (⊤ : IntermediateField k K)).toRingEquiv
      (RingEquiv.refl (⊤ : IntermediateField k K))
    ext x
    obtain ⟨y, rfl⟩ := (IntermediateField.botEquiv k
      (⊤ : IntermediateField k K)).symm.surjective x
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom,
      RingEquiv.refl_apply, IntermediateField.botEquiv_symm,
      ← IsScalarTower.algebraMap_apply]
    exact congrArg (fun z : k ↦ ((algebraMap k (⊤ : IntermediateField k K)) z).1)
      (IntermediateField.botEquiv_def (F := k) (E := (⊤ : IntermediateField k K)) y)
  exact AlgEquiv.Algebra.isSeparable (IntermediateField.topEquiv :
    (⊤ : IntermediateField k K) ≃ₐ[k] K)

/-- A finite separable extension tensored with an algebraically closed field is a product
of copies of that field indexed by the base-field embeddings. The number of factors is
the extension degree.
Source: Stacks Project, Tag 0FD1, proof, with Tags 030U, 00U3, 030N, and 09GU.
(blueprint: lem-pc-separable-tensor-algebraic-closure).

Proof: (1) Finite-dimensionality makes every element algebraic
(`def-weil-algebraic-element`), so a transcendence basis is empty
(`def-weil-pbc-transcendence-basis`). Applying `IsSeparableExtension` to the whole
finitely generated extension gives separable algebraicity
(`def-weil-pbc-separable-algebraic-extension`). Choose a primitive element
(`lem-weil-pbc-finite-separable-extension-primitive-element`), with monic separable
minimal polynomial P; its power basis gives K = k[T]/(P)
(`lem-weil-pbc-simple-algebraic-extension-power-basis`).
(2) `AdjoinRoot.tensorAlgEquiv` base changes this presentation; `AdjoinRoot.mapAlgEquiv`
along the tensor unit isomorphism identifies it with Omega[T]/(P bar).
(3) A Bezout identity for P and its derivative survives coefficient extension
(`def-pc-separable-polynomial`). The Chinese remainder decomposition is a product
of Omega indexed by roots (`lem-pc-separable-polynomial-alg-closed-quotient-product`).
(4) Evaluation at a root corresponds uniquely to a k-embedding of K into Omega.
`PowerBasis.liftEquiv` gives this correspondence directly. `AlgHom.card` counts the
embeddings as [K:k], and `Fintype.equivFinOfCardEq` identifies their index set with `Fin n`.
The tensor product carries the Omega-algebra structure on its right factor. -/
theorem separable_tensor_algebraicallyClosed_equiv_pi
    (k : Type u) (K : Type v) (Ω : Type w)
    [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra k Ω]
    [FiniteDimensional k K] [IsAlgClosed Ω]
    (hsep : Algebra.IsSeparableExtension k K) :
    Nonempty ((K ⊗[k] Ω) ≃ₐ[Ω] ((K →ₐ[k] Ω) → Ω)) ∧
      ∃ n : ℕ, FieldExtension.degree k K = (n : WithTop ℕ) ∧
        Nonempty ((K →ₐ[k] Ω) ≃ Fin n) := by
  classical
  have : Algebra.IsSeparable k K := separable_of_finite_separableExtension k K hsep
  let : Algebra k (Ω ⊗[k] k) := TensorProduct.instAlgebra
  let pb := Field.powerBasisOfFiniteOfSeparable k K
  let P := minpoly k pb.gen
  let Q := P.map (algebraMap k Ω)
  let P' := P.map (TensorProduct.includeRight (R := k) (A := Ω) (B := k)).toRingHom
  let e₁ : AdjoinRoot P ≃ₐ[k] K :=
    AdjoinRoot.equiv' P pb (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])
      (minpoly.aeval k pb.gen)
  let e₂ := AdjoinRoot.tensorAlgEquiv (R := k) (T := Ω) P P' rfl
  let e₃ := AdjoinRoot.mapAlgEquiv (TensorProduct.rid k Ω Ω) P' Q (by
    apply Associated.of_eq
    dsimp only [P', Q]
    rw [Polynomial.map_map]
    congr 1
    ext x
    simp [Algebra.smul_def])
  obtain ⟨_, e₄, _⟩ := Polynomial.exists_eval_quotient_algEquiv_pi_of_separable
    (Ω := Ω) P P.natDegree (minpoly.monic pb.isIntegral_gen)
    (Algebra.IsSeparable.isSeparable k pb.gen) rfl
  let er : (K →ₐ[k] Ω) ≃ {ρ : Ω // Q.eval ρ = 0} :=
    pb.liftEquiv.trans ((Equiv.refl Ω).subtypeEquiv fun x ↦ by
      simp only [Equiv.refl_apply, Q, P, Polynomial.eval_map_algebraMap])
  let e₅ := AlgEquiv.piCongrLeft Ω (fun _ : {ρ : Ω // Q.eval ρ = 0} ↦ Ω) er
  let e := (TensorProduct.commRight k Ω K).symm.trans
    ((TensorProduct.congr (AlgEquiv.refl : Ω ≃ₐ[Ω] Ω) e₁.symm).trans
      (e₂.trans (e₃.trans (e₄.trans e₅.symm))))
  refine ⟨⟨e⟩, Module.finrank k K, ?_,
    ⟨Fintype.equivFinOfCardEq (AlgHom.card k K Ω)⟩⟩
  simp [FieldExtension.degree, show Module.Finite k K from inferInstance]

end Algebra
