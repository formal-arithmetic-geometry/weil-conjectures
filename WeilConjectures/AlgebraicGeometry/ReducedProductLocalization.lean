/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Localization of a reduced tensor-product decomposition
-/

@[expose] public section

set_option autoImplicit false
universe u v
open scoped TensorProduct

/-- If the reduction of `B ⊗[R] C` is `C`-isomorphic to a finite product `∏ j, D j`, then for a
localization `C'` of `C` away from `x`, the reduction of `B ⊗[R] C'` is `C'`-isomorphic to
`∏ j, C' ⊗[C] D j`. -/
theorem reduced_product_localization
    (R : Type u) [CommRing R]
    (B : Type v) [CommRing B] [Algebra R B]
    (C : Type u) [CommRing C] [Algebra R C]
    (r : ℕ) (D : Fin r → Type u) [∀ j, CommRing (D j)] [∀ j, Algebra C (D j)]
    (hsplit : letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := B) (B := C)
      Nonempty (((B ⊗[R] C) ⧸ nilradical (B ⊗[R] C)) ≃ₐ[C] (∀ j, D j)))
    (x : C) (C' : Type u) [CommRing C'] [Algebra C C'] [IsLocalization.Away x C']
    [Algebra R C'] [IsScalarTower R C C'] :
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := B) (B := C')
    Nonempty (((B ⊗[R] C') ⧸ nilradical (B ⊗[R] C')) ≃ₐ[C']
      (∀ j, C' ⊗[C] D j)) := by
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := B) (B := C)
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := B) (B := C')
  obtain ⟨e⟩ := hsplit
  let A := B ⊗[R] C
  let T := C' ⊗[C] A
  let ebase : T ≃ₐ[C'] B ⊗[R] C' :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : C' ≃ₐ[C'] C')
      (Algebra.TensorProduct.commRight R C B).symm).trans
      ((Algebra.TensorProduct.cancelBaseChange R C C' C' B).trans
        (Algebra.TensorProduct.commRight R C' B))
  have hnilBase : nilradical (B ⊗[R] C') =
      (nilradical T).map ebase.toRingEquiv.toRingHom := by
    simpa only [nilradical, Ideal.zero_eq_bot, Ideal.map_bot] using
      (Ideal.map_radical_of_surjective ebase.surjective
        (by simp)
        (I := (⊥ : Ideal T))).symm
  let ered := Ideal.quotientEquivAlg (nilradical T)
    (nilradical (B ⊗[R] C')) ebase hnilBase
  let := Algebra.TensorProduct.rightAlgebra (R := C) (A := C') (B := A)
  have hnil : nilradical T = (nilradical A).map
      (Algebra.TensorProduct.includeRight (R := C) (A := C')).toRingHom := by
    change nilradical T = (nilradical A).map (algebraMap A T)
    simpa only [nilradical, Ideal.zero_eq_bot, Ideal.map_bot] using
      (IsLocalization.map_radical
        (Algebra.algebraMapSubmonoid A (Submonoid.powers x)) T (⊥ : Ideal A)).symm
  let equot : (T ⧸ nilradical T) ≃ₐ[C'] C' ⊗[C] (A ⧸ nilradical A) :=
    (Ideal.quotientEquivAlgOfEq C' hnil).trans
      (Algebra.TensorProduct.tensorQuotientEquiv C' A C' (nilradical A)).symm
  exact ⟨ered.symm.trans (equot.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : C' ≃ₐ[C'] C') e).trans
      (Algebra.TensorProduct.piRight C C' C' D)))⟩
