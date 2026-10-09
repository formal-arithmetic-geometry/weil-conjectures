/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Base change of symmetric algebras

The symmetric algebra commutes with base change: if `f : M → N` exhibits the `S`-module `N` as
the base change of the `R`-module `M`, then `Sym_S N` is the base change `S ⊗[R] Sym_R M`.

## Main definitions

- `SymmetricAlgebra.mapOfIsScalarTower`: the `R`-algebra map `Sym_R M → Sym_S N` induced by an
  `R`-linear map `M → N` into an `S`-module.

## Main statements

- `SymmetricAlgebra.isPushout_of_isBaseChange`: `Sym_S N` is the pushout of `Sym_R M` along
  `R → S`.
-/

@[expose] public section

open TensorProduct

namespace SymmetricAlgebra

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

variable (S) in
/-- The `R`-algebra map `Sym_R M → Sym_S N` induced by an `R`-linear map `f : M → N` into an
`S`-module. -/
noncomputable def mapOfIsScalarTower (f : M →ₗ[R] N) :
    SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra S N :=
  lift ((ι S N).restrictScalars R ∘ₗ f)

@[simp]
lemma mapOfIsScalarTower_ι (f : M →ₗ[R] N) (m : M) :
    mapOfIsScalarTower S f (ι R M m) = ι S N (f m) := by
  simp [mapOfIsScalarTower]

/-- If `f : M → N` exhibits `N` as the base change of `M` along `R → S`, then `Sym_S N` is the
base change of `Sym_R M`: the square of `R`-algebras `R → S`, `R → Sym_R M`, `Sym_R M → Sym_S N`,
`S → Sym_S N` is a pushout. -/
theorem isPushout_of_isBaseChange {f : M →ₗ[R] N} (hf : IsBaseChange S f) :
    letI := (mapOfIsScalarTower S f).toAlgebra
    Algebra.IsPushout R S (SymmetricAlgebra R M) (SymmetricAlgebra S N) := by
  let := (mapOfIsScalarTower S f).toAlgebra
  have : IsScalarTower R (SymmetricAlgebra R M) (SymmetricAlgebra S N) :=
    .of_algebraMap_eq fun r ↦ ((mapOfIsScalarTower S f).commutes r).symm
  let fwd : S ⊗[R] SymmetricAlgebra R M →ₐ[S] SymmetricAlgebra S N :=
    Algebra.TensorProduct.lift (Algebra.ofId S _) (mapOfIsScalarTower S f)
      (fun _ _ ↦ .all _ _)
  let bwd : SymmetricAlgebra S N →ₐ[S] S ⊗[R] SymmetricAlgebra R M :=
    lift (hf.lift ((Algebra.TensorProduct.includeRight (R := R) (A := S)).toLinearMap ∘ₗ ι R M))
  have hbwd (m : M) : bwd (ι S N (f m)) = 1 ⊗ₜ ι R M m := by
    simp [bwd, IsBaseChange.lift_eq]
  have h₁ : fwd.comp bwd = AlgHom.id S _ := by
    apply algHom_ext
    refine hf.algHom_ext _ _ fun m ↦ ?_
    simp [hbwd, fwd]
  have h₂ : bwd.comp fwd = AlgHom.id S _ := by
    apply Algebra.TensorProduct.ext (by ext) 
    apply algHom_ext
    ext m
    simp [fwd, hbwd]
  let e := AlgEquiv.ofAlgHom fwd bwd h₁ h₂
  refine ⟨IsBaseChange.of_equiv e.toLinearEquiv fun a ↦ ?_⟩
  simp [e, fwd, RingHom.algebraMap_toAlgebra]

end SymmetricAlgebra

