/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Conv

/-!

# Free and finitely presented module objects

Let `C` be an abelian monoidal category whose tensor product is additive in each variable, and
`R : C` an algebra object such that `R ⊗ -` is right exact, so that `Mod C R` is abelian.

* `Mod.free R n` is the free module `R^n = R ⊕ ⋯ ⊕ R` of rank `n`.
* A global section `s : Γ R = (𝟙 ⟶ R)` acts on the regular module `R` by right
  multiplication `Mod.rightMul s : R ⟶ R`, which is `R`-linear.
* A matrix `A : Matrix (Fin n) (Fin m) (Γ R)` defines the `R`-linear map
  `Mod.matrixMap A : R^m ⟶ R^n`, `(x_j)_j ↦ (∑_j x_j A_{ij})_i`.
* `Mod.cokernelMatrixMap A` is the module presented by `A`, i.e. the cokernel of
  `matrixMap A`.

For a ring `Λ` with a ring homomorphism `φ : Λ →+* Γ R` (for instance `𝒪_E` mapping to the
constant sections of the pro-étale sheaf `𝒪_{E,X}`), a finitely presented `Λ`-module
`Λ' = coker (A : Λ^m ⟶ Λ^n)` gives the `R`-module `Λ' ⊗_Λ R = cokernelMatrixMap (A.map φ)`.
The property of being isomorphic to such a module is `Mod.IsTensorOfFinitePresentation φ`.

-/

@[expose] public section

universe v u w

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

section Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (R : C) [MonObj R]

/-- Right multiplication by a global section, as an endomorphism of the regular module. -/
def rightMul (s : Γ R) : regular R ⟶ regular R :=
  Hom.mk' ((ρ_ R).inv ≫ R ◁ s.hom ≫ μ[R]) (by
    change μ[R] ≫ (ρ_ R).inv ≫ R ◁ s.hom ≫ μ[R] = R ◁ ((ρ_ R).inv ≫ R ◁ s.hom ≫ μ[R]) ≫ μ[R]
    rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc, MonObj.mul_assoc]
    simp)

@[simp]
lemma rightMul_hom (s : Γ R) : (rightMul R s).hom = (ρ_ R).inv ≫ R ◁ s.hom ≫ μ[R] := rfl

end Monoidal

section Abelian

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  (R : C) [MonObj R] [PreservesFiniteColimits (tensorLeft R)]

/-- The free module object of rank `n`. -/
noncomputable abbrev free (n : ℕ) : Mod C R :=
  ⨁ fun _ : Fin n ↦ regular R

/-- The `R`-linear map `R^m ⟶ R^n` given by a matrix of global sections, acting by right
multiplication. -/
noncomputable def matrixMap {n m : ℕ} (A : Matrix (Fin n) (Fin m) (Γ R)) :
    free R m ⟶ free R n :=
  biproduct.matrix fun j i ↦ rightMul R (A i j)

/-- The module object presented by a matrix of global sections: the cokernel of the
associated map of free modules. -/
noncomputable abbrev cokernelMatrixMap {n m : ℕ} (A : Matrix (Fin n) (Fin m) (Γ R)) :
    Mod C R :=
  cokernel (matrixMap R A)

/-- A module object is *locally free of rank `n`* in the trivial (global) sense if it is
isomorphic to `R^n`; see the geometric files for the local version. -/
def IsFree (M : Mod C R) : Prop :=
  ∃ n : ℕ, Nonempty (M ≅ free R n)

/-- Given a ring homomorphism `φ : Λ →+* Γ R`, a module object is *of the form `Λ' ⊗_Λ R` for
a finitely presented `Λ`-module `Λ'`* if it is isomorphic to the cokernel of a map of free
modules given by a matrix with entries in (the image of) `Λ`. -/
def IsTensorOfFinitePresentation {Λ : Type w} [Ring Λ] (φ : Λ →+* Γ R) (M : Mod C R) : Prop :=
  ∃ (n m : ℕ) (A : Matrix (Fin n) (Fin m) Λ), Nonempty (M ≅ cokernelMatrixMap R (A.map φ))

end Abelian

end CategoryTheory.Mod
