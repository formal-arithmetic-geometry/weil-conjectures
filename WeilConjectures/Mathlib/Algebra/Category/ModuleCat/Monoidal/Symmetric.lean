/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import WeilConjectures.Mathlib.LinearAlgebra.Coevaluation

/-!
# Finite free modules are dualizable in `ModuleCat R`

For a commutative ring `R` and a finite free `R`-module `M`, the dual module `Module.Dual R M`
is a monoidal-categorical dual of `M` in `ModuleCat R`: the contraction map and the
coevaluation map of a basis (`Module.Basis.coevaluation`) form an exact pairing
`ExactPairing M (ModuleCat.of R (Module.Dual R M))`. Consequently `M` has a right dual, and,
since `ModuleCat R` is symmetric monoidal, also a left dual.

This generalizes the rigidity of `FGModuleCat K` for a field `K`
(`Mathlib.Algebra.Category.FGModuleCat.Basic`) to commutative rings, in the finite free case;
the assembly follows that file. Note that over a general commutative ring the dualizable
objects are the finitely generated projective modules, so no rigidity statement for all of
`ModuleCat R` (nor for the finite free objects of a general `R`) is available here.

This file imports `Mathlib.CategoryTheory.Monoidal.Rigid.Braided` (for
`CategoryTheory.BraidedCategory.hasLeftDualOfHasRightDual`) and
`Mathlib.LinearAlgebra.FreeModule.Finite.Basic` (for finiteness of
`Module.Free.ChooseBasisIndex`) on top of the mirrored file, since none of these files
imports the others.

## Main declarations

- `ModuleCat.coevaluation`, `ModuleCat.evaluation`: the (co)evaluation morphisms between a
  finite free module and its dual in `ModuleCat R`.
- `ModuleCat.exactPairing`: `ExactPairing M (ModuleCat.of R (Module.Dual R M))` for finite
  free `M`.
- `ModuleCat.hasRightDual`, `ModuleCat.hasLeftDual`: a finite free module has a right and a
  left dual, both given by its dual module.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory Module

namespace ModuleCat

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R)

/-- The evaluation morphism of a module `M` in `ModuleCat R`, given by the contraction map
with the dual module. -/
def evaluation : of R (Dual R M) ⊗ M ⟶ 𝟙_ (ModuleCat.{u} R) :=
  ofHom (contractLeft R M)

theorem evaluation_apply (f : Dual R M) (x : M) :
    (evaluation M).hom (f ⊗ₜ x) = f x :=
  contractLeft_apply f x

variable [Module.Free R M] [Module.Finite R M]

/-- The coevaluation morphism of a finite free module `M` in `ModuleCat R`, given by the
coevaluation map of a choice of finite basis, see `Module.Basis.coevaluation`. -/
def coevaluation : 𝟙_ (ModuleCat.{u} R) ⟶ M ⊗ of R (Dual R M) :=
  ofHom (Free.chooseBasis R M).coevaluation

theorem coevaluation_apply_one :
    (coevaluation M).hom (1 : R) =
      ∑ i, Free.chooseBasis R M i ⊗ₜ[R] (Free.chooseBasis R M).coord i :=
  (Free.chooseBasis R M).coevaluation_apply_one

set_option backward.privateInPublic true in
private theorem coevaluation_evaluation :
    of R (Dual R M) ◁ coevaluation M ≫ (α_ (of R (Dual R M)) M (of R (Dual R M))).inv ≫
        evaluation M ▷ of R (Dual R M) =
      (ρ_ (of R (Dual R M))).hom ≫ (λ_ (of R (Dual R M))).inv := by
  ext : 1
  apply (Free.chooseBasis R M).contractLeft_assoc_coevaluation

set_option backward.privateInPublic true in
private theorem evaluation_coevaluation :
    coevaluation M ▷ M ≫ (α_ M (of R (Dual R M)) M).hom ≫ M ◁ evaluation M =
      (λ_ M).hom ≫ (ρ_ M).inv := by
  ext : 1
  apply (Free.chooseBasis R M).contractLeft_assoc_coevaluation'

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The dual module of a finite free module is its monoidal-categorical dual in
`ModuleCat R`: contraction and coevaluation form an exact pairing. -/
instance exactPairing : ExactPairing M (of R (Dual R M)) where
  coevaluation' := coevaluation M
  evaluation' := evaluation M
  coevaluation_evaluation' := coevaluation_evaluation M
  evaluation_coevaluation' := evaluation_coevaluation M

/-- A finite free module has a right dual in `ModuleCat R`, given by its dual module. -/
instance hasRightDual : HasRightDual M :=
  ⟨of R (Dual R M)⟩

/-- A finite free module has a left dual in `ModuleCat R`, given by its dual module, since
`ModuleCat R` is symmetric monoidal. -/
instance hasLeftDual : HasLeftDual M :=
  BraidedCategory.hasLeftDualOfHasRightDual (X := M)

end ModuleCat
