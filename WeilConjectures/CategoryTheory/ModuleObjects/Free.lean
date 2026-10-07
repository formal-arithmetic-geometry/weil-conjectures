/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian

/-!

# Free and finitely presented module objects

Let `C` be an abelian monoidal category whose tensor product is additive in each variable, and
`R : C` an algebra object such that `R ⊗ -` is right exact, so that `Mod C R` is abelian.

* `Mod.free R n` is the free module `R^n = R ⊕ ⋯ ⊕ R` of rank `n`.
* `Mod.IsFree R M`: `M` is isomorphic to `R^n` for some `n`.
* `Mod.IsFinitelyPresented R M`: `M` is isomorphic to the cokernel of a morphism
  `R^m ⟶ R^n` between free modules of finite rank.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.Mod

section Abelian

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  (R : C) [MonObj R] [PreservesFiniteColimits (tensorLeft R)]

/-- The free module object of rank `n`. -/
noncomputable abbrev free (n : ℕ) : Mod C R :=
  ⨁ fun _ : Fin n ↦ regular R

/-- A module object is *locally free of rank `n`* in the trivial (global) sense if it is
isomorphic to `R^n`; see the geometric files for the local version. -/
def IsFree (M : Mod C R) : Prop :=
  ∃ n : ℕ, Nonempty (M ≅ free R n)

/-- A module object is *finitely presented* if it is isomorphic to the cokernel of a morphism
`R^m ⟶ R^n` between free modules of finite rank. -/
def IsFinitelyPresented (M : Mod C R) : Prop :=
  ∃ (n m : ℕ) (f : free R m ⟶ free R n), Nonempty (M ≅ cokernel f)

end Abelian

end CategoryTheory.Mod
