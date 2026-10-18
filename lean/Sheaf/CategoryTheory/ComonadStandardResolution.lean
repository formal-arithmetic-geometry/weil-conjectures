/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Monad.Basic

/-!
# Data specifying a standard augmented simplicial resolution of a comonad

Source: Stacks Project, Simplicial, Example 0G5M (the data used in Lemma 0G5N)
(blueprint: def-trf-comonad-standard-resolution).
-/

@[expose] public section

universe v u

open CategoryTheory Opposite Simplicial

namespace CategoryTheory.Comonad

variable {C : Type u} [Category.{v} C]

/-- The actual iterated endofunctor, with zeroth power the identity.
Source: Stacks, Example 0G5M (blueprint: def-trf-comonad-standard-resolution). -/
def resolutionPower (T : C ⥤ C) : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | n + 1 => resolutionPower T n ⋙ T

/-- The prescribed terms, faces, degeneracies and degree-zero augmentation of the
standard comonad resolution. Heterogeneous equality compares the actual operators
across the equalities of their source and target functors; it does not replace
these functors by arbitrary isomorphic objects.
Source: Stacks, Example 0G5M and Lemma 0G5N
(blueprint: def-trf-comonad-standard-resolution). -/
def IsStandardSimplicialResolution (T : Comonad C)
    (B : SimplicialObject (C ⥤ C))
    (e : B ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C)) : Prop :=
  (∀ n : ℕ, B _⦋n⦌ = resolutionPower T.toFunctor (n + 1)) ∧
  (∀ (n : ℕ) (i : Fin (n + 2)),
    HEq (B.δ i)
      (Functor.whiskerRight
        (Functor.whiskerLeft (resolutionPower T.toFunctor (n + 1 - i.val)) T.ε)
        (resolutionPower T.toFunctor i.val))) ∧
  (∀ (n : ℕ) (i : Fin (n + 1)),
    HEq (B.σ i)
      (Functor.whiskerRight
        (Functor.whiskerLeft (resolutionPower T.toFunctor (n - i.val)) T.δ)
        (resolutionPower T.toFunctor i.val))) ∧
  HEq (e.app (op ⦋0⦌)) T.ε

end CategoryTheory.Comonad
