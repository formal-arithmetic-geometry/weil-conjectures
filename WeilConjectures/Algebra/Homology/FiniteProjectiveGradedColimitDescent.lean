/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.Projective
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.Algebra.FinitePresentationColimit

/-! # Descent of bounded graded finite projective modules

Source: Stacks Project, More on Algebra, Tag 0BC7, proof of (1), descent of terms.
(blueprint: lem-pc-finite-projective-graded-colimit-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- A bounded graded family of finite projective modules descends with the same support bounds.
Source: Stacks Project, More on Algebra, Tag 0BC7, proof of (1), and Algebra, Tags 05N7, 00NX.
(blueprint: lem-pc-finite-projective-graded-colimit-descent).

Proof: Only the finitely many degrees in [a,b] need models. Each term is finitely presented,
so descend a finite presentation by the object clause of finite-presentation colimit descent.
Write each original term as a summand of a finite free module. Descend the inclusion and
retraction by the map clause, then impose their retraction identity by the equality clause.
The resulting stage model is a summand of a finite free module, hence finite and projective.
Directedness gives a common stage for the finitely many terms. Extension of scalars preserves
finite projectivity, so transport all models to that stage. In other degrees use the zero
module; its base change is zero and is isomorphic to the given zero term. These models give
the required graded isomorphisms, with no differentials involved. For a preorder, first pass
to its antisymmetrization (equivalent as an indexing category), apply the partial-order
finite-presentation lemma there, and lift the resulting stage back. If b < a the interval is
empty: choose any stage and put zero in every degree. -/
theorem exists_finite_projective_graded_model_of_directed_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (X : ℤ → ModuleCat.{u} (colimit F : CommRingCat.{u})) (a b : ℤ)
    (hzero : ∀ n : ℤ, n < a ∨ b < n → IsZero (X n))
    (hfinite : ∀ n : ℤ, Module.Finite (colimit F : CommRingCat.{u}) (X n))
    (hprojective : ∀ n : ℤ, Module.Projective (colimit F : CommRingCat.{u}) (X n)) :
    ∃ (i : I) (M : ℤ → ModuleCat.{u} (F.obj i)),
      (∀ n : ℤ, n < a ∨ b < n → IsZero (M n)) ∧
      (∀ n : ℤ, Module.Finite (F.obj i) (M n)) ∧
      (∀ n : ℤ, Module.Projective (F.obj i) (M n)) ∧
      Nonempty (∀ n : ℤ, (extendScalars (colimit.ι F i).hom).obj (M n) ≅ X n) := by
  sorry

end ModuleCat
