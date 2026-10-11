/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.Mathlib.RingTheory.Henselian

/-!
# Filtered colimits of henselian pairs

Source: Stacks Project, More on Algebra, Lemma 0FWT (blueprint:
lem-weil-pbc-filtered-colimit-henselian-pair).
-/

universe u

open CategoryTheory CategoryTheory.Limits

/-- A directed colimit of henselian pairs is a henselian pair: for a nonempty directed set
`Λ`, a directed system of commutative rings `F` with ideals `J i` carried into each other by
the transition maps, every `(F.obj i, J i)` henselian, the union `I` of the images of the
`J i` in `colimit F` is an ideal, contained in the Jacobson radical, and `(colimit F, I)` is
henselian.
Source: Stacks Project, More on Algebra, Lemma 0FWT.
(blueprint: lem-weil-pbc-filtered-colimit-henselian-pair)

Proof sketch:
1. `Λ` is a filtered category, so every element of the colimit comes from a stage, two
   elements of stages agreeing in the colimit agree at a later stage, and the union of the
   images of the stage ideals is an ideal; an element of a stage landing in it lands in a
   stage ideal later on.
2. Each stage pair satisfies the factorization criterion (Stacks 09XI): its ideal lies in
   the Jacobson radical and coprime monic factorizations modulo it lift.
3. An element `u ∈ 1 + I` comes from some `1 + x` with `x ∈ J λ`, a unit at that stage,
   so `u` is a unit; hence `I` lies in the Jacobson radical.
4. A monic `f` over the colimit with a coprime monic factorization modulo `I` (the case
   of a zero quotient being trivial) descends with its factors and Bezout coefficients to
   one stage, where the factorization holds modulo the stage ideal after passing further.
5. Lift the factorization at that stage and map it to the colimit; by the factorization
   criterion `(colimit F, I)` is henselian. -/
theorem filteredColimit_henselianPair
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (F : Λ ⥤ CommRingCat.{u}) [HasColimit F]
    (J : ∀ i : Λ, Ideal (F.obj i))
    (hJ : ∀ {i j : Λ} (f : i ⟶ j),
      Ideal.map (F.map f).hom (J i) ≤ J j)
    (hH : ∀ i : Λ, HenselianRing (F.obj i) (J i)) :
    ∃ I : Ideal (colimit F : CommRingCat.{u}), (I : Set (colimit F : CommRingCat.{u})) =
      {x | ∃ (i : Λ) (a : F.obj i), (colimit.ι F i).hom a = x ∧ a ∈ J i} ∧
      I ≤ Ideal.jacobson ⊥ ∧ HenselianRing (colimit F : CommRingCat.{u}) I := by
  sorry
