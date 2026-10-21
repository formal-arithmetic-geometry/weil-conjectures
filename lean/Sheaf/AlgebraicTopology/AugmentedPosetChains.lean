/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Data.List.Pairwise

/-! # Augmented strict chains of a poset

Source: Stacks Project, simplicial.tex, Tag 019S and equation-homotopy-to-homotopy;
the augmented strict-poset adaptation in the DAG (blueprint: def-sfb-augmented-poset-chains).

## Main definitions

* `AlgebraicTopology.AugmentedPosetChains.complex`: strict chains with vertex-deletion boundary.
* `AlgebraicTopology.AugmentedPosetChains.bracket`: repeated tuples denote zero.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicTopology.AugmentedPosetChains

/-- Strict lists of length `n + 1`, including the empty list in degree `-1`.
Source: the augmented adaptation of Stacks Tag 019S
(blueprint: def-sfb-augmented-poset-chains). -/
def Simplex (P : Type v) [PartialOrder P] (n : ℤ) : Type v :=
  {l : List P // l.Pairwise (· < ·) ∧ (l.length : ℤ) = n + 1}

/-- The free module on strict chains in degree `n`. Below degree `-1` its basis is empty.
Source: the augmented adaptation of Stacks Tag 019S
(blueprint: def-sfb-augmented-poset-chains). -/
abbrev chains (R : Type u) [CommRing R] (P : Type v) [PartialOrder P] (n : ℤ) :=
  Simplex P n →₀ R

/-- A tuple denotes its strict-chain generator if it is strict and has the required length,
and zero otherwise. In particular, every repeated weak tuple denotes zero.
Source: the augmented adaptation of Stacks Tag 019S
(blueprint: def-sfb-augmented-poset-chains). -/
noncomputable def bracket (R : Type u) [CommRing R] {P : Type v} [PartialOrder P]
    (n : ℤ) (l : List P) : chains R P n :=
  open Classical in
  if h : l.Pairwise (· < ·) ∧ (l.length : ℤ) = n + 1 then
    Finsupp.single ⟨l, h⟩ 1
  else 0

/-- Alternating vertex deletion, including the vertex-to-empty-chain augmentation.
The differential is zero away from adjacent degrees.
Source: the augmented adaptation of Stacks Tag 019S
(blueprint: def-sfb-augmented-poset-chains). -/
noncomputable def boundary (R : Type u) [CommRing R] (P : Type v) [PartialOrder P]
    (i j : ℤ) : ModuleCat.of R (chains R P i) ⟶ ModuleCat.of R (chains R P j) :=
  if i = j + 1 then
    ModuleCat.ofHom (Finsupp.linearCombination R fun c : Simplex P i ↦
      ∑ k ∈ Finset.range c.val.length, (-1 : R) ^ k • bracket R j (c.val.eraseIdx k))
  else 0

/-- The deletion boundary has the chain-complex shape and squares to zero.
Source: Stacks Tag 019S, augmented strict-poset adaptation
(blueprint: def-sfb-augmented-poset-chains).

Proof: off adjacent degrees the definition is zero. On a strict generator, deleting
positions a < b in the two possible orders gives the same list, with signs
(-1)^(a+b-1) and (-1)^(a+b), so all terms cancel. For a two-vertex list the two
augmentations cancel. A vertex maps to the empty list, whose boundary is the empty
sum. Below degree -1 there are no generators. Extend these identities by linearity.
This is step 1 of lem-sfb-poset-augmented-chain-prism, directly on strict generators. -/
theorem boundary_laws (R : Type u) [CommRing R] (P : Type v) [PartialOrder P] :
    (∀ i j : ℤ, ¬ (ComplexShape.down ℤ).Rel i j → boundary R P i j = 0) ∧
      (∀ i j k : ℤ, boundary R P i j ≫ boundary R P j k = 0) := by
  sorry

/-- The integer-indexed augmented strict-poset chain complex. Degree -1 is free on
the single empty list (canonically R); degrees below -1 have empty basis and are zero.
Source: the augmented adaptation of Stacks Tag 019S
(blueprint: def-sfb-augmented-poset-chains). -/
noncomputable def complex (R : Type u) [CommRing R] (P : Type v) [PartialOrder P] :
    ChainComplex (ModuleCat.{max u v} R) ℤ where
  X n := ModuleCat.of R (chains R P n)
  d := boundary R P
  shape := (boundary_laws R P).1
  d_comp_d' := fun i j k _ _ ↦ (boundary_laws R P).2 i j k

end AlgebraicTopology.AugmentedPosetChains
