/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicTopology.AugmentedPosetChains
public import Mathlib.Order.Hom.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # The augmented strict-poset chain prism

Source: Stacks Project, simplicial.tex, Tag 019S, lemma-homotopy-s-N and
equation-homotopy-to-homotopy, with the DAG's augmented strict-chain adaptation
(blueprint: lem-sfb-poset-augmented-chain-prism).

## Main statements

* `AlgebraicTopology.AugmentedPosetChains.map_comm`: monotone maps commute with deletion.
* `AlgebraicTopology.AugmentedPosetChains.map_id` and `map_comp`: functoriality.
* `AlgebraicTopology.AugmentedPosetChains.prism_identity`: the displayed signed prism identity.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicTopology.AugmentedPosetChains

/-- Entrywise image on strict-chain generators, killing repetitions. It fixes the empty list.
Source: Stacks Tag 019S, the augmented strict-poset adaptation
(blueprint: lem-sfb-poset-augmented-chain-prism). -/
noncomputable def mapComponent (R : Type u) [CommRing R] {P Q : Type v}
    [PartialOrder P] [PartialOrder Q] (f : P →o Q) (n : ℤ) :
    (complex R P).X n ⟶ (complex R Q).X n :=
  ModuleCat.ofHom (Finsupp.linearCombination R fun c : Simplex P n ↦
    bracket R n (c.val.map f))

/-- Entrywise monotone image commutes with the boundary in every integer degree.
Source: Stacks Tag 019S, augmented strict-poset adaptation
(blueprint: lem-sfb-poset-augmented-chain-prism).

Proof: use weak tuples before quotienting by repetitions. Deletion commutes with
entrywise image. The span of repeated tuples is a subcomplex: adjacent equal entries
give two identical faces of opposite signs, and every other face remains repeated.
Monotone maps preserve repetitions. Thus the weak-tuple chain map descends to the free
module on strict tuples, with exactly mapComponent's formula. In degree zero both
composites augment a vertex to the empty generator; below zero the boundary is zero.
These are steps 2 and 3 of the node's proof. -/
theorem map_comm (R : Type u) [CommRing R] {P Q : Type v}
    [PartialOrder P] [PartialOrder Q] [Finite P] [Finite Q] (f : P →o Q) (i j : ℤ) :
    mapComponent R f i ≫ (complex R Q).d i j =
      (complex R P).d i j ≫ mapComponent R f j := by
  sorry

/-- The chain map induced by a monotone map, including the identity on the empty generator.
Source: Stacks Tag 019S, augmented strict-poset adaptation
(blueprint: lem-sfb-poset-augmented-chain-prism). -/
noncomputable def map (R : Type u) [CommRing R] {P Q : Type v}
    [PartialOrder P] [PartialOrder Q] [Finite P] [Finite Q] (f : P →o Q) :
    complex R P ⟶ complex R Q where
  f := mapComponent R f
  comm' := fun i j _ ↦ map_comm R f i j

/-- The chain map of the identity is the identity.
Source: Stacks Tag 019S, augmented strict-poset adaptation
(blueprint: lem-sfb-poset-augmented-chain-prism).

Proof: entrywise identity fixes every strict list and the empty list. Their free
generators span each degree, so the chain maps agree. This is step 4 of the node's proof. -/
theorem map_id (R : Type u) [CommRing R] (P : Type v) [PartialOrder P] [Finite P] :
    map R (OrderHom.id : P →o P) = 𝟙 (complex R P) := by
  sorry

/-- The chain maps preserve composition.
Source: Stacks Tag 019S, augmented strict-poset adaptation
(blueprint: lem-sfb-poset-augmented-chain-prism).

Proof: entrywise composite equals successive entrywise application, including on the
empty generator. A tuple collapsed by the first map remains repeated under the second,
so the zero convention respects composition. Extend from generators by linearity.
This is step 4 of the node's proof. -/
theorem map_comp (R : Type u) [CommRing R] {P Q S : Type v}
    [PartialOrder P] [PartialOrder Q] [PartialOrder S] [Finite P] [Finite Q] [Finite S]
    (f : P →o Q) (g : Q →o S) :
    map R (g.comp f) = map R f ≫ map R g := by
  sorry

/-- The prism's degree-one linear operator: at pivot k concatenate f of the first
k+1 vertices and g of the vertices from k onward, with coefficient (-1)^k.
It is zero in negative source degrees and outside degree one.
Source: Stacks Tag 019S, augmented strict-poset adaptation
(blueprint: lem-sfb-poset-augmented-chain-prism). -/
noncomputable def prismComponent (R : Type u) [CommRing R] {P Q : Type v}
    [PartialOrder P] [PartialOrder Q] (f g : P →o Q) (i j : ℤ) :
    (complex R P).X i ⟶ (complex R Q).X j :=
  if 0 ≤ i ∧ j = i + 1 then
    ModuleCat.ofHom (Finsupp.linearCombination R fun c : Simplex P i ↦
      ∑ k ∈ Finset.range c.val.length, (-1 : R) ^ k •
        bracket R j (((c.val.take (k + 1)).map f) ++ ((c.val.drop k).map g)))
  else 0

/-- Comparable monotone maps have the specified prism identity dh + hd = g_* - f_*
in every integer degree, including the augmentation.
Source: Stacks Tag 019S, equation-homotopy-to-homotopy and lemma-homotopy-s-N;
augmented strict-poset adaptation (blueprint: lem-sfb-poset-augmented-chain-prism).

Proof: first work on weak tuples. Monotonicity and f(x) ≤ g(x) make each pivot
tuple weakly increasing. An adjacent repetition persists in the g block for pivots
at or before it, and in the f block for later pivots, so the prism descends after
killing repetitions (step 5). Expand dH: a face j < k matches the (k-1,j) term
of Hd with opposite sign; a face j > k+1 matches the (k,j-1) term with opposite
sign. These pairings exhaust Hd (step 6). The two junction faces at each pivot
are A_k - A_(k+1), which telescope to the g image minus the f image. Descend to
strict chains (step 7). In degree zero d[f(x),g(x)] = [g(x)] - [f(x)], also when
the two entries coincide. In degree -1 both h terms vanish and both maps are the
identity on the empty generator. Below -1 the source module is zero. Empty P and
Q require no additional assumption (step 8). -/
theorem prism_identity (R : Type u) [CommRing R] {P Q : Type v}
    [PartialOrder P] [PartialOrder Q] [Finite P] [Finite Q]
    (f g : P →o Q) (hfg : ∀ x : P, f x ≤ g x) (n : ℤ) :
    prismComponent R f g n (n + 1) ≫ (complex R Q).d (n + 1) n +
        (complex R P).d n (n - 1) ≫ prismComponent R f g (n - 1) n =
      (map R g).f n - (map R f).f n := by
  sorry

end AlgebraicTopology.AugmentedPosetChains
