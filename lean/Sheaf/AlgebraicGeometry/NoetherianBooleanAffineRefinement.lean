/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Topology.LocallyClosed
public import WeilConjectures.AlgebraicGeometry.NoetherNormalization

/-!
# Boolean affine refinement compatible with finitely many closed subschemes

Source: Stacks Project, `etale-cohomology.tex`, Tag 095K, label
`lemma-decompose-quasi-finite-morphism`, proof: final Noetherian partition paragraph
(blueprint: lem-weil-pbc-noetherian-boolean-affine-refinement).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For an affine Noetherian scheme and a finite family of closed subschemes, there is a
finite affine reduced locally closed partition on which every closed subscheme has either
empty or full underlying pullback. The construction first forms the Boolean atoms of the
closed images and then refines each atom by the finite affine reduced partition theorem.
Source: Stacks Project, `etale-cohomology.tex`, Tag 095K, label
`lemma-decompose-quasi-finite-morphism`, proof: final Noetherian partition paragraph
(blueprint: lem-weil-pbc-noetherian-boolean-affine-refinement).

Proof:
1. Write the affine scheme as a spectrum and represent each closed immersion by a quotient;
   the Boolean membership atoms are locally closed, pairwise disjoint, and cover the space.
2. The quotient spectra and their open restrictions are Noetherian, so discard empty atoms.
3. Apply `Scheme.exists_partition_isImmersion_isAffine_isReduced` to each atom and compose
   the resulting immersions; the finite family remains disjoint and covering.
4. On each piece, Boolean membership says that each prescribed closed image is either
   disjoint from or contains the piece.
5. Closed immersion base change identifies the pullback image with the inverse image of the
   closed image, hence its underlying space is empty or all of the piece.
6. There are finitely many Boolean vectors and each affine refinement is finite; the empty
   scheme and the empty family are included.
-/
theorem exists_noetherian_boolean_affine_refinement
    {X : Scheme.{u}} [IsAffine X] [CompactSpace X] [IsLocallyNoetherian X]
    (r : ℕ) (C : Fin r → Scheme.{u}) (i : ∀ j, C j ⟶ X)
    [∀ j, IsClosedImmersion (i j)] :
    ∃ (n : ℕ) (R : Fin n → Scheme.{u}) (ι : ∀ α, R α ⟶ X),
      (∀ α, IsImmersion (ι α) ∧ IsAffine (R α) ∧ IsReduced (R α) ∧
        IsLocallyClosed (Set.range (ι α))) ∧
      Pairwise (fun α β : Fin n ↦
        Disjoint (Set.range (ι α)) (Set.range (ι β))) ∧
      (∀ x : X, ∃ α, x ∈ Set.range (ι α)) ∧
      ∀ (α : Fin n) (j : Fin r),
        Set.range (pullback.snd (i j) (ι α)) = ∅ ∨
          Set.range (pullback.snd (i j) (ι α)) = Set.univ := by
  sorry

end AlgebraicGeometry
