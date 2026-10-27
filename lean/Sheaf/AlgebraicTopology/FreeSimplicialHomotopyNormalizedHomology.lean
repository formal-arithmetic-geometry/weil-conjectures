/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicTopology.MooreComplex
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.Logic.Relation
import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance

/-!
# Homotopy equivalences on free normalized integral homology

Source: Stacks Project, `simplicial.tex`, Tag 08P2, Lemma `lemma-homotopy-equivalence`,
first proof paragraph, using Tags 019Y, 019S and 019T
(blueprint: lem-trf-free-simplicial-homotopy-normalized-homology).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicTopology

/-- Finite chains of cylinder homotopies to the two identities make the induced free
normalized integral homology maps mutually inverse, hence the forward map is bijective.
Here `S ⋙ AddCommGrpCat.free` has group `FreeAbelianGroup (S.obj m)` in degree `m`,
and `Functor.whiskerRight a AddCommGrpCat.free` sends `[s]` to `[a(s)]`.
`normalizedMooreComplex` uses the kernels of faces `d₁, ..., dₘ` and differential `d₀`;
in degree zero it is the whole group, with zero outgoing differential.
`Relation.EqvGen` expresses a finite chain with a cylinder homotopy in either direction
between consecutive maps, including the chain of length zero.

Source: Stacks Project, Tag 08P2, Lemma `lemma-homotopy-equivalence`, first proof paragraph
(blueprint: lem-trf-free-simplicial-homotopy-normalized-homology).

Proof for stage 3:
1. On basis vectors the degreewise free functor preserves identities and composition.
   The induced normalized chain maps do so as well. Their homology maps are induced by
   sending a cycle to its image, so preserve identities and composition, also in degree zero.
2. Apply `lem-cbc-normalized-alternating-homotopy-equivalence`, namely Mathlib's
   `DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex`, to each free
   simplicial abelian group. The natural inclusion `j` into alternating chains has a
   chain homotopy inverse `r`. A chain homotopy changes the image of a cycle by a boundary;
   hence the homology maps of `j` and `r` are mutually inverse.
3. For one cylinder homotopy, apply
   `lem-weil-pbc-simplicial-homotopy-free-chain-homotopy`, with integral coefficients.
   Mathlib's `SSet.Homotopy.chainComplexMap` and `congr_homologyMap` give equality on
   alternating free homology. Reverse cylinders give the same equality by symmetry.
4. Naturality of `inclusionOfMooreComplex` identifies the alternating map composed with
   the inclusion with the inclusion composed with the normalized map. Cancel the target
   inclusion's bijective homology map to obtain equality on normalized homology.
5. Induct on each finite homotopy chain to equate its endpoint homology maps.
   Apply this to `u ≫ v` and `v ≫ u`, then use functoriality from step 1 to obtain both
   inverse identities. The first gives injectivity of the forward map and the second gives
   surjectivity, using the reverse map to supply preimages. -/
theorem free_normalized_homology_inverse_of_homotopy_equivalence
    {K L : SSet.{u}} (u : K ⟶ L) (v : L ⟶ K)
    (hK : Relation.EqvGen (fun a b ↦ Nonempty (SSet.Homotopy a b)) (u ≫ v) (𝟙 K))
    (hL : Relation.EqvGen (fun a b ↦ Nonempty (SSet.Homotopy a b)) (v ≫ u) (𝟙 L))
    (n : ℕ) :
    (HomologicalComplex.homologyMap
        ((normalizedMooreComplex AddCommGrpCat.{u}).map
          (Functor.whiskerRight u AddCommGrpCat.free)) n ≫
      HomologicalComplex.homologyMap
        ((normalizedMooreComplex AddCommGrpCat.{u}).map
          (Functor.whiskerRight v AddCommGrpCat.free)) n = 𝟙 _) ∧
    (HomologicalComplex.homologyMap
        ((normalizedMooreComplex AddCommGrpCat.{u}).map
          (Functor.whiskerRight v AddCommGrpCat.free)) n ≫
      HomologicalComplex.homologyMap
        ((normalizedMooreComplex AddCommGrpCat.{u}).map
          (Functor.whiskerRight u AddCommGrpCat.free)) n = 𝟙 _) ∧
    Function.Bijective
      (HomologicalComplex.homologyMap
        ((normalizedMooreComplex AddCommGrpCat.{u}).map
          (Functor.whiskerRight u AddCommGrpCat.free)) n).hom := by
  sorry

end AlgebraicTopology
