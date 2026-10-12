/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.SeparatedAffineFunctionFieldSurjective
import Sheaf.RingTheory.JacobsonDenominatorFunctionField

/-! # Reciprocal functions on a two-open cover

Source: Stacks Project, Varieties Lemma 09NB, first paragraph and open-cover construction.
(blueprint: lem-sc-affine-complement-reciprocal-cover)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An affine open with finite complement admits a reciprocal function on an open
neighbourhood of its complement.

Source: Stacks Project, Varieties Lemma 09NB (varieties-lemma-find-globally-generated),
proof through the open-cover construction.
(blueprint: lem-sc-affine-complement-reciprocal-cover).

Proof: Set A = O(U), K = k(X), and B_x = O_{X,x} for x outside U. The stalks are
Noetherian local domains. Their dimension is one: the generic point lies in U and
strictly specializes to x, while chains in a stalk have length at most dim X = 1.
Both A and B_x have fraction field K. Separatedness makes A tensor B_x -> K
surjective. The common-denominator lemma 09N5 supplies nonzero f in A with inverse
in the maximal ideal of every B_x. Represent these inverse germs on neighbourhoods
V_x of x. All representatives have the same image f^{-1} in K and so agree on
nonempty overlaps by injectivity of regular functions into K; on empty overlaps
agreement is automatic. The sheaf axiom glues them to g on V = union V_x. Thus
U union V = X. On U intersect V the product fg is 1, again by injectivity into K.
Consequently g is a unit at every point of U intersect V. At each point outside U
its germ is in the maximal ideal by construction. This gives D(g) = U intersect V.
If the complement is empty, take V empty, f = 1, and its unique section g.
-/
theorem exists_affine_complement_reciprocal_cover
    (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated] [IsLocallyNoetherian X]
    [CompactSpace X] (hdim : topologicalKrullDim X = 1) (U : X.Opens)
    (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty)
    (hfin : (Set.compl (U : Set X)).Finite) :
    ∃ (V : X.Opens) (f : Γ(X, U)) (g : Γ(X, V)),
      U ⊔ V = ⊤ ∧
      X.presheaf.map (homOfLE inf_le_left).op f *
        X.presheaf.map (homOfLE inf_le_right).op g = 1 ∧
      X.basicOpen g = U ⊓ V := by sorry

end AlgebraicGeometry
