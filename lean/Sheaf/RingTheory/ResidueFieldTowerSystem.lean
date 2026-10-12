/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# A coherent system of flat local rings covering a residue-field extension

Source: Stacks Project, Algebra, Lemma 10.159.1 (Tag 03C3), first four proof paragraphs.
-/

@[expose] public section

universe u v

namespace IsLocalRing

/-- Source: Stacks Project, Algebra, Lemma 10.159.1 (Tag 03C3), first four proof paragraphs.
(blueprint: lem-weil-pbc-residue-field-tower-system)

Proof: Well-order the underlying set of K (lifted to the common universe). At each
index x take the colimit of the rings already constructed, using R at the first
index. Their compatible maps to K induce a map on this colimit. Each element is
represented at a stage: a nonzero image means that its representative is a unit,
and a zero image means that it belongs to the image of the maximal ideal of R.
Thus the colimit is local with this maximal ideal. Its underlying R-module is the
module colimit, by the representative and eventual-equality criteria; filtered
colimits preserve flatness. Now adjoin the element x. If it is transcendental over
this ring's residue field, localize the polynomial ring at the extended maximal
ideal. If it is algebraic, lift the coefficients of its monic minimal polynomial
and take the monic quotient. The former is flat by freeness and localization;
the latter is finite free, and integral contraction of maximal ideals shows it
is local. In both cases evaluation has kernel the extended maximal ideal and
its image is the simple field extension. Compose all earlier transition maps
with this new map. Transfinite recursion and induction give the directed-system
identities and compatibility with R and K. The image at index x contains x,
so the stage images cover K. The polynomial, quotient and localization
constructions, and colimits over subsets of K, all stay in Type (max u v).
No final colimit or residue-field isomorphism is asserted here. -/
theorem exists_residue_field_tower_system
    (R : Type u) [CommRing R] [IsLocalRing R] (K : Type v) [Field K]
    (ι : ResidueField R →+* K) :
    ∃ (_ : LinearOrder (ULift.{u} K))
      (A : ULift.{u} K → Type (max u v))
      (_ : ∀ i, CommRing (A i)) (_ : ∀ i, IsLocalRing (A i))
      (_ : ∀ i, Algebra R (A i))
      (f : ∀ i j, i ≤ j → A i →ₐ[R] A j),
      DirectedSystem A (fun i j h ↦ f i j h) ∧
      ∃ (ψ : ∀ i, A i →+* K),
        (∀ i j h x, ψ j (f i j h x) = ψ i x) ∧
        (∀ i, (algebraMap R (A i)).Flat) ∧
        (∀ i, (maximalIdeal R).map (algebraMap R (A i)) = maximalIdeal (A i)) ∧
        (∀ i, RingHom.ker (ψ i) = maximalIdeal (A i)) ∧
        (∀ i, (ψ i).comp (algebraMap R (A i)) = ι.comp (residue R)) ∧
        (∀ x : K, ∃ i a, ψ i a = x) := by sorry

end IsLocalRing
