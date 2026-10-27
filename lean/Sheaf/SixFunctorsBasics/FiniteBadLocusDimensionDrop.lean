/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Topology.NoetherianSpace
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! # Dimension drop for a bad locus under a finite morphism

Source: de Jong (1997), Lemma 5.7 proof, second paragraph, p.615
(blueprint: lem-sfb-finite-bad-locus-dimension-drop).
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- A finite morphism carries a spreading bad locus into the old one and lowers
its dimension when it avoids the generic points of the old locus.

Source: de Jong (1997), Lemma 5.7 proof, second paragraph, p.615
(blueprint: lem-sfb-finite-bad-locus-dimension-drop).

Proof, following the six steps of the node:
1. For either pair `(V, A)` or `(W, A_W)`, form the reduced closed structure on
   the bad closure and its components using
   `lem-weil-pbc-reduced-induced-closed-subscheme`. Noetherianity gives finitely
   many components (`lem-sc-noetherian-closed-subset-finite-components`), each
   with a unique generic point (`lem-weil-pbc-scheme-sober`). Their reduced
   structures are integral by `def-pc-integral-scheme`.
2. If a component generic point were outside the bad set, spreading would give
   a nonempty open of that component missing the bad set. Intersect it with
   the complement of all other components. This gives a nonempty open in the
   bad closure missing the dense bad set, a contradiction. Hence all component
   generic points belong to the bad set, and there are finitely many of them.
3. Continuity and `A_W ⊆ a ⁻¹' A` put the new closure inside the inverse image
   of the old closed locus. This also proves the empty-old-locus case.
4. A point of the new closure over an old component generic point specializes
   from a new component generic point. Step 2 puts that generic point in `A_W`.
   Its image lies in the old closure and generalizes an old maximal point,
   so is that same point by maximality and sobriety. This contradicts avoidance.
5. Take an affine neighbourhood of the image of a specialization using
   `lem-weil-pbc-affine-opens-basis`. Finiteness makes the affine ring map
   integral (`lem-weil-pbc-finite-algebra-is-integral`). Incomparability
   (`lem-weil-pbc-integral-incomparability`) makes the image of a strict
   specialization strict.
6. Map a length-`n` strict chain to the old closure and prepend a generic point
   of a component containing its first point. Step 4 makes the new step
   strict, so `n + 1 ≤ d` and `n < d`. Sobriety identifies these chains with
   chains of irreducible closed sets (`def-kun-topological-krull-dimension`).
   For `d = 0`, even a one-point chain is impossible. Otherwise the chain
   lengths have supremum at most `d - 1`, giving the dimension inequality.
   Empty loci have no points or chains, as required.
-/
theorem finite_bad_locus_dimension_drop
    (V : Scheme.{u}) [IsLocallyNoetherian V] [CompactSpace V]
    (hdimV : topologicalKrullDim V < ⊤) (A : Set V)
    (hspread : ∀ (T : Scheme.{u}) (i : T ⟶ V) [IsClosedImmersion i]
      [IsIntegral T] (ξ : T),
      IsGenericPoint ξ Set.univ → i ξ ∉ A →
        ∃ U : T.Opens, U ≠ ⊥ ∧ ∀ t : T, t ∈ U → i t ∉ A) :
    (∀ C ∈ irreducibleComponents ↥(closure A), ∀ ξ : ↥(closure A),
        IsGenericPoint ξ C → (ξ : V) ∈ A) ∧
      Set.Finite {ξ : ↥(closure A) |
        ∃ C ∈ irreducibleComponents ↥(closure A), IsGenericPoint ξ C} ∧
      (∀ (W : Scheme.{u}) [IsLocallyNoetherian W] [CompactSpace W]
        (a : W ⟶ V) [IsFinite a] (A_W : Set W),
        (∀ (T : Scheme.{u}) (i : T ⟶ W) [IsClosedImmersion i]
          [IsIntegral T] (ξ : T),
          IsGenericPoint ξ Set.univ → i ξ ∉ A_W →
            ∃ U : T.Opens, U ≠ ⊥ ∧ ∀ t : T, t ∈ U → i t ∉ A_W) →
        A_W ⊆ a ⁻¹' A →
        (∀ C ∈ irreducibleComponents ↥(closure A), ∀ s : ↥(closure A),
          IsGenericPoint s C → A_W ∩ a ⁻¹' ({(s : V)} : Set V) = ∅) →
        closure A_W ⊆ a ⁻¹' closure A ∧
          (∀ C ∈ irreducibleComponents ↥(closure A), ∀ s : ↥(closure A),
            IsGenericPoint s C →
              closure A_W ∩ a ⁻¹' ({(s : V)} : Set V) = ∅) ∧
          (∀ d : ℕ, (closure A).Nonempty →
            topologicalKrullDim
                (Scheme.IdealSheafData.vanishingIdeal
                  (⟨closure A, isClosed_closure⟩ : TopologicalSpace.Closeds V)).subscheme =
              (d : WithBot ℕ∞) →
              (∀ (n : ℕ) (c : Fin (n + 1) → ↥(closure A_W)),
                (∀ j : Fin n,
                  c (Fin.castSucc j) ⤳ c (Fin.succ j) ∧
                    c (Fin.castSucc j) ≠ c (Fin.succ j)) → n < d) ∧
              (d = 0 → closure A_W = ∅) ∧
              ((closure A_W).Nonempty →
                topologicalKrullDim
                    (Scheme.IdealSheafData.vanishingIdeal
                      (⟨closure A_W, isClosed_closure⟩ : TopologicalSpace.Closeds W)).subscheme <
                  topologicalKrullDim
                    (Scheme.IdealSheafData.vanishingIdeal
                      (⟨closure A, isClosed_closure⟩ : TopologicalSpace.Closeds V)).subscheme)) ∧
          (closure A = ∅ → closure A_W = ∅)) := by
  sorry

end AlgebraicGeometry
