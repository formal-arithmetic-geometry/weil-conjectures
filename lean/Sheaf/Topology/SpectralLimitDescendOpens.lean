/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.Hom

/-!
# Descent of compact opens in directed limits of spectral spaces

Source: Stacks Project, Topology, Lemma 0A30 (`lemma-descend-opens`), specialized to a
nonempty directed set (blueprint: lem-weil-pbc-spectral-limit-descend-opens).
-/

universe u v

namespace Topology

/-- Compact opens, inclusions between them, and finite union/intersection equalities descend
from a directed limit of spectral spaces to a stage.
Source: Stacks Project, Topology, Lemma 0A30
(blueprint: lem-weil-pbc-spectral-limit-descend-opens).

Proof outline:
1. The preimages of compact opens at stages form a basis: the initial topology gives
   generation by preimages of opens, and the compact-open bases at stages refine these.
   Directedness puts finitely many stages at one common stage. Spectral transition maps
   preserve compact opens, whose finite unions and intersections are compact open
   (`def-weil-spectral-space`). This includes the empty union and empty intersection.
2. Cover a compact open of the limit by this basis. Compactness reduces the cover to a
   finite union, which comes from one stage by step 1. This proves the first clause.
3. For an inclusion of two pulled-back compact opens, pass to the directed upper tail
   above both indices. At each stage take the difference of the two pulled-back opens.
   These differences are constructibly closed (`def-weil-pbc-constructible-topology`)
   and transition maps carry each difference into the preceding one.
4. If every difference were nonempty, the compatible-point theorem
   `lem-weil-pbc-spectral-limit-constructible-closed-nonempty` would give compatible
   points on the tail. Extend them to all indices using common upper bounds and the
   transition identities. The unique-point limit hypothesis gives a point of the limit
   in the first pulled-back open but outside the second, a contradiction. Thus some
   difference is empty, proving descent of inclusion.
5. For a finite union or intersection equality, combine the family into one compact
   open at the given stage (including the empty family). Apply inclusion descent twice
   and pass to a common upper bound. Preimages preserve unions and intersections, so
   the two inclusions give the requested equality. -/
theorem spectralLimit_descend_opens
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (S : I → Type u) [∀ i : I, TopologicalSpace (S i)] [∀ i : I, SpectralSpace (S i)]
    (f : ∀ (i j : I), i ≤ j → S j → S i)
    (hf : ∀ (i j : I) (h : i ≤ j), IsSpectralMap (f i j h))
    (hfid : ∀ (i : I) (x : S i), f i i le_rfl x = x)
    (hfcomp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (x : S k),
      f i j hij (f j k hjk x) = f i k (hij.trans hjk) x)
    (X : Type v) [TopologicalSpace X] (p : ∀ i : I, X → S i)
    (hp : ∀ i : I, Continuous (p i))
    (hpcomp : ∀ (i j : I) (h : i ≤ j) (x : X), f i j h (p j x) = p i x)
    (hlimit : ∀ a : ∀ i : I, S i,
      (∀ (i j : I) (h : i ≤ j), f i j h (a j) = a i) →
      ∃! x : X, ∀ i : I, p i x = a i)
    (htop : ‹TopologicalSpace X› =
      ⨅ i : I, TopologicalSpace.induced (p i) inferInstance) :
    (∀ U : Set X, IsOpen U → IsCompact U →
      ∃ (i : I) (V : Set (S i)), IsOpen V ∧ IsCompact V ∧ p i ⁻¹' V = U) ∧
    (∀ (i j : I) (U : Set (S i)) (V : Set (S j)),
      IsOpen U → IsCompact U → IsOpen V → IsCompact V →
      p i ⁻¹' U ⊆ p j ⁻¹' V →
      ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k), f i k hik ⁻¹' U ⊆ f j k hjk ⁻¹' V) ∧
    (∀ (i : I) (n : ℕ) (U : Set (S i)) (V : Fin n → Set (S i)),
      IsOpen U → IsCompact U → (∀ l : Fin n, IsOpen (V l) ∧ IsCompact (V l)) →
      p i ⁻¹' U = ⋃ l : Fin n, p i ⁻¹' V l →
      ∃ (j : I) (hij : i ≤ j), f i j hij ⁻¹' U = ⋃ l : Fin n, f i j hij ⁻¹' V l) ∧
    (∀ (i : I) (n : ℕ) (U : Set (S i)) (V : Fin n → Set (S i)),
      IsOpen U → IsCompact U → (∀ l : Fin n, IsOpen (V l) ∧ IsCompact (V l)) →
      p i ⁻¹' U = ⋂ l : Fin n, p i ⁻¹' V l →
      ∃ (j : I) (hij : i ≤ j), f i j hij ⁻¹' U = ⋂ l : Fin n, f i j hij ⁻¹' V l) := by
  sorry

end Topology
