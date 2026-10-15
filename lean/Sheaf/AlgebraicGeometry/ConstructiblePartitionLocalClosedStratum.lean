/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.Constructible
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.Topology.ConstructibleIsRetrocompact

/-!
# An affine neighborhood on which the selected constructible stratum is closed

Source: Stacks Project, Topology, Tags 004E, 005J and 09YH; Schemes, Tag 01IT
(blueprint: lem-sf-constructible-partition-local-closed-stratum).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A selected stratum of a finite locally closed constructible partition is closed on
an affine neighborhood of any of its points. Every stratum restricts to a locally closed
constructible subset there, and the selected stratum has quasi-compact open complement.
Source: Stacks Project, Topology, Tags 004E, 005J and 09YH; Schemes, Tag 01IT
(blueprint: lem-sf-constructible-partition-local-closed-stratum).

Proof:
1. Write `S k = W ∩ Z` with `W` open and `Z` closed, using
   `def-weil-locally-closed-subset`. Since `y ∈ W`, choose an affine open neighborhood
   `V ⊆ W` by `lem-weil-pbc-affine-opens-basis`. The selected stratum restricts to
   `Z ∩ V`, which is closed in `V`.
2. Restrict the open/closed presentation of each `S i` to `V` to obtain local closedness.
   Apply `lem-weil-pbc-constructible-open-restriction` (Tag 005J) to obtain constructibility
   in the subspace `V`.
3. By `def-weil-constructible-subset`, the complement of the selected restricted stratum
   is constructible. It is open by step 1. The affine scheme `V` is quasi-compact by
   `lem-weil-pbc-affine-scheme-qcqs`. Apply `lem-weil-pbc-constructible-is-retrocompact`
   (Tag 09YH) with the whole space of `V` as quasi-compact open test subset; its
   intersection with this complement is the complement itself, hence is quasi-compact. -/
theorem exists_affineOpen_closed_stratum (Y : Scheme.{u}) (N : ℕ)
    (S : Fin N → Set Y) (hcover : (⋃ i, S i) = Set.univ)
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (S i) (S j)))
    (hlocallyClosed : ∀ i, IsLocallyClosed (S i))
    (hconstructible : ∀ i, Topology.IsConstructible (S i))
    (y : Y) (k : Fin N) (hy : y ∈ S k) :
    ∃ V : Y.Opens, IsAffineOpen V ∧ y ∈ V ∧
      IsClosed (Subtype.val ⁻¹' S k : Set V) ∧
      (∀ i, IsLocallyClosed (Subtype.val ⁻¹' S i : Set V) ∧
        Topology.IsConstructible (Subtype.val ⁻¹' S i : Set V)) ∧
      IsCompact ((Subtype.val ⁻¹' S k : Set V)ᶜ) := by
  sorry

end AlgebraicGeometry
