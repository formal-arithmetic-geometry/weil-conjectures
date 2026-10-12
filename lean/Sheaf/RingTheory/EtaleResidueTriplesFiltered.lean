/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Filteredness of étale residue triples over an arbitrary field

Source: Stacks Project, Tag 04GW, filteredness argument in Lemma 10.155.11.
The argument uses only the fixed residue-field embedding, not separable closedness.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Étale residue triples are filtered for any field with a fixed residue-field embedding.
Source: Stacks Project, Tag 04GW, first three paragraphs of the proof of Lemma 10.155.11.

Proof: The identity triple `(R, p, χ)` gives nonemptiness. For two triples with rings
`S` and `T`, their maps to `K` agree on `R`, so induce a map `S ⊗[R] T → K`.
Its kernel is a prime over both pointed primes; extension to its residue field gives
an embedding in `K`. Base change and composition show that this tensor product is
étale over `R`, giving a common successor. For parallel maps `β₁, β₂ : S → T`, form
`E = T ⊗[S] T` using these maps and `U = E ⊗[T ⊗[R] T] T` using multiplication.
Maps between étale `R`-algebras are étale, as is their diagonal; hence the needed
base changes and composites are étale. The map `T → K` extends to `U` because it
agrees after `β₁` and `β₂`. Its kernel and residue-field extension give another triple.
The rightmost map `T → U` respects the pointing and equalizes the parallel maps:
the tensor relation in `E` identifies `β₁(s) ⊗ 1` with `1 ⊗ β₂(s)`, and the final
base change identifies these with their images from the rightmost `T`.
These are the three filteredness conditions. No closure or algebraicity property of
`K` is used. The identity triple also covers the case `K = κ(p)`.
(blueprint: lem-weil-pbc-etale-triples-filtered-colimit-filtered) -/
theorem etaleResidueTriples_filtered_part
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K) :
    IsFiltered (EtaleResidueTriples R p K χ) := by
  sorry

end AlgebraicGeometry.Scheme
