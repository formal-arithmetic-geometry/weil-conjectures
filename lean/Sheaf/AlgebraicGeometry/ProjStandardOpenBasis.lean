/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Sheaf.AlgebraicGeometry.ProjStandardOpenProperties

/-!
# Positive-degree standard opens of Proj form an affine basis

Source: Stacks Project, Algebra Lemma 00JP (5), and Constructions Lemma 01MB
(blueprint: lem-sc-proj-standard-open-basis).
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry.Proj

/-- The standard opens of positive-degree homogeneous elements form a basis of `Proj`,
and each of these opens is affine. Source: Stacks Project, Algebra Lemma 00JP (5)
and Constructions Lemma 01MB (blueprint: lem-sc-proj-standard-open-basis).

Proof:
1. Apply clause (0) of `lem-weil-pbc-proj-standard-open-inclusion`: for every
nonnegatively graded commutative ring, these positive-degree standard opens form a basis.
Concretely, decompose an arbitrary element into homogeneous components; its basic open
is the union of their basic opens. A degree-zero component's basic open is the union
of basic opens of its products with positive-degree homogeneous elements, since a
point of Proj does not contain the irrelevant ideal (Stacks, Tag 00JP (3)--(5)).
2. For every positive-degree homogeneous `f`, `def-nagata-affine-proj` identifies
its standard open with the spectrum of the degree-zero homogeneous localization
`HomogeneousLocalization.Away` via `Proj.basicOpenIsoSpec`. Thus it is affine
(Stacks, Tag 01MB). -/
theorem isBasis_positiveDegree_basicOpen_and_isAffineOpen
    {S : Type u} {σ : Type v} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
    (𝒮 : ℕ → σ) [GradedRing 𝒮] :
    TopologicalSpace.Opens.IsBasis
        {U : (Proj 𝒮).Opens | ∃ (f : S) (d : ℕ), 0 < d ∧ f ∈ 𝒮 d ∧ U = basicOpen 𝒮 f} ∧
      (∀ (f : S) (d : ℕ), 0 < d → f ∈ 𝒮 d → IsAffineOpen (basicOpen 𝒮 f)) := by
  sorry

end AlgebraicGeometry.Proj
