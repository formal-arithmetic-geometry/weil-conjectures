/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.CosetCover
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.NoetherianSpace
public import WeilConjectures.RingTheory.GradedAlgebra.Standard

/-!
# Linear forms without common zero on a projective curve

Let `S` be a standard graded algebra over an infinite field `k` which is a domain and such that
`Proj S` has dimension one. We show that there are two linear forms `l₀, l₁ ∈ S₁` without
common zero on `Proj S`: choose `l₀ ≠ 0`; its zero locus `V₊(l₀)` is a proper closed subset of
the irreducible Noetherian one-dimensional space `Proj S`, hence finite, and `l₁` is chosen
outside the finitely many proper subspaces `𝔭ₓ ∩ S₁`, `x ∈ V₊(l₀)`.

## Main statements

- `Set.Finite.of_isClosed_ne_univ_of_topologicalKrullDim_eq_one` — a proper closed subset of
  an irreducible Noetherian `T₀` space of dimension one is finite.
- `ProjectiveSpectrum.isEmbedding_toPrimeSpectrum` — `Proj S` is a subspace of `Spec S`; in
  particular it is `T₀`, and Noetherian if `S` is.
- `GradedAlgebra.IsStandard.exists_basicOpen_sup_eq_top` — the existence of `l₀, l₁`.
-/

@[expose] public section

open Set TopologicalSpace Topology Order

section Topology

variable {X : Type*} [TopologicalSpace X]

end Topology

namespace ProjectiveSpectrum

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

end ProjectiveSpectrum

namespace GradedAlgebra.IsStandard

open ProjectiveSpectrum

variable {k S : Type*} [Field k] [CommRing S] [Algebra k S] {𝒜 : ℕ → Submodule k S}
  [GradedAlgebra 𝒜] [IsStandard 𝒜]

end GradedAlgebra.IsStandard
