/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Finite complements of affine opens on integral curves

Source: Stacks Project, Varieties, Tag 09ND, proof of
`lemma-dim-1-noetherian-integral-separated-has-ample`, second sentence
(blueprint: lem-sc-affine-complement-finite-on-integral-curve).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A nonempty affine open in a Noetherian integral scheme of topological dimension one
has finite complement. Source: Stacks Project, Varieties, Tag 09ND, proof, second sentence
(blueprint: lem-sc-affine-complement-finite-on-integral-curve).

Proof:
1. The complement of the open `U` is closed. Nonemptiness of `U` allows the
   point-outside-open lemma to apply to every point of this complement.
2. Integrality makes `X` irreducible. The uniqueness of generic points in
   `lem-sc-scheme-sober` makes `X` Kolmogorov: distinct points have distinct singleton
   closures, so an open separates them. Dimension one implies dimension at most one.
   Thus `lem-sc-dim-one-point-outside-open-closed` says every point outside `U` is closed.
3. Apply `lem-sc-noetherian-closed-points-finite` to the closed complement: a closed
   subset of a Noetherian scheme all of whose points are closed is finite. -/
theorem IsAffineOpen.finite_compl_of_integral_dim_one
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (hdim : topologicalKrullDim X = 1) {U : X.Opens}
    (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) :
    ((U : Set X)ᶜ).Finite := by
  have _ := hU
  let : IsNoetherian X := IsNoetherian.mk
  exact U.isOpen.finite_compl_of_topologicalKrullDim_le_one hdim.le hne

end AlgebraicGeometry
