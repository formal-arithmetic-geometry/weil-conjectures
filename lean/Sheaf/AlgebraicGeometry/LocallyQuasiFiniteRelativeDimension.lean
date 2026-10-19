/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.RingTheory.QuasiFiniteAtPrimeZeroFibreDimension
import WeilConjectures.RingTheory.QuasiFiniteAtPrime

/-!
# Locally quasi-finite morphisms and relative dimension zero

Source: Stacks Project, Morphisms of Schemes, Tag 0397, lemma-locally-quasi-finite-rel-dimension-0
(blueprint: lem-trf-locally-quasi-finite-relative-dimension-zero)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism locally of finite type is locally quasi-finite exactly when every fibre has
local topological Krull dimension zero at the point corresponding to each source point.

Source: Stacks Project, Morphisms of Schemes, Tag 0397, lemma-locally-quasi-finite-rel-dimension-0
(blueprint: lem-trf-locally-quasi-finite-relative-dimension-zero).
Proof: Fix a source point and choose affine neighbourhoods of it and of its image. The induced
finite-type ring map identifies the corresponding affine fibre with an open neighbourhood of the
point in the scheme-theoretic fibre, and the canonical homeomorphisms preserve local Krull
dimension. The affine ring equivalence between quasi-finiteness at a prime and zero local fibre
dimension gives the forward and reverse implications. Quantifying over all source points yields
the stated equivalence; for an empty source both sides are vacuous.
-/
theorem isLocallyQuasiFinite_iff_topologicalKrullDimAt_fiber_eq_zero
    {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType f] :
    f.IsLocallyQuasiFinite ↔
      ∀ x : X, topologicalKrullDimAt (f.asFiber x) = 0 := by
  sorry

end AlgebraicGeometry.Scheme.Hom
