/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Connected.Basic
public import WeilConjectures.AlgebraicGeometry.IsRegularScheme

import WeilConjectures.AlgebraicGeometry.AffineFiniteTypeAlgebra
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.Maximal
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.NoetherianSpace

/-!
# Components of an affine scheme regular at its closed points

Source: Weil conjectures blueprint, `sec-algebraic-groups-lie-algebras`,
`sk-p-geometry/lem-wf-smooth-components-disjoint.md` and its proof
(blueprint: lem-wf-smooth-components-disjoint).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An affine scheme of finite type over a field whose local rings at closed points are
regular has finitely many, pairwise disjoint, clopen irreducible components, and these are
exactly its connected components.

Source: Weil conjectures blueprint, `sk-p-geometry/lem-wf-smooth-components-disjoint.md`
(blueprint: lem-wf-smooth-components-disjoint).

Proof:
1. Write `X = Spec A` using affineness. The structure morphism makes `A` a finite-type
   algebra over `k` by `lem-pc-affine-finite-type-algebra`. If `X` is empty, both collections
   of components are empty and all conclusions hold.
2. By `lem-weil-pbc-spec-irreducible-components-minimal-primes`, components are `V(p)` for
   minimal primes `p`. If two meet at `q`, choose a maximal ideal `m` containing `q` by
   `lem-weil-pbc-proper-ideal-contained-in-maximal`.
3. The point `m` is closed. By `lem-weil-pbc-affine-open-stalk-localization` its local ring
   is `A_m`, regular by the hypothesis and a domain by `lem-sc-regular-local-domain`.
4. The kernel `K` of `A -> A_m` is prime. For each minimal prime `p` contained in `m`,
   the fraction criterion of `def-weil-pbc-localization-at-prime` gives `K <= p`: if an
   element `a` maps to zero, some `s` outside `m` has `s*a = 0`, and primality forces
   `a` into `p`. Minimality then gives `K = p`. Thus the two components coincide.
5. `lem-wf-affine-noetherian-components` gives finiteness. Components are closed by
   `def-weil-irreducible-components` and cover by `lem-sc-irreducible-components-cover`.
   Each complement is the finite union of the other components, so each component is clopen.
6. Each component is nonempty and connected by `lem-pc-irreducible-space-connected`.
   For a point in it, `lem-sfb-connected-component-maximality` places it inside that point's
   connected component. Clopenness prevents the connected component from meeting its
   complement, so the two agree. The covering gives every connected component this way. -/
theorem components_of_regular_closed_points {k : Type u} [Field k] (X : Scheme.{u})
    [IsAffine X] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (hreg : ∀ x : X, x ∈ closedPoints X → IsRegularLocalRing (X.presheaf.stalk x)) :
    (irreducibleComponents X).Finite ∧
      (irreducibleComponents X).Pairwise Disjoint ∧
      (∀ C ∈ irreducibleComponents X, IsClopen C) ∧
      irreducibleComponents X = Set.range (fun x : X => connectedComponent x) := by
  sorry

end AlgebraicGeometry
