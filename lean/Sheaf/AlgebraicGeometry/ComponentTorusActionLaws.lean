/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G6
-/
module

public import Sheaf.AlgebraicGeometry.MonoschemeToricRealization
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# Action laws for the canonical coaction on a monoscheme component

Source: ILO, Travaux de Gabber, Exposé VIII, Proposition 3.2.2 and 3.2.4,
printed p.103 (blueprint: lem-trf-component-torus-action-laws).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Monoscheme

/-- The specified chartwise torus coaction on a component satisfies the group-action
laws, even when the ambient monoscheme has other connected components.

Source: ILO VIII 3.2.2 and 3.2.4, p.103
(blueprint: lem-trf-component-torus-action-laws).

Proof: Restrict the finite affine monoid cover to the component. Its charts have the
same generic lattice. On a chart with monoid P the action comorphism sends e^p to
 e^degree(p) tensor e^p. It preserves scalars, so its spectrum is a morphism over k.
The two associativity comorphisms both send e^p to
 e^degree(p) tensor e^degree(p) tensor e^p, since lattice comultiplication is diagonal.
The unit comorphism fixes e^p, since augmentation sends every lattice monomial to one.
The identities on these monomials extend by linearity to the whole chart algebra.
The coactions preserve the chart: localizing at e^a localizes the second tensor factor,
since the first factor e^degree(a) is a unit. Hence the action preserves every chart
and the identities can be tested on the chart product covers. The coactions agree on
intersections because germ maps commute with restriction. Scheme-morphism gluing and
its uniqueness therefore give the over-base, associativity, and unit identities for
`torusAction`, whose chart formula is fixed by `existsUnique_torusAction`. Package
these identities as `ModObj`. No connectedness of the ambient monoscheme is used.
Rank zero gives the trivial group action; an empty ambient monoscheme has no component. -/
theorem component_torus_action_laws (k : Type u) [Field k]
    (M : Fine.{u}) (hM : Fine.IsTorsionFree M) (C : ToricComponent M) :
    ∃ action : ModObj
        ((Spec (.of (MonoidAlgebra k C.lattice))).asOver (Spec (.of k)))
        (Over.mk (componentToBase k C)),
      action.smul.left = torusAction k C := by sorry

end AlgebraicGeometry.Monoscheme
