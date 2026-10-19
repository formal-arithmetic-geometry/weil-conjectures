/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Finite birational morphisms onto normal integral schemes

Source: Stacks Project, Morphisms, Tag 0AB1 (lemma-finite-birational-over-normal)
(blueprint: lem-trf-finite-birational-normal-iso).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A finite birational morphism to a normal integral scheme is an isomorphism.

Source: Stacks Project, Morphisms, Tag 0AB1 (lemma-finite-birational-over-normal)
(blueprint: lem-trf-finite-birational-normal-iso).

Proof: for a nonempty affine open `V` of `Y`, finiteness makes its inverse image
`U` affine and gives a finite ring map from the sections of `V` to those of `U`.
The generic-point equality and the bijective transported stalk map identify both
rings with the same fraction field, so the ring map is injective and birational.
Every localization of the target affine ring at a maximal ideal is a normal domain
by the target local-ring hypothesis; the local-to-global normal-domain criterion
therefore makes the target affine ring integrally closed. Every element of the
finite source algebra is integral over it, hence belongs to it, so the affine ring
map is an isomorphism. These affine isomorphisms glue over `Y`; the empty open has
empty inverse image. The proof uses [def-pc-integral-scheme],
[def-weil-finite-integral-morphism], [def-sc-function-field], and
[def-weil-pbc-normal-ring], together with the affine fraction-field and
normal-domain lemmas recorded in the item proof dependencies.
-/
theorem isIso_of_finite_birational_normal
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f]
    (hgeneric : f (genericPoint X) = genericPoint Y)
    (hbirational : Function.Bijective
      ((Y.presheaf.stalkCongr (Inseparable.of_eq hgeneric)).inv ≫
        f.stalkMap (genericPoint X) : Y.functionField ⟶ X.functionField))
    (hnormal : ∀ y : Y,
      IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y)) :
    IsIso f := by
  sorry

end AlgebraicGeometry
