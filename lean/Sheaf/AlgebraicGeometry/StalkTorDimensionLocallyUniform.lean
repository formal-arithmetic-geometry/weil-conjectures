/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectMorphism
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Uniform stalk Tor bounds near a point

Source: Stacks Project, Tags 069C and 09U9.
(blueprint: lem-pc-stalk-tor-dimension-locally-uniform).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Stalkwise finite Tor dimension becomes uniformly bounded on a neighbourhood.
Source: Stacks Project, More on Morphisms, Tag 069C, `lemma-check-perfect-stalks`,
(3) implies (2); Cohomology of Sheaves, Tag 09U9.

Proof: work in affine neighbourhoods of the source point and its image. A finite
presentation of the source algebra B as a quotient of a polynomial algebra over
A is pseudo-coherent since A is Noetherian. At every prime of that polynomial
algebra, B localizes either to zero or to a module of finite Tor dimension over
the corresponding localization of A, by the stalkwise hypothesis. The polynomial
fibres have finite global dimension, so these localized polynomial modules are
perfect. The local criterion for perfection of a pseudo-coherent module makes B
perfect over the polynomial algebra. Thus A to B is a perfect ring map and B has
finite Tor dimension d over A. Localizing at a source prime and its image preserves
this bound. In particular every source stalk in the chosen affine neighbourhood
has Tor groups zero in all degrees greater than d, for every target-stalk module.
No finite subcover of X is used. An empty source has no point to check; a flat
morphism permits d = 0.
(blueprint: lem-pc-stalk-tor-dimension-locally-uniform). -/
theorem stalkTorDimension_locally_uniform
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hperfect : HasStalkwiseFiniteTorDimension f) :
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ d : ℕ,
      ∀ y : X, y ∈ U → ∀ M : ModuleCat.{u} (Y.presheaf.stalk (f y)),
        ∀ j : ℕ, d < j →
          IsZero (((Tor' (ModuleCat.{u} (Y.presheaf.stalk (f y))) j).obj
            ((ModuleCat.restrictScalars (f.stalkMap y).hom).obj
              (ModuleCat.of (X.presheaf.stalk y) (X.presheaf.stalk y)))).obj M) := by sorry

end AlgebraicGeometry
