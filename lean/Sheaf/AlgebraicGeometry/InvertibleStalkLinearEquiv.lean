/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import WeilConjectures.AlgebraicGeometry.Ample
import all Sheaf.Paper.NonvanishingSectionTrivializes
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes
import WeilConjectures.Topology.PresheafModuleStalkFunctor

/-! # The stalk of an invertible module has rank one

Source: Stacks Project, Modules, Lemma 01CY, proof.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Local triviality of an invertible module gives a rank-one trivialization of each stalk.

Source: Stacks Project, Modules, Lemma 01CY, proof.
(blueprint: lem-weil-pbc-invertible-stalk-linear-equiv).

Proof: Trivialize L on an open neighbourhood U of y. The restriction isomorphism
carries the unit free generator to a section t which freely generates L on every
smaller open. The linear map a ↦ a • germ(t) is surjective because every module germ
has a representative on a neighbourhood inside U, where t generates. It is injective
because equality of germs gives equality on a common smaller neighbourhood, where
scalar multiplication by the restricted generator is injective. Its inverse gives the
asserted linear equivalence. The assertion is vacuous on an empty scheme. -/
theorem invertible_stalk_linearEquiv (Y : Scheme.{u}) (L : Y.Modules)
    [L.IsInvertible] (y : Y) :
    Nonempty (↑(TopCat.Presheaf.stalk L.val.presheaf y) ≃ₗ[Y.presheaf.stalk y]
      ↑(Y.presheaf.stalk y)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
