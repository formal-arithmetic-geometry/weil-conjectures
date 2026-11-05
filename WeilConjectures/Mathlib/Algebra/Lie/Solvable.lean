/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Solvable

/-!
# Solvability from the derived algebra, and the radical under isomorphisms

A Lie algebra whose derived algebra `⁅L, L⁆` is solvable is itself solvable. The image of a
solvable ideal under a surjective morphism of Lie algebras is solvable, so the solvable radical is
preserved by isomorphisms; in particular it is a characteristic ideal.

## Main declarations

* `LieIdeal.isSolvable_map`: the image of a solvable ideal under a surjective morphism is
  solvable.
* `LieAlgebra.map_radical`: an isomorphism of Lie algebras maps the radical onto the radical.

## Blueprint

The blueprint subsection `det-d-lie` consists of definitions and facts already in Mathlib:
* `def-wf-lie-algebra`: `LieRing`/`LieAlgebra`, `LieIdeal`, `LieAlgebra.derivedSeries`,
  `LieAlgebra.IsSolvable`, the quotient `L ⧸ I`, `LieModule`, `LieModule.toEnd`;
* `def-wf-semisimple-lie-algebra`: `LieAlgebra.HasTrivialRadical`;
* `def-wf-lie-radical-centre`: `LieAlgebra.radical`, `LieAlgebra.center`, and
  `LieAlgebra.HasCentralRadical`; the Killing form is `killingForm`;
* `lem-wf-sum-of-solvable-ideals`: `LieAlgebra.isSolvableAdd`.

`LieAlgebra.map_radical` implements `rem-ptr-wf-lie-radical-centre-3`.
-/

@[expose] public section

namespace LieAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

end LieAlgebra

namespace LieIdeal

open LieAlgebra

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L']
  [LieAlgebra R L']

end LieIdeal

namespace LieAlgebra

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L']
  [LieAlgebra R L']

end LieAlgebra
