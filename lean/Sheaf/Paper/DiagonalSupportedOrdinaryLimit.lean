/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Paper.DiagonalTowerLimitInterface

/-! # The normalized ordinary limit of the supported quotient tower

Source: diagonal tower limit proof, paragraph (1), and Stacks Tag 099L.
(blueprint: lem-sfb-diagonal-supported-ordinary-limit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- The completed supported constant is the ordinary limit of its quotient tower,
with the coefficient-unit normalization at every projection.

Source: blueprint latest, `sk-prop-diagonal-tower-limit.proof.md`, paragraph (1);
the cokernel source calculation in `sk-prop-diagonal-tower-system`, step (3);
Stacks Tag 099L.
(blueprint: lem-sfb-diagonal-supported-ordinary-limit).

Proof: extend the supported integral constant to constant Z_l coefficients.
The normalized supported scalar-extension isomorphism identifies this with the
supported constant Z_l-module. At level n, the coefficient quotient map has kernel
l^(n+1) and is an epimorphism. Exact closed direct image preserves its cokernel.
The cokernel universal property of D identifies each level, uniquely preserving
the quotient map, with that supported finite constant. The transition equations
of D make these identifications a natural isomorphism of towers. Closed direct
image preserves inverse limits, and forgetting module structure creates them.
The inverse limit of the finite constant coefficient rings is the actual
completed coefficient sheaf; its scalar action is the action restricted along
the canonical constant-to-completed coefficient map. Thus this tower limit is
the restriction of diagonalCompletedSource. Its map from the supported integral
constant takes an integer to that integer times one. The uniqueness assertion
for diagonalCompletedGenerator identifies this map with the named generator.
Composing the limit comparison with the n-th projection therefore recovers the
specified scalar-adjunction unit followed by D's quotient map. This construction
uses only the ordinary presentation, includes n=0, and on the empty scheme all
maps and objects are zero. No derived-limit or completeness assertion is used. -/
theorem diagonal_supported_ordinary_limit (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (D : DiagonalReductionPresentation l (diagonalScalarExtension l (diagonalSurface Y))) :
    ∃ s : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
        (diagonalCompletedSource l Y) ≅ limit (D.E.obj (diagonalIntegralSource Y)),
      ∀ n : ℕ,
        diagonalCompletedGenerator l Y ≫ (diagonalForget l (diagonalSurface Y)).map
          (s.hom ≫ limit.π (D.E.obj (diagonalIntegralSource Y)) (op n)) =
        (diagonalScalarAdjunction l (diagonalSurface Y)).unit.app (diagonalIntegralSource Y) ≫
          (diagonalForget l (diagonalSurface Y)).map
            ((D.π n).app (diagonalIntegralSource Y)) := by sorry

end AlgebraicGeometry.ProEtale
