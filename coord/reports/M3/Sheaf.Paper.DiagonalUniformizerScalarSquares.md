## What changed

Proved `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonal_uniformizer_restriction_square`
in `Sheaf.Paper.DiagonalUniformizerScalarSquares`. The construction works for an arbitrary
coefficient morphism: a normalized scalar/pullback isomorphism gives the restriction/direct-image
isomorphism by uniqueness of right adjoints. The derived-mate factorization and the ordinary
`comapUpperStarIso_mate` identity give exactly the required full cochain-unit equation.
`rightDerivedUnique` transports the integral canonical model to the supplied model `R`.

Added proved private helpers for transport of adjunction mates, the exact derived-adjunction
identity, transport of a normalized square between universal right-derived models, and
construction of the canonical and arbitrary-model squares.
The standalone compile passed in 48.8 seconds. The delivery axiom probe identified only the
original mate-invertibility theorem as depending on `sorry`; its compile took 41.6 seconds.
The unused-variable linter is locally disabled for square existence because its retained
uniformizer hypothesis is unnecessary for this stronger argument.
Only proof imports were added. Existing public signatures, public imports and definitions
are unchanged. The square-existence node now records this route.

## Proved and sorry left

Closed 1 of the 2 original holes; added 0 holes and split off 0 statements.

- Closed: `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonal_uniformizer_restriction_square`
  (`lem-diagonal-uniformizer-restriction-square`).
- Left unchanged: `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonal_uniformizer_restriction_mate_isIso`
  (`lem-diagonal-uniformizer-restriction-mate-isIso`). This is the only remaining `sorry` in the
  delivery. It still needs the perfect quotient/projection argument.

The existing packaging theorem `diagonal_uniformizer_scalar_squares` continues to use these
same two declarations. This is a partial proof delivery, not a decomposition.

## No longer needed

The proof of square existence does not use
`lem-sfb-integral-finite-scalar-perfect-model` / `Sheaf.Paper.IntegralFiniteScalarPerfectModel`:
no finite free quotient resolution, uniformizer regularity or flatness is needed for existence
of the normalized restriction square. Its dependency was removed from the square-existence
node. It remains a planned dependency of mate invertibility, so no module is globally pruned.
No original import was removed, and no module or declaration was withdrawn.

## Where the brief, the DAG or earlier work was wrong

The square-existence node's old proof unnecessarily began with a finite free quotient
resolution. That resolution belongs to the proof of mate invertibility; existence follows
from the general restriction comparison and universal derived units. The statements are
unchanged, and no mathematical statement is disputed.

The supplied perfect-model theorem uses `Padic.coefficientExtensionIntegers`, whereas this
item uses `PadicAlgCl.integers` and the actual quotient by the given `π`. Those coefficient
presentations cannot simply be treated as definitionally identical. The mate-invertibility
hole was retained rather than replacing it with a further equivalent obligation.

The two general normalized-comparison nodes
`lem-sfb-internal-pull-normalization-existence` and
`lem-sfb-normalized-scalar-restriction-push`, together with
`new-comap-upper-star-iso-mate`, are used as tools from the proper-base-change units.
They supply coefficient-adjunction compatibility; there is no corresponding
coefficient-independent normalization statement in the diagonal unit. Their declarations
have complete proofs. Existing `tool_uses` approvals were not edited.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
