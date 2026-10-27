## What changed

Proved `WeilConjectures.SystemProjectionFormula.projection_triangle` in
`Sheaf.Paper.SystemProjectionTriangleCompatibility`. The only added import is the private proof
import `Sheaf.SixFunctors.TriangleProjectionCompositorContraction`. The theorem statement, section
binders and public import remain unchanged. No other Lean module is changed.

The proof normalizes the supplied triangle's factorization equations and bundles its six
schemes and maps as finite-type quasi-compact objects over the fixed field. Properness supplies
the ambient finiteness properties, and the cartesian square supplies quasi-compactness of its
open map. It applies the existing simultaneous-system `TriangleEquations` clause of
`AlgebraicGeometry.ProEtale.CompactCompositionProjection.triangleProjectionCompositorContraction`.
Adjunction cancellation identifies its mate with the intrinsic gamma. Naturality of the proper
compositor identifies its alpha with `triangleWord`. Postcomposition with the inverse
factorization transport, followed by tensor and functor laws, yields the required equation.

All private helpers are proved. Five private definitions give existing projection, composition
and pullback-transport components explicit object types; their data are constructed directly
from the supplied maps. A generic alpha component identity handles naturality before
specializing the categories. A structural triangle eliminator keeps concrete derived-category
terms out of equality-elimination motives. Proved realization identities translate the bundled
component equation to the native system notation. Small realization records are locally
`implicit_reducible`, while large derived constructions stay locally irreducible. Both native
and bundled morphism-property instances are supplied explicitly. These interfaces avoid
expanding the concrete localization during matching and kernel checking. Transparency remains
respected. The neighboring projection modules' removal of competing semilinear instances is
used within this module; no exported instance declaration changes.

The node's `proof`, `proof_deps` and `proof_origin` now describe this argument. Its statement,
Lean attachment and other fields are unchanged.

## Proved and sorry left

Closed `WeilConjectures.SystemProjectionFormula.projection_triangle`
(node `lem-pur-system-projection-triangle-compatibility`): 1 of 1 original holes closed.
Holes added: 0. Split-off statements: 0. Holes left in the delivered module: 0.

The imported contraction theorem is an existing stated dependency; its existing proof
obligations are unchanged. No new axiom, unproved helper, arbitrary existence witness or
hollow definition is introduced.

The dependency cycle check passes. After profiling cleanup, the complete proof compiled in
44.3 seconds. The unused-section-variable linter is disabled only for the public theorem,
preserving its original separatedness binders. All source lines are at most 100 characters;
the delivered module contains no `sorry` or forbidden primitive. Delivery compilation and
preflight are performed by `deliver3.py`.

## No longer needed

The original dependency `lem-sf-composition-projection-mate` and its module
`Sheaf.SixFunctors.CompositionProjectionMate` are unnecessary for this proof. Its existing
strictly narrower dependency `lem-sf-triangle-projection-compositor-contraction` supplies exactly
the component equation needed, without the broader invertibility, naturality and associativity
conclusions. The item node records this direct dependency.

No existing Lean import was removed, and no module is withdrawn or claimed globally unreachable.
Other consumers retain their dependencies. The replacement remains within the same dependency
unit and preserves the unit route.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction is needed. The dependency uses bundled finite-type objects over
the field, whereas this statement uses unbundled schemes. The proof constructs that interface
explicitly. Its alpha word orders the proper and open compositors differently from
`triangleWord`; naturality relates the two orders.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
