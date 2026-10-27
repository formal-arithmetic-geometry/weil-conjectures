## What changed

Implemented `AlgebraicGeometry.Etale.resolution_section_cocycle_sheafification`
without changing its statement, existing definitions, or imports. Updated its existing
node's proof and proof origin to describe the direct cycle computation, retaining the
same proof dependencies. Five proved private helpers establish the cycle projection,
its evaluation formula, the ordinary adjunct formula, the sheafification adjunction
identity on cycles, and the component formula for the sections comparison.

The proof represents the section class by a cycle. The two cycles agree after their
monomorphic inclusions: the single-complex comparisons cancel, shift comparisons have
the prescribed middle component, and naturality of `normalizationSectionsIso` identifies
the generator with the ordinary adjunction unit. The sheafification unit and counit
then send this cycle to its sheaf homology class. Finally, the proof postcomposes with
the two existing inverse resolution comparisons. All cycle and sheafification identities
are proved before evaluating or postcomposing with the resolution comparison. Local
irreducibility keeps the cocycle comparison and chain evaluation folded outside their
explicit formula calculations. Evaluated identities are composed directly to avoid
equality transports through the full category expressions.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.resolution_section_cocycle_sheafification`
(`lem-weil-pbc-resolution-section-cocycle-sheafification`).

No holes added, no split-off statements, and no `sorry` remains in the delivered module.
The existing imported declarations are retained.

## No longer needed

None. Both public imports are required by the unchanged statement. No node or module
is withdrawn, and the existing proof dependencies and unit route are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The ordinary cycle calculation can be completed
using Mathlib's chosen left homology data and their projection identities; it requires
no further split of this obligation.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
