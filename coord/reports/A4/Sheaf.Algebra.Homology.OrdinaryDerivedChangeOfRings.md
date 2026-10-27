## What changed

Proved `ModuleCat.nonempty_ordinaryDerivedChangeOfRings` in the assigned module.
The proof constructs the ordinary cochain universal pair from the existing K-flat
resolving-class theorem, transfers pointwise universality from homotopy complexes,
and derives the scalar-extension tensor isomorphism in two variables. The proved
`ofLaxSquare′` coherence construction supplies the oplax structure; invertibility
of its maps gives the required strong monoidal structure and both normalizations.
All additional helpers are private and proved. All existing public signatures,
definition bodies and public imports are preserved. The docstring and the attached
node's proof route now describe the direct ordinary-module argument; the node's
previous generic ringed-site steps are retained for its generic declarations.

Private proof imports add ordinary K-flat invariance, K-flat scalar extension,
the resolving-class theorem, initial-functor limit transport, monoidal-square
coherence, the derived localization unit, and two-variable derivability.
No new public declaration, definition repair or consumer adaptation is needed.
Preflight requires a record for the private helpers' section-variable commands:
`coord/changes/A4-ordinary-derived-change-of-rings-private-contexts.md` records
the unchanged interface and the two unchanged consumers. The helper contexts end
before the existing public theorem; they introduce no public instance or notation.

## Proved and sorry left

Closed 1 of 1 original holes:
`ModuleCat.nonempty_ordinaryDerivedChangeOfRings`
(node `lem-pur-derived-change-of-rings`).

Added 0 holes; split off 0 statements. The assigned module has 0 remaining
`sorry` occurrences. This is a proof from existing library declarations, including
the existing resolving-class theorem, rather than a replacement statement or a
new assumption. Every private helper is proved.

## No longer needed

No existing import, node or module is withdrawn. The punctual-site equivalence
and transport construction proposed by the old theorem docstring is unnecessary:
the ordinary-module K-flat APIs already supply the universal pair in the required
Hom universe. The generic ringed-site module remains publicly imported because
it is an existing compatibility interface and remains needed by other consumers.
The node's old generic proof dependencies therefore remain recorded. No source
library declaration or dependency is removed.

## Where the brief, the DAG or earlier work was wrong

The existing node described only the generic ringed-site construction, whereas its
current Lean attachment also includes the ordinary-module strong monoidal pair.
Added the ordinary proof steps without changing the node statement or any Lean
signature. The original punctual-site route is longer than the direct ordinary
K-flat construction. Existing general derived-monoidal functor interfaces fix a
larger Hom universe and cannot simply be instantiated at these endpoints; the
universe-polymorphic two-variable localization and square-coherence APIs avoid
that mismatch. Their elementary interface and limit-cone glue is proved locally.
The use of `ofLaxSquare′` needs counit isomorphisms only on K-flat models; it does
not assert that the counit is invertible on arbitrary complexes.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
