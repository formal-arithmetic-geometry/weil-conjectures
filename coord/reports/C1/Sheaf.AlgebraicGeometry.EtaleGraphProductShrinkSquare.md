## What changed

Replaced the proof hole in `AlgebraicGeometry.Etale.etaleGraphProductShrinkSquare`
with a componentwise proof from canonical derived open composition and the horizontal
pasting law of the particular normalized proper/open exchange family.

The private helpers construct a transported open compositor, prove the open rectangle
identity, and prove exchange cancellation for arbitrary coefficient objects and an
arbitrary input morphism. The final theorem specializes that morphism to the inverse
composite graph triangle and uses naturality of the common final proper compositor.
The target signature and every existing definition are unchanged.

Added the proof-only `import all
Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons` to reuse its proved
private canonical open-compositor identification and concrete formalism. Only these
arbitrary-scheme construction/coherence helpers are used; none of its public theorems
with Noetherian hypotheses is applied. This is a tool use, not a replacement of the
unit route. The import-direction and DAG checks find no dependency path back to this item.
Updated only the item's node proof, proof dependencies and proof origin.
The complete file compiled in 34.5 seconds during profiling. Profiling options were
removed for the final delivery check. Extracting the selected horizontal law once
and keeping the large maps locally irreducible reduced checking time; all such
attributes are local and no shared interface changes.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Etale.etaleGraphProductShrinkSquare`
(node `lem-pur-etale-graph-product-shrink-square`).
Added zero holes; zero holes remain in the delivered module. No split-off statements.
All private helper theorems have complete proofs.

## No longer needed

No original import was removed. The public shrink-word import remains necessary for
the unchanged statement and its canonical maps.

The original planned proof dependencies `lem-pur-etale-graph-product-ambient-pasting`,
`lem-cbc-extension-zero-composition`, and
`lem-amb-natural-transformation-whisker-exchange` are not direct premises of the proof.
The retained product-geometry node and the shrink-word module supply the map
equations and instances. Derived open associativity is obtained through the existing concrete
formalism rather than descending the sheaf-level coherence theorem again. Naturality
and functor laws handle the whiskering calculation componentwise. The proper ambient
pasting theorem is not needed for this Q-only equation.
These are removals from this node's proof plan; no shared module is withdrawn, and
other consumers and the necessary public import closure are preserved.

## Where the brief, the DAG or earlier work was wrong

The DAG overestimates the needed ambient theory: the Q equation follows from horizontal
pasting and derived open associativity alone, after specializing a general input
morphism to the graph triangle. No false statement or definition repair was found.
The proof handles both selected rows uniformly after a proved component formula; it
does not replace the original hole by two fixed-row holes. Empty and identity opens
satisfy the same functorial and cancellation equations, with no extra hypotheses.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
