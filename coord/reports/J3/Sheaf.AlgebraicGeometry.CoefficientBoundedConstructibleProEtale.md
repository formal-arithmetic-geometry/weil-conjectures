## What changed

Restored Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale verbatim from
its assigned quarantine archive to the active path named in coord/rework.tsv. The
restored definition AlgebraicGeometry.ProEtale.coefficientBoundedConstructibleProEtale
retains the original coefficient universes, qcqs scheme hypotheses, affine-local
constructibility in every cohomological degree, and one ordered finite interval of
nonzero cohomology. Both public imports and the existing generic interface are kept.
This is a concrete restoration of an absent module, not a rebase or withdrawal.

The module compiled cleanly on the server in 3.1 seconds, together with a temporary
unchanged copy of the already-landed affine-constructibility dependency (3.5 seconds).
The initial standalone check stopped because that dependency has no published object
file yet. The temporary dependency is excluded from the delivery. A separate importer
check then compiled in 3.0 seconds and verified the expected full-subcategory inclusion
and all four generic reexports. #print axioms of the coefficient predicate reported
only propext, Classical.choice and Quot.sound. Temporary check sources are excluded.

Reviewed Stacks proetale.tex, definition-constructible (Tag 09AJ), the blueprint unit,
the node, and the actual standard-cohomology definition. The restoration preserves
the discrete constant-ring presentation without asserting new equivalences to generic
internal modules. Empty schemes, zero coefficients, zero complexes, arbitrary ordered
bounds and independently larger coefficient universes retain their existing meaning.
No arbitrary witness is chosen from an unproved existence theorem.

The consumer scan includes every archived direct importer and the finite-Tor comparison
consumer. Their declarations and public interfaces require no adaptations: this is a
byte-for-byte restoration. Change record with consumer table:
coord/changes/J3-restore-coefficient-bounded-constructible.md.

## Proved and sorry left

Original explicit holes: 0. Holes closed: 0. Holes added: 0. Holes remaining in the
item: 0. There is no split or new theorem. The only item declaration is the explicit
predicate AlgebraicGeometry.ProEtale.coefficientBoundedConstructibleProEtale,
attached to sk-def-sfb-bounded-constructible. It contains no sorry, no unproved witness
selection and no hidden definition field. This delivery makes no claim to have proved
the separately imported generic weak-Serre triangulatedness theorem.

## No longer needed

None. No import, declaration, node, module, proof dependency or unit step is removed.
The quarantine archive remains intact. The node's Lean attachment and proof plan
are unchanged. LeanFinder found only ambient derived-category bounds; Loogle returned
ordinary bound/ordering lemmas; the Mathlib grep for boundedConstructible and
CoefficientBoundedConstructible found no direct replacement. The existing definition
is the required interface, so no replacement construction or new node is introduced.

## Where the brief, the DAG or earlier work was wrong

The assigned item is a zero-hole restoration after a cluster build quarantine.
Its absence from lean/ did not mean withdrawal. The archive compiles against the
already-repaired current affine-constructibility dependency without changing its body.
No error in this definition's statement or data was found. The initial missing object
file is a published-build limitation, resolved for verification by compiling the current
dependency unchanged in the sandbox; it is not a new proof obligation or a tool bypass.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
