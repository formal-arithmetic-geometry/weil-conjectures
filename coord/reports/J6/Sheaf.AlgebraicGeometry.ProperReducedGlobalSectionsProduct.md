## What changed

Proved `AlgebraicGeometry.Scheme.proper_reduced_globalSections_product` with its signature
unchanged. The proof obtains Noetherian topology from properness, applies the existing
`Scheme.GlobalSectionsBijective.of_isAlgClosed` to each clopen connected component,
and constructs the product equivalence by the sheaf gluing axiom. Restriction identities
prove compatibility with the actual scalar map and the required pointwise germ formula.
The empty scheme is included, using the empty-cover sheaf instance.

Validation: the final module compiled cleanly through `lcompile.py` in 5.2 seconds,
with no errors or warnings. The theorem signature was checked byte-for-byte against
the original; the delivered file has zero `sorry` occurrences.

Added proof-only imports `WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective` and
`WeilConjectures.Mathlib.Topology.NoetherianSpace`. Updated the item's DAG proof,
proof dependencies, and proof origin to this route. No definitions, existing signatures,
public imports, other modules, or target statements changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.proper_reduced_globalSections_product`
(node `lem-weil-pbc-proper-reduced-algclosed-global-sections-product`).
Added zero holes; split off zero statements. No `sorry` remains in the delivered module.

## No longer needed

Removed these proof-only imports:

- `Sheaf.AlgebraicGeometry.Coherent`
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Scheme`
- `WeilConjectures.Mathlib.RingTheory.Artinian.Ring`
- `WeilConjectures.AlgebraicGeometry.Coherent`
- `WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`

The proof no longer directly needs `pqf-def-coherent`,
`pqf-lem-coherent-ft-locnoeth`, or `lem-pc-coherent-hi`:
Noetherian topology gives finite clopen components directly, and the existing connected
scalar theorem supplies their section rings. The finite-dimensional partition-size bound,
maximal clopen partition, and extension-by-zero quotient argument are unnecessary.
`lem-pc-scheme-connected-iff-idempotents` and
`lem-pc-alg-closed-reduced-algebra-no-idempotents-dim-one` are no longer direct dependencies;
the connected-scheme scalar theorem encapsulates those algebraic steps.
Withdrew the four obsolete top-level `tool_uses` approvals for
`pqf-lem-coherent-ft-locnoeth`, `lem-pc-coherent-hi`,
`lem-pc-scheme-connected-iff-idempotents`, and
`lem-pc-alg-closed-reduced-algebra-no-idempotents-dim-one`.
Some removed modules remain transitively imported by the existing library theorem;
this delivery claims no withdrawal of those modules from the entire targets' closure.

## Where the brief, the DAG or earlier work was wrong

The old proof plan was valid but longer than necessary. The existing library declaration
`Scheme.GlobalSectionsBijective.of_isAlgClosed`, attached to `lem-sc-global-functions`,
already applies to every proper reduced connected scheme, with no curve or dimension
hypothesis. Its declaration is stronger than that node's curve-specialized prose.
The source of the shorter component argument is Stacks Tag 0BUG, proof of (2)-(3),
which explicitly uses Noetherian topology to make the connected components open.
The unit route is unchanged; this auxiliary node realizes no unit step of its own.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
