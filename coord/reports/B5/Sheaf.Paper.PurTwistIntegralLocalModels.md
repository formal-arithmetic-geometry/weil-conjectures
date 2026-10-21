## What changed

Proved the integral scalar-extension local models using the completed coefficient
pushout, scalar-extension local bases, and ordinary finite quotient comparison.
All helper constructions and lemmas are private to the item module. The public
statement and all definitions it uses are unchanged. No new modules or public
statements are introduced.

The finite comparison is proved from the sectionwise uniformizer-adic completion
and its evaluation kernels. Its scalar-extension adjunction identifies maps into
finite-level modules with maps linear over the completed coefficient ring.
Nonvanishing follows by evaluation at a point on a covering member.

Change record: `coord/changes/B5-pur-twist-integral-local-proof.md` documents
the private helper commands requested by preflight. No consumer is adapted.

Validation: the complete module compiled remotely in 30.0 seconds without
warnings. `#print axioms AlgebraicGeometry.Scheme.purTwistIntegralLocalModels`
reported exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.purTwistIntegralLocalModels` (one original hole).
Added: none. Remaining in this module: none.
The proof obtains its covering family directly from the given rank-one hypothesis.
It does not claim to close holes in imported modules.

## No longer needed

This proof needs pro-etale unit local models, exactly as its statement requests.
It does not need the stronger finite etale trivializations, geometric stalk
finiteness, constructibility, or derived support assertions described in the old
proof plan. Accordingly its direct proof dependencies no longer include
`lem-pur-twist-coefficient-comparison`, `lem-pur-twist-root-local-models`,
`lem-weil-pbc-constant-completion-equivalence`,
`lem-weil-proetale-weakly-etale-localization`,
`lem-weil-pbc-etale-cover-geometric-point-lift`,
`lem-weil-proetale-constant-sheaf-stalk`,
`lem-weil-valued-dvr-finite-quotients`,
`def-weil-finite-torsion-constructibility`, `def-weil-cohomological-support`,
or `def-weil-constructible-subset`.
This is local dependency pruning; these nodes may remain needed elsewhere.
No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old plan proved several assertions absent from the actual local-model
statement. Pro-etale trivializations suffice for both displayed covering clauses.
For the finite comparison, the available general constant-completion equivalence
uses a single universe for site objects and morphisms, while this site has
objects in `Type (u+1)` and morphisms in `Type u`. The proof instead reuses the
proved continuous-section and completion helpers at the actual site universes.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
