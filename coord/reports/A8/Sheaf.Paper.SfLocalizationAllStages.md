## What changed

Proved `WeilConjectures.sfLocalizationExceptionalLimit` by transporting the defining
Roos triangle of the exceptional value along its specified finite reduction
comparisons. The proof transports the product, conjugated quotient transitions,
first-map projections and connecting arrow explicitly. No statement or definition
was changed.

The retained attempt also developed a generic Weil-lifting helper. It compiles,
but its application still requires the coefficient-specific Frobenius comparisons
and exactness interfaces. It is preserved in sandbox notes and omitted from the
Lean delivery because the remaining theorem does not yet use it.

## Proved and sorry left

Closed: `WeilConjectures.sfLocalizationExceptionalLimit` (one of three original holes).
Added: none. Split off: none. This is a partial delivery, not a completed proof of
the all-stage proposition.

Remaining: `WeilConjectures.sfLocalizationAllStages` and
`WeilConjectures.sfLocalizationAllStages_weil`, both attached to
`prop-sf-localization-all-stages`.

The completed limit proof uses completeness of the specified exceptional value;
it does not establish existence of a localization package. The first remaining
hole still needs construction of the finite, integral, rational and common-stage
packages, including the recorded comparisons and quantitative Tor intervals.
The second still needs the geometric-fibre specialization and the normalized
Frobenius comparisons before the generic fixed-pair argument can apply.

## No longer needed

No original import, node or module was pruned: the two remaining all-stage proofs
still require their planned dependencies. The unused private Weil helper and its
new proof-only import of
`WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction` were omitted from
this delivery. No new proof obligations were introduced.

## Where the brief, the DAG or earlier work was wrong

No statement dispute was found. The retained exceptional inverse-limit proof is
compatible with the current sources. Searching the source library found a proved
abstract recollement API, but its use still requires transport to the actual
coefficient functors and constructible subcategories; it does not by itself prove
the two remaining statements.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
