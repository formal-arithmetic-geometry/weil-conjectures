## What changed

Proved `WeilConjectures.sfQcqsCompactSupport_finiteMates` in its existing module,
with its signature and public imports retained. Private helpers identify the ordinary
restriction comparison by its section formula, identify its derived comparison by
its universal cochain-unit normalization on K-injectives, and transfer the existing
perfect-quotient projection formula between the two scalar adjunction choices.
The ordered proper/open factorization then proves the stated finite comparisons.

Added proof-only imports of `SfCompleteDirectImageReduction`,
`ProEtaleRingSheafChangeAdjunction`, and `IntegralCoefficientPresentationComparison`
to reuse their proved normalization helpers. Updated the item's DAG proof and
proof dependencies to record this route. No shared definition or interface changed.

The proper-factor calculation applies to every ambient complex and every scheme
morphism. Its use here retains every original geometric and constructibility binder.
The argument also covers the zero input, empty schemes, identity morphisms and
exponent one: all the normalization identities and projection-formula statements
are universal, and the exponent is always n+1.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.sfQcqsCompactSupport_finiteMates`
(node `lem-qcqs-compact-support-finite-mates`).

No holes remain in the delivered module. No holes or split statements were added.
The full file compiled through lcompile.py in 29.4 seconds during profiling;
development profiling options were removed before delivery.
This proof uses the already stated `PurCompactSupport.openComparison_isIso` and
the existing perfect-quotient projection-formula proof infrastructure; it does not
claim to close their underlying dependencies.

## No longer needed

No original import or node was removed, and no module is withdrawn or pruned.
The finite-field/finite-Tor theorem `PurCompactSupport.reductionComparison_isIso`
and the later `integralCoefficientComparison` conclusion are not used. Only the
existing normalized open isomorphism and proper/open factorization from that
module are used. Completeness and Roos-limit assembly from the main theorem of
`SfCompleteDirectImageReduction` are not used; its already proved private
projection-formula and normalization helpers suffice.

## Where the brief, the DAG or earlier work was wrong

The item's proof step named no dependencies despite invoking a non-elementary
perfect-quotient projection formula and normalized proper/open comparisons.
Those dependencies now appear explicitly in the node. The missing glue was the
identification of the specified mates across the two existing scalar-adjunction
presentations; it is proved here, without another split or stronger hypotheses.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
