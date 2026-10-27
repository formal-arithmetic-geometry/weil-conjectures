## What changed

The proof of `WeilConjectures.FrobeniusExchange.modelRationalScalar_existsUnique`
localizes the specified integral scalar isomorphism using the existing private
`localizedIso` theorem of `Sheaf.Paper.SfScalarExtensionComposition`. Its normalized
components determine it uniquely. The source and target cases use the existing
literal localization equalities. Private proved tensor-localization and
scalar-conjugation helpers replace expensive unfolded calculations in existing proofs.
The public statements, definitions and public imports are retained. Local folding
of localization and stage-beta data, with the existing stage-category cache exposed,
avoids repeated expansion during endpoint checks. The full candidate compiled in 34.6 seconds.

The node `def-weil-operation-exchange-coefficient-descent` records this proof and its
scalar-extension-composition dependency. The proof-context changes are recorded in
`coord/changes/H6-frobenius-exchange-proof-context.md`.

## Proved and sorry left

One of the seven original holes is closed:

- `WeilConjectures.FrobeniusExchange.modelRationalScalar_existsUnique`.

Six original holes remain, all attached to
`def-weil-operation-exchange-coefficient-descent`:

- `WeilConjectures.FrobeniusExchange.intrinsicCompactificationCoherence`.
- `WeilConjectures.FrobeniusExchange.intrinsicCompactificationComparison_refinement`.
- `WeilConjectures.FrobeniusExchange.pullback_linear`.
- `WeilConjectures.FrobeniusExchange.modelScalarMap_isIso`.
- `WeilConjectures.FrobeniusExchange.stageBeta_coherence`.
- `WeilConjectures.FrobeniusExchange.stageExchange_compatible`.

No holes are added and no statements are split off.

## No longer needed

No public imports, declarations, nodes or modules are withdrawn. Existing geometric
and coefficient dependencies remain needed by the constructions and retained obligations.
The rational comparison uses the existing general localized-isomorphism theorem,
avoiding a separate construction for each coefficient embedding.

## Where the brief, the DAG or earlier work was wrong

The rational comparison requires only localization of the specified integral isomorphism;
its general existence and normalization calculation already occur in
`SfScalarExtensionComposition`. Large chosen tensor and derived-functor constructions
must remain folded while their normalization equations are used. Isolated proofs of
pullback linearity and intrinsic compactification coherence were also developed, but
have not yet passed the full item compile and are not counted as delivered proofs.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
