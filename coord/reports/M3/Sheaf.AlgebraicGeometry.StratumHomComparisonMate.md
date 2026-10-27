## What changed

The item now constructs the two normalized natural stratum Hom isomorphisms by the
parametrized tensor-Hom adjunction, transported projection isomorphism, ordinary adjunction
and actual supplied exceptional adjunction. It proves the boundedness witness by the source
library's tensor-left adjunction cohomological bound. From the exact comparison equality it
proves every conditional invertibility assertion by functoriality and cancellation.

The equality of the two normalized evaluation pairings is isolated in
`Sheaf.AlgebraicGeometry.StratumHomPairingIdentity`. It assumes the already normalized
isomorphisms and the boundedness witness, and asserts only the displayed arrow equality.
It is strictly a part of the original argument: it neither constructs those isomorphisms,
proves the witness, nor proves any conditional invertibility clause. The item combines these
parts by actual Lean proofs, rather than applying a renamed copy of its original conclusion.

`Sheaf.AlgebraicGeometry.StratumHomComparisonData` holds the original canonical definitions
so the new equality lemma can use them without importing its consumer. The original module
publicly re-exports them, preserving the declaration names and transitive public imports.
Explicit result types on derived maps/adjunctions and an irreducible generic normalization
predicate avoid repeated reduction of large derived constructions. The ordinary adjunction
bodies are unchanged. Unfolding the generic predicates gives exactly the original formulas.
There is no data selected from an unproved existence statement.

The earlier retained all-in-one proof attempt was checked first as instructed. It failed at
native tensor comparison, transported projection specialization and the final mate assembly;
it was never a validated zero-hole proof. Its scratch files are retained outside the packet.
The present extraction separates an uncompleted mathematical step, rather than splitting a
completed proof merely to avoid the compile limit. All three modules compile through lcompile.py --all. A whitespace warning in the item was
then corrected; deliver3.py performs the final compilation, axiom probes and packet checks.

## Proved and sorry left

Closed original hole:
`AlgebraicGeometry.StratumHomComparisonMate.stratumHomComparisonMate`
(node `lem-sf-stratum-hom-comparison-mate`), from the one split equality theorem.
The item contains zero remaining textual holes. Both normalized isomorphism constructions,
the boundedness argument and the deduction of all seven IsIso clauses have complete proofs.

Added hole:
`AlgebraicGeometry.StratumHomComparisonMate.normalizedComparisonIdentity`
in `Sheaf.AlgebraicGeometry.StratumHomPairingIdentity`
(node `lem-sf-stratum-hom-pairing-identity`), with its source and complete evaluation/mate
argument in the docstring. Its proof is exactly `:= by sorry`.

This is a decomposition: one upper hole closed and one strictly smaller equality hole added,
net zero holes closed. The new data module has zero holes; none of its definitions is hollow.

## No longer needed

The following original proof-only imports are removed from this item's proof:

- `Sheaf.Algebra.Homology.BoundedAboveRHomHyperExt`,
  `lem-per-bounded-above-rhom-hyperext`: the tensor-left adjunction supplies the needed bound.
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`,
  `lem-sf-ringed-derived-closed-symmetric-monoidal`: native constant-coefficient adjunctions
  construct the normalized Hom isomorphisms.
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`,
  `lem-sfb-ringed-derived-monoidal-comparisons`: the remaining pairing step uses the native
  tensor comparison and the immersion projection-comparison square.
- `Sheaf.Paper.ProjectionMateExact`, `lem-weil-pbc-ringed-projection-mate-exact`:
  ordinary unbounded native adjunctions and the specified D+ mate suffice.

No module is withdrawn or deleted. Original public imports are retained transitively through
the data module, including the unit's stratum ambient Hom statement. The split equality
node still records the native projection, fixed-mate, exact-square, pullback coherence,
closed-immersion normalization and exceptional counit dependencies it needs. Those nodes
are not pruned merely because their remaining consumer proof is postponed.

## Where the brief, the DAG or earlier work was wrong

No statement dispute. The original planned hyper-Ext argument and general ringed-site
construction are unnecessary for these fixed-scalar derived categories. The unit route is
preserved: construct the normalized stratum isomorphisms, compare evaluation pairings using
the specified ordinary and exceptional counits, and infer invertibility. Zero current Lean
importers has not been used to withdraw any unfinished DAG dependency.

The new pairing statement was checked on zero P, zero M and the identity immersion. All
comparisons reduce to the corresponding zero arrows or the counit-normalized internal Hom
identity. For arbitrary inputs, both sides have the same fixed source and target and use
the given canonical mate, Delta and gamma; no independently chosen comparison is substituted.

## New nodes

`def-sf-stratum-hom-comparison-data` records the extracted, fully constructed canonical
comparison maps and normalization predicates. It introduces no postponed theorem or data.

`lem-sf-stratum-hom-pairing-identity` records only equality of the two evaluation-normalized
composites. Its proof plan spells out uncurrying, the fixed mate counit, compatibility of the
projection square, the exceptional counit, and injectivity of transposition.

Definition/interface change record:
`coord/changes/stratum-hom-normalization-interfaces.md`.
It contains the old and new declarations verbatim and the consumer audit. No other group's
module is adapted. The target signatures are untouched; their definition-meaning review is
reopened by the predicate/interface change.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
