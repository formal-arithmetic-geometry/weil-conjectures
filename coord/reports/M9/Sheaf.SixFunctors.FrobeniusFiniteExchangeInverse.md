## What changed

Proved `WeilConjectures.FrobeniusExchange.frobenius_finite_exchange_inverse` in
`Sheaf.SixFunctors.FrobeniusFiniteExchangeInverse`. Existing public signatures,
definition bodies, attributes and public imports are unchanged.

Six proved private helpers assemble the argument. `equivalenceOfInverse` checks
the categorical inverse-functor assembly, and `intrinsicPullbackEquivalence`
constructs the inverse pullback using the existing intrinsic derived composition
and identity isomorphisms. `tensorExchangeIso` applies the existing fully faithful
mate theorem and transports through the recorded pullback coordinate changes.
`inverseComposite` proves cancellation of three factors with their specified
inverses. `transportAssembly` applies this to arbitrary scheme compactifications,
and `finiteTransport` specializes that proved result to the retained geometric
compactification and its specified comparison. The last two helpers keep the
large comparison construction out of the final kernel conversion.

The main proof applies the mate argument to the direct and proper Frobenius
arrows and composes with the canonical open-square isomorphism. The chosen
compact isomorphism has the published forward transformation literally as its
hom field and the composite construction's inverse. The two requested inverse
formulas follow from these actual isomorphisms. No replacement exchange is
chosen. The complete proof compiled in 27.3 seconds before removing an unused
experimental helper; final delivery validation checks the cleaned version.

Updated the existing node's proof and proof dependencies to describe this route.
No new public declarations, modules, nodes or holes are introduced.


## Proved and sorry left

Closed one hole:
`WeilConjectures.FrobeniusExchange.frobenius_finite_exchange_inverse`
(node `lem-weil-frobenius-finite-exchange-inverse`).

Added zero holes. Zero `sorry` remain in the delivered module. All six private
helpers have complete proofs. The existing declared dependencies may still
have their own holes; these are not new holes in this delivery.

The proof treats arbitrary ambient unbounded complexes. Empty schemes and zero
objects require no exception: all equivalence and natural-isomorphism arguments
apply to them. Identity maps and identity open parts specialize the same
composition formulas. The comparison is evaluated only on the retained origin
witness and its existing pulled witness, so no independence of compactification
or new origin witness is asserted.

## No longer needed

Removed private imports:

- `Sheaf.AlgebraicGeometry.IsomorphismDerivedPullbackEquivalence`:
  `lem-weil-isomorphism-derived-pullback-equivalence` is unnecessary for this
  proof. The composition/identity API already gives the intrinsic equivalence
  directly, without coefficient-prime-unit assumptions.
- `Sheaf.AlgebraicGeometry.FrobeniusOpenSquare`:
  `lem-trf-frobenius-open-square` is unnecessary here. The exact Galois open
  square is already provided by `lem-weil-frobenius-square-cartesian` and used
  in the retained `frobeniusFiniteOpenExchange` definition.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  no new application of `lem-weil-pbc-comparison-pullback` is required. The
  existing `pulledCompactOrigin` construction already retains the witness.

No separate invocation of `prop-compactification-coherence-detailed` is needed
in the proof: `frobeniusFiniteComparison` is already the specified isomorphism.
The comparison and witness constructions still depend on the corresponding
coherence results transitively; these modules are not withdrawn or claimed
unnecessary to the whole library. All public imports are preserved. Removed
obsolete direct proof dependencies and their corresponding existing tool-use
entries from the node; the remaining tool-use entry keeps its original order.
No Lean modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The planned proof was
longer than needed: the intrinsic pullback composition and identity API gives
an equivalence directly; the statement already supplies the canonical open
exchange and witnessed compactification comparison as actual isomorphisms.
Thus no new boundedness or witness-preservation proof is necessary in this
module. The unit statement and its realized proof steps are unchanged.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
