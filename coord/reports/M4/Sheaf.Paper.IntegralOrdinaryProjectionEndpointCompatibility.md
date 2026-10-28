## What changed

Repaired `WeilConjectures.integralOrdinaryProjection_endpointCompatibility` in
`Sheaf.Paper.IntegralOrdinaryProjectionEndpointCompatibility`. The old theorem
asserted compatibility of arbitrary independently chosen endpoint isomorphisms.
The replacement constructs an isomorphism of the two specified projection arrows.
Its proof removes the invertible open factor, applies the scalar projection mate
square using `scalarPull_tensor_coefficient_coherence` and the existing proved
`quotient_proper_mate`, realizes the finite proper projection, and restores the
open factor. Existing private realization helpers are reused with proof-only
`import all`; no source-library declaration is changed. A separate theorem records
the final normalization of the two realized finite inputs. Instance selections and
exclusions are scoped locally to the private proofs.

Adapted the proof of `integralOrdinaryProjection_endpointComparisons` in
`Sheaf.Paper.IntegralOrdinaryProjectionArrowComparison` to extract the two endpoint
isomorphisms and the square equation from that arrow isomorphism. Both declarations
in that consumer keep their signatures and visibility. Updated both affected DAG
proof records. The unit's proper/open and finite-realization route is preserved.
Change record: `coord/changes/M4-integral-ordinary-projection-endpoints.md`.

## Proved and sorry left

Original item: one hole, in
`WeilConjectures.integralOrdinaryProjection_endpointCompatibility`.
The original assertion is false and has been corrected, rather than proved as
written. The corrected construction is proved from the existing scalar mate and finite
realization lemmas, together with one strictly smaller input-normalization statement.
The item hole is replaced by one new hole in
`WeilConjectures.integralOrdinaryProjection_reducedInputsNormalization`, in the new module
`Sheaf.Paper.IntegralOrdinaryProjectionEndpointNormalization`. Thus this is a
decomposition: one item hole closed, one lower hole added, net zero. It is not counted
as a complete proof of the original hole. No other `sorry` remains in the three
delivered modules. The consumer's previously proved statements remain proved with
identical types.

## No longer needed

Removed the public import of
`Sheaf.Paper.IntegralOrdinaryProjectionEndpointIsoData`; neither this proof nor its
adapted consumer uses `integralOrdinaryProjection_endpointIsoData` or
`IntegralOrdinaryProjectionEndpointData`. The endpoint-data module and its node
`lem-sf-ordinary-projection-endpoint-iso-data-q2` are unnecessary on this route.
No files are withdrawn and no adopted source declaration is removed.

The old planned dependencies
`lem-pbc-completed-scalar-projection-perfect-iso`,
`lem-weil-pbc-ringed-exchange-tensor-coherence`,
`lem-sf-open-projection-factor-coefficient-change`, and
`lem-sf-projection-scalar-square` are not used by this proof. They are replaced by
the existing quotient proper mate, scalar-pull tensor coherence, and the generic
projection mate square. Their modules may still serve other branches of the DAG.
These planned nodes correspond to `Sheaf.Paper.CompletedScalarProjectionPerfectIso`,
`Sheaf.Paper.RingedExchangeTensorCoherence`,
`Sheaf.Paper.OpenProjectionFactorCoefficientChange`, and
`Sheaf.Paper.ProjectionScalarSquare`. This removes their explicit edges from this
node; it does not withdraw them or assert that their other consumers are obsolete.
In particular, `ProjectionScalarSquare` remains imported transitively through
`FiniteProjectionOperationPresentation` and `ProjectionFiniteReduction`; that
module is retained.
The finite proper projection presentation, finite compact-support projection
map, and integral coefficient data remain needed.

## Where the brief, the DAG or earlier work was wrong

The old endpoint-compatibility statement was already marked STATEMENT-DISPUTED.
Its data structure imposes no relation between its source and target fields, so
its universal commutativity assertion is false: on a nonzero identity projection,
change the target isomorphism by minus identity with odd residue characteristic.
The hypotheses still hold and the commutative square fails. The blueprint asks
for compatible comparisons to exist; it does not assert compatibility of arbitrary
choices. The corrected statement constructs the required arrow isomorphism,
and the consumer's original existential statement follows without any weakening.
Earlier splitting did not establish this construction. The scalar mate and finite
realization lemmas already exist and are used here. The final input normalization
is isolated as one new, strictly smaller obligation: it has no completed projection
arrow, proper scalar mate or open scalar comparison in its conclusion. It only
transports the finite projection inputs along the existing finiteReductionIso.
The generic naturality and coordinate-equation proofs compile, but specializing and
composing their native derived-category instances repeatedly exceeded the kernel/time
limit. Attempted fixes included canonical instance selection, boxed input isomorphisms,
abstract coefficient helpers, an irreducible arrow wrapper with explicit equality
lemmas, and normalizing the proper/open inputs before realization. The remaining
statement records just the final finite-input transport, with its full proof in words;
the main theorem combines the actual scalar and realization steps in Lean.

## Statement corrected

Old statement: every pair of endpoint isomorphisms in
`IntegralOrdinaryProjectionEndpointData` satisfies the projection square. Its two
fields are independent, so the target-automorphism counterexample above applies.
The current blueprint, `sk-thm-sf-pf-adic.proof.md`, proper projection reduction
paragraph, says that reduction identifies the actual canonical projection with
the torsion projection. The replacement proves this as an arrow isomorphism.

The original DAG has no nodes listing this item in `stmt_deps` or `proof_deps`;
its Lean consumer was missing that dependency in the metadata. The adapted
`lem-sf-ordinary-projection-endpoint-comparisons` now cites this item and holds:
take the left and right isomorphisms of its constructed arrow isomorphism.
The consumer's complete existential statement and the later reduction comparison
are unchanged. No unit statement or target statement is corrected.

## New nodes

`lem-sf-ordinary-projection-reduced-input-normalization-m4`, realized by
`WeilConjectures.integralOrdinaryProjection_reducedInputsNormalization` in
`Sheaf.Paper.IntegralOrdinaryProjectionEndpointNormalization`: transport between
the realized finite coordinate projection at the pbc scalar inputs and the realized
finite native projection at the normalized scalar inputs. One named theorem hole
remains there. This uses only input naturality and the coordinate defining equation;
it is strictly part of the full scalar-reduction comparison.

Validation: `lcompile.py --all` compiled the normalization module (8.0 s), item
(21.9 s), and adapted consumer (7.1 s), in import order. The consumer's two
signatures remain verbatim. The final delivery preflight checks the completed packet.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntegralOrdinaryProjectionArrowComparison": "cede513105f39988dd089a53d8d7309d2c110c28", "Sheaf.Paper.IntegralOrdinaryProjectionEndpointCompatibility": "87f4aa8571607f9e91e7f3b875058840abf677ed", "Sheaf.Paper.IntegralOrdinaryProjectionEndpointNormalization": "3457f3bf28dd5b911ad5a18bc166894290dd5b57"}, "results": {}, "time": "2026-10-28T12:19:53+0800", "transitive": 0, "version": 1}
```

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
