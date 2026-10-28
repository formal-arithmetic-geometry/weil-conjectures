## What changed

Replaced the hole in `binary_composition_realization` by a proof assembling both
endpoint equations. The support normalization reuses the proved inverse-coordinate
normalization in `FiniteSupportOriginComparison` and identifies its compositor by
`cartesianCompactSupportCompositor`. Private categorical helpers tensor this equation,
move the coefficient units by naturality, and paste the target square. The
restricted pullback compositor is identified before mapping through the concrete
coefficient equivalence; this keeps the kernel conversion small.
The pullback cancellation is first proved as an equality of natural
isomorphisms and then evaluated at the input. The final pasting is checked at
generic categories before coefficient specialization, and the conversion to
mapped isomorphisms is stated with the native endpoints.

Added `Sheaf.Paper.FinitePullbackCompositionRealization` for the unary pullback
composition calculation used before tensoring. This separates the exact-localization
coherence calculation from compact support, the supplied Cartesian triangle, and
both tensor endpoints. Existing public declaration signatures and target statements are unchanged.
The existing definitions and endpoint structure are moved verbatim into
`FiniteProjectionCompositionData`, publicly imported by the item module, to keep
the checking of the structure and its proof in separate compilations.
`binaryPullCast` uses morphism-indexed equality induction, with a proved
generic equality to its original `pCongr` map. This avoids comparing whole
derived functors during component conversion. Its three direct importers are
checked against the construction.

`iterationTensorComparison` factors its two existing maps through the explicitly
typed generic `unitTensorRealization`. The existing iteration proof uses a proved
private helper for this constructor; its public signatures are preserved.

The construction in `CartesianCandidateCompositor` is factored through its
existing generic core to avoid expensive concrete kernel conversions. Its
signature and specified map are unchanged. All four affected modules compiled
against the changed definition: `CartesianCandidateCompositor`,
`CartesianCandidateSiteSquare`, `CartesianCompactSupportCompositor`, and
`ProjectionCompatibleTriangleAssembly`. Those three consumer sources are unchanged.

All changed and new Lean modules compile through `lcompile.py` in import order.
The item compiles in 13.2 seconds; the slowest changed module is
`FiniteProjectionIterationRealization` at 50.7 seconds. The three existing direct
importers also compile: iteration-triangle pasting unchanged (38.3 seconds), the
adapted triangle square (25.6 seconds), and the binary square unchanged
(44.8 seconds). The unchanged verification copies are excluded from the packet.

## Proved and sorry left

The original module had one hole: `binary_composition_realization`. Its body now
proves both endpoint equations from the declared dependencies and the new unary
pullback lemma. Among the changed and new files, one hole is closed and one is added. This is a decomposition,
with zero net holes closed, rather than an unconditional proof of the entire item.

The sole new remaining hole is
`WeilConjectures.CompactSupportFiniteProjection.fixedPullRealization_composition`,
node `lem-sf-finite-pullback-composition-realization`. It concerns only unary
pullback composition in fixed coefficient coordinates. It has neither a support
functor nor tensor endpoints and is strictly the pullback part of the original
node's third step. Its docstring gives the exact localization and coefficient-unit
cancellation proof. No definition contains a hole; all private helpers are proved.

## No longer needed

No original import or dependency module is withdrawn. The proof uses the
inverse-coordinate support normalization already proved inside
`FiniteSupportOriginComparison`. Its public
`originSupportComparison_composition` is not applied; the proof uses the proved
private `fixedSupportComparison_composition_app` from that same module, avoiding
a second expansion and cancellation of its origin witnesses. The iteration module remains needed for
its explicit comparisons and the retained `iteration_realization_factors` theorem.
No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The plan's third step combines two distinct calculations: coherence of unary
pullback realization with the canonical left-derived compositor, and tensoring
and pasting that equation with support naturality. The new node isolates the
first calculation. Its statement is tested conceptually on identity morphisms,
zero inputs, empty schemes, and exponent one; these require exactly the same
functoriality and equivalence identities. No statement is disputed or weakened.

## Forced adaptations

`Sheaf.Paper.FiniteProjectionBinaryTriangleSquare` is unclaimed. Its original
`total_component_realization` fails against the changed `binaryPullCast` with:

```text
error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```

Its factor helper concludes with `pCongr`; the target comparison now uses
`morphismPullbackCongr`. Added the proved private
`scalar_factor_realization_morphism`, eliminating the indexing equality and
applying the unchanged original helper at reflexivity. Only the callee in
`total_component_realization` changes. Every existing signature is retained.
Its DAG proof records the new transport dependency. No hole is introduced.
The adapted module and its unchanged direct importer are checked together.
The exact change is documented in
`coord/changes/T3-BinaryPullCast-morphism-transport.md`.

## New nodes

`lem-sf-finite-pullback-composition-realization` realizes the unary pullback
normalization needed in the original node's third step, in the new module
`Sheaf.Paper.FinitePullbackCompositionRealization`. The original node's proof,
proof dependencies, and proof origin now describe the actual endpoint pasting.
The unchanged candidate construction and its consumers are documented in
`coord/changes/T3-CartesianCandidateCompositor-generic-construction.md`.
The existing candidate-constructor node records use of the generic core.

`def-sf-morphism-pullback-congruence` records the constructed equality transport
and its proved equality to the original `pCongr` in the new module
`Sheaf.SixFunctors.PullbackEqualityTransport`. No hole is added by either declaration.
The use in `binaryPullCast` is documented in
`coord/changes/T3-BinaryPullCast-morphism-transport.md`.

`def-sf-unit-tensor-realization` records the actual inverse-unit and tensor
construction in `Sheaf.Paper.UnitTensorRealization`, with no hole. The change to
its existing iteration consumer and its proof helper is documented in
`coord/changes/T3-FiniteProjectionIterationRealization-generic-construction.md`.

`def-sf-finite-projection-composition-data` records the relocated existing
constructions and endpoint structure in `FiniteProjectionCompositionData`. It
adds no mathematical claim or hole; all existing names and signatures stay the same.

`lem-sf-finite-projection-composition-source` records the proved source endpoint
in `FiniteProjectionCompositionEndpointProofs`. The remaining proved private
endpoint helpers are compiled beside it and imported only by the final proof.
This additional split adds no hole; it separates completed proof checks from the
last endpoint pasting.

## Related modules compiled before delivery

5 related module(s) compiled against this delivery by deliver3.py: 5 OK.

```json
{"capped": false, "direct": 4, "left_out": 0, "own": {"Sheaf.Paper.FiniteProjectionBinaryTriangleSquare": "04bc0bf21fab481f2b6c5a60d97440643d7c418f", "Sheaf.Paper.FiniteProjectionCompositionData": "b84f6ac78492c8084396f525ca5933ebd4d6c950", "Sheaf.Paper.FiniteProjectionCompositionEndpointProofs": "af492b9f12bd9f55d4fe1614d5260d1000b971bb", "Sheaf.Paper.FiniteProjectionCompositionRealization": "2679a057a2a33c83c7a779e9f19f37d38cbd40ea", "Sheaf.Paper.FiniteProjectionIterationRealization": "57fd55fdbf886ddbfb3e80122ca54a0be64ece16", "Sheaf.Paper.FinitePullbackCompositionRealization": "aa7d3a78edd5ed230d67a7b9118a181ec4a3c5b4", "Sheaf.Paper.UnitTensorRealization": "0c1a774656c204131b3b6c08c8cc876f56bebb6b", "Sheaf.SixFunctors.CartesianCandidateCompositor": "d83e2316f558cb611021434b2aa40f67ea4c79b9", "Sheaf.SixFunctors.PullbackEqualityTransport": "66aa1edc2431c14ffae77bf22cd8ea08fd4d5953"}, "results": {"Sheaf.Paper.FiniteProjectionBinaryIterationTrianglePasting": {"hash": "f704713d97e7a793c4a3e5cec389f7e4931c23ca", "status": "OK"}, "Sheaf.Paper.FiniteProjectionBinarySquare": {"hash": "6c3902bd17672dafe7eeed3a47aa806dbb6ee6bf", "status": "OK"}, "Sheaf.SixFunctors.CartesianCandidateSiteSquare": {"hash": "8a5ae29b4ee80cb57540b8353cc0d49f11f76ff8", "status": "OK"}, "Sheaf.SixFunctors.CartesianCompactSupportCompositor": {"hash": "f330e266c3295f90212e50d974d8a4a70f002e08", "status": "OK"}, "Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly": {"hash": "71b31f8d82dbd4557aba93076a67ba7f373f3c2f", "status": "OK"}}, "seconds": 71, "time": "2026-10-28T10:01:00+0800", "transitive": 1, "version": 1}
```

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
