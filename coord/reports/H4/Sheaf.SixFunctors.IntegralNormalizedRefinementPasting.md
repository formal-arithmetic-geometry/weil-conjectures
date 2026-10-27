## What changed

Replaced the sorry in
`WeilConjectures.IntegralSystemRealization.integralNormalizedRefinementPasting`
by a complete Lean proof from the existing `completedShriekRefinementLaws` and the
smaller reverse-map comparison `integralRefinementTransposeRealization`.
The proof derives actual inverse maps, their identity and composition laws,
conjugation under total limit, integral identities through the faithful inclusion,
and the outside-factor formula by cancellation. No theorem signature changed. The unused-variable linter is disabled only around
this theorem because its unchanged statement names a lambda index used only implicitly.

Moved the ten existing word/context/map/instance constructions verbatim into the new
`Sheaf.SixFunctors.IntegralNormalizedRefinementData` and publicly reexported them in
the original module. The new comparison module imports the data without an import cycle.
No source-library module was edited. The original node's prose statement and stmt_deps
are unchanged; its Lean declaration list now owns only the theorem, and the new definition
node records the relocated data used by the proof.

The three delivered modules compile individually in less than 60 seconds. The final
main proof compiled in 14.3 seconds before its narrowly scoped linter adjustment;
the delivery checks revalidate the complete packet and its axioms.

Change record: `coord/changes/H4-integral-normalized-refinement-reduction.md`.

## Proved and sorry left

Closed one original hole:
`WeilConjectures.IntegralSystemRealization.integralNormalizedRefinementPasting`
(node `lem-sf-integral-normalized-refinement-pasting`). Its proof body is complete.

Added one hole:
`WeilConjectures.IntegralSystemRealization.integralRefinementTransposeRealization`
(node `lem-sf-integral-refinement-transpose-realization`). It is the whole proof of
one public theorem in its own module, with its source and proof in words. This statement
compares a single reverse refinement with its actual open-unit-normalized integral mate;
it has no F, rho or r and asserts no identity/composition laws. Its arbitrary outside-context
clause is exactly the comparison clause used by the original proof. It is strictly a step
of that proof, rather than the original theorem under another name.

The data module has zero holes. The item now has zero holes. Delivery total: one hole
closed, one added, net zero. This is a decomposition, not a net proof-progress claim.
The private inverse-square and inverse-or-zero helpers are completely proved.

## No longer needed

The item no longer directly imports
`Sheaf.SixFunctors.IntegralCompactificationSystemRealization`,
`Sheaf.SixFunctors.CompletedShriekCompositionLaws`,
`Sheaf.SixFunctors.AmbientProperOpenPasting`,
`Sheaf.Paper.FiniteFieldFiber`, `Sheaf.Paper.FiniteTorAmplitudeSites`,
`Sheaf.Paper.IntegralCompactSupportCoefficientComparison`,
`Mathlib.Algebra.Homology.DerivedCategory.Basic`,
`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
`WeilConjectures.Compactification.RefinementCategory`,
`Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`,
`Sheaf.SixFunctors.GeneratorReductionStatement`, or
`Sheaf.SixFunctors.SemilinearProperOpenMatePasting`.
Their statement data are already provided through the retained imports or the extracted
module. The inverse-or-zero construction uses GeneratorReductionData directly.

The original node's direct proof dependencies on ambient pasting, generator reduction,
integral-system realization, reconstruction, and semilinear mate pasting are replaced
by the already proved completed-shriek laws and the explicit smaller comparison.
Those original nodes remain in the comparison's proof plan; they are not globally pruned.
No module is withdrawn, no unit route is bypassed, and no whole-library pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The earlier plan reproved reverse-system invertibility and pasting that are now already
available as `completedShriekRefinementLaws`. Those are used directly.
The current server queue is a one-hole proof assignment, despite the historical rework
row and old bad-import log. The present source compiles without that import failure.

The missing nontrivial connection is equality of the actual reverse system realization
with the prescribed integral open-adjunction mate, not invertibility or system pasting.
It remains stated separately with the original geometric and domain hypotheses, including
arbitrary finite proper/open outside contexts. No extra absolute separatedness is used.
Edge cases checked in the argument: identity refinements, zero input, empty opens,
identity outside context, and composable refinements. Inversion is used only after the
existing laws prove the reverse arrow invertible; the inverse-or-zero zero branch is
therefore never used. No equality is inferred by evaluating finite levels.

## New nodes

`def-sf-normalized-refinement-context-data` owns the ten existing relocated constructions
in IntegralNormalizedRefinementData. Their definitions and public instance declarations
are identical to the original source. It adds no mathematical assumption or hole.

`lem-sf-integral-refinement-transpose-realization` states the remaining normalized reverse
realization comparison in IntegralRefinementTransposeRealization. Its proof plan expands
the proper/open mate and compositor, identifies the integral mate by its adjunction
transpose, and propagates the square through outside factors by recursive realization
naturality. It is original steps 2 and the whiskering part of 5. Mathlib searches found
generic adjunction/limit API, but no theorem of this geometric content.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralNormalizedRefinementData": "e9f0b6e1a995eb3b49aa1d691e0c7d8f425060c4", "Sheaf.SixFunctors.IntegralNormalizedRefinementPasting": "b32deb85da648bb9c49ab07dff91712c562e556b", "Sheaf.SixFunctors.IntegralRefinementTransposeRealization": "b35036476a2b46cc15de73d5260a43370ddb5f9b"}, "results": {}, "time": "2026-10-28T00:54:46+0800", "transitive": 0, "version": 1}
```

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
