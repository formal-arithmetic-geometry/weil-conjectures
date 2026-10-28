## What changed

Proved `WeilConjectures.ScalarExtensionTower.scalarPullbackCompletionRoos` with its
original statement. The proof constructs a normalized scalar realization for the
specified coefficient calculus, fixes its strict scalar coordinates using the
supplied tensor formula, and rewrites the completion augmentation through its
normalization. The reduction/limit counit and pullback normalization identify the
E-side map. The existing normalized scalar Roos counit theorem and a strict
quotient-square calculation then give the required ordinary scalar/pullback chain.

Added five proved helper modules: `FixedCalculusScalarModel`,
`ScalarPullbackStrictTower`, `ScalarRoosFunctorNaturality`, and `ScalarCompletionPresentationNormalization`, and `IntegralScalarRoosCounitNormalization`.
Each has a DAG node.
Only the item and new helper modules are changed; no existing public signature,
public import, definition, instance or attribute is changed. Proof-local unfolding
keeps the nested quotient and derived functors compatible without changing a
shared definition. The conventions unit has empty realized lists, so its route is
preserved.

Validation: the first delivery compile passed the four original helpers, but
rejected the main file at 66.9 seconds. After the existing proof-local folding
optimizations, the independent ordinary-model counit comparison was extracted
into a proved module. The extracted counit module compiled in 20.1 seconds and the main file in
52.3 seconds. The complete packet is checked again by delivery preflight.
No profiler options remain.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.ScalarExtensionTower.scalarPullbackCompletionRoos`.
The five new helper declarations are
`WeilConjectures.fixedCalculusScalarModel`,
`WeilConjectures.ScalarExtensionTower.scalarPullbackStrictTower`, and
`WeilConjectures.scalarRoos_functor_naturality`, and
`WeilConjectures.ScalarExtensionTower.scalarCompletionPresentationNormalization`, and
`WeilConjectures.ScalarExtensionTower.integralScalarRoosCounitNormalization`.
No new holes are introduced; no direct `sorry` remains in the delivery.

This is a proof from the project's existing declarations. In particular it uses
`WeilConjectures.scalarModelRoos_counit_normalization`
(`lem-trf-scalar-model-roos-counit-normalization`), whose existing proof has a hole.
Its transitive holes remain obligations of their existing items, not new holes.

## No longer needed

The item does not need a direct use of
`lem-pur-coherent-reference-quotient-comparison` /
`Sheaf.Paper.CoherentReferenceQuotientComparison`: the generic coherent quotient
comparison for a specified ordinary/derived model suffices. It also does not use
`lem-pur-scalar-pullback-quotient-ext` /
`Sheaf.Paper.ScalarPullbackQuotientExt`: the strict square is checked directly on
its nested generators, and the scalar qD comparison uses scalar generator
extensionality. These nodes are removed from this item's proof dependencies;
they are not withdrawn or claimed globally unnecessary.

Removed the temporary proof import `IntegralScalarExtensionWellDefined` from
the main module after moving its generator argument into the presentation helper.
The old statement module had only its necessary public coordinate import, which
is retained. No existing module is withdrawn, and no source-library declaration
is removed. The ordinary quotient scalar comparison remains needed in the helper;
the ordinary quotient pullback comparison remains available through pullback
normalization. No scalar completion inverse or derived-completeness assumption
is introduced.

## Where the brief, the DAG or earlier work was wrong

The original node's route through a reference quotient calculus is longer than
needed. A fixed-calculus scalar realization can be constructed directly from the
existing compatible quotient models, so no residue-characteristic invertibility
assumption is necessary. The whole-system scalar counit theorem already isolates
the derived-limit compatibility; only its strict quotient and functor-naturality
steps need new proved helpers. The original theorem's hypotheses and conclusion
are unchanged.

Edge cases use the same adjunction and tensor-unit equations: zero complexes,
empty sites, identity pullback and scalar embeddings, first quotient, and ramified
embeddings introduce no division, nonemptiness or characteristic assumptions.

## New nodes

`lem-pur-fixed-calculus-scalar-model` records the normalized scalar realization for
any fixed calculus, constructed by localization from compatible ordinary/derived
quotient models.

`lem-pur-scalar-pullback-strict-tower` records the ordinary strict tower square;
its generator argument retains all quotient transitions and differentials.

`lem-pur-scalar-roos-functor-naturality` records the additive Roos map's naturality
in the functor, proved using both cocone coordinates and product projections.

`lem-pur-scalar-completion-presentation-normalization` records the proved source
presentation calculation, independently of pullback and target-system maps. It
was extracted after local folding of large Roos definitions did not bring the
combined file below 60 seconds (profiling showed 29.4 seconds tactic execution,
31.2 seconds type checking and 25.5 seconds linting, with overlapping times).

`lem-pur-integral-scalar-roos-counit-normalization` records the fully proved
transport of the existing normalized scalar Roos counit across the ordinary and
derived scalar model comparisons. It is independent of pullback and any good
source representative, and introduces no hole.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FixedCalculusScalarModel": "5930260f6be2098bf7a32952d3e9d349fede9f0d", "Sheaf.Paper.IntegralScalarRoosCounitNormalization": "bbfc970fbefa21383b890577500408c5d879953c", "Sheaf.Paper.ScalarCompletionPresentationNormalization": "8c5726f109f823c1fb9f2e94c6aee4194da26516", "Sheaf.Paper.ScalarPullbackCompletionRoos": "60ef8fcc77945f9af3e45df19623f8980856b67c", "Sheaf.Paper.ScalarPullbackStrictTower": "5bf602af878547992c4b8a6620efc61e1486b688", "Sheaf.Paper.ScalarRoosFunctorNaturality": "c550acebbd521eb7c65d749ff022ef6d09af58a1"}, "results": {"Sheaf.Paper.ScalarPullbackRightRoosNormalization": {"hash": "316d36ea6ba547f9c2cbc8528a701919e32a1ba0", "status": "OK"}}, "seconds": 94, "time": "2026-10-28T15:43:33+0800", "transitive": 0, "version": 1}
```

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
