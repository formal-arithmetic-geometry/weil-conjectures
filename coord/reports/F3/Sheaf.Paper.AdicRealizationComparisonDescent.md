## What changed

Constructed the integral realization reindexing comparison as a composite of existing
natural isomorphisms in `Sheaf.Paper.AdicRealizationIntegralReindex`. The pullback
inclusion equalities are in `Sheaf.Paper.AdicRealizationPullbackInclusions`. Its component
and rational-localization lemmas are in `Sheaf.Paper.AdicRealizationReindexComponents`.
This proves integral naturality, invertibility, and the exact component formula with both literal
localization transports. Categorical scalar localization then gives the uniquely
normalized comparison on every rational finite stage. The component calculation is
proved for abstract functors before specialization, which avoids simplifying the
chosen derived-category structures. The constructed isomorphism and its normalization
proof are stored together in `IntegralRealizationReindexData`, with a small projection
API; the constructor is irreducible. The local files enable respectTransparency.
The normalization proof uses the abstract component lemma with the object equations
induced by the proved functor equalities. Proof irrelevance identifies their equality
transports with the prescribed localization transports. This avoids unfolding the
coefficient categories while matching the component formula. The scalar-extension
functor is explicitly typed with the native module category, so its map and the
normalization statement use the same category instance.

Replaced the item's existential hole by an assembly proof: coefficient-enlargement
squares give naturality on transition isomorphisms, and the existing common-stage
representative factorization gives naturality on every arrow. The resulting natural
isomorphism has the required integral representative agreement.

The remaining coefficient-enlargement square is isolated in
`Sheaf.Paper.AdicRealizationReindexScalar`. It concerns explicitly constructed
components at two nested fields, with no existential comparison and no assertion of
naturality on arbitrary common-stage arrows. No existing signature, definition,
instance, public import, target statement, or other existing module is changed.

Final validation: `lcompile.py --all` compiled the five cleaned-source modules in
import order: pullback inclusions 26.3 s, integral comparison 44.1 s, rational components
10.9 s, scalar square 8.7 s, and the assigned module 5.4 s. No profiling options
remain. The original theorem signature is byte-for-byte unchanged. The DAG declaration
records and dependency references were cross-checked against the delivered sources.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.AdicQbarRealization.exists_realization_comparison_descent`
(node `lem-sf-adic-realization-comparison-descent`).

Proved `realizationAgreement_of_components` and
`realizationRationalReindex_existsUnique`. The integral comparison itself is a real
composite construction. Also proved `realizationPullback_inclusion_eq`,
`realizationPullback_localization_eq`, `realizationCompletionPullbackIso_inv_app`,
`realizationReindexComposite_hom`, `realizationReindexComposite_core`, and
`realizationReindexComposite_normalized`. The completion-unit comparison is explicitly
constructed as `realizationCompletionPullbackIso`. The rational comparison is selected from an existence-unique
theorem whose component condition fixes it on every object.

Added one hole:
`WeilConjectures.AdicQbarRealization.realizationIntegralReindex_scalar`
(node `lem-sf-adic-realization-reindex-scalar`).

This is a decomposition: one original hole closed, one strictly smaller scalar-square
hole added, net zero holes closed. Integral construction, rational naturality, and
common-stage assembly are proved; compatibility across distinct coefficient fields
remains. There are zero holes in the item, pullback-inclusions, integral-construction, and
component modules, and one in the scalar module. Imported pre-existing theorem holes are not claimed as closed.

## No longer needed

No pre-existing import was removed: the item's sole public import remains. The proof
adds only private imports of the scalar comparison and stage naturality helper.

The item no longer uses these original dependencies directly:
`lem-weil-isomorphism-derived-pullback-comparison-normalization`,
`lem-weil-isomorphism-comparison-natural`, `lem-weil-isomorphism-derived-pullback`,
`def-weil-rationalization-karoubi`, `lem-weil-finite-free-completed-scalar-comparison`,
`lem-weil-isomorphism-comparison-scalar-extension`,
`def-weil-algebraically-closed-coefficients`, and
`def-weil-derived-pullback-tensor-hom`. They are replaced at this level by the
constructed component theorem, the scalar square, and stageComparison_naturality.

The scalar square still needs the specified finite-free completion and scalar-extension
normalizations, and the component construction still uses the existing rational and
common-stage operations. These underlying nodes/modules are therefore not claimed
pruned from the target closure. No whole module is withdrawn or declared unnecessary.
The separate isomorphism constructibility theorem and comparison-natural theorem
are unnecessary direct inputs to the component construction: podCompletedToTower_laws
already supplies naturality and invertibility on the required constructible inputs.

## Where the brief, the DAG or earlier work was wrong

The previous single proof step did not supply a native common-stage comparison that
could simply be applied. Its finite naturality and scalar-compatibility arguments
were still to be assembled. The supplied balanced comparison isomorphisms and
podCompletedToTower_laws do suffice to construct the integral natural isomorphism;
there is no need to assert its existence again or add hypotheses to the target.

The native comparison does not require a new proof of arbitrary rational-arrow
naturality: the existing raw scalar localization theorem supplies it from integral
naturality. Likewise StageComparisonNaturality already proves the common-stage
quotient argument. The remaining obligation is only their explicit mixed scalar
square, not the original existence theorem under another name.

## New nodes

`lem-sf-adic-realization-pullback-inclusions`: the two proved inclusion and localization
functor equalities, and the constructed complete-input comparison with its inverse
component equation. Its generic stage-morphism helper is private and used only in a
theorem proof.

`lem-sf-adic-realization-integral-reindex`: the explicit integral composite, its abstract
component and equality-transport lemmas, and the constructed data record carrying the
literal normalization proof. The projection API avoids unfolding the constructor.

`lem-sf-adic-realization-reindex-components`: the proved construction and exact integral
component formula, together with unique extension to the rational finite stage.
The literal localization transports agree by proof irrelevance.

`lem-sf-adic-realization-reindex-scalar`: the coefficient-enlargement square for those
constructed components, still open. Its docstring gives the whole-cone normalization,
finite-free scalar and balanced-section argument and records identity, ramified,
zero-object and empty-scheme cases. It assumes no common-stage comparison.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AdicRealizationComparisonDescent": "9898dcf3ae87550c93b1c1c749b7db0a36562903", "Sheaf.Paper.AdicRealizationIntegralReindex": "5074d89e1c678b1fb2961a824b67b4e271ed1c64", "Sheaf.Paper.AdicRealizationPullbackInclusions": "f392a583b870128df979c7e4e18a041b03314fbe", "Sheaf.Paper.AdicRealizationReindexComponents": "f7e50c63fe72705d895da46baac13152914c9668", "Sheaf.Paper.AdicRealizationReindexScalar": "35fafc3457f8a894b35287614f5feb07c09b85c1"}, "results": {"Sheaf.Paper.AdicIntegralReindexingDescent": {"hash": "6ec8ec034cbf312bd88caba1ee1571de4b518c20", "status": "OK"}}, "seconds": 35, "time": "2026-10-28T11:26:36+0800", "transitive": 0, "version": 1}
```

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
