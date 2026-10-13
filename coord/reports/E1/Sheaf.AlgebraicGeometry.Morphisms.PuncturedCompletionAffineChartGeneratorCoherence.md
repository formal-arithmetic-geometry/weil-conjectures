## What changed

Replaced the sole hole in
`AlgebraicGeometry.Scheme.CompletionGluingData.affine_chart_transition_generator_coherence`
with proofs of both equations. The existing signature, visibility, and docstring are
unchanged. All helpers are private and fully proved in the original module.

Added proof imports `Mathlib.Algebra.Module.LocalizedModule.IsLocalization` and
`Mathlib.AlgebraicGeometry.Morphisms.Flat`. The square proof uses affine pullback
sections as a ring pushout, transports the two spectral section rings with `ΓSpecIso`,
and compares the pushout with a tensor product. Tensor induction, the supplied
scalar and generator formulas, and section naturality give the two restriction
formulas. Injectivity and `d_prime` finish the square.

The cocycle proof uses six actual triple-section equivalences obtained from affine
principal-open localization. Two localization uniqueness checks extend the generator
identities to full map identities. Injectivity then proves the cocycle. Updated the
original node's proof, proof_deps, and proof_origin to describe this argument.

## Proved and sorry left

The replacement closes the one original hole:
`AlgebraicGeometry.Scheme.CompletionGluingData.affine_chart_transition_generator_coherence`
(node `lem-sbc-punctured-completion-affine-chart-generator-coherence`).
No holes are split off or added, and no `sorry` remains in the delivered module.
No data are selected from a holed existence statement. In particular, the proof does
not call `exists_affine_chart_transitions`: the chart data are the given hypothesis T.

Validation: the actual delivered module compiles against the published green build.
Generic tests of the localization, tensor, square, and cocycle arguments also compile;
their axiom probes show only `propext`, `Classical.choice`, and `Quot.sound`.
The final delivery dry run supplies the module's complete axiom and preflight checks.

## No longer needed

No original import, node, or module is pruned: all four original dependencies are
used for the types and canonical localization/tensor maps. The source's
`exists_affine_chart_transitions` theorem is not used as a proof dependency; the
module's supplied structures and definitions are needed. No new modules or nodes
are delivered. The proof establishes the cocycle on all fractions as an intermediate
result, while retaining the original conclusion on generators unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was disputed or changed, and no other module was adapted.
The unit `sk-prop-input-spreading` has no realized nodes to bypass; the proof retains
the chart-generator coherence step in the existing route.

The item was dispatched before its transition dependency became available in the
published green build. Initial local compilation and delivery dry runs failed at that missing import.
The green publication at 21:55 UTC resolved this, and the actual module was then
compiled. The dependency was never copied or redefined.

Source checks: [Stacks Tag 0BLH](https://stacks.math.columbia.edu/tag/0BLH)
(first two proof paragraphs), [Tag 05EL](https://stacks.math.columbia.edu/tag/05EL)
(item (1)), and [Tag 01I6](https://stacks.math.columbia.edu/tag/01I6)
(affine section modules). The constructions cover empty intersections, zero
principal opens, repeated indices, and the vacuous chart family t=0. The affine
base-change tensor theorem requires no flatness hypothesis.

## Second reading by E1

1. **Interface and accidental changes.** Compared the delivered module with the repository version. The target theorem signature and all existing declarations are byte-for-byte unchanged; only two proof-only Mathlib imports, private helpers, and the theorem proof were added. The DAG node changes only describe the delivered proof route and dependencies.

2. **Proof and axioms.** Compiled the delivered module with `lcompile.py`; it succeeds without warnings. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations. The proof constructs section localizations and affine tensor equivalences explicitly; no data is chosen from an unproved existence theorem.

3. **Statements and searches.** No statement was split off and no new public theorem was added. The private helper claims are intermediate constructions proved in the file. Searched the local Lean library and recorded Mathlib searches in the node; no duplicate coherence theorem was found.

4. **Route and pruning.** The proof follows the unit route: localization for the cocycle and affine pullback tensor comparison for the square, followed by tensor induction and restriction naturality. Both added imports are used by the proof; the original public transition import remains necessary for all interfaces and hypotheses. No proof dependency or module can be pruned.

5. **DAG agreement.** Checked the node's theorem statement against Lean and checked that its four proof steps, dependency union, and proof origin describe the actual implementation. The unit's realized route is unchanged. The only change beyond the proof is the node's corresponding proof metadata.

No further changes were needed in this second reading.
