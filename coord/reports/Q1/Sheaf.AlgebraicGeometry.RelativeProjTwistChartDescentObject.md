## What changed

Replaced the proof hole of
`AlgebraicGeometry.Scheme.GradedAlgebraData.exists_twist_chart_descent_object`
by construction of normalized affine restriction comparisons, a proof of their
composition law, and application of general module descent. The statement,
public import, and definitions of the item are unchanged.

Three private helpers contain the Proj-specific argument:

- `baseChange_data` constructs the scalar-extension algebra equivalence from
  graded base change and proves the homogeneous-component span equality.
- `restriction_comparison` applies the existing proved scalar-extension
  comparison theorem to every affine restriction, with its chart hypotheses
  verified by `Proj.map_preimage_basicOpen` and `Proj.awayι_comp_map`.
- `restriction_comparison_comp` proves the complete normalized composition law,
  including equality transport, using the existing proved composition theorem,
  the explicit three base-ring algebra structures, `A.res_comp`,
  `Proj.map_congr`, and `A.relProjFunctor.map_comp`.

The main proof chooses these comparisons in all degrees, takes their degree-one
parts as transitions on `A.relProjGluingData.cover`, proves the required cocycle,
and obtains the charts. It then supplies the previously constructed normalized
comparisons together with the resulting chart squares to
`TwistChartCompatibility`.

Added proof-only imports of `RelativeProj.GradedTensor`,
`ProjScalarExtensionTwistCompositionLaw`, and `DirectedTensorModuleDescent`.
Only the last module is new. It states general effectivity for already supplied
coherent module isomorphisms on a locally directed open cover. Its interface has
no graded algebra, Proj, twist, fraction formula, or requirement to construct
transition maps. Its docstring gives the common-refinement overlap construction
and proof following Stacks 01LI and Sheaves 04TN/00AL/00AM.

No other existing Lean module or public interface was changed. No source-library
file was changed. The item node now describes the actual proof and its
composition-law dependency; the new module has its own node.

## Proved and sorry left

Original holes: 1. Original holes replaced by complete Lean proofs: 1,
`AlgebraicGeometry.Scheme.GradedAlgebraData.exists_twist_chart_descent_object`
(node `lem-trf-relative-proj-twist-chart-descent-object`). Its proof uses the
new effectivity theorem below. The three private helpers are fully proved and
contain no holes.

Added holes: 1,
`AlgebraicGeometry.Scheme.Modules.exists_directed_tensor_module_descent`
(node `lem-trf-directed-tensor-module-descent`, new module
`Sheaf.AlgebraicGeometry.DirectedTensorModuleDescent`). Its entire proof is
`by sorry`. There are no other holes in the delivery.

This is a decomposition, not a net closure of a sorry: one upper hole closed,
one generic gluing hole added, net zero. The Proj-specific local isomorphism
construction and normalized cocycle are now proved in Lean; the unproved
argument is only the passage from supplied coherent transition maps to a global
module. In particular this does not restate the item or assume its normalized
comparison conclusion.

Edge cases checked in the new statement: identity transitions follow from the
composition hypothesis and invertibility, including the pullback unit laws;
empty intersections are covered by the same local agreement/gluing argument;
an empty covering forces the scheme empty. No quasi-coherence or finiteness
hypothesis has been added. The index is thin, as required for the affine-open
application. Both delivered modules compile together in import order via `lcompile.py --all`.
The item compiled in 6.6 seconds; the new theorem module compiled in 2.5 seconds
and was reused from cache on the final check. Final compile result:
`a2016158ccf757406fa322ec`, exit code 0. No errors or warnings were reported.

## No longer needed

No module or node is pruned, and no original import is removed.
`lem-weil-pbc-glue-sheaves-of-modules` moves from the item's direct proof
plan to the new generic effectivity node: it remains needed there, so this is
not pruning. `lemma-nagata-relative-proj-exists` and the original
scalar-extension comparison remain needed. The composition-law node is now
an explicit dependency. An unused tentative proof import of
`WeilConjectures.Topology.GlueSheavesOfModules` was removed from the new
module; the future proof of its theorem can import it when used.

## Where the brief, the DAG or earlier work was wrong

The original plan compressed two different operations into “apply module-sheaf
object descent”: produce normalized Proj transition maps and their coherent
composition, then turn a locally directed-cover datum into the explicit
overlap datum accepted by `glue_sheaves_of_modules`. The existing gluing
theorem takes modules restricted to open images and overlap isomorphisms;
it does not directly take normalized tensor pullbacks on a directed cover.
Stacks 01NR refers to 01LI for exactly this common-refinement gluing step.
The new node records this missing bridge, with the omitted compatibility
checks written out in words. The new statement is a genuine gluing step after
the algebraic construction and cocycle have been proved, rather than another
name for the original Proj descent obligation.

No mathematical statement error was found. The blueprint unit route and target
statements are preserved. Searches of the entire DAG and imported blueprint
found no node for this particular directed module effectivity interface;
three kinds of Mathlib searches are recorded from the actual search log.

## New nodes

`lem-trf-directed-tensor-module-descent`, in
`dag/nodes/sec-trace-formula/lem-trf-directed-tensor-module-descent.json`,
states and explains effectivity of supplied coherent normalized module
transitions on a locally directed open cover. It depends on normalized
pullback and the existing sheaf-of-modules gluing theorem. Its source is
Stacks Constructions 01LI with Sheaves 04TN/00AL/00AM; its proof is expanded
for arbitrary modules and the normalized pullback convention. The attached
Lean signature is copied verbatim from the new module. No existing definition
or statement changed, so no change record or forced adaptation is required.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 1 INFRA, 1 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.DirectedTensorModuleDescent": "3f092f5de241c0c0092d951c6d24b4218f5dd459", "Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescentObject": "a4e3582cd889d13480eb1af5a2d55bce3de1eabb"}, "results": {"Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescent": {"hash": "331320495611872c88b7bbdcc5bc7042430c4d0f", "status": "INFRA"}, "Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescentTransition": {"hash": "6104f245446d3dbaaec9abb08c262b2a1f6744f5", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T08:02:00+0800", "transitive": 0, "version": 1}
```

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
