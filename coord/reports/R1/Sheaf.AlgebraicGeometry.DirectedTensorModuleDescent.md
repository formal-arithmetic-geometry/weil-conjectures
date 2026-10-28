## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_directed_tensor_module_descent`
without changing its signature. The main module privately imports the new
`Sheaf.AlgebraicGeometry.DirectedTensorMatchingSections`.

Constructed the descended module as a genuine multiequalizer of the pushforwards
of the supplied chart modules. The relation index consists of pairs of cover
indices with an inhabited hom, keeping the limit in universe `u` even when the
index category has hom universe `v`. Its projection adjoints are the canonical
chart maps. The normalized adjunction's uniqueness comparison gives their exact
specified compatibility, including the equality transports.

The new `Sheaf.Topology.DirectedSheafMatching` proves extension and uniqueness
of matching sections. Given a section on a chart, invert the local transition
on each common lower chart, glue over their open images, and extend using the
pushforward's support property. A further common refinement proves agreement
on overlaps. This includes empty intersections: unique gluing over an empty
family gives the unique section of a sheaf on the empty open.

The new `Sheaf.AlgebraicGeometry.DirectedTensorMatching` constructs the module,
projections and charts, and proves the mate, composition and chart equations.
`Sheaf.AlgebraicGeometry.DirectedTensorMatchingSections` identifies its sections
with matching families through preservation of multiequalizers by section
evaluation. The preceding extension theorem makes each projection bijective
on opens in its chart's image. The proved open-immersion pullback-unit theorem
then makes each canonical tensor chart an isomorphism. The canonical isomorphisms
are named `tensorMatchingChartIso`; their compatibility is
`tensorMatchingChartIso_condition`. They are the explicit witnesses in the main
theorem. This proves effectivity with the originally requested tensor normalization.

The cocycle isomorphism/hom conversion is proved with all functors abstract.
For the final chart equation, a comparison of four abstract isomorphism factors
uses the specified hom maps. Replaying the short mate/projection calculation
in its hom-equation argument avoids a kernel timeout when specializing the
nested chart-equation theorem. The chart isomorphism has an irreducible
construction and a proved hom-map formula. No shared definition is changed.

Validation: all four delivered modules compile in import order, with no new
holes. The final matching-sections module takes about 17 seconds and the main
theorem about 3 seconds, below the per-file limit.

The empty index category causes no exception: the construction is the terminal
module and the chart and compatibility clauses have no instances. No arbitrary
witness from an unproved existence theorem is used for any construction.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.exists_directed_tensor_module_descent`
(node `lem-trf-directed-tensor-module-descent`).

All new constructions and supporting theorems are proved, including
`TopCat.Sheaf.existsUnique_matching`,
`AlgebraicGeometry.Scheme.Modules.tensorMatchingChart_condition`, and
`AlgebraicGeometry.Scheme.Modules.tensorMatchingChart_isIso`.
Holes closed: 1. Holes added: 0. Sorries left in the delivery: none.
This is a proof, not a decomposition into unfinished statements.

## No longer needed

The item's former planned proof dependency
`lem-weil-pbc-glue-sheaves-of-modules`, realized by
`AlgebraicGeometry.glue_sheaves_of_modules` in
`WeilConjectures.Topology.GlueSheavesOfModules`,
is not used. Its general Over-open gluing interface would require substantial
transport between the original cover members and their open images. The direct
matching-family construction proves the needed effectivity from ordinary sheaf
section gluing instead. Its module was not originally imported by the item and
is not added. This prunes that dependency from this item's proof only; the
existing module and declaration are preserved for their other users.

No original public import is removed. The tensor pullback definition dependency
`def-pc-module-pullback` is retained. No unit statement or unit proof step is
bypassed, and no existing module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No disputed statement or source error was found. The DAG's overlap-isomorphism
route is valid, but a direct multiequalizer construction avoids formalizing
additional equivalences of chart categories. The original theorem's historical
docstring describes the overlap route; the updated node and the new modules
describe the implemented matching-family proof.

## New nodes

`lem-trf-directed-sheaf-matching-sections`: proved, generic unique extension of
matching sections for a thin locally directed family of opens, with explicit
local bijectivity and support hypotheses. It is implemented in
`Sheaf.Topology.DirectedSheafMatching` and uses no unproved statement.

`def-trf-directed-tensor-matching-module`: the explicit multiequalizer construction
and its canonical normalized chart equation, implemented in
`Sheaf.AlgebraicGeometry.DirectedTensorMatching`. No object is chosen from a
mere unproved existence assertion.

`lem-trf-directed-tensor-matching-chart-is-iso`: proved local invertibility of the
constructed charts, implemented in
`Sheaf.AlgebraicGeometry.DirectedTensorMatchingSections`, using the generic
matching theorem and the already proved open-immersion pullback-unit result.

No existing definition or statement is changed, and no change record is needed.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.DirectedTensorMatching": "79d925ab7d2aaafb97ca5876dc81f105b38918cb", "Sheaf.AlgebraicGeometry.DirectedTensorMatchingSections": "f1404e75a3729a3fc4e4ac0223f798068ac05900", "Sheaf.AlgebraicGeometry.DirectedTensorModuleDescent": "49cac6b4e41386d117305242e1fa8a4cf81d05f4", "Sheaf.Topology.DirectedSheafMatching": "e467fdb703bd16a9888028400e91ccb735fa700d"}, "results": {}, "time": "2026-10-28T11:40:09+0800", "transitive": 0, "version": 1}
```

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
