## What changed

Replaced both original sorry proofs in `Sheaf.Topology.InverseImageModule` without changing
any declaration signature or definition. Added proof-only imports of
`Sheaf.Topology.InverseImagePresheafModule`, `Sheaf.Topology.InverseImageOperationExt`, and
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify`.

The presheaf helper transports the module structures supplied by the existing
`PresheafOfModules.topologicalPullbackAdjunction` along its natural abelian-presheaf
isomorphism. Mathlib's module sheafification then gives the actual inverse-image section
instances, semilinear restrictions, and semilinear unit. Map linearity follows by a
proved general extensionality lemma, naturality of the inverse-image map and unit,
and original module-map linearity.

The extensionality lemma is proved using local surjectivity of sheafification,
pointwise Lan colimit representatives, a common filtered index, and separatedness.
All three delivered modules compile locally without warnings.

## Proved and sorry left

Proved `TopCat.Sheaf.exists_inverseImageModuleInstances` and
`TopCat.Sheaf.inverseImageMap_smul` (both under node
`def-pc-topological-inverse-image-module`). Also proved
`TopCat.Sheaf.exists_inverseImagePresheafModuleInstances`
(`lem-pc-inverse-image-presheaf-module`) and `TopCat.Sheaf.inverseImageOperation_ext`
(`lem-pc-inverse-image-operation-ext`). There is no sorry in any delivered module.

The proofs depend on the existing named theorem
`PresheafOfModules.topologicalPullbackAdjunction`, which remains sorry in
`Sheaf.Algebra.Category.ModuleCat.Presheaf.TopologicalPullback`
(node `lem-pc-presheaf-module-inverse-image-adjunction`). This is the remaining
stage-3 dependency, not a new gap or axiom in this delivery.

## No longer needed

No original library import or DAG dependency was removed: the original node had no
proof dependencies recorded. Both new helper modules are used by the proof. Their
imports were narrowed to the algebraic categories and sites they need.

Discarded the earlier sandbox's `inverseImageModule_val_obj` lemma and
`inverse-image-module-val-carrier` node: they were only a reflexive carrier equality
and did not discharge either assigned sorry. They had not been delivered or landed.
No established blueprint unit statement or proof step is bypassed; the item's unit
record has empty `realized.statement` and `realized.steps` lists.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's claim that the explicit constructions were absent overlooked
`PresheafOfModules.topologicalPullbackAdjunction` and Mathlib's
`PresheafOfModules.Sheafify.module`. The existing coprojection formula is sufficient
after transport of the module instances along the underlying natural isomorphism.
The earlier attempt only added a lemma and left both assigned sorries unchanged;
this delivery replaces both proofs.

The item's original node had an empty proof plan and no proof dependencies. Its
sandbox copy now records the route actually compiled. The new operation-extensionality
statement makes no additivity or module assumptions, so it is not a restatement of
map linearity. Its empty-open case follows from separatedness on the empty cover;
zero sheaves, empty spaces, and non-surjective continuous maps cause no extra hypotheses.
The presheaf transport is valid on every open, including the empty open, because it
uses an isomorphism rather than choosing a point or a nonempty neighbourhood.

## New nodes

`lem-pc-inverse-image-presheaf-module`, in
`Sheaf.Topology.InverseImagePresheafModule`: the section module instances and unit law
transported from the existing concrete presheaf-module pullback theorem. Fully proved;
its only non-Mathlib proof dependency is the existing presheaf pullback node.

`lem-pc-inverse-image-operation-ext`, in `Sheaf.Topology.InverseImageOperationExt`:
a general criterion for equality of restriction-compatible binary operations on
inverse-image sheaves, using only unit-image agreement. Fully proved from Mathlib.
Search records include the unavailable LeanSearch service and successful LeanFinder
and source searches; no failed service is represented as a negative search result.
No definition or existing statement changed, so no change record is required.


## Second reading by U1

1. Compared every delivered module with the repository version. Existing declarations and definitions retain their signatures byte for byte; only proof bodies and proof-only imports changed.
2. Compiled all three modules with `lcompile.py --all`; the compile is clean. There are no `sorry`s in delivered files, and the axiom probes show only `propext`, `Classical.choice`, `Quot.sound` for the new extensionality theorem. The presheaf and module theorems transitively use `sorryAx` only through the existing named `topologicalPullbackAdjunction` theorem.
3. Checked each split-off statement against its Lean declaration, docstring, node, and searches. Both helper statements are genuine intermediate reductions, with no duplicate declaration found; the operation extensionality statement is strictly more general than module-map linearity.
4. Read the proofs from the target downward. The module proof uses the existing presheaf pullback theorem, transports its module structure through the additive isomorphism, then uses Mathlib sheafification and local extensionality. No shorter applicable route was found. The filtered-colimit and sheafification dependencies required by the proofs remain recorded; no old dependency is unused. The unit route has no realized statement or steps to bypass.
5. Checked the node records against the actual proof terms and dependencies. The new helper nodes record their sources, proof routes, declarations, and search results; the item node records the three proof steps and their dependencies.

Changed during second reading: removed the unused public `Mathlib.Algebra.Category.Grp.FilteredColimits` import from `InverseImageOperationExt`; the ring filtered-colimit import remains public because it supplies instances required by the helper's exposed statement. No declarations or definitions were otherwise changed.
