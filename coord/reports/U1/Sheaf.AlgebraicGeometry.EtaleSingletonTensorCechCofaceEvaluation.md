## What changed

Proved `AlgebraicGeometry.Scheme.singletonTensorCech_coface_raw_projection`.
A proved private helper carries out the same calculation for an arbitrary presheaf
on `Over U`: unfold the cosimplicial map, evaluate `Pi.lift_π_apply`, and identify
the constant-zero source tuple by reflexivity. The helper fixes the étale over-category
while keeping the presheaf abstract; this avoids the expensive category conversion
of the previous generic-category attempts. The public theorem specializes this
calculation to the tensor-section presheaf.

The existing proof of `singletonTensorCech_coface_evaluation` is retained.
Expanded the docstring of the remaining map-down theorem into the complete
restriction calculation. Every public signature and the import list are unchanged.
No definitions or other Lean modules are changed. The second reader corrected the three
existing nodes' proof records to match the actual calculation and assembly.

## Proved and sorry left

Original direct holes: two. Closed: one. Added or split off: zero.

Closed: `AlgebraicGeometry.Scheme.singletonTensorCech_coface_raw_projection`
(node `new-etale-singleton-tensor-cech-coface-raw-projection`).

Remaining: `AlgebraicGeometry.Scheme.singletonTensorCech_coface_map_down`
(node `new-etale-singleton-tensor-cech-coface-map-down`). Its proof remains
exactly `by sorry`, with its source and full proof in words in its docstring.

The already-proved assembly
`AlgebraicGeometry.Scheme.singletonTensorCech_coface_evaluation`
(node `lem-sc-singleton-tensor-cech-coface-evaluation`) still depends on that
remaining theorem. The private helper has a complete proof and no new hole.
This is a partial proof delivery, not a decomposition or a claim that the import
closure is sorry-free.

## No longer needed

No imports, nodes, or library modules are pruned. The old proof-dependency edge to
`new-etale-affine-singleton-tensor-degree-comparison-hom-normalization` is removed
from all three nodes: no normalization theorem is applied. That definition node
remains a statement dependency, and its module remains publicly imported because
the signatures use its singleton Čech constructions. The assembly instead records
the raw-projection and map-down nodes that its proof actually applies. The sole public import
`Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization`
is needed by the statements and supplies the singleton Čech constructions.
Unused experimental helpers were removed from the delivered module.
The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox report claimed a sorry-free file; the repository and sandbox
actually contained two direct helper holes, and the reported proof did not compile.
This report describes the checked partial result instead.

The timeout is not a tool failure or a mathematical dispute. A helper over a fully
generic category timed out when instantiated at the étale over-category. Fixing
that category made the raw coface proof compile. The restriction-map equation,
universe-lift evaluation, and projection-normalization calculations were also
proved in experiments, but their final specialization to the concrete coface
continued to exceed the kernel check limit. No incomplete experimental proof,
new axiom, limit increase, or shifted hole is included in this delivery.

The remaining statement is consistent with its degree-zero and zero-section
edge cases. Its full mathematical proof remains the stated functorial restriction
calculation; the outstanding work is to make its concrete specialization check
efficiently. No source statement or blueprint unit has been bypassed.


## Second reading by U1

1. **Visible interface — pass.** Read the repository and sandbox module whole and
   compared them with `diff -u`. All three existing public theorem signatures are
   byte for byte unchanged: the scheme, quasi-coherent module, étale objects,
   arrow, degree, omitted index, arbitrary section and both sides of every equality
   are identical. The only Lean differences are the proved private projection
   helper, the raw-projection proof and the expanded map-down docstring. There are
   no definition changes, new hypotheses, weakened conclusions or change records.
   The sole public import supplies definitions occurring in those signatures.

2. **Proof and axioms — pass, partial result.** Compiled the delivered module with
   `lcompile.py`: exit code 0, no warnings. In a scratch copy, printed axioms for
   all three public theorems. Raw projection uses only `propext`,
   `Classical.choice`, `Quot.sound`; map-down and the assembly also use `sorryAx`.
   The private helper unfolds the coface map, applies `Pi.lift_π_apply` and closes
   by reflexivity. There is exactly one direct hole, the reported public named
   map-down theorem; no new hole, hollow definition or forbidden declaration.
   The assembly correctly takes `congrArg ULift.down` of raw projection and
   composes with map-down.

3. **Split statements and small cases — pass.** No statement is split off by this
   delivery. Reviewed the two existing intermediate nodes, which isolate distinct
   parts of the argument rather than restating the final downstairs equality.
   Raw projection is proved for an arbitrary presheaf on `Over U`, with no extra
   tensor or normalization hypothesis. For degree zero, `Fin 2` indexes the two
   retained projections to the one-factor product, exactly as required. The
   constant-zero tuple remains constant zero after either omission. For zero
   section groups the maps send zero to zero. Map-down uses only the actual
   definitions of `etaleTensorSectionsSheaf`, `etaleTensorSectionsPresheaf`,
   `sheafCompose`, opposite forgetful functor and `uliftFunctor`; its expanded
   docstring gives the full restriction calculation. Loogle found
   `Pi.lift_π_apply`; LeanFinder found `AddCommGrpCat.uliftFunctor_map`.
   Searched local Mathlib, upstream and `lean/Sheaf` for lifted-map evaluation,
   coface evaluation and projection calculations. The upstream
   `TopCat.Presheaf.cechComplexFunctor_d_π` is about the differential on opens,
   and does not replace this individual coface on `Over U`. No shorter complete
   declaration was found. A scratch attempt to close map-down by direct
   reflexivity timed out at the unchanged 60-second limit and was not delivered.

4. **Top-down route and pruning — pass after metadata repair.** The proof uses
   Mathlib's product projection equation first, then the existing tensor-section
   definitions; it introduces no unproved replacement theorem. The only import
   is necessary to state the theorems, and there is no proof-only public import.
   The old normalization proof-dependency edges are now listed under
   `## No longer needed`; that module stays as a statement dependency. Read
   `dag/units/sk-prop-h2.json`: its statement and step realization arrays are
   empty, and no unit realization or chapter route is changed. No library module
   is pruned.

5. **DAG agreement — pass after repair.** The raw-projection node now records the
   actual Mathlib projection calculation and constant-tuple reduction, with no
   normalization theorem dependency. The still-open map-down node now records
   the full definitional restriction calculation as its proof plan. The assembly
   node now names the raw-projection and map-down nodes as its proof dependencies
   and explains the `congrArg`/transitivity composition. Updated only `proof`,
   `proof_deps` and `proof_origin` of these existing nodes; their statements,
   Lean signatures, statement dependencies and unit are unchanged. No new nodes
   require creation-field review.

Second reading changed the three existing DAG proof records and this report.
The checked Lean proof and the remaining named hole were retained.
