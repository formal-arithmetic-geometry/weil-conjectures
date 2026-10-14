## What changed

The existing signature of `AlgebraicGeometry.ordinaryEvaluation_component_over_transport`
and all existing definitions and instance declarations are byte for byte unchanged.
Its proof combines summand/projection transport, the image of the supplied local
evaluation equation, and a tensor-Hom component identity. Three proof-only imports
supply these steps. The existing public imports are retained because its signature
uses their scheme predicate, complexes and canonical unit comparison.

New modules contain the actual `schemeOrdinaryEvaluationComponent` construction,
a proved component criterion, a proved summand/projection transport theorem, and
one admitted tensor-Hom component identity. No arbitrary object is selected from
an unproved existence theorem; the component repeats the actual formula and the
same specified Hom projections already used by the existing predicate.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.ordinaryEvaluation_component_over_transport`
by a complete combination proof. Added exactly one hole:
`AlgebraicGeometry.ordinaryEvaluation_over_component_identity`, node
`lem-pc-ordinary-evaluation-over-component-identity`.

The new theorems `AlgebraicGeometry.ordinaryEvaluation_transport_summand_projection`
(node `lem-pc-ordinary-evaluation-transport-summand-projection`) and
`AlgebraicGeometry.schemeOrdinaryEvaluation_of_components`
(node `lem-pc-scheme-ordinary-evaluation-of-components`) have complete proofs.
The second reader closed the two holes the first reader had left in these theorems.
The new component definition contains no sorry. The only new admitted theorem is
strictly part of the original argument: it has no chain map f, no total tensor
comparison c, and no evaluation-predicate hypothesis or conclusion.

This is a decomposition, not an axiom-free proof of the original theorem:
one original hole closed minus one added hole is net zero. The admitted component identity
accounts for `sorryAx` in the parent proof; no whole-library progress is claimed.

## No longer needed

No public import was removed and no module is claimed globally pruned.
The old direct proof dependencies were `def-pc-ordinary-evaluation-data`,
`def-pc-scheme-ordinary-evaluation-formula`, `lem-pc-ordinary-evaluation-tensor-summands`,
and `lem-sc-hom-complex-projections`. The first, second and fourth remain used through
the new component and transport declarations and their signatures. The tensor-summands
existence declaration is no longer used by this item's proof: it works with the
already supplied c and hc instead of constructing them. Its node is retained for
other users. The item's new direct proof dependencies are the three new theorem nodes.

The rejected full-predicate core and fixed-index restatements are absent. No unit
statement or proof step is bypassed; `sk-thm-picard-duality.json` has empty `realized`
statement/step arrays, and this item is below its unit route.

## Where the brief, the DAG or earlier work was wrong

The first report left an unnecessary definitional component-criterion hole and a
routine totalization/naturality hole. Both are now closed. The criterion requires
controlled unfolding of the existing formula, not a further mathematical assumption.
The transport proof uses Mathlib `HomologicalComplex.ι_mapBifunctorMap`, the supplied
summand equation, the supplied projection equation, inverse cancellation and map_comp.
Its earlier DAG proof mistakenly invoked the local evaluation hypothesis, which is
absent from that theorem; the record now describes the actual proof.

The admitted component identity's earlier written argument treated arbitrary local
sections as global morphisms from the unit. The revised docstring uses extension by
zero from each open to apply naturality legitimately. Comparing e to actual Hom
reindexing gives a common invertible scalar, and the inverse scalar from d cancels
the scalar at the output. The normalized monoidal unit similarly fixes the tensorator
on local pure tensors. The naturality assumption does not say e is the canonical map.

Sources checked online: [Stacks 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
for Hom-complex projections and tensor-Hom constructions;
[Stacks 08DL](https://stacks.math.columbia.edu/tag/08DL) for open restriction;
[Stacks 08DQ](https://stacks.math.columbia.edu/tag/08DQ) for the ordinary evaluation
calculation within the perfect-duality argument. These provide the constructions;
the arbitrary-natural-comparison cancellation is the explicit supplementary argument
in the new theorem's docstring, not a quoted theorem of those tags.

The local elaboration attributes, unused-variable settings and the new theorem's
800000-heartbeat budget are documented in
`coord/changes/ordinary-evaluation-transport-local-elaboration.md`.
The single-file wall-clock limit stays 60 seconds.

## New nodes

`lem-pc-ordinary-evaluation-transport-summand-projection` in
`OrdinaryEvaluationTransportSummandProjection.lean`: proved transport of one summand
and projection, for arbitrary f and arbitrary dual comparison d.

`lem-pc-ordinary-evaluation-over-component-identity` in
`OrdinaryEvaluationOverComponentIdentity.lean`: the one remaining hole, cancellation
of dual and output transport in the actual local component.

`def-pc-scheme-ordinary-evaluation-component` in
`SchemeOrdinaryEvaluationComponent.lean`: the actual single-component construction.

`lem-pc-scheme-ordinary-evaluation-of-components` in the same module: proved abstract
component criterion connecting that construction to the unchanged predicate.

Change record: `coord/changes/ordinary-evaluation-transport-local-elaboration.md`.

## Second reading by H4

1. **Unchanged visible statements: PASS.** Compared each delivered module with
   the repository. Only the item is an existing module; its theorem signature,
   original docstring, instance signatures and instance bodies are byte for byte
   unchanged. `stage3_delivery.diff_module` reports no changed statement. The
   additions are proof imports, local elaboration attributes/settings and a
   private congruence helper. The other three modules are new. The local changes
   are declared in the change record; no target or existing definition changes.

2. **Proof and trust checks: PASS.** Compiled the four delivery modules in import
   order with lcompile.py: 42.7, 52.0, 16.5 and 32.5 seconds, without warnings.
   A source scan finds exactly one sorry, the entire proof of the named public
   component-identity theorem; no axiom, unsafe, opaque, implemented_by, extern,
   skipKernelTC or hollow definition appears. The two newly closed helper proofs
   use actual equations and definitional unfolding, respectively. Scratch axiom
   prints and compilation of the unchanged direct importer are recorded below.

3. **Split statement and searches: PASS after repair.** The remaining hole is
   a component cancellation identity, not the original predicate under another
   name. It omits f, c and the local-evaluation hypothesis. Checked degree-zero
   complexes, r+q nonzero, zero complexes, empty opens and a negative/scalar-twisted
   natural comparison e. In the last case its scalar cancels between d inverse
   and e at the output. Its written proof now justifies local naturality using
   extension by zero. Independent msearch queries with leanfinder, loogle and
   grep, and rg across lean/, found total-summand naturality for the transport
   proof, but no existing arbitrary-natural-e component cancellation theorem.
   The remaining theorem has a matching node and complete proof in words.

4. **Shortest route, imports and unit route: PASS after repair.** Closed both
   unnecessary first-worker helper holes: the criterion by unfolding identical
   formulas, transport by Mathlib summand naturality and inverse cancellation.
   Public imports serve signatures; imports serving only the main proof are
   plain imports. The no-longer-needed section accounts for every old direct
   proof dependency and distinguishes local dependency removal from globally
   pruned modules. No globally pruned module is claimed. Read the unit's
   `realized` record; this refinement stays below its unchanged route.

5. **DAG agreement: PASS after repair.** Matched all five nodes to the Lean
   declarations, refreshed their recorded signatures, and checked new-node
   fields, sources and searches. Corrected the summand node's false reference
   to an evaluation hypothesis and replaced the component node's proof with
   the local scalar cancellation argument. The main node records exactly the
   three supplied component steps combined in its actual Lean proof.

Second reading changed two admitted helper proofs to complete proofs, repaired
and expanded the remaining hole's natural-language proof, and corrected the
DAG, searches, change record and progress/pruning report. The original target
signature and its mathematical meaning remain unchanged.

Final verification: scratch `#print axioms` gives only propext, Classical.choice
and Quot.sound for the summand/projection theorem, component criterion and actual
component construction. The component identity and main theorem additionally use
sorryAx, as expected for the one remaining hole. The unchanged direct importer
`OrdinaryEvaluationOverTensorFormula.lean` compiles against the delivered overlay
without warnings in 28.6 seconds. Scratch files stay outside the delivery set.
