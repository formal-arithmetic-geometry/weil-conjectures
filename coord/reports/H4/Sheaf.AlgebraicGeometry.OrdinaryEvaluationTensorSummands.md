## What changed

Proved `AlgebraicGeometry.exists_ordinaryEvaluation_tensor_summands` in
`lean/Sheaf/AlgebraicGeometry/OrdinaryEvaluationTensorSummands.lean`, preserving its complete
signature and both original public imports.

The proof constructs the open-site monoidal structure with Mathlib's monoidal localization
API and `exists_localizedOpen_sheafification_iso`. Presheaf reindexing preserves braiding on
pure tensors. A private descent construction proves braiding for the induced sheaf functor.
Private helpers `scalarIso`, `scalarIso_unit`, and `normalize` then transport the structure
along an explicit scalar natural automorphism, giving exactly the prescribed unit while
preserving symmetry. The private theorem `exists_normalizedOpen_coreMonoidal` assembles this
sheaf-level construction.

Two componentwise complex isomorphisms use the inverse tensorator in every bidegree.
Composing their totalization with inverse `mapTotalIso` gives the requested comparison.
`map_ι_mapTotalXIso_inv` and `ιTotal_map` prove its exact summand equation.

Added proof-only imports of `Sheaf.AlgebraicGeometry.LocalizedOpenSheafification` and
`Mathlib.CategoryTheory.Localization.Monoidal.Functor`. The second reader removed the
redundant direct imports of `Mathlib.CategoryTheory.Monoidal.CoherenceLemmas` and
`WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap`; both APIs are publicly
reexported by the original `SchemeOrdinaryEvaluationFormula` import. Updated the item's DAG proof,
proof dependencies, and proof origin to describe this implementation. A local irreducibility
attribute keeps the proof on the equivalence API instead of unfolding
`Scheme.Modules.overEquiv`; this fixes the combined file's earlier compile timeout. The
braiding descent helper returns a theorem rather than a constructed class, avoiding further
unfolding of class data. No interface changes, consumer adaptations, new modules, or new
nodes are delivered. Preflight conservatively classified the added local proof commands
as an interface change, so their scope and unchanged signatures are documented in
`coord/changes/H4-ordinary-evaluation-tensor-summands-proof-locality.md`.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.exists_ordinaryEvaluation_tensor_summands`
(node `lem-pc-ordinary-evaluation-tensor-summands`). No `sorry` remains in the assigned module;
no holes were added. All five private helpers are proved or explicitly constructed.
The complete delivered module compiled without warnings through `lcompile.py --all`
in 50.3 seconds, within the unchanged 60-second file limit. The delivery dry run also checks
all added constants for forbidden axioms; the first dry run passed this compilation and
axiom probe before requesting the local-command change record.

The proof uses no boundedness, perfectness, or nonemptiness hypothesis. The empty open,
zero ring, and zero-complex cases are covered by the same constructions. The unit's route
is preserved: the item's unit has no realized statement or step attached to this node,
and the original sheaf-reindexing and tensor-totalization steps are both implemented.

## No longer needed

No original imports were removed, and no global module pruning is claimed.
The second reader removed two redundant proof-only imports added by the first worker:
`Mathlib.CategoryTheory.Monoidal.CoherenceLemmas` (already reexported through
`OrdinaryEvaluationData`, `TensorClosed`, and `Monoidal.Closed.Basic`) and
`WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap` (already reexported through
`CanonicalPullbackTensorComparison`, `DerivedTensorStructure`, and the K-flat API).
Their declarations remain used through those original imports; neither is global pruning.
`Sheaf.AlgebraicGeometry.LocalizedOpenTensorEquivalence` and
`Sheaf.AlgebraicGeometry.TotalTensorOverEquivIso` were checked as possible shortcuts;
the proof does not import either. Their natural or existential comparison statements do
not specify the normalized unit together with the required summand equations.
The original three DAG dependencies remain; the existing
`lem-pc-sheaf-modules-tensor-closed` is now also recorded for the preadditivity instances.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original proof plan specifies direct coefficient
reindexing with its prescribed unit. The implementation first lifts a braided monoidal
structure through the existing sheafification comparison and then normalizes its unit
by a fully proved scalar-automorphism calculation. This proves exactly the unchanged
existential statement and the unchanged summand equations.

Mathlib and project searches found monoidal localization and totalization APIs, but no
one-line theorem combining the requested normalization and summand equations. Loogle's
query `Functor.CoreMonoidal` returned an unknown-identifier result; local source inspection
found the declaration and its transport API. Stacks Tags 01CD and 0A8X were read online;
the local literature source paths named in the node are absent on this machine.

## Second reading by H4

1. Compared the complete delivered module with the repository using `diff -u` and
   separately checked the theorem signature byte for byte. Verdict: unchanged signature,
   original docstring, public imports, and both preadditivity instance signatures and bodies.
   Added helpers are private; section variables and the irreducibility attribute are local.
   The existing change record documents these elaboration commands; no consumer adaptation
   or target semantic change occurs.
2. Independently compiled the full module through `lcompile.py --all`: clean in 44.5 s.
   A scratch copy with `#print axioms` for all five private helpers and the public theorem
   compiled cleanly in 41.6 s. Every printed declaration depends only on `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The delivered source has no
   `sorry` or forbidden declaration mechanisms. The sheafification comparison used for
   construction is proved, not an unproved existence theorem; MonoidalPreadditive is Prop.
   Verdict: genuine proof, no hollow data.
3. No statements or holes were split off and no new public declarations or nodes were
   added. Read each private helper: the scalar identity automorphism is constructed from
   unitors, its unit component is proved, normalization transports an existing structure,
   and descent uses localization extensionality and cancellation of an isomorphism.
   Empty opens, zero coefficient rings and zero complexes require no excluded cases;
   unbounded complexes use preserved coproducts. Searched the public Mathlib source for
   scalar-unit normalization and braided transport/descent, inspected localization's
   braided API, and ran an independent Loogle query for coreMonoidalTransport (identifier
   unavailable to the service). Verdict: no split-off duplication or restatement.
4. Read the proof from its existential conclusion downward, and compared the proved
   LocalizedOpenTensorEquivalence and TotalTensorOverEquivIso shortcuts. Those statements
   do not provide the normalized unit, symmetry and pinned total summand equation required
   here. The current proof uses the existing localization and totalization APIs directly.
   All original proof dependencies are retained, so the old-dependency pruning list is
   empty. Read dag/units/sk-thm-picard-duality.json: realized.statement and its single
   realized step are empty; no realized unit route is bypassed. Verdict: route preserved.
   Found two redundant newly added imports through public-import traversal and removed
   them: CoherenceLemmas and TotalComplexMap. Their APIs remain used and available through
   the unchanged original imports. The two remaining proof-only imports supply genuinely
   additional APIs.
5. Compared the original and delivered node JSON. Only proof, proof_deps and proof_origin
   differ. Their three steps match presheaf reindexing and braided descent, scalar unit
   normalization, and bicomplex/total summand transport respectively. The added dependency
   on lem-pc-sheaf-modules-tensor-closed correctly records the two existing preadditivity
   instances. All other node fields and the stored Lean statement are unchanged.
   Verdict: DAG agrees with Lean; no new-node obligations.

Second-reading changes: removed the two redundant proof-only imports and updated this
report to identify them. No proof body, existing declaration, node, or change record needed
repair. Closed one original hole, added zero holes; this is a proof, not a decomposition.

The final module after removing the two redundant imports independently compiled without
errors or warnings in 38.1 s through `lcompile.py --all`; all Lean lines meet 100 columns.
