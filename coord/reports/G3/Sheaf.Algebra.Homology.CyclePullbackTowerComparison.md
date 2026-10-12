## What changed

Repaired reviewer X-6c272 (head 6c272bd40), E2 / brief point 4 in
`Sheaf.Algebra.Homology.CyclePullbackTowerComparison`.

Constructed `CochainComplex.CyclePullback.canonicalComparison` explicitly:
proved the recursive stage identity, including the boundary `i = N`; identified
the term with the next functor-category pullback followed by T; evaluated the
pullback and kernel with Mathlib's canonical isomorphisms; applied `T.mapIso`.
Every construction and equality proof is complete. No arbitrary existential
witness, unproved existence theorem, hollow definition or new hole is used.

Proved both canonical projection equations. Replaced the false helper
`tower_comparison_second` with its equation for this fixed canonical isomorphism.
Preserved the entire existing signatures of `tower_comparison_first` and
`tower_comparison`. The combined theorem now returns `canonicalComparison` and
its two proved equations, without choosing a witness from the first theorem.

Added public imports of Mathlib's kernel and pullback preservation modules,
needed in public construction bodies. All other transport and indexing helpers
are private and fully proved. Updated all three existing module nodes and added
`def-tower-canonical-comparison-g3` for the explicit construction. The changed
helper signature, verbatim old/new signatures and its sole user are recorded in
`coord/changes/tower_comparison_second.md`. No forced adaptations are needed.

## Proved and sorry left

No `sorry` remains anywhere in the delivered module. No holes were added and no
intermediate statements were split off.

- `CochainComplex.CyclePullback.tower_comparison_first`: proved with its original
  signature (node `new-tower-comparison-first`).
- `CochainComplex.CyclePullback.tower_comparison_second`: the false original
  arbitrary-comparison claim is retired; the corrected canonical-comparison
  projection equation is proved (node `new-tower-comparison-second`). This is
  not a proof of the original false statement.
- `CochainComplex.CyclePullback.tower_comparison`: its original existential
  signature is unchanged and its new proof is complete (node
  `lem-pc-cycle-pullback-tower-comparison-stage3`).
- `CochainComplex.CyclePullback.tower_comparison_canonical_first` and
  `CochainComplex.CyclePullback.term_step_eq`: new, fully proved helpers.
- `CochainComplex.CyclePullback.canonicalComparison`, `evaluatedPullbackIso` and
  `indexedPullback`: real constructions with fully proved data.

Both baseline named holes are syntactically removed. Semantically, this proves
one original holed theorem unchanged and replaces one false holed helper with
its true, proved correction. The target-reachable existential comparison now
has a proof that uses no `sorryAx`; no credit is claimed for proving the false
original helper. The pinned ledger determines the final project net.

Validation: the delivered module compiles cleanly through `lcompile.py`.
A scratch copy of this exact module with `#print axioms` checks for the canonical
construction and all four comparison/projection theorems reports only
`propext`, `Classical.choice` and `Quot.sound`; no `sorryAx` remains. The delivery
dry run passes compilation and preflight except for the independent second
reading, which the next worker writes. Nothing is pushed.

## No longer needed

No baseline import or module is pruned: the construction still needs the
explicit tower module. Both added Mathlib imports are used.

Removed the circular proof edges from `new-tower-comparison-first` and
`new-tower-comparison-second` back to the combined theorem
`lem-pc-cycle-pullback-tower-comparison-stage3`. They now depend on the explicit
canonical construction and the tower data. The combined theorem uses those
canonical projection equations; its old arbitrary-witness route is retired.

No `CyclePullbackTowerComparisonCore` module or node is introduced. The unit
`sk-thm-picard-semicon` has empty realized lists for this part; its statement and
steps remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The returned helper asserted that preserving the first projection forces the
second projection equation. The reviewer's rational-vector-space example
refutes that: with B terminal, F zero, N = 0, i = -1, T(X) = X ⊕ ℚ and π the
first projection, swapping the comparison's coordinates preserves its zero
first projection but changes the differential map; evaluation at (1,0)
distinguishes the maps. The repair removes that universal claim entirely.

The [Stacks Project, Lemma 05T7 (1)](https://stacks.math.columbia.edu/tag/05T7)
defines the augmentation and differential from the same descending pullback
construction. The canonical comparison now preserves those two constructed
maps, as the source requires. No assertion about an arbitrary comparison is
used. The revised proof checks both the boundary i = N and the recursive case
i < N, and it does not require T to preserve kernels or pullbacks: evaluation
preserves them, and T only maps the resulting isomorphism.

The second node's `statement`, `lean.statement`, `stmt_deps`, `proof`,
`proof_deps`, and `statement_change` record the correction. Its sole existing
citer, `lem-pc-cycle-pullback-tower-comparison-stage3`, retains its statement and
has a repaired proof. The `statement_change.by` field uses `G3 stage 2` because
that is the existing validator's required format for statement corrections;
this work is a stage-3 repair.

## New nodes

`def-tower-canonical-comparison-g3` records the explicitly constructed canonical
comparison and its supporting public construction declarations. Its only
statement dependency is the existing explicit tower data. The Lean proof of
the recursive term identity and all limit comparison data are complete, so the
node adds no new proof task or hole. LeanFinder and local grep found Mathlib's
canonical projection machinery; LeanSearch returned Internal Server Error and
is recorded as unavailable.

Change record: `coord/changes/tower_comparison_second.md`.

## Second reading by G3

1. **Interfaces: pass with the declared correction.** Read the full repository/sandbox
   diff. The complete signatures of `tower_comparison_first` and
   `tower_comparison` are byte-identical. No existing tower definition changes.
   The only existing signature change is `tower_comparison_second`, recorded
   with verbatim old/new signatures in `coord/changes/tower_comparison_second.md`.
   A scan of all Lean sources finds its only user in this module; a scan of all
   node statement/proof dependencies finds only the combined comparison citer.
   That citer and the downstream `CyclePullbackCore` application retain their
   original existential contract. No target statement changes.

2. **Proof and construction: pass.** Compiled the exact delivered module with
   `lcompile.py`, cleanly in 3.2 seconds. Verified that the scratch axiom-check
   copy is exactly this module before its appended commands; compiled it and
   checked `canonicalComparison`, `tower_comparison_canonical_first`,
   `tower_comparison_first`, `tower_comparison_second`, and `tower_comparison`.
   Each uses only `propext`, `Classical.choice`, and `Quot.sound`.
   Scanned the whole source: no sorry, sorryAx, axiom, unsafe, opaque,
   implemented_by, or extern. The construction uses proved stage equalities,
   Mathlib limit comparisons, pullback.map and T.mapIso, never an arbitrary
   witness from an existence theorem. Read the transport proofs: stage equality
   transports current, next and degree; the two projection transports reduce
   by equality elimination; naturality of pi gives both pointwise equations.

3. **New facts and small cases: pass.** There are no split-off holes. Read the
   canonical-construction node and its Lean data, and Stacks Project tag 05T7
   (1), especially its descending pullback step and initial stage. This item
   compares an already constructed tower, so it needs neither a surjectivity
   hypothesis on pi nor preservation of limits by T. Evaluation preserves the
   kernel and pullback, and T maps their isomorphism. The i=N branch uses the
   actual initial zero stage at N+1; for i<N the depth identity supplies the
   successor step. Empty B makes all pointwise claims vacuous; T equal to the
   identity and the zero complex are also covered without extra hypotheses.
   Rechecked the old helper's counterexample: for the terminal B, rational
   vector spaces, F=0, N=0 and T(X)=X direct-sum Q, term 0 is Q and term -1 is
   Q direct-sum Q. Its differential is the first projection, whereas swapping
   the comparison coordinates gives the second projection; the augmentation
   is zero in both cases. Thus the corrected fixed-comparison equation is
   needed and the original universal statement is false. This correction is
   explicitly not credited as a proof of the old helper.
   Independently searched with Loogle query `"pullback", "iso"` (12 hits,
   including pullbackComparison), and read Mathlib's PreservesPullback.iso and
   projection equations. Local searches in the upstream WeilConjectures tree
   and lean/Sheaf found no other recursive comparison. The implementation
   already uses the existing canonical Mathlib machinery; no shorter complete
   route or duplicated holed statement was found.

4. **Route and pruning: pass.** Read CyclePullbackTower and every proof helper.
   The proof opens the comparison using the actual recursion and existing
   Mathlib limit isomorphisms, then pairs proved projection equations. All three
   imports are needed: the tower supplies the public objects, while both added
   public Mathlib imports occur in the public evaluatedPullbackIso construction
   body. The No longer needed section records the removed circular proof edges
   from the two helpers to the combined theorem; neither old dependency of the
   combined theorem is omitted. No module is pruned. Read
   dag/units/sk-thm-picard-semicon.json: realized.statement is empty and its sole
   realized.steps list is empty, so no realized unit step is bypassed or changed.

5. **DAG agreement: pass.** Compared all four sandbox nodes with the repository.
   The combined node changes only proof/proof_deps/proof_origin; its proof uses
   the canonical constructor and both projection declarations. The first node
   changes only those proof fields and its Lean record to include the proved
   canonical first-projection helper. The second node additionally records its
   declared statement correction, definition dependencies and sole citer.
   The new definition node has source, chapter/unit, blueprint provenance,
   created and Lean records, three recorded searches (including the explicitly
   unavailable LeanSearch service), and empty definition proof dependencies.
   Its data and all its supporting declarations are fully proved, so it adds
   no new task. All proof edges describe the actual canonical route.

Second-reading changes: appended this independent review only. No Lean proof,
statement, import, node or change record needed repair. The delivery closes the
original hole in tower_comparison_first; it also retires the false original
hole in tower_comparison_second in favor of a proved corrected statement. It
adds zero holes, and the unchanged combined comparison is now axiom-clean.
