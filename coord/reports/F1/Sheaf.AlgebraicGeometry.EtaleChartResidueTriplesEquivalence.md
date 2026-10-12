## What changed

Repair of reviewer X-7ead6 point 2: replaced both truncated signature blocks in
`coord/changes/etale-chart-ring-iso-retirement.md` with the complete old and new
declaration signatures verbatim, including all let clauses and conclusions.
Verified each block against its corresponding Lean source. No Lean or DAG changes
were needed for this repair.

Retired the unused disputed declaration
`AlgebraicGeometry.Scheme.etale_chart_residue_triples_equivalence_ring_iso`.
Corrected its node `split-etale-chart-ring-iso` to the source's existential
compatible-equivalence assertion and attached it to the already proved combined
theorem. Preserved both existing proofs, all remaining signatures and all imports.
The previous attempt's alternative spectrum construction is archived in scratchpad
and is excluded from this delivery: the current library already proves the results.

Change record: `coord/changes/etale-chart-ring-iso-retirement.md`.

Validation: the item compiled cleanly through lcompile.py (8.6 seconds).
The delivery dry run printed OK and passed preflight except for the second reading,
which is reserved for the independent reader. Nothing was pushed.

## Proved and sorry left

Holes proved: none. Holes added: none. Holes retired: one, the unused false
`AlgebraicGeometry.Scheme.etale_chart_residue_triples_equivalence_ring_iso`
(node `split-etale-chart-ring-iso`). This is a statement correction and retirement,
not a proof of the old universal statement and not a decomposition.
There are no direct sorries left in the item. The two existing equivalence theorems
retain their baseline proofs and their dependencies unchanged.

## No longer needed

The universal arbitrary-equivalence assertion of `split-etale-chart-ring-iso`
is no longer needed; no Lean declaration or DAG node cites it. The corrected node
uses the existing source-correct combined theorem. No imports or modules are removed.
No realized unit statement or step is bypassed.

The corrected node no longer uses these old proof dependencies:

- `def-weil-open-immersion`
- `def-weil-affine-spectrum`
- `def-weil-residue-field`
- `def-weil-geometric-point`
- `def-weil-pbc-relative-separable-closure`
- `def-weil-pbc-etale-residue-triples`
- `lem-weil-pbc-etale-composition-cancellation`
- `def-weil-pbc-pointed-etale-neighbourhoods`
- `def-weil-etale-morphism`

This removes edges from the corrected node only. The retained combined theorem
still uses affine spectrum and the chart construction/fullness/essential-surjectivity
route. No module becomes unreachable as a result of this retirement.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: an arbitrary equivalence need not preserve the pointed ring
diagrams. The source constructs one compatible equivalence. Twisting embeddings
by an automorphism of an algebraic closure of Q contradicts the alleged formulas
on the nonnormal real cubic field Q(cuberoot(2)); the complete argument appears in
the change record. Previous retries replaced an already proved functor theorem,
so correctly failed the “nothing is proved” guard. This delivery instead retires
the unused false assertion under the statement-correction rules.

The source-correct existential theorem already has a complete proof in the current
baseline. No false result is proved, no target is weakened, and no new hole is used.
The statement_change schema requires the historical by-format “F1 stage 2” even
for a stage-3 correction; proof_origin records the stage-3 worker accurately.

## Earlier second reading (a previous round; superseded)

1. **Visible declarations:** Compared the delivered module with the repository version. The only declaration change is the intentional retirement of `etale_chart_residue_triples_equivalence_ring_iso`, documented in `coord/changes/etale-chart-ring-iso-retirement.md`; all retained declaration signatures and imports are byte-for-byte unchanged.
2. **Compilation and axioms:** Recompiled the module with `lcompile.py`; it succeeds. The retained theorems contain no `sorry`, and the delivery introduces no axioms, unsafe declarations, or hollow definitions. The retired declaration is not reintroduced.
3. **Statements and nodes:** The universal compatibility assertion is false in general, as documented by the counterexample in the change record. The corrected DAG node records the source-correct existential compatible equivalence and points to the existing theorem; no new split-off theorem or hole is added.
4. **Pruning and route:** The retained proofs use the existing construction, full-faithfulness, and essential-surjectivity results. No import can be removed without changing the public proof environment, and no realized unit statement or step is bypassed. The retired declaration has no downstream users.
5. **DAG agreement:** The module proofs and the node's `proof`, `proof_deps`, `proof_origin`, and statement-change record agree: the combined theorem supplies the existential result, while the false universal declaration is retired. The delivery dry run passes all checks except this section before it was added.

Changed during second reading: added this review record only; no Lean source, node, or change record was altered.


## Second reading by F1

1. **Visible declarations — pass.** Diffed the sole delivered Lean module against
   the repository. Only the explicitly disputed, unused
   `AlgebraicGeometry.Scheme.etale_chart_residue_triples_equivalence_ring_iso`
   is removed, as recorded in `coord/changes/etale-chart-ring-iso-retirement.md`.
   Both retained theorem signatures, proofs, the private faithfulness lemma,
   all definitions and all imports are byte-for-byte unchanged. Checked both full
   signature blocks in the change record against the respective Lean sources;
   they match verbatim. `tools/downstream.py --uses` finds only the retired
   declaration itself among 248 downstream modules and the item; no adaptation
   is needed. No target signature or definition changes.
2. **Proof and axioms — pass.** Compiled the delivered module with `lcompile.py`
   without errors or warnings (8.9 seconds). A fresh scratch copy of this exact
   module, not the archived alternative construction, compiled with `#print axioms`
   for both retained equivalence theorems (8.4 seconds). Each uses exactly
   `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.
   Scanned the delivered Lean tree: no `sorry`, forbidden declarations or hollow
   definitions. The proof obtains H, δ and the formulas from the construction,
   proves faithfulness using affine global sections, applies fullness and essential
   surjectivity, and retains δ and its formulas under H.asEquivalence.
3. **Split statements and mathematics — pass.** No new statement, split-off theorem
   or hole is introduced. Read Stacks
   [04HX](https://stacks.math.columbia.edu/tag/04HX), proof's affine-neighbourhood
   translation, and [04HT](https://stacks.math.columbia.edu/tag/04HT), residue
   embeddings. They justify the constructed translation, not the retired universal
   claim. Checked the change record's counterexample with A = Q and Ω = Qbar:
   residue embeddings lie in K, twisting by a Q-automorphism preserves triples
   and their morphisms, but for L = Q(cuberoot(2)) a twist to a nonreal conjugate
   changes the embedded subfield. An invertible δ cannot change the image of L;
   hence the claimed point formula fails. The identity twist causes no such
   obstruction, consistent with the retained existential theorem.
4. **Route and pruning — pass after report repair.** Read the construction,
   fullness and essential-surjectivity interfaces and the main node's proof plan.
   The unchanged proof is their direct assembly, with elementary affine
   faithfulness; no shorter replacement or new statement is needed. The three
   public imports support the signatures (pointSmallEtale, ΓSpecIso, triples);
   the three plain imports are used by the proofs. Inspected
   `dag/units/sk-thm-p1.json`: the retired node is not in its realized statement
   or steps, and no unit route changes. Added all nine removed old proof
   dependencies under `## No longer needed`; no imports or modules are pruned.
5. **Node agreement — pass.** The corrected node's statement and Lean signature
   match those of `lem-weil-pbc-etale-chart-residue-triples-equivalence` exactly.
   Its single proof step cites that existing theorem, and proof_deps is precisely
   that citation; proof_origin explains the retirement. This is reuse of an
   already proved theorem, not a new sorry restating the item. The historical
   universal signature, former dependencies and source are preserved in
   statement_change. Searched all DAG nodes and units: there are no citers of
   the retired node. No new node was added.

Changed during this second reading: completed the removed-dependency list,
updated the downstream count in the change record from 237 to 248, and appended
this independent review. No Lean or DAG changes. Holes proved: zero of the one
baseline hole; holes retired: one false unused statement; holes added: zero.
