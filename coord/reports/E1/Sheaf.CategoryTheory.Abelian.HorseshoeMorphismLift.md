## What changed

Added and proved `CategoryTheory.InjectiveResolution.corrected_middle_map`, the
strict final algebraic correction step of the horseshoe argument. It takes a
preliminary middle map and a defect correction map satisfying the row, differential,
and augmentation identities, and constructs the corrected middle map. The requested
`exists_horseshoe_morphism_lift` declaration and signature are unchanged.

## Proved and sorry left

`CategoryTheory.InjectiveResolution.corrected_middle_map` is proved by composition
linearity. `CategoryTheory.InjectiveResolution.horseshoe_preliminary_data` remains `sorry` (node
`lem-weil-pbc-horseshoe-preliminary-data`), and the target
`CategoryTheory.InjectiveResolution.exists_horseshoe_morphism_lift` is proved from it; the
preliminary construction is the degreewise splitting, defect factorization, and null-homotopy
construction are not yet formalized. The remaining target sorry is recorded by its
existing node `lem-weil-pbc-horseshoe-morphism-lift`.

## No longer needed

None; the existing import is still needed for the target statement.

## Where the brief, the DAG or earlier work was wrong

The previous attempt split off an equivalent restatement of the target. This delivery
replaces that with a strict sublemma: it only performs the final correction once the
intermediate maps and their identities have been constructed.

## New nodes

`lem-weil-pbc-horseshoe-correction` records the proved strict correction lemma.

`lem-weil-pbc-horseshoe-preliminary-data` records the Step 1--3 intermediate datum,
which remains a named sorry for a subsequent worker.

## Earlier second reading (a previous round; superseded)

The target signature is unchanged. The correction lemma is a strict algebraic
substep, and the preliminary-data theorem is the remaining Step 1--3 construction;
its `sorry` is explicitly recorded by its new node. The target proof combines these
with the proved correction lemma.

## Second reading by E1

1. **Declarations unchanged.** I diffed the delivered module against the repository
version. The existing target signature is byte-for-byte unchanged; the only additions
are the two declarations recorded in the new DAG nodes.

2. **Compilation and proof status.** The module compiles with `lcompile.py`. There are
no forbidden commands or hollow definitions. `corrected_middle_map` is fully proved;
the only remaining `sorry` is the named `horseshoe_preliminary_data`, and its source,
natural-language proof plan, and matching split node are recorded.

3. **Statement review.** `corrected_middle_map` is a true strict algebraic reduction:
it constructs `χ - q` and uses composition linearity. `horseshoe_preliminary_data`
contains the intermediate maps and their required identities, while leaving the actual
Step 1--3 construction open; it is therefore strictly smaller than the target and is
not an equivalent restatement. Searches recorded by `msearch.py` found no existing
declaration.

4. **Pruning and route.** The target still uses the prescribed preliminary-data route
and the final correction step. No existing import or proof dependency became unused;
the public Mathlib import is needed by the statements.

5. **DAG agreement.** The correction node records its elementary proof and has no
proof dependencies. The preliminary-data node records its split status, exact Lean
statement, source, and proof dependencies. The target proof now follows these two
declarations exactly, and the unit route remains unchanged.

Changed only the report: no Lean repair was necessary after compilation and diff review.
