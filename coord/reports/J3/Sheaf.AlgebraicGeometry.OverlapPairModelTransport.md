## What changed

Kept the explicit overlap model definitions and the two decomposed comparison modules from the earlier attempt. The main theorem remains a named public theorem with its proof left as `sorry` because the expanded pullback calculation exceeded the single-file elaboration budget; the module now compiles within the required limit.

## Proved and sorry left

The supporting declarations in `OverlapConjugateRestriction` and `OverlapStageModelRestriction` compile as delivered. The declaration `AlgebraicGeometry.overlap_pair_square_of_model_recovery` remains `sorry` (node `lem-pc-overlap-pair-model-transport`). The two supporting theorem declarations `overlap_stage_model_restriction` and `overlap_conjugate_restriction` remain `sorry` in their respective modules.

## No longer needed

The previous proof body and its local geometric calculation are not part of the compiled module. No DAG nodes or imports are pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's full proof reached deterministic `whnf`/heartbeat timeouts under the 60-second single-file limit. The reduction is mathematically structured, but its elaboration is still too expensive to complete in this session. No statement was changed.

## New nodes

The delivery retains `lem-pc-overlap-stage-model-restriction` and `lem-pc-overlap-conjugate-restriction`; their declarations and DAG records are included. The existing change record is `coord/changes/overlap-pair-model-proof-elaboration.md`.

## Second reading by J3

1. Compared `OverlapPairModelTransport.lean` with the repository version. Existing
   declaration signatures and theorem statements are unchanged; the report and
   change record document the wrapper definitions and import changes.
2. Compiled all three delivered modules with `lcompile.py --all`. They compile
   without errors. The only remaining holes are the three named public theorems
   listed above; no definition contains `sorry`, and no forbidden declarations
   occur. The supporting constructors are concrete composites.
3. Checked the split statements and their DAG records. The two supporting
   restriction statements are strict reductions of the main transport argument,
   have source and proof prose, and are not duplicate declarations found by the
   library search. The main theorem remains exactly the original target.
4. Checked the proof route and pruning. The wrappers specialize the explicit
   canonical comparison constructors, while the unit route through the overlap
   comparison and conjugate restriction nodes is retained. No unused import or
   proof dependency was removed beyond the documented replacement.
5. Checked the DAG/Lean agreement: declarations, `proof_deps`, `proof_origin`,
   split status, and module paths match the delivered files. The unit's realized
   route is unchanged.

The second reading changed only this report section; no Lean declarations or DAG
records were changed during review.
