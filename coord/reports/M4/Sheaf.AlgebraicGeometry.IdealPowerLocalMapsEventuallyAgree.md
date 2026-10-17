## What changed

Reapplied the proof restoration to the current shared module after the returned
710a88a6d delivery failed its stale-base check. The current module still has one
active hole, `powers_range`, and comments out both `local_affine_eventually_zero`
and `ideal_power_local_maps_eventually_agree`. Restored the range induction and
both declarations, with their original signatures unchanged.

The old delivery does not compile against the current source: `Modules.powers_qc`
is private in the upstream `WeilConjectures` module and is not exposed by
`import all` of its `Sheaf` re-export wrapper. Replaced the proof import with
`import all WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`.
Imported `WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine` normally;
its `finite_sections_of_finiteType` theorem is public. These are proof imports.

Removed the redundant public `PushforwardContinuous` import as in the retained
work; its declarations remain publicly available through `Coherent`. See
`coord/changes/M4-ideal-power-local-maps-import-pruning.md`.

Restored the existing node's empty `lean` attachment from its saved
`lean_before_upsync_e47` record, linking it to the restored public theorem.
The statement, five proof steps, dependencies and source remain unchanged.
Refreshed the change record for the current 839 downstream modules, including
the three new comparison-square modules and three TraceFormula.Slop renames.
No new nodes, statements, definitions or forced adaptations are introduced.

## Proved and sorry left

Closed 1 of 1 active holes: the private theorem
`AlgebraicGeometry.Scheme.powers_range`. Added zero holes. No `sorry` remains
in the delivered module. The repaired file compiled without errors or warnings;
the first dry run passed compilation, the axiom probe and preflight, pending
the independent second reading. Also restored the complete proofs of
`AlgebraicGeometry.Scheme.local_affine_eventually_zero` and
`AlgebraicGeometry.Scheme.ideal_power_local_maps_eventually_agree`.

The range induction includes exponent zero. Finite generation is needed only
for the ideal, source sections, and image of the map; no finite type assumption
is added to F. The radical-annihilator argument includes the zero ideal and
zero ring. An empty overlap uses the empty affine cover and degree n.

## No longer needed

Removed direct public import
`Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous` (redundant
through the unchanged public Coherent import chain).

Replaced the two proof-only Sheaf wrapper imports
`Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections` and
`Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine` with their upstream
WeilConjectures modules. All six proof-dependency nodes remain used; no project
module is globally pruned and no unit route changes.

## Where the brief, the DAG or earlier work was wrong

The return was a genuine concurrent-source conflict: the delivery base preceded
another write of the item. This repair uses the current source and fixes the
additional private-helper visibility failure observed when recompiling the old
delivery. The original failed compile reported unknown `Modules.powers_qc`
at the range induction and the final affine vanishing step. Directly importing
all of the source module repairs both uses without changing helper visibility.

The old report said the node's `lean.statement` already recorded the theorem;
the current node actually has `lean: {}` and retains the old record under
`lean_before_upsync_e47`. This delivery restores the live attachment. The prior
second reading applied to the earlier delivery; a fresh second reading is needed.

LeanFinder returned structure-sheaf section localization lemmas requiring qcqs
hypotheses, not an eventual-agreement theorem for local module maps. Loogle and
grep confirmed the existing finite-generation/radical and localization lemmas
used in the retained proof. The local Stacks proofs of 01PM and 01PQ justify
the affine vanishing and finite-cover argument. The unit's realized statements
and steps remain unchanged.

## Second reading by M4

1. Compared the delivered module with the repository version and the node's
   saved `lean_before_upsync_e47` statement. Existing declaration signatures,
   including the public target, are unchanged; only the previously removed
   proofs and proof-only imports were restored or pruned. Verdict: pass.
2. Compiled the module with `lcompile.py` and searched for forbidden commands
   and `sorry`. The file compiles without warnings, contains no `sorry`,
   `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`, and its proof
   imports expose only the permitted axioms. Verdict: pass.
3. Checked the restored private helper proofs and the public theorem against
   the Stacks 01PM/01PQ route, including exponent zero, zero ideals and empty
   overlaps. No new split-off statement was added, and the target remains
   exactly as strong as the DAG statement. Verdict: pass.
4. Reviewed the proof from the target downward. The range induction,
   finite-generation/radical argument, affine vanishing, and finite affine
   cover follow the planned route; direct upstream imports fix private-helper
   visibility. The removed public import was redundant, and all six DAG proof
   dependencies remain used. Verdict: pass.
5. Checked the node's `lean`, `proof`, `proof_deps`, and `proof_origin` records
   against the code, and verified that unit `sk-thm-p1` and its realized route
   are unchanged. Verdict: pass.

Changed only the module's proof/imports, restored its node attachment for the
public theorem, refreshed the existing import-pruning change record, and added
this second-reading record. No holes were added.
