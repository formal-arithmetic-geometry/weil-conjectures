## What changed

Verified the existing repair and simplified the final witness proof: the Ext.comp_zero
rewrite now closes the goal directly, replacing a separate explicitly instantiated exact step.
The listed repair #1428 was already completed: the witness concludes with the vanishing equation,
with an explicit Ext type on zero, and contains neither an existential proof witness nor True.
Both public theorems and both private helpers have complete proofs. Local compilation passed
in 14.8 seconds without warnings. No signatures, definitions or imports changed.

## Proved and sorry left

Holes closed by this delivery: none (0 of 0). Holes added: none. Sorries left: none.
Already proved: CategoryTheory.Sheaf.exists_presheaf_ext_local_killing_witness
(node lem-sc-presheaf-free-ext-local-killing-witness) and
CategoryTheory.Sheaf.exists_presheaf_ext_local_killing
(node lem-sc-presheaf-free-ext-local-killing), together with the private helpers
epi_locally_surjective and exists_presheaf_cover_lift.
The proof uses Ext.exists_epi_comp_eq_zero from ExtEpiEffacement, whose current source
also has a complete proof. This report does not count the previously landed proofs as new work.

## No longer needed

None. All imports remain needed. The witness uses lem-sc-ext-epi-effacement and the main
conclusion uses the witness, exactly as the current DAG records. No new route or pruning.

## Where the brief, the DAG or earlier work was wrong

The dispatch describes a module containing sorry, but the checked-out module has none.
The node records show a prior proof landing on 2026-10-14. The repair queue still lists
upstream review #1428 although coord/changes/presheaf-ext-local-killing-witness-padding.md
records that the padding repair landed on 2026-10-13. Its corrected statement is already
present. No further statement repair is warranted; only the final proof step was simplified. The unit route is unchanged.

## Second reading by B4

1. **Statements and accidental changes.** Compared the delivered module with the repository version. The only difference is the proof body of `exists_presheaf_ext_local_killing_witness`: the final `Ext.comp_zero` step is included directly in the rewrite. All public theorem signatures, private helper types, definitions, and imports are byte-for-byte unchanged. Verdict: pass.

2. **Proof and axioms.** Compiled `lean/Sheaf/CategoryTheory/Sites/PresheafFreeExtLocalKilling.lean` with `lcompile.py`; it succeeds without warnings. The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition. A scratch `#print axioms` check for both public theorems reports only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.

3. **Statements split off.** No statements were added or split off by this delivery. The existing witness and conclusion nodes are true, retain their exact hypotheses and conclusions, and the module uses the existing `lem-sc-ext-epi-effacement` dependency. Search of the local Lean sources found no duplicate declaration needed for this proof. Verdict: pass.

4. **Route and pruning.** The proof follows the recorded unit route: Ext epi-effacement, local-surjectivity construction, presheaf cover lift, then Ext composition and zero. The rewrite simplification does not bypass any unit step. All current imports are used: the public imports provide the statement-level site and sheaf APIs, while `ExtEpiEffacement` supplies the proof dependency. No pruning is warranted. Verdict: pass.

5. **DAG agreement.** The existing node proof, `proof_deps`, and `proof_origin` agree with the declarations and proof route. No node files or change records require edits. Verdict: pass.

Changed in this second reading: only this report section; the proof body was already the reviewed sandbox change and required no further repair.
