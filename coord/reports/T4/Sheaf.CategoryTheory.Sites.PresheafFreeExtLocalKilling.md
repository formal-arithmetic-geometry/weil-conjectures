## What changed

The assigned module already contains complete proofs of both public theorems
and both private helpers in the repository snapshot. The padded witness conclusion
from upstream review #1428 has already been repaired. Retained all signatures and imports; replaced the witness proof’s final
`simp` step by `exact Ext.comp_zero _ _ _ _ _`; clarified the final theorem's proof documentation to record
that the witness directly supplies the vanishing equation. This is verification
of an already completed repair, not new proof progress.

## Proved and sorry left

Holes closed in this delivery: none (0 of 0). Holes added: none.
No sorry remains in this module. The existing complete declarations are
CategoryTheory.Sheaf.exists_presheaf_ext_local_killing_witness
(node lem-sc-presheaf-free-ext-local-killing-witness) and
CategoryTheory.Sheaf.exists_presheaf_ext_local_killing
(node lem-sc-presheaf-free-ext-local-killing), together with the private helpers
epi_locally_surjective and exists_presheaf_cover_lift. The imported
CategoryTheory.Abelian.Ext.exists_epi_comp_eq_zero is also already proved.

## No longer needed

None. All current imports support the existing statements or proof. The witness
node uses lem-sc-ext-epi-effacement; the final node uses the witness. No new
nodes, modules, or proof dependencies are introduced or pruned.

## Where the brief, the DAG or earlier work was wrong

The dispatch brief says the module still contains sorry, but the checked-out
module has none. Both nodes record the W2 proof landing on 2026-10-14. The repair
queue still names upstream review #1428, although the witness signature already
has an unpadded equality conclusion and its change record records a landed T3
repair. No further signature correction is needed. No new proof is claimed.

## Second reading by T4

1. Compared the sole delivered module with the repository using `diff -u`.
   All four declaration signatures, visibility, constructions and imports are
   byte-for-byte unchanged. The only Lean changes are the explicit `Ext.comp_zero`
   proof step and the final theorem's documentation. No change record is required.
2. Compiled the delivered module with `lcompile.py`: no errors or warnings.
   Compiled a scratch copy with `#print axioms` for both private helpers and both
   public theorems: each uses only `propext`, `Classical.choice`, `Quot.sound`.
   Scanned for forbidden declarations and sorry: none. The presheaf is explicitly
   constructed as a subtype of pairs; no data is chosen from an unproved theorem.
3. No statements or holes were split off or added. Read the construction for empty
   presheaves, zero classes, and q=1: empty fibers cause no exception, and positive
   degree effacement supplies the required epimorphism. The existing witness is
   fully proved, so the final theorem's equivalent conclusion conceals no hole.
4. Read the proof top downward and searched Mathlib with `msearch.py` grep for
   `isLocallySurjective_iff_epi`, plus source searches in both Lean roots.
   The Type-valued equivalence does not apply directly to abelian sheaves;
   the general EpiMono variant additionally assumes WEqualsLocallyBijective,
   absent here with an unrestricted object universe and Type v values. Retained
   the correct image-subsheaf argument. Both public imports provide signature
   vocabulary and instances; ExtEpiEffacement remains a private proof import.
   Every old proof dependency is used, so `No longer needed: None` is complete.
   Read sk-prop-cd.json: its realized entries are unchanged and no unit is bypassed.
5. Read both item nodes, the effacement dependency, and the landed padding change
   record. The signatures match their lean.statement fields; proof steps,
   proof_deps and proof_origin agree with the actual proof. No new node is needed.

Second-reading changes: corrected `What changed` to disclose the existing
explicit Ext.comp_zero edit, and corrected the reported prior proof group from
V1 to W2. Retained the correct Lean proofs. This delivery closes 0 holes out of
0 and adds 0 holes; it verifies an existing completed repair, not new progress.
