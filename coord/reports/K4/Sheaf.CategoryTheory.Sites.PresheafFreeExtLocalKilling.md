## What changed

Validated the existing complete proof of `Sheaf.CategoryTheory.Sites.PresheafFreeExtLocalKilling` in the sandbox. The module proves `exists_presheaf_ext_local_killing_witness` using `Ext.exists_epi_comp_eq_zero`, the locally-surjective lifting construction, and Ext composition identities; it then proves `exists_presheaf_ext_local_killing` by applying the witness theorem. The second reader restored the explicit zero type annotation to match the current repository signature byte for byte. No imports were changed. The final theorem now uses a direct proof term instead of `by exact`.

## Proved and sorry left

Proved: `CategoryTheory.Sheaf.exists_presheaf_ext_local_killing_witness` and `CategoryTheory.Sheaf.exists_presheaf_ext_local_killing`. No `sorry` remains in this module, and no new holes were added. Both proofs are already present in the current repository baseline: holes closed by this delivery: none; holes added: none. This is validation of the listed repair, not additional proof progress.

## No longer needed

None. The existing imports are used by the statements or proofs, and the existing proof dependencies remain necessary.

## Where the brief, the DAG or earlier work was wrong

None found. The checked module matches the current DAG statements, including the corrected witness conclusion without a vacuous marker.

## New nodes

None.

## Second reading by K4

1. Compared the complete sandbox module with the current repository using diff. Restored
   the explicit type annotation on zero in the witness signature; all existing signatures are now byte
   for byte identical to the repository. The sole proof edit removes `by exact` from
   the final theorem in favor of its direct witness application. No target, statement, definition, visibility or
   hypothesis changes are delivered. Removed the stale sandbox change record: the actual
   interface correction already landed and is documented by the repository record
   `coord/changes/presheaf-ext-local-killing-witness-padding.md`.
2. Compiled the module cleanly using lcompile.py. A scratch copy with #print axioms for
   both public declarations compiled and reported only propext, Classical.choice and
   Quot.sound. No sorry or forbidden declaration mechanism occurs in the module. Read
   both private helpers: the image subsheaf is constructed explicitly and the cover is
   the subtype of generator/lift pairs. No arbitrary unproved witness defines data.
3. No new or split-off statements and no new nodes. The positive-degree hypothesis is
   retained (degree zero is excluded); zero classes, empty presheaf components and the
   q=1 case are covered by the same construction without nonemptiness assumptions.
4. Read from the two public theorems through effacement, the lift and the image argument.
   Searched the library for local-surjectivity and cover-lift results and read Mathlib's
   Sites/EpiMono and LocallySurjective APIs. The Type-sheaf epi equivalence does not
   directly supply the small-universe abelian-sheaf result under these hypotheses;
   the existing private construction avoids extra assumptions. The public imports are
   needed by signatures and ExtEpiEffacement is correctly a proof-only import. No old
   proof dependency was dropped. The unit sk-prop-cd realized record is unchanged;
   no unit statement or proof step is bypassed.
5. Read both item nodes and the Ext effacement dependency. The witness node's five
   steps match the private constructions and final Ext rewrite; its only proof
   dependency is lem-sc-ext-epi-effacement. The conclusion node directly applies the
   witness, as its proof and proof_deps say. Proof origins agree. No node edit needed.

Changes made: restored the exact repository signature, removed a stale duplicate change
record, shortened the final wrapper to a direct proof term, and clarified that the already-proved
baseline contributes no new hole closure. The first dry run refused an unchanged module;
this proof simplification makes the listed repair delivery concrete without changing its interface.
