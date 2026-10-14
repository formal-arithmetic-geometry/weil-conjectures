## What changed

Copied Sheaf.Paper.CartierEquality into the sandbox and verified the existing proof
of cartier_equality by lcompile.py (2.3 seconds, no warnings). Clarified the inline comment at the finite-extension specialization. No signatures,
definitions, imports or DAG records were changed. The proof follows the recorded
complete-intersection model, cotangent model and rank-nullity argument.

## Proved and sorry left

Existing complete proof verified: cartier_equality
(lem-weil-pbc-cartier-equality).
Holes closed by Q2: zero. Holes added: zero. Sorries left in the item: none.
The module already had no sorries when this assignment started. This is verification
of landed work, not new proof progress or decomposition. The two imported model
theorems remain dependencies and are already proved: independent axiom probes of
both and of cartier_equality show only propext, Classical.choice and Quot.sound.
Their proofs are not new progress by Q2.

## No longer needed

None. No imports, nodes or modules are newly pruned. Both project proof imports are
used by the existing argument. The finite-transcendence-basis step is supplied by
Mathlib.FieldTheory.FinTrdeg, as the existing DAG records.

## Where the brief, the DAG or earlier work was wrong

The brief says this module still contains sorry, but the current repository contains
a complete proof and its DAG records Y3's accepted proof landing
20261014T030649-L-345453 on 2026-10-14. The explicit IntermediateField.FG hypothesis
requested by upstream review #1428 is also already present. No repair is needed.


## Second reading by Q2

1. Interface: PASS. Compared every delivered module (one) with the repository
   using diff -u. The only change is the inline comment after `intro hfinite`;
   the existing theorem signature, visibility, definitions and imports are byte
   for byte unchanged. No statement change record is needed.
2. Proof: PASS. Compiled the delivered module with lcompile.py, without errors
   or warnings. A scratch copy with #print axioms for cartier_equality,
   FieldTheory.exists_completeIntersection_fractionField_model and
   Algebra.exists_fractionField_completeIntersection_cotangent_model reports
   exactly propext, Classical.choice and Quot.sound. No sorry or forbidden
   declaration occurs in the delivered module. No data is defined by choosing an
   arbitrary witness from an unproved existence statement.
3. Split statements: PASS (none). No declaration, node or hole is added. Read the
   two existing model theorem statements and proofs: they supply respectively a
   genuine regular-sequence fraction-field presentation and the kernel/cokernel
   linear equivalences, rather than restating the dimension assertion. The zero
   transcendence-degree and zero-dimensional coordinate cases are covered by
   the same natural-number rank-nullity identities, without division or truncated
   cancellation.
4. Route and pruning: PASS. The finite-basis step uses Mathlib FinTrdeg; both
   project proof imports are used directly. The remaining argument is finite
   dimensional rank-nullity, followed by the cardinal cast and finite-extension
   specialization. Launcher msearch grep for `H1Cotangent trdeg` found no match;
   independent rg over lean/Sheaf and lean/WeilConjectures found no alternative
   Cartier formula (only this theorem and its caller). Public imports provide
   notions occurring in the public signature; all proof-only imports are plain.
   No old proof dependency is dropped, so No longer needed remains None.
   Read dag/units/sk-thm-p1.json realized: this below-unit argument preserves the
   route and changes none of its realizations.
5. DAG: PASS. Read lem-weil-pbc-cartier-equality.json, including its recorded
   statement, three proof steps, proof_deps and proof_origin. The Lean proof
   matches the finite basis, complete-intersection model, cotangent model and
   rank-nullity steps. Its recorded Lean signature is identical. No new node is
   required and no existing node needs an update.

Second-reading changes: corrected the report's inaccurate assertion that the two
model proofs remain unresolved; both are already proved with permitted axioms.
Kept the first reader's accurate inline comment. No proof or signature changes.
This delivery verifies one already-proved theorem, closes zero holes, adds zero
holes and splits off zero statements; it claims no new proof progress.
