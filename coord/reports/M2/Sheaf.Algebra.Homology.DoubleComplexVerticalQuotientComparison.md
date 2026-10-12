## What changed

Replaced the first worker's equivalent mapping-cone acyclicity hole with a real
columnwise reduction. The original module now proves
`HomologicalComplex₂.verticalQuotientToLower_total_quasiIso` by evaluating the
actual cokernel, applying the restricted complementary truncation comparison,
and assembling the existing first-quadrant cone filtration and degreewise filtered
acyclicity APIs. Added the new helper module
`Sheaf.Algebra.Homology.RestrictedComplementaryTruncationComparison`.
All added imports in the original module are proof-only `import`s; its original
public import, declarations, definitions, signatures and docstrings are unchanged.
Removed the first worker's mapping-cone theorem and its cyclic DAG node.

## Proved and sorry left

Closed one original hole:
`HomologicalComplex₂.verticalQuotientToLower_total_quasiIso`.
Added one strictly simpler hole:
`CochainComplex.restrictedComplementaryTruncationComparison_quasiIso`, node
`lem-sp-restricted-complementary-truncation-comparison`, in its own new module.
No sorry remains in the item's module. This is a decomposition, not a net proof:
one original hole closed, one lower hole added, net zero. The proof also relies on
existing open statements in the cone-filtration and filtered-complex import closure;
these are not new holes added by this delivery.

## No longer needed

The first worker's newly added public MappingCone import, equivalent cone-acyclicity
theorem and new acyclicity node were removed before delivery. No repository import
was removed and no module was pruned. The old direct proof dependency
`def-sp-double-complex-vertical-window` is no longer needed in the proof route; it
remains a statement dependency and its module remains transitively imported by
DoubleComplexVerticalTowerMaps. The old proof dependency
`lem-sp-double-complex-vertical-tower-maps` remains, since its actual cutoff
construction is used in the evaluated cokernel proof.

## Where the brief, the DAG or earlier work was wrong

The first worker's mapping-cone acyclicity statement was equivalent to the whole
item by Mathlib's cone criterion, not strictly part of the argument. Its proof_deps
also cited the very target it was meant to prove, giving a circular plan. Its
remaining-hole docstring omitted the full comparison and transport argument.
Contrary to its report, existing first-quadrant cone-filtration and degreewise
filtered-acyclicity APIs already support the totalization assembly. Only the
restricted complementary truncation/cokernel transport step is left open here.
The unit's existing realized record is unchanged; no node used by that record is
bypassed (the realized statement and step lists are empty for this imported unit).

## New nodes

`lem-sp-restricted-complementary-truncation-comparison` states the comparison for
any cokernel cofork of the restricted canonical upper inclusion, with the canonical
projection factorization equation. It involves one natural-indexed complex and no
totalization, so it is strictly the column step. Its docstring explains the cokernel
transport, integer Mathlib comparison, homology at zero and all endpoint cases.
Actual leanfinder, loogle and grep searches found the integer comparison but no
exact restricted cofork theorem; leansearch was unavailable and is recorded as such.
No interface change record is needed.

## Second reading by M2

1. Compared both delivered modules against the repository. The helper module is new.
   In the existing module every signature, definition body, visibility and docstring
   is byte-for-byte unchanged; only proof imports and the original sorry body changed.
   No existing statement or definition was altered. Verdict: pass.
2. Compiled both modules locally in import order through lcompile.py, with no errors
   or warnings. Checked all delivered source for forbidden declarations and hollow
   definitions; the only remaining sorry is the named helper theorem. Printed axioms
   for every declaration in the existing module and the new theorem in scratch copies:
   only propext, Classical.choice, Quot.sound and expected sorryAx from open statements.
   Verdict: pass as a decomposition, not a sorry-free proof.
3. Checked the remaining helper's statement and universal-property hypotheses. Its
   map is uniquely determined by the factorization equation and cokernel cofork.
   Tested zero columns, a<=0 (isomorphism), a=1, a positive boundary, and a column
   concentrated in degree zero. Restriction is justified at degree zero by vanishing
   negative terms, not by a false general restriction-preserves-quasi-isomorphisms
   claim. Read Mathlib's integer comparison and searched with different queries;
   no exact restricted cofork result was found. Complete proof docstring and matching
   node supplied. Verdict: true and strictly simpler; remains open.
4. Used existing APIs for the totalization argument; all added original-module
   imports are proof-only and used. The helper has one public Mathlib import required
   by its signature. All retired candidate additions and old direct proof dependencies
   are accounted for above. Read sk-prop-av-pqf-finite.realized: unchanged, with no
   required realized node removed. Verdict: route preserved; no modules pruned.
5. Updated the original node's proof, proof_deps and proof_origin to match evaluation,
   the helper, the cone filtration and degreewise acyclicity. Added a complete new node
   whose statement matches the Lean signature and whose proof_deps equals the union of
   proof-step uses. No dependency back to the original theorem; no cycle.
   Verdict: pass.

Second reading changed the equivalent cone restatement into a compiled columnwise
reduction, moved the one remaining obligation into its own reusable module, restored
the original target docstring, removed the accidental public proof import, and
repaired the report and DAG route.
