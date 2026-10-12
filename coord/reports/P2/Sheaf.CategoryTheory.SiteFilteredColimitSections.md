## What changed
Added the auxiliary theorem `siteFilteredColimit_sections_inverse` as the explicit inverse step, and proved `siteFilteredColimit_sections_bijective` from it using `Function.bijective_iff_has_inverse`.

## Proved and sorry left
`siteFilteredColimit_sections_bijective` is proved. `siteFilteredColimit_sections_inverse` remains sorry (node `aux-site-filtered-colimit-sections-inverse`). `siteFilteredColimit_sections_isIso` remains sorry (node `lem-weil-pbc-site-filtered-colimit-sections-finite-coverings`).

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The inverse construction and abelian-group comparison remain substantial sheaf-colimit arguments; the bijectivity declaration can be reduced cleanly to the named inverse statement.

## New nodes
`aux-site-filtered-colimit-sections-inverse` (existing sandbox node) records the inverse construction used by the proved bijectivity theorem.

## Earlier second reading (a previous round; superseded)
The bijectivity proof applies the inverse equations directly and preserves the target statement. The auxiliary inverse statement has exactly the canonical map and is strictly a component of the argument.

## Second reading by P2

1. I compared the delivered Lean module with the repository version. Existing declaration
signatures and definitions are unchanged byte for byte; the only additions are the named
auxiliary inverse theorem and the proof of `siteFilteredColimit_sections_bijective`.
Verdict: pass.

2. I compiled all sandbox modules with `lcompile.py --all`; compilation succeeds. The only
remaining `sorry`s are the two named split theorems listed in the report, with no hollow
definitions, forbidden declarations, or unexpected diagnostics. A scratch `#print axioms`
check shows the proved declaration uses only the allowed axioms plus `sorryAx` transitively
through the explicitly split inverse theorem. Verdict: pass.

3. The inverse statement is a genuine two-sided inverse assertion for the canonical map,
strictly smaller than the item and mathematically sufficient. It has the required source,
docstring, node, and recorded search audit; no existing Mathlib or Sheaf declaration
duplicates it. Verdict: pass.

4. The bijectivity proof takes the shortest available route through
`Function.bijective_iff_has_inverse`; no imports were removable because the module's public
statements and typeclass assumptions use them. The item node proof and dependencies were
pruned to the auxiliary inverse node, while the remaining isomorphism theorem stays split.
Verdict: pass.

5. The DAG proof and `proof_deps` now match the Lean proof. The unit `sk-thm-p1` route and
its realized steps are preserved; this auxiliary reduction does not bypass a unit step.
Verdict: pass.

I changed the item node's proof metadata to record the actual inverse reduction and appended
this second-reading record. No Lean proof text required repair.

## Second reading by P2

1. I compared the delivered Lean module with the repository version. Existing declaration
signatures and definitions are unchanged byte for byte; the only additions are the named
auxiliary inverse theorem and the proof of `siteFilteredColimit_sections_bijective`.
Verdict: pass.

2. I compiled all sandbox modules with `lcompile.py --all`; compilation succeeds. The only
remaining `sorry`s are the two named split theorems listed in the report, with no hollow
definitions, forbidden declarations, or unexpected diagnostics. A scratch `#print axioms`
check shows the proved declaration uses only the allowed axioms plus `sorryAx` transitively
through the explicitly split inverse theorem. Verdict: pass.

3. The inverse statement is a genuine two-sided inverse assertion for the canonical map,
strictly smaller than the item and mathematically sufficient. It has the required source,
docstring, node, and recorded search audit; no existing Mathlib or Sheaf declaration
duplicates it. Verdict: pass.

4. The bijectivity proof takes the shortest available route through
`Function.bijective_iff_has_inverse`; no imports were removable because the module's public
statements and typeclass assumptions use them. The item node proof and dependencies were
pruned to the auxiliary inverse node, while the remaining isomorphism theorem stays split.
Verdict: pass.

5. The DAG proof and `proof_deps` now match the Lean proof. The unit `sk-thm-p1` route and
its realized steps are preserved; this auxiliary reduction does not bypass a unit step.
Verdict: pass.

I changed the item node's proof metadata to record the actual inverse reduction and appended
this second-reading record. No Lean proof text required repair.
