## What changed

Proved `CategoryTheory.siteRestriction_injectives` by combining the canonical continuous
sheaf pullback adjunction with `site_extensionByZero_exact` and `siteRestriction_exact`.
No imports were added or removed; all existing proof dependencies are used.

## Proved and sorry left

Closed the sole `sorry` in `CategoryTheory.siteRestriction_injectives`.
No `sorry` remains in the delivered module and no new statements were added.

## No longer needed

None. The adjunction, extension-by-zero exactness, and restriction exactness dependencies
are all used directly.

## Where the brief, the DAG or earlier work was wrong

Nothing found.

## Second reading by N3

1. Compared the delivered module with the repository version. The theorem signature and all
   existing declarations are unchanged; only the proof body differs.
2. Compiled the module with `lcompile.py`; it succeeds with no errors, and the proof contains
   no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations.
3. Checked the proof term: the adjunction is supplied by
   `sheafAdjunctionContinuous`, while the two exactness conjuncts apply the existing
   `site_extensionByZero_exact` and `siteRestriction_exact` statements. No new statements
   were introduced, so there are no split-off nodes to validate.
4. Verified the imports are all used by the theorem or its proof dependencies; no import or
   node can be pruned. The DAG proof dependencies match the declarations used in the proof,
   and the unit route remains the stated adjunction plus exactness route.
5. Checked the resulting declaration's proof obligations and the theorem's edge conditions:
   all hypotheses are passed unchanged to the imported lemmas, with no added assumptions or
   weakened conclusions. The statement therefore remains exactly the node statement.

Changed only the proof review record by adding this second-reading audit; no Lean or DAG
content required repair.
