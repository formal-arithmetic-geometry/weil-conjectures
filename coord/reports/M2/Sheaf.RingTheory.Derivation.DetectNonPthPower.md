## What changed
Added two named intermediate theorems isolating the fraction-field derivation and denominator-clearing steps. The target theorem now combines them in a complete Lean proof. The intermediate proofs remain `sorry` as strictly smaller obligations.

## Proved and sorry left
Closed `Derivation.exists_apply_ne_zero_of_not_pth_power`. Sorries remain in `Derivation.exists_fraction_field_derivation_of_not_pth_power` and `Derivation.exists_domain_derivation_of_fraction_derivation`, each recorded by a new node.

## No longer needed
No imports or existing nodes were pruned.

## Where the brief, the DAG or earlier work was wrong
The six-step DAG route cannot be completed directly within this item; the two intermediate statements expose the fraction-field and denominator-clearing obligations separately.

## New nodes
Added `lem-weil-pbc-fraction-field-derivation-nonzero` and `lem-weil-pbc-domain-derivation-from-fraction`.

## Earlier second reading (a previous round; superseded)
The target proof compiles and uses only the two strictly smaller intermediate statements. Their proofs remain open for subsequent workers.

## Second reading by M2
1. Compared the delivered module with the repository version. The target declaration's
   signature and all existing declarations are unchanged; only its proof and two explicitly
   split intermediate declarations were added.
2. Compiled the module with `lcompile.py`; it succeeds. The only remaining `sorry`s are the
   two named intermediate theorems, each public, documented, and represented by a DAG node.
3. Checked the two split statements against Lemma 07PH. The fraction-field statement is the
   field-valued Steps 1--5 obligation, and the domain statement is the denominator-clearing
   Step 6 obligation. Both are true, strictly below the target proof, and use no altered target
   hypothesis or conclusion. No existing Mathlib or Sheaf declaration duplicates them.
4. The target combines the two split obligations directly, preserving the unit route through
   fraction-field detection followed by denominator clearing. No unused imports or old proof
   dependencies were identified.
5. The node records match the Lean declarations, sources, proof origins, and `split` status;
   both new nodes carry the required documentation and module metadata.

Changed only the report by recording this review. No Lean statements, definitions, imports, or
DAG records were changed during second reading.
