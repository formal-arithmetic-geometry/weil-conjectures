## What changed

Added two strictly smaller component theorems, each isolating one conjunct of the target characterization, and proved the target by combining them. The component proofs remain named `sorry` obligations for parallel workers. Added proof-only imports for the two component modules.

## Proved and sorry left

The target `ModuleCat.hasProjectiveResolutionLE_iff_ext_vanishing` is proved by a real conjunction of the two component theorems. Sorry remains in `ModuleCat.projective_resolution_ext_degree` and `ModuleCat.projective_resolution_ext_all_degrees`, each with a corresponding new DAG node.

## No longer needed

No stated dependency imports were removed; all existing imports remain available for the component proofs. The target proof itself uses only the two component declarations.

## Where the brief, the DAG or earlier work was wrong

The original target was too large to close directly within this worker session. Its conjunction naturally decomposes into two strict component equivalences, which are suitable independent stage-3 items.

## Second reading by T1

1. Compared the delivered characterization module with the repository version. The target
   declaration is byte-for-byte unchanged; only its proof and proof-only imports differ.
   Verdict: passed.
2. Compiled all three sandbox modules with `lcompile.py --all`. There are no errors or
   warnings, and the only remaining `sorry`s are the two named split component theorems.
   No forbidden declarations or hollow definitions were introduced. Verdict: passed.
3. Checked both split statements against the two conjuncts of the target. Each has the
   same hypotheses and one strictly smaller conjunct as conclusion, with no weakening.
   Their docstrings now record the induction, long-exact-sequence, and splicing argument;
   each has a corresponding DAG node whose Lean statement is recorded verbatim. Verdict:
   passed.
4. The target proof uses the two component declarations directly, preserving the unit
   route; no shorter proved declaration was available. Duplicate proof-only imports were
   removed. Verdict: passed.
5. Verified the DAG proof dependencies and origins describe the two component obligations
   and the target's conjunction proof. Verdict: passed.

Changed the characterization imports to remove duplicate proof-only imports, expanded the
component theorem proof docstrings, and corrected both new node statements and Lean
declaration records to describe the exact component signatures.

## New nodes

`lem-weil-pbc-projective-resolution-ext-degree` and `lem-weil-pbc-projective-resolution-ext-all-degrees` record the two component obligations and their source in Stacks 065R.

## Earlier second reading (a previous round; superseded)

The target compiles and its proof is exactly the conjunction of the two component declarations. Each component has a strictly smaller conclusion (one conjunct), preserves the target signature, and follows the unit route by leaving the induction details to the named component obligations.
