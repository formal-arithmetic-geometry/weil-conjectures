## What changed
Added proof-only imports and reduced the target to two strictly smaller named statements, primal and dual base-change invertibility. Added one module for each intermediate statement.

## Proved and sorry left
The target theorem `picard_pullback_base_change` is proved by conjunction of the two intermediate declarations. Sorries remain in `picard_pullback_base_change_primal` and `picard_pullback_base_change_dual`, each with a dedicated DAG node.

## No longer needed
No imports from the original module were removed.

## Where the brief, the DAG or earlier work was wrong
The planned local-frame argument was too large to complete in this session, so it was split into the primal and dual assertions.

## New nodes
`lem-sc-picard-pullback-base-change-primal` and `lem-sc-picard-pullback-base-change-dual`, corresponding to the two named intermediate theorems.

## Earlier second reading (a previous round; superseded)
The target proof is a direct conjunction of the primal and dual statements, with unchanged target signature. The two new statements are strict conjunctive components and match the remaining local-frame steps.

## Second reading by S2
1. **Interface and accidental changes.** Compared each delivered file with the repository
   version. The existing target declaration is byte-for-byte unchanged; only its proof and
   proof-only imports changed. The two additional modules contain the strict primal and dual
   conjuncts and introduce no altered existing declaration.
2. **Compilation and proof status.** Compiled all three modules with `lcompile.py --all`.
   They compile cleanly. The target is proved; the only remaining `sorry`s are the two named
   split statements, each documented and represented by its DAG node. No definitions contain
   `sorry`, and no forbidden axioms or unsafe declarations were added.
3. **New statements.** Checked both split statements against the target and source description:
   each has exactly the same hypotheses and one conjunct as conclusion, so each is true and
   strictly simpler than the target. They are not duplicates of declarations already in the
   library, and their nodes carry sources, proof plans, and Lean records.
4. **Pruning and route.** The target keeps the finite-locally-free tensor-unit and base-change
   imports, and its proof follows the two conjuncts. No old proof dependency was removed, and
   the unit `sk-prop-av-cube` route is not bypassed by the conjunction step.
5. **DAG agreement.** Verified declaration names, statements, proof dependencies, and
   `proof_origin` in both new nodes against their Lean modules; the target node remains the
   original statement and records the split route.

Changed after this reading: added the required second-reading record to this report; no Lean
code or DAG statements required repair.
