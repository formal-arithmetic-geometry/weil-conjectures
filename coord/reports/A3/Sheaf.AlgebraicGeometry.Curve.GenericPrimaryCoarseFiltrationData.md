## What changed
Split the construction into two named intermediate theorems in `GenericPrimaryCoarseFiltrationCore` and `GenericPrimaryAnnihilator`, and proved the target theorem by combining them. Added proof-only imports for both modules.

## Proved and sorry left
The target `exists_generic_primary_coarse_filtration_data` is proved by a complete Lean term combining the two intermediate results. The new declarations `exists_generic_primary_coarse_filtration_core` and `exists_primary_annihilator` remain `sorry`, each with a DAG node.

## No longer needed
No imports or existing DAG dependencies were pruned; all original construction dependencies remain available to the intermediate theorem.

## Where the brief, the DAG or earlier work was wrong
The full construction and annihilator argument could not be completed directly in the available time, so they were split into strictly smaller named statements.

## Earlier second reading (a previous round; superseded)
The decomposition is structurally valid; the target combines the two strictly smaller statements without changing its signature.

## New nodes
`lem-sc-generic-primary-coarse-filtration-core` in `GenericPrimaryCoarseFiltrationCore.lean` and `lem-sc-generic-primary-annihilator` in `GenericPrimaryAnnihilator.lean`.

## Second reading by A3

1. I compared the delivered target module with the repository version. The target
   declaration has the same signature byte for byte; the only change is its proof and
   the two proof-only imports. The two new declarations are separate, strictly smaller
   statements, and their signatures match their DAG nodes.
2. I compiled all three delivered modules with `lcompile.py --all`. Compilation succeeds;
   the only remaining `sorry`s are the two named split-off theorems. No forbidden
   declarations or hollow definitions occur. The target proof itself is complete.
3. The split-off statements are true consequences required by the source construction:
   the core theorem omits only the annihilator conjunct, while the annihilator theorem
   states exactly that omitted conjunct. Neither duplicates an existing library theorem.
4. The proof follows the declared route: the target applies the core construction and
   then the primary annihilator, preserving the unit's filtration and cover route. The
   new node proof dependencies record the imported construction ingredients.
5. Imports were checked against the declarations and signatures. The added imports are
   proof-only in the target; no old proof dependency can be removed because the core
   theorem retains the original construction route. The dry-run delivery check passes.

Changes made during this reading: none to the Lean statements or proofs; this report
section records the review and validation.
