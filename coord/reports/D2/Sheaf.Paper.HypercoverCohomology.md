## What changed
The target theorem is reduced to two named coefficient-category clauses. The new modules
`Sheaf.Paper.HypercoverCohomologyAbelian` and `Sheaf.Paper.HypercoverCohomologyModule`
state the abelian and module parts, respectively, and the target combines them by `refine`
and `exact`. The two clause proofs remain explicit named `sorry`s because the injective
resolution and refinement argument is not formalized by the available declarations.

## Proved and sorry left
`AlgebraicGeometry.hypercover_cohomology` is proved by combining the two strict clauses.
Sorry remains in `hypercover_cohomology_abelian_part` (node
`thm-weil-pbc-hypercover-cohomology-abelian-part`) and
`hypercover_cohomology_module_part` (node
`thm-weil-pbc-hypercover-cohomology-module-part`).

## No longer needed
No imports or proof-dependency nodes from the original module were removed; the clause
modules retain the parent theorem's stated dependencies needed by the planned argument.

## Where the brief, the DAG or earlier work was wrong
The original monolithic proof plan is not executable from current declarations: its spectral
sequence and finite lifting steps are only statement-level theorems. Splitting into the two
coefficient clauses gives strictly smaller, independently provable obligations and a real
Lean reduction of the target.

## New nodes
`thm-weil-pbc-hypercover-cohomology-abelian-part` and
`thm-weil-pbc-hypercover-cohomology-module-part`, with their corresponding modules under
`lean/Sheaf/Paper/`.

## Earlier second reading (a previous round; superseded)
A second D2 worker should check that the two coefficient clauses are strict parts of the
parent statement, that their signatures match the Lean declarations exactly, and that the
parent proof combines them without changing any hypotheses or conclusions.

## Second reading by D2

1. **Statements and accidental changes.** Compared the delivered parent module with the repository version. The target theorem signature is byte-for-byte unchanged. The two added declarations are strict conjunct clauses with the same hypotheses and corresponding conclusions; no existing declaration was weakened or altered.
2. **Proof and axioms.** Compiled all three sandbox modules successfully. The parent proof has no `sorry`; the only remaining `sorry`s are the two explicitly named clause theorems, each documented and attached to its DAG node. No forbidden declarations were introduced.
3. **Split statements and nodes.** Checked both split signatures against the parent conjunction and their node JSON. Each is a strict part of the target, with source, proof origin, and matching Lean declaration. The unresolved mathematical obligations are the injective-resolution/refinement comparisons described in their docstrings; no shorter existing library theorem was found.
4. **Pruning and route.** The parent now imports only the public statement dependencies and the two clause modules privately. Removed the old proof-only imports from the parent. Updated the parent node proof and `proof_deps` to the two clause nodes; the unit route remains unchanged (the unit has no realized step for this target).
5. **Compilation review.** `lcompile.py --all` passes for the three modules. The parent theorem combines the clauses directly without changing hypotheses or conclusions.

Changed the parent imports and proof, updated its DAG proof metadata, and recorded the two clause modules as the only remaining split obligations.
