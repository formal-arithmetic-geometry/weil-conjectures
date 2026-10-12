## What changed

The target theorem now reduces its universal degree quantifier to the new degreewise
lemma `schemeDerivedQCohProperty_of_isPseudoCoherent_degree`. The degreewise lemma is
stated in `Sheaf.AlgebraicGeometry.PseudoCoherentQCohDegree` and records the local
finite-free-model argument from Stacks Tag 08E5 as its remaining proof hole.

## Proved and sorry left

The target declaration `schemeDerivedQCohProperty_of_isPseudoCoherent` is proved by
introducing an arbitrary degree and applying the degreewise lemma. One sorry remains,
in `schemeDerivedQCohProperty_of_isPseudoCoherent_degree`; its node is
`lem-sc-pseudo-coherent-qcoh-degree`.

## No longer needed

The proof-only imports `Sheaf.AlgebraicGeometry.Coherent`,
`Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`, and
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` were removed. The
degreewise proof hole records those results as dependencies of its new node instead.

## Where the brief, the DAG or earlier work was wrong

The original node's single global proof step was too large to close directly in this
session. It was decomposed into the strictly smaller fixed-degree local-model statement.

## New nodes

`lem-sc-pseudo-coherent-qcoh-degree` is the fixed-degree quasi-coherence statement,
with module `Sheaf.AlgebraicGeometry.PseudoCoherentQCohDegree`.

## Earlier second reading (a previous round; superseded)

The fixed-degree statement is strictly weaker than the target (it fixes one integer
degree), its imports and source match the Tag 08E5 local-model argument, and the target
proof combines it by the defining universal quantifier.

## Second reading by M3

1. **Diff and statements.** Compared the delivered target module with the repository version; the existing target signature is byte-for-byte unchanged, and its proof now only introduces the degree and applies the fixed-degree theorem. The new degreewise declaration matches its DAG node exactly.

2. **Compilation and axioms.** Compiled both modules with `lcompile.py --all`; both pass. The target has no `sorry`; the only remaining `sorry` is the explicitly named `schemeDerivedQCohProperty_of_isPseudoCoherent_degree`, with node `lem-sc-pseudo-coherent-qcoh-degree`. No forbidden declarations occur. The degreewise theorem's proof is intentionally open and its docstring gives the complete Tag 08E5 local-model proof plan.

3. **Statements and nodes.** Checked that the fixed-degree theorem is a strict decomposition of the all-degrees target, with the same hypotheses and exact cohomology-sheaf conclusion for one `n`. Its source, proof steps, dependencies, and Lean record agree. No duplicate declaration was found in the repository search.

4. **Pruning and route.** The target proof uses only the degreewise node, preserving the item's degreewise route. Removed stale proof-only imports from the target and removed the redundant public `DerivedCategory` import from the degreewise module because `PseudoCoherentComplex` already exports it. The report's no-longer-needed imports and DAG dependency reduction remain accurate.

5. **Unit and delivery consistency.** The node remains in `sk-thm-picard-duality`; no target statement or definition changed, and no forced adaptation or change record is needed. The unit route is retained through the degreewise local-model step.

Changed: pruned the redundant `DerivedCategory` import and added this second-reading audit; no theorem statements or definitions were changed.
