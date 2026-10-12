## What changed
Split `Field.brauerScalarDefect_eq_iff` into its two strictly simpler directional implications, each stated in a dedicated module and left as a named theorem, then proved the original equivalence by composing them.

## Proved and sorry left
Closed `Field.brauerScalarDefect_eq_iff`.
Left `Field.brauerScalarDefect_eq_of_brauerEquivalent` and `Field.brauerEquivalent_of_brauerScalarDefect_eq` as the two decomposition sorries, with nodes `lem-sc-brauer-scalar-defect-faithful-forward` and `lem-sc-brauer-scalar-defect-faithful-backward`.

## No longer needed
None; the parent definition import is used by both directional statements.

## Where the brief, the DAG or earlier work was wrong
The full scalar-defect faithfulness argument requires the tensor-product and finite Galois descent construction; it was reduced to the two directional components so the upper theorem is fully assembled in Lean.

## New nodes
Added `lem-sc-brauer-scalar-defect-faithful-forward` and `lem-sc-brauer-scalar-defect-faithful-backward`, with corresponding modules.

## Earlier second reading (a previous round; superseded)
The directional statements are strictly simpler than the original iff and the item theorem combines them without changing its signature; both new declarations retain the unit route and are ready for independent proof.

## Second reading by U3

1. **Repository comparison.** Compared the delivered parent module with the repository version. The theorem signature and all existing declarations are unchanged; only the proof body and the two explicitly listed imported split modules were added.
2. **Compilation and proof hygiene.** Compiled all three delivered modules with `lcompile.py --all`; they compile cleanly. The parent theorem is fully proved. The only remaining `sorry`s are the two named directional theorems, each public, documented, and represented by its corresponding split node. No definitions contain `sorry`, and no forbidden declarations were introduced.
3. **Statements and nodes.** Checked both directional statements against the original equivalence: each is a strict implication with the same hypotheses and conclusion in the appropriate direction. Their DAG nodes match the Lean declarations, source, proof dependencies, and `status: split`; no duplicate library theorem was found.
4. **Route and pruning.** The parent theorem composes the two directional results directly, preserving the unit route. The parent scalar-defect definition import remains necessary; no unused imports or proof-dependency nodes were identified.
5. **Axioms and interfaces.** The declarations expose only the intended public interfaces. The split theorem proofs remain open with `sorryAx` pending their stated nodes; the closed parent theorem adds no extra axioms beyond those inherited from its dependencies.

Changed in this second reading: added this audit section only; no Lean statements or proofs were altered.
