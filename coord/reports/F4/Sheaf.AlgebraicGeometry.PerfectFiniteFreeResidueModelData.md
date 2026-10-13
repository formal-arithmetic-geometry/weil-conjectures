## What changed
Added two proof-obligation modules splitting `finiteFiberData` into finite residue-fibre cohomology and bounded Betti support. The target module imports both and combines them with a constructive pair.

## Proved and sorry left
Closed upper hole: `AlgebraicGeometry.Scheme.finiteFiberData` (1 of 1 original holes), by combining the two conjuncts.
Added holes: `AlgebraicGeometry.Scheme.finiteFiberCohomology` (node `new-perfect-finite-residue-cohomology-finite`) and `AlgebraicGeometry.Scheme.finiteFiberCohomologyBounded` (node `new-perfect-finite-residue-cohomology-bounded`). Both remain whole-proof `sorry` theorems.
This is a decomposition, not a completed mathematical proof: one hole closed, two added, net -1 before the maintainer's closure ledger. `finiteFiberData` still depends on `sorryAx`. No hole in a definition and no witness construction was added.

## No longer needed
No modules or imports were pruned. Both original public imports are required by signatures; both added plain imports are required only by the target proof.
The old `proof_deps` entry `def-pc-perfect-complex` is no longer a direct proof dependency of `finiteFiberData`: its proof now uses the two new nodes. It remains a statement dependency and a dependency of both new obligations, so `PerfectComplex` stays imported.

## Where the brief, the DAG or earlier work was wrong
The DAG proof plan requires substantial missing infrastructure connecting strictly perfect sheaf complexes to residue-field homology. No existing declaration provides this bridge, so the argument was split into the two mathematically independent conjuncts.

## New nodes
`new-perfect-finite-residue-cohomology-finite` and `new-perfect-finite-residue-cohomology-bounded` are added under `dag/nodes/sec-abelian-varieties/`.

## Earlier second reading (a previous round; superseded)
The target proof is a direct conjunction of the two strictly simpler obligations. Both new statements preserve all hypotheses and exactly the corresponding conjunct of the original target; the unit route is retained.


## Second reading by F4

1. **Interfaces: PASS.** Compared the target module with the repository using `diff -u`. The entire existing `finiteFiberData` signature and docstring are byte-for-byte unchanged. Only its proof and two plain proof imports differ. There are no existing declarations in the two new modules, no target edits, no definition edits, and no forced adaptations.
2. **Proof and axioms: PASS as a decomposition.** All three modules compile through `lcompile.py` in import order. The only direct holes are the two named public theorems listed above. Checked for forbidden declarations/attributes and for holes in definitions: none. The scratch `#print axioms` audit of all three theorem names reports only `propext`, `Classical.choice`, `Quot.sound`, and expected `sorryAx`. The conjunction is valid but not axiom-free.
3. **Split obligations: PASS after documentation repair.** Each obligation is exactly one conjunct, strictly weaker than the conjunction, with identical hypotheses. Checked zero complexes, rank-zero retracts, a complex in a single arbitrary degree, and reversed bounds (forcing all terms zero); empty schemes have no point x and empty neighbourhoods cannot satisfy x ∈ V. Pullback of a bounded flat complex computes the derived fibre; exact evaluation on the one-point spectrum and scalar transport identify its homology. The finite-dimensional cycles/quotient argument gives finiteness; zero terms outside the original bounds give bounded Betti support without needing the finiteness conjunct. Neither theorem chooses data from an unproved existence statement. Independently searched with LeanFinder, Loogle, and Mathlib grep through `msearch.py`, and searched `lean/` by residue cohomology, bounded fibres, and strictly perfect complexes. Generic derived bounds, homology vanishing, and local-model comparison infrastructure exist, but no declaration closes either entire obligation in a short application. The two helpers are not renamings of the whole item. Checked the sources [Stacks 0BCD](https://stacks.math.columbia.edu/tag/0BCD) and [08C4](https://stacks.math.columbia.edu/tag/08C4).
4. **Route and imports: PASS.** Kept the direct conjunction reduction and all required imports. Public imports serve signatures and added imports serve only the proof. No unit realization is bypassed: `sk-prop-av-cube` has empty `realized.statement` and `realized.steps[0]`, and this item is a subsidiary local-model node. Its statement remains in the original parent route. The report now distinguishes removal of an old direct proof edge from pruning a module.
5. **DAG: PASS after repair.** Added the missing sandbox copy of the existing target node, replacing its old proof plan and direct `proof_deps` by the exact two helper applications, and updating `proof_origin`. New nodes have matching ids, chapter/unit, source, creation and blueprint records, strictly smaller statements, proof steps, the independent recorded searches (LeanSearch was also attempted but returned Internal Server Error; its unavailability is recorded without a verdict), and now verbatim complete Lean signatures. Their proof-dependency unions agree with their steps.

Second reading changed only documentation and records: expanded both new theorem docstrings into complete natural-language proofs; made both new node statements self-contained and their Lean signatures verbatim; recorded independent searches; synchronized the target DAG proof; and corrected hole accounting and the no-longer-needed direct edge. The Lean proof and all signatures were kept.
