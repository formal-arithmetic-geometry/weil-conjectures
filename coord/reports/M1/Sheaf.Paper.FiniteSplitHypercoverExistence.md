## What changed

Closed `AlgebraicGeometry.FiniteSplitEtaleHypercover.exists_finite_split_hypercover`
without changing its signature or any definition. The proof constructs the constant
simplicial identity étale X-scheme, proves the ordinary hypercover condition directly
from `Over.mkIdTerminal`, and specializes the existing
`exists_finite_split_replacement`. Its sole added proof import is
`Sheaf.Paper.FiniteSplitHypercoverReplacement` (plain `import`). The existence node
records this reduction.

## Proved and sorry left

Holes closed (1):
`AlgebraicGeometry.FiniteSplitEtaleHypercover.exists_finite_split_hypercover`
(node `lem-weil-pbc-finite-split-hypercover-existence`).
Holes added (0): none. No `sorry` remains in the delivered module, and no new
statement or definition is added. This proof still depends on the existing open
`AlgebraicGeometry.FiniteSplitEtaleHypercover.exists_finite_split_replacement`
(node `lem-weil-pbc-finite-split-hypercover-replacement`); its axiom closure therefore
contains `sorryAx`. This delivery closes the local hole, not the transitive proof.

## No longer needed

No original import was removed and no module is claimed globally pruned. The old
direct proof dependencies `def-weil-pbc-finite-split-hypercover`,
`lem-weil-pbc-etale-covering-affine-refinement`,
`lem-weil-pbc-etale-covering-base-change`,
`lem-weil-pbc-qcqs-finite-affine-open-cover`, and
`lem-weil-pbc-qcqs-morphism-permanence` are replaced by the ordinary hypercover
definition and the finite split replacement theorem. These construction dependencies
remain available transitively through the replacement node. The old direct dependency
`def-weil-pbc-etale-site` is retained. The first worker's proposed upstream refinement
import is removed, and the identical sandbox copy of
`Sheaf.Paper.FiniteSplitHypercoverRefinement` is excluded from delivery.

## Where the brief, the DAG or earlier work was wrong

The first worker applied the upstream `exists_and_cofiltered`, which is itself
`sorry`, while its node is realized by the Sheaf theorem already proved from this
existence theorem. Recording that proposed dependency would create a DAG cycle.
It also imports a duplicate public declaration into downstream modules that define
the Sheaf counterpart. The repaired proof specializes the independent all-degree
replacement construction instead. No target statement, public signature, or definition
was changed.

## Second reading by M1

1. Compared every sandbox Lean file with its repository version. The refinement
   file was identical and is excluded; the delivered existence module changes only
   its proof and a plain proof import. Its signature and existing docstring are
   byte-for-byte unchanged. No change record is needed.
2. Compiled the repaired module locally with `lcompile.py`; no errors or warnings.
   Checked the source for forbidden declarations and proof holes. An explicit
   `#print axioms` check confirms only standard axioms and the permitted `sorryAx`
   inherited from the existing replacement theorem. No data is selected into a
   definition from an unproved existence theorem: K is explicitly constructed and
   the replacement witness is eliminated only inside a proposition proof.
3. No statements were split off and no new nodes were added. Read the existing
   replacement statement and its construction: it applies to the explicitly proved
   ordinary hypercover and provides exactly the witness used. The constant matching
   argument works at degree zero (the empty diagram), in every positive degree,
   and for the empty base scheme.
4. Searched the library for existing existence, constant-hypercover, and refinement
   declarations and read the source stronger theorem and the Sheaf reduction. The
   repaired route uses the existing independent replacement construction; it adds
   no duplicate lemmas. The unit `sk-prop-h2` and its realized fields are unchanged;
   the reduction stays below its Kummer proof step. No original import is unused.
5. Compared the changed node with the Lean proof and the old node. Only `proof`,
   `proof_deps`, and `proof_origin` change. The two proof steps describe the terminal
   matching verification and replacement specialization, and the dependencies are
   precisely their union. The replacement node has no dependency on existence.

Changed on second reading: replaced the upstream conjunction projection with the
constant-hypercover/replacement proof; removed the unrelated identical refinement
copy; corrected the node, pruning claims, and accounting of the remaining dependency.
