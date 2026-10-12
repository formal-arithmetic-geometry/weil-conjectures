## What changed
Replaced the entire proof of `CochainComplex.twoTermCoimage_quasiIso` with a direct
Mathlib proof. At degree q, a morphism from the canonical homology cokernel sequence
transfers exactness to the differential followed by `b.f q`; the latter is epi by hb.
`ShortComplex.quasiIso_iff_of_zeros'` then gives the homology isomorphism. Monicity
handles q-1 and zero terms handle all other degrees. The original signature is
byte for byte unchanged. No definition or other existing declaration changed.

Removed the proposed `CochainComplex.twoTermCoimage_quasiIsoAt` and its unlanded node:
it was an equivalent restatement with a circular node dependency, not a reduction.
Replaced the two original imports by
`Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors` and
`Mathlib.Algebra.Homology.QuasiIso`. Both are public because the theorem's statement
uses `singleFunctor` and `QuasiIso`. Updated the original node's proof and origin. Recorded the public import change in
`coord/changes/TwoTermCoimageQuasiIsoImports.md`.

## Proved and sorry left
Hole closed: `CochainComplex.twoTermCoimage_quasiIso`
(node `lem-weil-pbc-two-term-coimage-quasiiso`). Holes added: none.
No sorry remains in the delivered module; one of one original holes is closed.
This is a proof, not a decomposition. The proposed unlanded hole
`CochainComplex.twoTermCoimage_quasiIsoAt` has been removed rather than delivered.
Compilation through lcompile.py is clean (about 3 seconds).
A scratch-copy `#print axioms CochainComplex.twoTermCoimage_quasiIso` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`.

## No longer needed
Removed direct imports:
- `Mathlib.Algebra.Homology.Embedding.CochainComplex`: no truncation or embedding
  construction is used; the single-complex interface has a narrower import.
- `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`: supplied transitively
  by the imports needed for the public signature.

No old proof-dependency node is pruned: both `def-sp-abelian` and
`def-weil-abstract-derived-category` remain used as Mathlib notions. No Sheaf module
is made unreachable by this delivery. The proposed unlanded node
`lem-weil-pbc-two-term-coimage-quasiiso-at` is removed from the sandbox.

## Where the brief, the DAG or earlier work was wrong
The first worker's per-degree statement quantified over every degree and assumed
all the original hypotheses; via `quasiIso_iff` it was equivalent to the item.
Its node cited the item as its proof dependency, creating a circular route if the
item were updated to cite it. Its docstring lacked a source and a complete proof,
and the node's Lean statement was not a verbatim copy. All these faults disappear
with its removal. The original homology calculation is fully provable from
Mathlib, without any split-off statements.

## Second reading by B2
1. Compared the complete module with the repository version and compared the
   original theorem signature as a string: byte-identical, including indentation.
   Only imports and the proof of the original theorem remain changed. No data
   construction, hypothesis, conclusion, universe, or visibility was altered.
2. Compiled the delivered file through lcompile.py with no warnings or errors.
   Scanned for sorry, axiom, unsafe, opaque, implemented_by, and extern: none.
   The scratch-copy axiom print contains only the three permitted axioms.
3. Rejected the proposed degreewise sorry as an equivalent restatement and its
   circular node dependency. Removed it and its node. Independent searches used
   msearch.py Loogle (`ShortComplex.Exact`), LeanFinder (exactness under epi
   precomposition), and grep (`quasiIso_iff_of_zeros|exact_iff_of_epi_of_isIso_of_mono`),
   as well as rg on Mathlib and lean/Sheaf. Mathlib's existing cokernel and
   short-complex lemmas close the whole item; no new statement is delivered.
   Checked zero K, a zero incoming differential, and arbitrary negative q: the
   proof uses only integer adjacent-degree inequalities and categorical
   epi/mono/iso laws, all valid in these cases.
4. Read Stacks Tags [08J5](https://stacks.math.columbia.edu/tag/08J5),
   [0118](https://stacks.math.columbia.edu/tag/0118), and
   [010V](https://stacks.math.columbia.edu/tag/010V), and the existing node's
   degreewise plan. The direct proof implements precisely that calculation.
   Read `dag/units/sk-thm-properbasechange.json`, including realized: this item
   realizes no unit statement or step and this change bypasses none. Both old
   proof-dependency nodes remain. Imports are narrowed to the two modules needed
   by the signature. The sole direct importer, UpperTruncationStepSES, already
   imports Embedding.CochainComplex and ShortComplex.HomologicalComplex itself;
   it needs no adaptation to the narrower public imports.
5. Updated the existing node's proof steps to name the exact Mathlib arguments:
   cokernel exactness, the epi/iso/mono comparison, and quasiIso_iff_of_zeros'.
   The proof_deps remain the two Mathlib notion nodes; proof_origin records the
   source and B2 formalization. The original statement and lean signature record
   are unchanged. No new node is needed. The import change record is
   `coord/changes/TwoTermCoimageQuasiIsoImports.md`; preflight required it because
   public imports affect the exported environment.

Changes made by the second reader: removed the restatement and circular node,
proved the original theorem completely, narrowed imports, corrected the progress
report, and synchronized the original node's proof description.
