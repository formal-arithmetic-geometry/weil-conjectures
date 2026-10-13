## What changed

Replaced the core theorem's proof hole by a real composition of two strictly smaller
intermediate statements. Added `PicardUniversalRankMatchLocusCoreRank`, which states
representability of the two direct-image rank clauses, and
the compatibility theorem in the same module, which identifies that rank-only condition
with `PicardUniversalRankMatch`. The core theorem applies both results. The two new
intermediate theorems remain explicitly named `sorry`s for parallel proof.

## Proved and sorry left

Proved: `AlgebraicGeometry.Scheme.exists_picardUniversalRankMatchLocus_core`.
Sorry left: `AlgebraicGeometry.Scheme.exists_picardUniversalRankMatchLocus_core_rank`
(node `lem-sc-picard-universal-rank-match-locus-core-rank`) and
`AlgebraicGeometry.Scheme.picardUniversalRankMatchCoreCondition_iff`
(node `lem-sc-picard-universal-rank-match-locus-core-rank`, as a second declaration).

## No longer needed

None; all original imports remain available to the new rank construction statement.

## Where the brief, the DAG or earlier work was wrong

The original node's proof plan had no Lean dependencies and could not be made concrete
without stating the rank-locus construction and its compatibility with the final rank
condition. These are now exposed as two independent intermediate nodes.

## New nodes

Both intermediate declarations are stated in
`lean/Sheaf/AlgebraicGeometry/PicardUniversalRankMatchLocusCoreRank.lean`.

The new nodes are `lem-sc-picard-universal-rank-match-locus-core-rank` and
`lem-sc-picard-universal-rank-match-locus-core-compat`.

## Earlier second reading (a previous round; superseded)

The core proof compiles and uses the rank-only construction plus the compatibility
statement. The two new declarations are strict intermediate parts of the rank-locus
argument and are recorded by their DAG nodes.

## Second reading by V3

1. **Interface comparison.** Compared both delivered modules with the repository
   versions. The existing core theorem has the identical signature; the only change is
   its proof and a proof-only import of the new rank module. The new module adds the
   rank-condition definition and the two explicitly split intermediate theorems.
   **Verdict: pass.**
2. **Proof and axioms.** Compiled both files with `lcompile.py --all`; they compile
   cleanly. The core theorem has no `sorry`. The two intermediate theorems retain their
   named `sorry`s, with no `sorry` in the definition and no forbidden declarations.
   **Verdict: pass, conditional on the two documented split nodes.**
3. **Statements and nodes.** The rank-only theorem is strictly weaker than the target
   (it omits the third pulled-back rank clause), and the compatibility theorem is the
   exact bridge needed by the core proof. Both statements have matching DAG nodes,
   sources, proof plans, and Lean records. **Verdict: pass.**
4. **Pruning and route.** The proof uses the rank-locus construction and then the
   compatibility bridge, preserving the unit's immersion route. Every original import
   remains needed by the public hypotheses or declarations; no import or proof
   dependency can be removed. **Verdict: pass.**
5. **Search and duplication.** Searched the library for the new condition and for an
   existing rank-locus/compatibility theorem; none exists. The declarations therefore
   do not duplicate upstream or Mathlib results. **Verdict: pass.**

Changed only this report section after the second reading; no Lean statements or DAG
statements were changed.

