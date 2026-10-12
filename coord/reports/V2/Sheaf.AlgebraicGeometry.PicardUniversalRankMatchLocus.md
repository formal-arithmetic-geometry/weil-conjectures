## What changed
Added a core representability theorem and a structural finiteness theorem. The target theorem now combines them by a complete Lean proof.

## Proved and sorry left
The target `exists_picardUniversalRankMatchLocus` is proved. The decomposition leaves `exists_picardUniversalRankMatchLocus_core` and `picardUniversalRankMatchLocus_structural` as named sorry theorems.

## No longer needed
No imports or planned dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong
The full Stacks argument is substantial; it was split into the immersion construction and the independent finiteness upgrade.

## New nodes
`lem-sc-picard-universal-rank-match-locus-core`, `lem-sc-picard-universal-rank-match-locus-structural`.

## Earlier second reading (a previous round; superseded)
Compiled both sandbox modules with `lcompile.py --all`; the target proof is a direct composition of the two strictly smaller named statements. No signature or definition changes were made.

## Second reading by V2

1. **Signatures and visibility.** Compared the delivered target module with the repository version. The existing target declaration is byte-for-byte unchanged; the only interface addition is the explicitly split structural theorem and the proof-only Core import.

2. **Compilation and axioms.** Compiled both sandbox modules with `lcompile.py --all`; both compile successfully. The two split theorems remain the only named `sorry`s, with no sorry in definitions or unsafe declarations.

3. **Statements and nodes.** Checked that the target proof applies the core theorem and then the structural theorem with exactly matching hypotheses and conclusion. The two split statements are strict intermediate conclusions and have matching DAG nodes.

4. **Shortest route and pruning.** The target is a direct composition of the two split results. Removed the three old proof-only imports (`PerfectDirectImageBaseChange`, `PerfectLowestCohomologyLocus`, and `ProperNormalizedFibres`) from the target module; they are no longer used by its proof or signatures, and updated the target node proof dependencies accordingly.

5. **Unit route.** The decomposition preserves the representing immersion route of `sk-prop-av-cube`: core representability is followed by the finiteness upgrade, with no change to the target statement or definitions.

I changed only the target proof/imports, added the Core module and its node, added the structural split theorem and node, and updated the target node's proof route and dependencies.
