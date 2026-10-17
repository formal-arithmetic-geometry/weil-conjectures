## What changed

Closed `AlgebraicGeometry.ProEtale.CondensedRing.residueExchangePull_flatModel_comparison` by
reducing it to a counit-normalized mate calculation and composing with the residue upper-star
counit. Added `Sheaf.Paper.IntegralResiduePullFlatModelMateNormalized` for the remaining
categorical calculation.

## Proved and sorry left

- Proved: `residueExchangePull_flatModel_comparison` (1 target hole closed).
- Added: `residueExchangePull_flatModel_mate_normalized` (1 sorry split off). Its statement is
the normalized equality obtained after composing the target composite with the inverse residue
upper-star counit; it is strictly a subcalculation and is not the target statement.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted the explicit counit normalization needed to type the mate
calculation in the derived categories. This delivery records that normalization as a new DAG
node.

## New nodes

- `new-integral-residue-pull-flat-model-comparison-mate-normalized`: normalized mate equation
used by the target proof; its proof remains `sorry` for a subsequent worker.

## Second reading by A2

1. Compared the delivered comparison module with the repository version. The theorem
   statement is unchanged byte for byte; only proof imports and proof text were added.
   Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. The comparison theorem
   compiles, and the only remaining `sorry` is the named normalized mate theorem.
   No forbidden declarations or hollow definitions were introduced. Verdict: pass.
3. Checked the normalized statement against the counit mate identity and the existing
   `residueExchangePull_ordinary_unit`; it is a strict subcalculation of the target and
   has the source and a proof plan in its docstring and DAG node. Verdict: pass.
4. Checked pruning and imports. `IntegralResiduePullSquareData` is public because its
   declarations occur in signatures; `IntegralResiduePullOrdinaryUnit` and the derived
   counit compatibility module are proof-only imports. The unit route remains through
   the comparison node and the normalized mate node. Verdict: pass.
5. Checked the DAG against the Lean declarations and ran the required Mathlib searches.
   The normalized node now records its complete Lean signature and search results, and
   the target node's proof dependencies match the imports used by the proof. Verdict:
   pass.

Changed the unused simp argument, completed the normalized node metadata, recorded the
required searches, and added this second-reading report. The normalized mate theorem
remains the sole split-off hole.
