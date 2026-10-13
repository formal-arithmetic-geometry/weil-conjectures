## What changed

Proved `HomologicalComplex₂.finiteStripGradedMap_epi` by installing the split-epimorphism
property and applying the standard `IsSplitEpi` to `Epi` instance. Added the proof-only
import of `Sheaf.Algebra.Homology.FiniteStripConeGradedMapSplitEpi`.

## Proved and sorry left

Closed `finiteStripGradedMap_epi`. Added the strictly structural intermediate theorem
`finiteStripGradedMap_factorThru_epi`, whose proof remains `sorry` and is recorded by node
`lem-sc-finite-strip-cone-graded-map-split-epi`.

## No longer needed

None; the original definition module remains needed.

## Where the brief, the DAG or earlier work was wrong

The original worker's split-epimorphism intermediate was too strong in a general abelian
category: an arbitrary source image need not split. The needed structural step is only
that the row map is epic onto the filtration step, and this is split off instead.

## New nodes

`lem-sc-finite-strip-cone-graded-map-split-epi` in
`dag/nodes/sec-picard-framework/lem-sc-finite-strip-cone-graded-map-split-epi.json`.

## Second reading by A4

1. The target declaration and all existing signatures were compared byte for byte with the repository; the target signature is unchanged. Verdict: pass.
2. Both sandbox modules compile with `lcompile.py`; the target proof has no sorry. The split-off theorem remains the only named sorry and has its DAG node. Verdict: pass after repair.
3. The original split-epimorphism statement was too strong in a general abelian category, since arbitrary source images need not split. It was replaced by the strictly weaker and needed row-cover epimorphism statement, which is true by the hsteps image description. Verdict: repaired.
4. The proof now uses the row-cover theorem, the image-factor isomorphism, and the cokernel quotient epi; no imports were removed. The unit route remains the canonical row-to-graded quotient route. Verdict: pass.
5. The DAG node and Lean declaration now agree on the row-cover theorem, its proof dependency, and split status. Verdict: pass.

Changed the intermediate theorem from the invalid `IsSplitEpi` claim to `finiteStripGradedMap_factorThru_epi`, adjusted the target proof to compose this epi with the canonical isomorphism and quotient epi, and updated the corresponding node metadata.

The split-off hole is `HomologicalComplex₂.finiteStripGradedMap_factorThru_epi` (node `lem-sc-finite-strip-cone-graded-map-split-epi`); the target `finiteStripGradedMap_epi` is closed.
