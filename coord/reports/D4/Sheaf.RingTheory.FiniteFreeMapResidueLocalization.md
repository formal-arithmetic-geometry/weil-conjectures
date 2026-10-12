## What changed
Added the proof-only import `Sheaf.RingTheory.FiniteFreeMapResidueLocalizationStrong` and proved
`Module.finiteFreeMap_residue_localization` by applying its stronger split-map statement. The
strong statement records a left inverse in the injective case and two-sided inverses in the
bijective case; the target follows by the standard left/right inverse criteria.

## Proved and sorry left
The target declaration `Module.finiteFreeMap_residue_localization` is proved. The new intermediate
declaration `Module.finiteFreeMap_residue_localization_strong` remains a named `sorry`, with node
`lem-pc-finite-free-map-residue-localization-strong`; it is the strict matrix-minor/adjugate
subproblem described in that node.

## No longer needed
No imports or proof-dependency nodes were removed; the target now depends on the new strong
intermediate node.

## Where the brief, the DAG or earlier work was wrong
The DAG's matrix argument is mathematically appropriate but too large to complete in this item;
it was split into the explicit split-map intermediate theorem while preserving the target's exact
statement.

## New nodes
`lem-pc-finite-free-map-residue-localization-strong` in
`dag/nodes/sec-abelian-varieties/lem-pc-finite-free-map-residue-localization-strong.json`.

## Earlier second reading (a previous round; superseded)
The target proof applies the stronger intermediate only by projections and standard inverse
criteria; the target signature is unchanged. The new statement is strictly stronger because it
supplies explicit linear left/right inverses, and its matrix-minor proof route matches Tag 00O0.

## Second reading by D4

1. Compared both delivered modules with the repository versions. The target theorem signature is byte-for-byte unchanged; the only target change is its proof, and the added strong module is a new split-off declaration. Verdict: pass.
2. Compiled both modules with `lcompile.py --all`; there are no errors, forbidden declarations, or unsanctioned `sorry`s. The target proof uses only inverse criteria and the split-off theorem. Verdict: pass.
3. Reviewed the strong statement and its node. It is a true, strictly stronger matrix-minor intermediate, with the required source, proof description, and search record; no existing library theorem duplicates it. Verdict: pass.
4. The proof follows the stated shortest available route through the strong intermediate. The proof-only import is needed, and no prior imports or dependency nodes became unnecessary. Verdict: pass.
5. The target and strong node records agree with the Lean declarations and proof dependencies; the unit route remains represented by the target node. Verdict: pass.

I changed only this report section; no Lean proof or statement changes were needed during second reading.
