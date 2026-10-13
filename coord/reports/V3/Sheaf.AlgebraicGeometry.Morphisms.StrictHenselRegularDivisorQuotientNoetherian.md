## What changed
Proved `strictHenselizationRing_noetherian_of_regular` by applying the regular divisor quotient theorem at divisor zero and transferring Noetherianity across the zero-ideal quotient ring equivalence. The proof obtains nontriviality from `AlgebraicGeometry.strictHenselizationLocalStructure`, since `IsLocalRing` extends `Nontrivial`. Replaced the auxiliary nontriviality dependency with the existing local-structure dependency and removed the auxiliary module and node.

## Proved and sorry left
Closed one local hole: `AlgebraicGeometry.Scheme.strictHenselizationRing_noetherian_of_regular` (node `lem-sbc-strict-hensel-regular-divisor-quotient-noetherian`). Added zero holes and split off zero statements. No sorry remains in the delivered module. This is a reduction to existing dependencies, not a claim of an axiom-free target: the axiom check still reports `sorryAx` from imported open statements, alongside `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed
The old proof dependency `lem-sc-strict-henselization-noetherian` and its direct import `Sheaf.RingTheory.StrictHenselizationNoetherian` are no longer used. `Sheaf.Paper.StrictHenselizationLocalStructure` remains a private proof import. The earlier sandbox-only auxiliary `StrictHenselizationRingNontrivial` module and node are absent from this delivery; they were not part of the repository baseline. This reports direct dependency pruning, not a claim that the Noetherian module disappears from the entire targets import closure.

## Where the brief, the DAG or earlier work was wrong
The earlier delivery introduced an unnecessary nontriviality theorem even though `AlgebraicGeometry.strictHenselizationLocalStructure` already supplies `IsLocalRing`, which extends `Nontrivial`. The erroneous residue-field-to-colimit proof sketch is removed: geometric lifts instead induce neighbourhood-ring-to-Ω maps.

## New nodes
None. The proof dependency is the existing `lem-weil-pbc-strict-henselization-local-structure` node.

## Earlier second reading (a previous round; superseded)

1. Replaced the auxiliary theorem and node with the existing `strictHenselizationLocalStructure` dependency. The target theorem signature is unchanged.
2. The proof obtains `IsLocalRing` directly from `strictHenselizationLocalStructure`; this supplies nontriviality through the typeclass hierarchy and compiles cleanly.
3. Deleted `StrictHenselizationRingNontrivial.lean` and its DAG node. No new sorry remains in this item.
4. Updated the proof text and dependencies in the target node to match the Lean proof and recorded the private import change.

The import change and direct importer are recorded in
`coord/changes/strict-henselization-noetherian-imports.md`.

## Second reading by V3

1. **Interface — pass.** Compared every delivered Lean module (one) with its repository version using `diff -u`. The existing theorem signature and docstring are byte-for-byte unchanged. There are no new declarations or definitions. Public proof imports are privatized/removed as recorded in `coord/changes/strict-henselization-noetherian-imports.md`. The unchanged sole direct importer, `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient`, compiles against a freshly compiled copy of the delivered module.
2. **Proof — pass, conditional on existing open dependencies.** Compiled the module with `lcompile.py`; no errors or warnings. A scratch copy with `#print axioms AlgebraicGeometry.Scheme.strictHenselizationRing_noetherian_of_regular` reports exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. No textual sorry, forbidden declaration mechanism, or hollow definition occurs in the delivered module. The local-ring structure is proof data (`IsLocalRing : Prop`), not an arbitrary mathematical object chosen from an unproved existence theorem.
3. **Split statements — pass (none).** No new statements or nodes and no added holes. Checked the zero-divisor specialization: both quotients are by the zero ideal, regularity transfers along `RingEquiv.quotientBot`, and `IsLocalRing` supplies `Nontrivial`, excluding a unit zero. Mathlib's `IsRegularRing` extends `IsNoetherianRing`, justifying the extracted instance.
4. **Route and pruning — pass.** Searched the library with alternate Noetherian/strict-henselization expressions and Mathlib through `msearch.py grep`; no shorter direct theorem about this canonical ring was found. The existing abstract strict-henselization Noetherian theorem needs a comparison not present here, whereas the existing quotient theorem specializes directly at zero. The statements need only the retained public imports; both Sheaf proof dependencies are plain imports. The old node's sole proof dependency `lem-sc-strict-henselization-noetherian` is explicitly listed as no longer directly needed. Read `dag/units/sk-prop-input-spreading.json`: this below-unit change preserves its statement, steps and `realized` fields and does not bypass a realized unit step.
5. **DAG — pass.** The node statement and Lean statement record are unchanged. Its proof, proof dependencies and proof origin match the zero-quotient reduction and the local-structure dependency; no new-node metadata is needed.

Second reading changed only this report: named the hole closed, documented the remaining imported axiom dependency, and distinguished direct pruning and a discarded sandbox auxiliary from whole-library pruning. The Lean proof and node were left intact.
