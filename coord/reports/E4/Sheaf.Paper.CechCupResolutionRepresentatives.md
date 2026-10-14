## What changed

Replaced the original `sorry` of `AlgebraicGeometry.Scheme.Modules.cechCup_resolution_representatives` without changing its signature, visibility or docstring. Added two proof-only imports: `Sheaf.Paper.CechCupResolutionComparisonExists` and `Sheaf.Paper.CechCupSignedAxisPairing`. Three proved private helpers establish cycle-class surjectivity, computing-resolution-class surjectivity, and that the paired section is a cocycle.

The proof obtains computing comparisons, lifts the prescribed input classes to global resolution cocycles, and forms their paired cocycle by Leibniz. The signed-axis operation identifies its total homology class with that of the original Cech cup. Cancelling the target comparison isomorphism gives the required class equality. No cohomology cup product is assumed.

The second reading found that the signed-axis source had been withdrawn from the current library while its compiled artifact remained available. The delivery therefore includes `Sheaf.Paper.CechCupSignedAxisPairing` and its node explicitly as a split, rather than claiming an existing source dependency. No existing statement or definition changed.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.Scheme.Modules.cechCup_resolution_representatives`, node `lem-sc-cech-cup-resolution-representatives`. Its three private helpers are proved; the item module has no `sorry`.

Added one lower hole: `AlgebraicGeometry.Scheme.Modules.cupCech_signed_axis_pairing`, node `lem-sc-cech-cup-signed-axis-pairing`, in `Sheaf.Paper.CechCupSignedAxisPairing`. This is a decomposition: one original hole closed and one lower hole added, with no claimed net hole reduction. The split gives only the signed total-homology operation and its axis formulas. It does not supply computing comparisons, global representatives, or their specified sheaf-cohomology classes. The item's proof supplies these other steps separately.

Both modules compile through `lcompile.py`; the delivery preflight passes. A scratch copy with `#print axioms AlgebraicGeometry.Scheme.Modules.cechCup_resolution_representatives` reports `propext`, `Classical.choice`, `Quot.sound`, and inherited `sorryAx`. No definition contains a hole or chooses arbitrary data from an unproved existence theorem.

## No longer needed

Both original public imports remain necessary for the unchanged statement. No module is claimed globally pruned, and no existing file is deleted.

The old immediate proof dependencies `lem-sc-module-cup-godement-aw`, `lem-sc-module-cup-flasque-acyclicity`, and `lem-sc-cech-comparison-map-naturality` are replaced by `lem-sc-cech-cup-resolution-comparison-exists` and `lem-sc-cech-cup-signed-axis-pairing`. Godement/flasque construction remains upstream of the comparison-existence theorem. The proof does not invoke coefficient-map naturality separately.

The item does not import `Sheaf.Paper.CechCupResolutionBetaClassPairing` or `Sheaf.Paper.CechCupResolutionTotalPairing`. The new split states the total-homology interface directly; lower cochain-pairing modules are possible ingredients of its future proof, not direct dependencies used in the item proof.

## Where the brief, the DAG or earlier work was wrong

The first worker treated the signed-axis interface as an existing source dependency because compilation could load its stale compiled artifact. `deliver3.py` correctly rejected the missing source. The second reader restored it as an explicit smaller split and corrected the progress accounting.

The mathematical route remains the signed Cech comparison diagram. Read Stacks Tags 07MB and 0FKV online; these give the signed total cochain morphism and flasque comparison diagram. The split's docstring explains the finite-diagonal construction, Leibniz identity, descent through boundaries, and axis formulas. At degree zero the incoming differential vanishes; zero classes, zero sheaves and an empty family need no nonemptiness hypotheses. This is a proposition asserting existence, not data chosen in a definition.

Second-reader searches through `msearch.py` used bilinear homology/Leibniz queries with LeanFinder, Loogle and grep. No replacement for the signed-axis theorem was found. Existing cochain-pairing modules supply a lower cochain construction rather than the homology operation and both axis formulas. Searches and results are recorded in `searches.jsonl`. The unit `sk-prop-av-cube` has empty realized-node arrays at this level; its record was unchanged.

## Second reading by E4

1. Compared each delivered existing module and node against the repository. The existing theorem's signature is byte for byte unchanged, as are its visibility, docstring and all existing definitions. Only proofs, proof imports and permitted node proof metadata changed.
2. Compiled the item and checked its axioms in a scratch copy. The preflight compiles both delivered modules. No forbidden declaration or hollow definition is present. The only new hole is the named signed-axis theorem listed above; its source and complete natural-language construction are in its docstring.
3. Checked the split against the signed total construction, including degree zero, zero sheaves and empty families. It is true and strictly a part of the representative argument, without the comparison isomorphisms or representative choices asserted by the item. Distinct second-reader library/Mathlib searches found no exact replacement. The new node matches it.
4. Read the proof from its conclusion back to the inputs: its shortest used interface is the signed-axis operation and computing comparison existence. The report lists all three old immediate proof dependencies removed. No realized unit node is bypassed; no global pruning is claimed.
5. Checked the existing node's proof steps and dependency union against the Lean proof. Checked the new node's statement, proof, dependencies, provenance, searches and Lean record. They describe the actual construction and remaining obligation.

Second reading changed the delivery from an incorrectly claimed hole-free proof to an explicit decomposition, adding the missing signed-axis source and node, correcting its attribution and progress accounting, and documenting the missing-source failure. The item proof itself required no repair.

## New nodes

`lem-sc-cech-cup-signed-axis-pairing`: `Sheaf.Paper.CechCupSignedAxisPairing` states the signed total Cech homology pairing and its two axis formulas, sourced to Stacks Tags 07MB and 0FKV. Its natural-language proof constructs the signed finite-diagonal cochain pairing, descends it to homology, and evaluates both axes. It is strictly smaller than the representative comparison theorem. The source and node were adapted from the previously withdrawn G3/S2 split; obsolete review records were removed. No change record is needed because no existing signature or definition changes.
