## What changed

The target module now chooses a computing module cup resolution, lifts the two scalar cohomology classes to resolution cycles, constructs the paired target cycle from the Leibniz equation, and applies the new resolution-class scalar cup comparison before using the supplied `hcup` equation. The copied local cycle and class-surjectivity arguments are complete Lean proofs. The target module imports `Sheaf.AlgebraicGeometry.ScalarCupResolutionClassCompatibility` as a proof dependency. The new module records the remaining scalar Ext versus module-resolution comparison as one strictly smaller public theorem with its proof left for the next stage.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.Modules.scalarCup_moduleCup_compatibility` in the item module. The new theorem `AlgebraicGeometry.Scheme.Modules.scalarCup_resolution_class_compatibility` remains `sorry`; it has node `new-sc-scalar-cup-resolution-class-compatibility` and is the only added hole.

## No longer needed

No import or existing DAG node is removed relative to the repository baseline. The baseline
already has no `Sheaf.Paper.ModuleCohomologyCupProduct` import; the delivered proof uses
`Sheaf.Paper.ModuleCupPairingExists` and the new comparison module as plain proof imports.
The local helper proofs make the needed cycle and class-surjectivity arguments directly.

## Where the brief, the DAG or earlier work was wrong

The target DAG plan omits a public bridge between scalar Ext cup classes and the sectionwise pairing of an arbitrary `CupResolutionPairing`. The library provides the resolution class surjectivity, Leibniz cycle construction, and module cup resolution independence, but no declaration identifying `scalarCohomologyCup` with that resolution class. The new node isolates precisely this missing bridge and leaves the outer theorem as a genuine reduction to it. No target statement or existing definition was changed.

## New nodes

`new-sc-scalar-cup-resolution-class-compatibility` is stated in `lean/Sheaf/AlgebraicGeometry/ScalarCupResolutionClassCompatibility.lean` and is copied to `dag/nodes/sec-abelian-varieties/new-sc-scalar-cup-resolution-class-compatibility.json`.

## Second reading by W4

1. I compared the delivered target module with the repository version. The theorem
`AlgebraicGeometry.Scheme.Modules.scalarCup_moduleCup_compatibility` has the same
signature byte for byte; only proof-only imports, private helper proofs, and the proof body
were added. The added split theorem is in a new module and has a distinct, strictly smaller
interface. Verdict: unchanged target statement and no accidental definition change.

2. I compiled both delivered modules with `lcompile.py --all`; both compile without errors
or warnings. The target proof has no `sorry`; the only remaining `sorry` is the named theorem
`AlgebraicGeometry.Scheme.Modules.scalarCup_resolution_class_compatibility`, and its DAG node
is `new-sc-scalar-cup-resolution-class-compatibility`. The target's axiom report contains
`sorryAx` only through that explicitly named open theorem; the split theorem itself has the
expected `sorryAx` pending its proof. No forbidden declarations or hollow definitions occur.
Verdict: valid stage-3 proof with one documented split-off hole.

3. I searched the Lean library for existing declarations matching the split theorem and for
other scalar-cup resolution-class bridges. No existing declaration states this result. The
new statement is the exact missing bridge used by the target reduction, with the concrete
cycle and pairing hypotheses retained. Its source, proof plan, searches, node metadata, and
docstring are present. Verdict: true as the intended resolution comparison and exactly as
strong as needed.

4. The proof follows the target downward: it selects a computing pairing, lifts both input
classes by the existing surjectivity argument, constructs the paired cocycle from Leibniz,
uses the supplied `hcup`, and reduces to the split bridge. The old experimental
`ModuleCohomologyCupProduct` proof import is removed; `ModuleCupPairingExists` and the new
bridge are plain proof imports. The unit remains `sk-prop-av-cube`, and the target route is
preserved through the resolution pairing. Verdict: imports are pruned and the planned route
is retained.

5. The target node's proof now matches the Lean proof steps and its existing proof
dependencies remain applicable. The new node records its declaration, module, source,
strictly smaller statement, proof dependencies, searches, origin, chapter, and unit.
No existing node or target statement was changed. Verdict: DAG and Lean agree.

I changed only the target proof/imports, added the local helper proofs and the new split
module/node, and appended this second-reading record. No existing statement or definition
was altered.
