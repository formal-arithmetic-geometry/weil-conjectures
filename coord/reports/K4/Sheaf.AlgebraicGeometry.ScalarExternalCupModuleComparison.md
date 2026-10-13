## What changed

Restored and proved `Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison`.
The proof composes scalar/module cup compatibility with scalar/module pullback
comparison and uses the defining equation for `externalCup`. Added the two
strictly simpler prerequisite theorem modules required by the proof:
`ScalarCupModuleCupCompatibility` and `ScalarModuleCohomologyPullbackComparison`.
All three modules compile in import order.

## Proved and sorry left

Proved:
- `scalarExternalCup_moduleComparison`.

Sorry left (new prerequisite nodes):
- `scalarCup_moduleCup_compatibility`
  (`lem-sc-scalar-cup-module-cup-compatibility`).
- `scalar_moduleCohomologyPullback_comparison`
  (`lem-sc-scalar-module-cohomology-pullback-comparison`).

## No longer needed

None. Both prerequisite comparisons are used directly by the completed proof.

## Where the brief, the DAG or earlier work was wrong

The current branch omitted the target module and its prerequisite modules because
an earlier batch was reverted. The prior reviewed proof and node records provide
the correct interfaces; no statement or definition was changed.

## New nodes

The two prerequisite theorem modules and their node records are included:
`lem-sc-scalar-cup-module-cup-compatibility` and
`lem-sc-scalar-module-cohomology-pullback-comparison`.

## Earlier second reading (a previous round; superseded)

Compiled all three modules with `lcompile.py --all`; the target theorem compiles
without `sorry`, while the two strictly smaller prerequisite comparisons retain
their documented `sorry`s and matching nodes. The target signature is unchanged,
and its proof uses both prerequisites after unfolding `externalCup`.
The target node `lem-sc-scalar-external-cup-module-comparison` is restored as part
of this delivery. The change record is
`coord/changes/scalar-external-cup-module-comparison.md`.

## Second reading by K4

1. **Statements and interfaces.** Compared all three delivered declarations with
the repository DAG records and source definitions. The target and both split-off
theorem signatures are unchanged from their recorded statements; verdict: pass.

2. **Proof and axioms.** Compiled all three modules with `lcompile.py --all`.
The target theorem has no `sorry`; the two prerequisite theorems retain exactly
their documented `sorry`s. No forbidden declarations or hollow definitions were
introduced. Verdict: pass.

3. **New statements.** Searched the Lean library and DAG for the three declaration
names and for scalar cup/pullback comparison statements. The two prerequisite
claims are strictly simpler than the target and are needed by its proof; neither
is already present. Verdict: pass.

4. **Pruning and imports.** The target proof uses both prerequisite modules and
all three of its public imports; the prerequisite imports are required by their
signatures. No import or proof dependency can be removed. Verdict: pass.

5. **DAG and route.** The node proof/proof_deps agree with the theorem proof,
including both split prerequisites, and the chapter/unit metadata is preserved.
The unit route remains recorded unchanged. Verdict: pass.

Changed only the delivery report metadata and second-reading record; no Lean
statement or definition was changed.
