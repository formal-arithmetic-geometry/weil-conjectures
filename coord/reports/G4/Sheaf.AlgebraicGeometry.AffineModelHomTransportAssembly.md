## What changed

Completed `AlgebraicGeometry.exists_affineModelHomTransportAssembly` in
`Sheaf.AlgebraicGeometry.AffineModelHomTransportAssembly`, preserving its statement.
The proof uses the existing affine derived Hom equivalence, composes with the supplied
geometric equivalences, conjugates by the supplied object comparisons, and applies
both coherence equations in `affineModelComparisonData`. Proved private helpers supply generic Hom conjugation and its chain-map formula.
The public proof chooses the stage equivalences simultaneously and combines their
chain-map equations directly with the two comparison-data identities by equality
transitivity and congruence.
Updated the existing node's final proof step to record the completed assembly.
No public definitions, signatures, or imports changed.

Read the pinned Stacks `perfect.tex`, affine comparison proof (Tag 06Z0) and affine
part of the Hom descent proof (Tag 09RE). The unit record
`sk-thm-picard-semicon` has empty realized lists; the prescribed route is preserved.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_affineModelHomTransportAssembly`
(blueprint: `lem-pc-affine-model-hom-transport-assembly`).
No sorries remain in the delivered module; no holes or new nodes were added.
This completes the assembly from the existing named affine-equivalence dependency;
it does not claim to discharge that dependency's remaining transitive holes.

## No longer needed

None. All three existing imports are used: the public comparison-data import supplies
the statement, `AffineQCohDerivedEquivalence` supplies the affine Hom comparison,
and `Mathlib.CategoryTheory.HomCongr` supplies isomorphism conjugation.
The existing proof dependency `lem-pc-affine-qcoh-derived-equivalence` remains needed.
No nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The node's final step described the assembly as
still left with sorry; it now records the completed proof. Type inference through
functor objects and large equivalence expressions was expensive, so the proof uses
explicit scalar-extension complexes and equality transitivity with congruence.
A larger collection of local aliases was removed to reduce kernel conversion work.
No statement or shared definition was changed, and the compile time limit was kept.

Validation: the complete module compiled through `lcompile.py` against the published
build in 56.0 seconds. There are no `sorry` occurrences or lines over 100 characters.

## Second reading by G4

1. Compared the delivered Lean module with the repository version. Existing declaration signatures and definitions are unchanged byte for byte; only private proof helpers, the target proof, and the DAG proof metadata changed. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds with no errors, no `sorry`, and no forbidden declarations. The target proof uses only the permitted logical axioms through its dependencies. Verdict: pass.
3. Checked the proof route and split-off statements against the imported declarations and searches. No new statements or nodes were added, and the completed theorem is exactly the existing target statement. Verdict: pass.
4. Checked pruning and imports. The public comparison-data import is required by the statement; the affine derived equivalence and HomCongr imports are used by the proof. No obsolete imports or proof dependencies were found. Verdict: pass.
5. Checked the DAG node and unit metadata. The node proof now records the completed affine transport and its proof dependency remains `lem-pc-affine-qcoh-derived-equivalence`; the unit route is preserved and no realized unit step was bypassed. Verdict: pass.

Changed only this report section; no Lean declarations, interfaces, or imports were altered during second reading.
