## What changed

Proved `AlgebraicGeometry.exists_flat_model_of_boundedAbove_model` by applying the functorial bounded-above flat replacement to the given representative and transporting the derived-category isomorphism across the localized quasi-isomorphism. The proof uses only the existing `BoundedFlatReplacement` dependency.

## Proved and sorry left

The declaration `AlgebraicGeometry.exists_flat_model_of_boundedAbove_model` is proved. No `sorry` remains in the delivered module.

## No longer needed

Removed `Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation`; it is unused by the statement and proof.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan is accurate. The unused `HasDerivedCategory B.Modules` hypothesis is retained to preserve the target signature.

## Second reading by G1

1. Compared the delivered module with the repository version. The theorem signature is byte-for-byte unchanged; only imports and the proof body changed. Verdict: pass.
2. Compiled the module and checked the theorem axioms. Compilation succeeds, with only the permitted axioms `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `axiom`, `unsafe`, or hollow definition is present. Verdict: pass.
3. The proof uses the existing bounded-above flat replacement theorem and localization isomorphism criterion. No new split-off statements were added, and the target statement is unchanged. Verdict: pass.
4. The proof follows the unit route through functorial bounded-above flat replacement; the former presentation import is unused and was removed. Verdict: pass.
5. The DAG node's declaration, proof dependency, and proof origin agree with the Lean proof; no node files require changes. Verdict: pass.

Changed the imports to expose only the modules needed by the statement and to import the bounded flat replacement theorem privately; no proof repair was needed.

The import-interface change is recorded in `coord/changes/BoundedAboveModelFlatReplacement-imports.md`; the sole direct importer already imports the removed presentation module itself, so no forced adaptation was necessary.
