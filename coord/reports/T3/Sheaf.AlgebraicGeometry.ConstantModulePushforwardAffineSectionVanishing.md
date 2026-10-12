## What changed

Filled the proof of `AlgebraicGeometry.Etale.exists_constantModulePushforward_affine_section_eq_zero` in `Sheaf.AlgebraicGeometry.ConstantModulePushforwardAffineSectionVanishing`, without changing its signature. Constructed the base-changed diagram and limiting cone explicitly, established qcqs objects and affine transitions, transferred the zero section through the existing additive section comparisons, applied the injectivity half of global-section continuity, and reflected the resulting equality back to modules. The geometric construction follows the companion `ConstantModuleLimitAffineSectionDescent` proof; the vanishing transfer and injectivity argument are written here.

Added proof-only imports of `Sheaf.AlgebraicGeometry.GlobalSectionsLimitComparison`, `Sheaf.AlgebraicGeometry.ConstantModulePullbackSectionComparison`, `Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected`, and `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic`. Updated the existing DAG node's proof, proof_deps and proof_origin to match this route. No target, statement, definition or public import changed. No new node is needed. The unit's realized steps are preserved.

## Proved and sorry left

Closed the one hole in `AlgebraicGeometry.Etale.exists_constantModulePushforward_affine_section_eq_zero` (node `lem-weil-pbc-constant-module-affine-section-vanishing`). No sorry remains in the delivered module and no hole was added elsewhere. This is a proof from existing stated dependencies: the imported comparison `AlgebraicGeometry.Etale.exists_constantModule_pullback_section_comparison` still has its existing sorry (node `lem-weil-pbc-constant-module-pullback-section-comparison`), and the existing global-section theorem has its own transitive proof obligations. These modules are not changed by this delivery. This does not claim an axiom-free proof of all transitive dependencies.

## No longer needed

Removed the direct imports `WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity` and `WeilConjectures.ConstructibleSheaf.Defs`. The latter remains available through the unchanged public import of `ConstantModulePushforwardFunctoriality`; its constant-pullback comparison is used by the imported section-comparison theorem.

The direct proof dependency `lem-weil-pbc-etale-section-continuity` and its module `WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity` are not needed on this route: global-section continuity is applied directly after base change. The old direct dependency `lemma-constructible-pullback-constant` is now encapsulated in `lem-weil-pbc-constant-module-pullback-section-comparison` and remains needed there. `lem-weil-pbc-constant-module-pushforward-functoriality` remains a statement dependency and public import because it defines the displayed maps; its id/comp theorem is not used in this proof. `lem-weil-pbc-qcqs-morphism-permanence` remains a proof dependency, realized by Mathlib instances and `quasiSeparatedSpace_of_quasiSeparated`. No globally unreachable-module claim is made.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The earlier plan spelled out coefficient and section comparisons rather than naming the now-existing `ConstantModulePullbackSectionComparison`. It also inserted the section-continuity wrapper at the terminal object; global-section continuity already supplies precisely the needed assertion and avoids that wrapper. The edge cases (zero module, empty pullbacks, singleton system) are covered by additive equivalences preserving zero and the existing continuity theorem. Initial local validation could not load the recently landed section-comparison module because it was absent from the published green build; no declaration was duplicated to work around this.

## Second reading by T3

1. The delivered module was diffed against the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof-only imports, proof text, and the matching DAG proof metadata differ. Verdict: pass.

2. The module compiles with `lcompile.py`; it contains no remaining `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof uses only existing theorem dependencies, with the transitive sorry dependencies explicitly identified above. Verdict: pass.

3. The existing node statement is unchanged and the proof follows the stated base-change, section-comparison, and global-section injectivity route. No new split-off statement was added, and no duplicate library theorem was introduced. Verdict: pass.

4. The route is pruned to the direct global-section comparison. Removed section-continuity and constructible-constant proof imports are recorded under `## No longer needed`; the unit's realized route and required functoriality import remain. Verdict: pass.

5. The DAG proof, proof dependencies, and proof origin in the delivered node agree with the Lean proof and its imports. Verdict: pass.

Changed during second reading: added this review record only; no Lean declarations or statements were changed.
