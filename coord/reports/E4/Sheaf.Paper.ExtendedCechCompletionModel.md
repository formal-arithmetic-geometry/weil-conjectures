## What changed

The reflector theorem `CategoryTheory.ringedExtendedCech_reflector_properties` is now proved by a real reduction. A new module, `Sheaf.Paper.ExtendedCechReflectorCore`, isolates the two genuinely difficult clauses: completeness of the internal-Hom output and the universal mapping bijection. The existing private naturality calculation supplies the naturality clause, and `unit_isIso_of_complete_universal` derives the unit-isomorphism clause.

The change record is `coord/changes/extended-cech-reflector-core.md`.

The delivery removes the unused proof-only imports and the private cone/precomposition helpers that were only needed by the former admitted reflector proof. The module and its new core compile together with the permitted compiler.

## Proved and sorry left

Closed one existing hole: `CategoryTheory.ringedExtendedCech_reflector_properties`.

One existing hole remains: `CategoryTheory.exists_ringedExtendedCech_global_model`.

One strictly smaller hole was added: `CategoryTheory.ringedExtendedCech_reflector_core`, in `Sheaf.Paper.ExtendedCechReflectorCore`, node `lem-weil-pbc-extended-cech-reflector-core`. It contains the finite localization-filtration and sequential-localization comparison argument required for completeness and the universal mapping bijection. No sorry occurs in a definition.

The original `CategoryTheory.exists_ringedExtendedCech_completion_model` theorem remains a complete conjunction proof from the global-model and reflector clauses.

## No longer needed

The reflector proof no longer uses the old private `precomp_bijective_of_internalHom_isIso` and `precomp_bijective_of_cone_internalHom_zero` helpers. Consequently their proof-only imports are removed: `Sheaf.Algebra.Homology.RhomGlobalSections`, `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`, `Sheaf.CategoryTheory.RingedSiteCompleteElementsIdeal`, `Sheaf.CategoryTheory.SiteCoveringAxioms`, `Sheaf.CategoryTheory.SpecialCocontinuousSheafEquivalence`, `Sheaf.Paper.RingComplexFunctorial`, `Sheaf.Paper.RingedLocalizationRHomCalculus`, `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`, and `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`. The remaining imports support the public statements or the retained completion-unit naturality proof.

The reflector node's former empty proof dependency list is replaced by `lem-weil-pbc-extended-cech-reflector-core`; the naturality and universal-unit helper proofs are private declarations in the item module and need no separate DAG nodes.

No unit-level route is bypassed, and no existing dependency module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The direct reflector proof plan requires the missing finite localization-filtration and sequential-localization comparison. The parent theorem's naturality and final unit-isomorphism clauses are formal consequences once completeness and the universal mapping bijection are available, so retaining all four clauses in one admitted theorem obscured a strictly smaller remaining obligation. The new node records that precise obstruction.

Searches with LeanFinder, Loogle, `msearch.py`, and repository grep found no existing declaration for either the global model or the core reflector clauses. The Stacks proof constructs the global complex by special-cocontinuous site descent and proves the reflector by local contraction; those constructions are not present as reusable Lean declarations.

## New nodes

`lem-weil-pbc-extended-cech-global-model`, `lem-weil-pbc-extended-cech-reflector-properties` (the landed split interface record, refreshed for this delivery), and `lem-weil-pbc-extended-cech-reflector-core`, realized by `CategoryTheory.ringedExtendedCech_reflector_core` in `Sheaf.Paper.ExtendedCechReflectorCore`. It states only completeness of the completion output and the universal mapping bijection, strictly less than the parent reflector theorem. Its proof remains the named finite-filtration/sequential-localization obligation described in its docstring.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
