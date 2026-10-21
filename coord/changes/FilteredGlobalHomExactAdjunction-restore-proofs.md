# CochainComplex.FiniteFiltered.exactFilteredComplex

## Reason

Restore the assigned quarantined module with five completed proofs and repair the
retired filtered-map constructor used only inside its existing functor-law proofs.
Preserve all public signatures, public imports, definition data, DAG attachments and
the quarantined archive. The remaining theorem is marked STATEMENT-DISPUTED; the
report gives the normalization problem and the positive-grade sign test.

## Old

In `exactFilteredComplex.map_id` and `.map_comp`, respectively:

```lean
    change FilteredObject.HomPreservingSteps.mk _ _ =
      FilteredObject.HomPreservingSteps.mk _ _
```

The archived source fails with unknown-constant errors for that constructor.
The five helper theorems had `sorry` proofs.

## New

In both existing proofs:

```lean
    change FilteredObject.Hom.mk _ _ =
      FilteredObject.Hom.mk _ _
```

The five helper theorems are proved. The unclaimed dependency
`Sheaf.Algebra.Homology.FilteredDerivedHomCalculus` also receives a proof of its
existing `CochainComplex.FiniteFiltered.graded_laws`; its signature is verbatim:

```lean
theorem graded_laws (bounded : Bool) (p : ℤ) :
    (∀ K : Complex A bounded,
      FilteredObject.gradedMapSteps (𝟙 K : K ⟶ K).hom p = 𝟙 (K.obj.filtration.gradedPiece p)) ∧
    (∀ (K L M : Complex A bounded) (f : K ⟶ L) (g : L ⟶ M),
      FilteredObject.gradedMapSteps (f ≫ g).hom p =
        FilteredObject.gradedMapSteps f.hom p ≫ FilteredObject.gradedMapSteps g.hom p) := by
```

Only that theorem's proof is changed in the dependency. The remaining data and
nine postponed theorem proofs are untouched. In the assigned module, the graded
comparison is placed before the inversion theorem, with one proved private
naturality lemma. Every public signature is unchanged. Redundant private imports are removed as listed in report.md.
All four original public imports are retained verbatim. No mathematical definition
or statement is changed, and no target meaning changes.

## Users

`tools/downstream.py` with `--allow-missing --uses filteredGlobalHomExactAdjunction
exactFilteredComplex` reports zero current downstream modules and zero users.
A source scan of both Lean roots and quarantine finds no additional Lean importers
or external uses. This does not authorize withdrawal: the node's parent dependency
edges remain, as does the preserved archived module. The calculus module has the
downstream modules listed below; `--uses graded_laws` finds no external textual user of that name. These consumers need no adaptation,
since a proof replacement preserves every signature and definition. There are no
forced consumer adaptations and no target-statement review is reopened.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.FilteredGlobalHomExactAdjunction | M2 | Restored; five holes closed; functor-law constructor updated; signatures and data unchanged. |
| Sheaf.Algebra.Homology.FilteredDerivedHomCalculus | unclaimed | Prove graded_laws; no interface change. |
| Sheaf.Algebra.Homology.FilteredDerivedHomCalculusUniverse | T2 | No adaptation; unchanged interface. |
| Sheaf.Algebra.Homology.FilteredTruncationData | unclaimed | No adaptation. |
| Sheaf.Algebra.Homology.FilteredTruncationTriangle | unclaimed | No adaptation. |
| Sheaf.Algebra.Homology.UniformFilteredTruncation | unclaimed | No adaptation. |
| Sheaf.AlgebraicGeometry.LocalizationFiltrationDescent | unclaimed | No adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleLocalizationFilteredSection | unclaimed | No adaptation. |
| Sheaf.CategoryTheory.FilteredBifunctorGradedComparison | unclaimed | No adaptation. |
| Sheaf.CategoryTheory.FilteredDerivedOperationLifts | unclaimed | No adaptation. |
| Sheaf.CategoryTheory.FilteredFunctorGradedComparison | unclaimed | No adaptation. |

## Status

landed 20261021T005740-L-1887954 2026-10-21 (merge of deliver/M2/Sheaf.Algebra.Homology.FilteredGlobalHomExactAdjunction)
