# CategoryTheory.Triangulated.TStructure.truncationCohomologyComparison

## Reason

The stage-3 preflight conservatively classifies added `omit` and theorem-scoped
`set_option` commands as a change visible to other modules. Record those commands
for independent review. They support proof elaboration and the private helper;
every existing public signature, attribute, definition and public import is preserved.

## Old

No private `comparison_hom_app` or `truncation_comparison_comp` helper existed.
There were no theorem-scoped proof settings. The existing theorem bodies were `sorry`.
The ambient section variables and every public declaration have the same text in the
old and new versions.

## New

The new private helper starts with:

```lean
omit triC in
private lemma comparison_hom_app (j : ℤ) (K : C) :
```

The `omit` applies to this private helper alone. It removes an unused triangulated
instance from that helper's signature, not from any public declaration.

These settings wrap the two existing t-exactness helper theorems:

```lean
set_option linter.unusedSectionVars false in
```

They retain the existing inferred section parameters while avoiding an unused-variable
warning in these elementary proofs.

These settings wrap the existing naturality, composition, identity, square and vertical
theorems individually:

```lean
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
```

They permit elaboration through existing `truncLE`, `truncLT` and `truncGE` definitions.
They neither change those definitions nor introduce a global option or attribute.
The two new private helpers have complete proofs. No new public declaration is added.

## Users

`tools/downstream.py Sheaf.CategoryTheory.Triangulated.CohomologyComparisonPasting
--uses truncationCohomologyComparison` reports zero downstream modules and only the
item itself as a textual user. A search of both Lean roots for all nine theorem names
and the comparison definition finds only this module. The DAG parent
`lem-a1-texact-coefficient-stage-descent` still needs the unchanged statements; no
withdrawal is proposed. No target definition is changed or target review reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Triangulated.CohomologyComparisonPasting | G7 (item) | Nine proofs completed; scoped proof commands and two private helpers; public API unchanged. |

## Status

landed 20261023T102800-L-2971910 2026-10-23 (merge of deliver/G7/Sheaf.CategoryTheory.Triangulated.CohomologyComparisonPasting)
