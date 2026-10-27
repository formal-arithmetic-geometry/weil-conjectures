# Private helper binders in Sheaf.Paper.AnchoredPureCurveCriterion

## Reason

The delivery adds three local `omit ... in` commands on proved private lemmas to
avoid unused-section-variable warnings. The source interface scanner reports any
changed nondeclaration command as an interface change. These commands affect only
the immediately following private theorem. Every existing public signature,
definition body, attribute and public import is unchanged.

## Old

There were no such private helpers or local omit commands.
The existing declarations remain verbatim in signature and definition body.

## New

```lean
omit [IsAlgClosure ℚ_[l] Ω] [IsSeparated X₀.hom] in
private theorem finiteSpectrum_iff

omit [IsSeparated X₀.hom] in
private theorem closedPoint_card_gt_one

omit [IsSeparated X₀.hom] in
private theorem curve_purity_at_point
```

Each command is scoped to its following private theorem, whose proof is complete.
The new public theorem `WeilConjectures.classicalRealized_anchor_eigenvalue` is in
a separate new module and is used through a private proof import.

## Users

`tools/downstream.py Sheaf.Paper.AnchoredPureCurveCriterion --uses anchoredFiniteLocalSpectrum`
reports zero downstream modules and only the item's own occurrences of that definition.
That definition, and every other existing public declaration, is unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AnchoredPureCurveCriterion | D4 | New private helpers omit unnecessary binders locally; existing API is unchanged. |
| Sheaf.Paper.ClassicalRealizedAnchorEigenvalue | new in D4 delivery | New smaller residual theorem, privately imported by the item. |

## Status

landed 20261025T122710-L-1798032 2026-10-25 (merge of deliver/D4/Sheaf.Paper.AnchoredPureCurveCriterion)
