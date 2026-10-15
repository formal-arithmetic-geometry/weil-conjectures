# ProEtale finite coproduct module imports

## Reason

The proofs compile without directly exporting `Mathlib.CategoryTheory.Sites.Subcanonical`.
The target's statements and proof use the sheaf and Yoneda declarations already supplied by
`Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`; the new split module also compiles without
that direct public import. Removing the redundant public edge keeps proof-only dependencies
private and avoids changing the public import surface unnecessarily.

## Old

```lean
-- ProEtaleFiniteCoproductEvaluation.lean
public import Mathlib.CategoryTheory.Sites.Subcanonical

-- ProEtaleFiniteCoproductSections.lean
public import Mathlib.CategoryTheory.Sites.Subcanonical
```

## New

Neither module has a direct `Mathlib.CategoryTheory.Sites.Subcanonical` import. All existing
public declarations and theorem signatures are unchanged.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation`
reports 25 transitive downstream modules. They continue to compile against the retained public
imports and see no declaration or signature change. The new sections module is imported only
by the target in this delivery; the target is the forced direct user of its new theorem.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation | B3 | Redundant public import removed; theorem signature unchanged. |
| downstream modules of the target | various / unclaimed | No effect; all existing declarations and signatures remain available. |

## Status

landed 20261015T161022-L-259317 2026-10-15 (merge of deliver/B3/Sheaf.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation)
