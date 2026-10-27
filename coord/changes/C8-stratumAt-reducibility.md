# AlgebraicGeometry.ProEtale.StratifiedConstantModels.stratumAt

## Reason

The stratum scheme occurs inside the coefficient ring, module category, and finite
product factor types. Regular-definition transparency makes dependent comparisons
expand the pulled-back ring and monoidal structure before reducing the subtype's
value. Diagnostics show the resulting expression contains the full sheafification
and adjunction constructions. Make the same occurrence code reducible to its literal
record, so the domain projection reduces before comparing coefficient instances.
No data, mathematical predicate, hypothesis, or conclusion changes.

## Old

```lean
def stratumAt {X : Scheme.{u}} (S : Scheme.FiniteLocallyClosedStratification X)
    (s : Fin S.n) : Stratum X :=
  ⟨S.domain s, S, s, rfl⟩
```

## New

```lean
abbrev stratumAt {X : Scheme.{u}} (S : Scheme.FiniteLocallyClosedStratification X)
    (s : Fin S.n) : Stratum X :=
  ⟨S.domain s, S, s, rfl⟩
```

## Users

`tools/downstream.py Sheaf.Paper.StratifiedConstantModelProductBound --uses stratumAt`
reports zero downstream modules and one module mentioning the name:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.StratifiedConstantModelProductBound | C8 | Same type and body; transparent stratum projections avoid coefficient expansion. |

The unfinished parent DAG route still needs this item. No withdrawal is proposed.
The target statements and the meanings of all definitions they use are unchanged;
this abbreviation is definitionally equal to the original record construction.

The item's `product` also becomes an abbreviation with its body retained verbatim:

```lean
-- Old:
def product {X : Scheme.{u}} (I : Stratum X → Type (u + 1))
    (F : ∀ T : Stratum X, I T → Modules Λ T.val) (j : Index X I) : Modules Λ X :=
  ∏ᶜ fun s : Fin j.1.n ↦
    (CondensedRing.lowerStar Λ (j.1.immersion s)).obj (F (stratumAt j.1 s) (j.2 s))
-- New:
abbrev product {X : Scheme.{u}} (I : Stratum X → Type (u + 1))
    (F : ∀ T : Stratum X, I T → Modules Λ T.val) (j : Index X I) : Modules Λ X :=
  ∏ᶜ fun s : Fin j.1.n ↦
    (CondensedRing.lowerStar Λ (j.1.immersion s)).obj (F (stratumAt j.1 s) (j.2 s))
```

The downstream search for the module returns zero downstream modules, so its only
existing consumer is the same item. The parent DAG dependency is retained.

## Status

landed 20261023T230556-L-3445492 2026-10-23 (merge of deliver/C8/Sheaf.Paper.StratifiedConstantModelProductBound)
