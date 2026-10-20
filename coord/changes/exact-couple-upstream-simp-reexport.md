# CategoryTheory.BigradedExactCouple.derived_alpha, derived_f, derived_g

## Reason

The item has no remaining holes. Its three public simp lemmas duplicate, with identical
names, types and attributes, the declarations in the adopted source module
`WeilConjectures.CategoryTheory.ExactCoupleExtension` (lines 62–72). Redirect the two direct importers to that
module and withdraw the redundant Sheaf module. Keeping local copies risks
constant-name collisions when a consumer imports both modules. No adopted source file
is changed.

## Old

```lean
import WeilConjectures.CategoryTheory.DerivedCoupleMapExactness
public import WeilConjectures.CategoryTheory.ExactCouple

@[simp] theorem derived_alpha (X : BigradedExactCouple C s) (p q : ℤ) :
    X.derived.alpha p q = (Classical.choice X.derivedMaps_exists).alpha p q := by
  simp [derived]

@[simp] theorem derived_f (X : BigradedExactCouple C s) (p q : ℤ) :
    X.derived.f p q = (Classical.choice X.derivedMaps_exists).f p q := by
  simp [derived]

@[simp] theorem derived_g (X : BigradedExactCouple C s) (p q : ℤ) :
    X.derived.g p q = (Classical.choice X.derivedMaps_exists).g p q := by
  simp [derived]
```

## New

```lean
public import WeilConjectures.CategoryTheory.ExactCoupleExtension
```

In both `Sheaf.CategoryTheory.FilteredHomologyExactCouple` and
`Sheaf.AlgebraicGeometry.TruncationExchangeCouple`, replace the old public import
`Sheaf.CategoryTheory.ExactCouple` with the new public import displayed above.
Withdraw `lean/Sheaf/CategoryTheory/ExactCouple.lean` using `deleted.txt`.
The three lemmas above are supplied verbatim by this public import, in the same
namespace and universes. The previous public import of upstream `ExactCouple` is
retained transitively. The additional upstream `ExactCoupleShifted` import defines
only its existing shifted-map API; no local copy of that module exists.

## Users

`python3 tools/downstream.py Sheaf.CategoryTheory.ExactCouple` lists the following
ten transitive users. Only the two direct import lines require edits. Claims checked on 2026-10-20.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FiniteRangeComparison | unclaimed | Same upstream couple and three simp lemmas; no adaptation. |
| Sheaf.AlgebraicGeometry.TruncationExchangeAbutment | unclaimed | Same upstream couple and three simp lemmas; no adaptation. |
| Sheaf.AlgebraicGeometry.TruncationExchangeCouple | unclaimed | Public import redirected; all declarations unchanged. |
| Sheaf.CategoryTheory.FilteredHomologyCoupleComputations | unclaimed | Same upstream couple and three simp lemmas; no adaptation. |
| Sheaf.CategoryTheory.FilteredHomologyCoupleQuotientPages | unclaimed | Same upstream couple and three simp lemmas; no adaptation. |
| Sheaf.CategoryTheory.FilteredHomologyExactCouple | unclaimed | Public import redirected; all declarations unchanged. |
| Sheaf.CategoryTheory.FilteredHomologyTowerDifferential | unclaimed | Same upstream couple and three simp lemmas; no adaptation. |
| Sheaf.CategoryTheory.FilteredHomologyTowerForwardRepresentatives | unclaimed | Same upstream couple and three simp lemmas; no adaptation. |
| Sheaf.CategoryTheory.FilteredHomologyTowerQuotients | unclaimed | Same upstream couple and three simp lemmas; no adaptation. |
| Sheaf.Paper.ExactCoupleDifferential | unclaimed | Same upstream couple and three simp lemmas; no adaptation. |

The direct importers are `FilteredHomologyExactCouple` and `TruncationExchangeCouple`.
`FilteredHomologyTowerForwardRepresentatives` explicitly uses `derived_f`; its exact
statement is preserved. The other eight users need no edits. Both adapted modules are unclaimed; their
public import edits retire a redundant intermediate import. No declaration signature,
attribute, proof, or data changes. There are no definition changes, new hypotheses, or altered
target meanings. The DAG node `def-sp-exact-couple` already points to the source
`WeilConjectures.CategoryTheory.ExactCouple`; its attachment and proof remain valid.

## Status

landed 20261020T132021-L-1402487 2026-10-20 (merge of deliver/P5/Sheaf.CategoryTheory.ExactCouple)
