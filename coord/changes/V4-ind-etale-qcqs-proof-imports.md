# AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_affine_locally_indEtale

## Reason

The proof uses the coefficient comparison internally, so its import is private.
The statement uses module-valued sheaves, rather than `ringedSiteModules`, and needs
only the ordinary etale site, the ind-etale universe transport and the derived
exchange interface. Remove unused public imports along with the unused proof imports.
The declaration signature and all definitions are unchanged.

## Old

```lean
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import WeilConjectures.SixFunctors.BaseChange.Derived
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.IndEtaleQcqsDirectImageBaseChange | V4 | Its proof uses the private coefficient comparison; statement unchanged. |

There are no direct Lean importers: searching both library roots for
`^(public )?import Sheaf.AlgebraicGeometry.IndEtaleQcqsDirectImageBaseChange$`
returned none. Unfinished DAG parents still need this theorem; it is retained with
its exact signature and Lean attachment. No consumer adaptation is necessary.
The target statements and definitions used by them are unchanged.

## Status

landed 20261026T083321-L-2322469 2026-10-26 (merge of deliver/V4/Sheaf.AlgebraicGeometry.IndEtaleQcqsDirectImageBaseChange)
