# Sheaf.CategoryTheory.Abelian.RHomDerivedRoofShift imports

## Reason

The shift theorem assumes a roof-normalized comparison and never invokes the
existence theorem `exists_rhom_hom_derived_roof`. Import its required definitions
directly, so its proof closure does not include that unrelated existence hole.
This is a public-import interface change, with no declaration signature or
mathematical definition changed.

## Old

```lean
public import Sheaf.CategoryTheory.Abelian.RHomDerivedRoof
```

## New

```lean
public import Sheaf.CategoryTheory.KInjectiveBridge
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import Sheaf.CategoryTheory.Abelian.RHomDerivedRoofShiftInjective
```

## Users

`tools/downstream.py Sheaf.CategoryTheory.Abelian.RHomDerivedRoofShift --uses
rhom_hom_derived_roof_shift` reports the item itself and RHomDerivedConnecting as
explicit declaration users. The latter is also the only direct importer.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Abelian.RHomDerivedRoofShift | G1 | theorem type and visibility unchanged; definition imports made explicit |
| Sheaf.CategoryTheory.Abelian.RHomDerivedConnecting | unclaimed | forced addition of one proof import of RHomDerivedRoof |

No target statement or definition used by a target changes. The adapted module's
original fails against the pruned dependency with `Unknown identifier
exists_rhom_hom_derived_roof` at line 105. Its only changed line is an added
`import Sheaf.CategoryTheory.Abelian.RHomDerivedRoof` immediately before its
existing proof import of RHomDerivedRoofShift. With that line it compiles. Every
existing signature and visibility in the adapted module is identical.

## Status

landed 20261013T095954-L-2459150 2026-10-13 (merge of deliver/G1/Sheaf.CategoryTheory.Abelian.RHomDerivedRoofShift)
