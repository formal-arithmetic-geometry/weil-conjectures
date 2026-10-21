# CategoryTheory.siteRepresentableAlgebraicPullback (public imports)

## Reason

The complete proof uses the existing source-library representable comparison,
Mathlib sheaf limits, and the group-object natural-isomorphism API. The broad
covering-axiom and inverse-image tensor modules supply no theorem needed here.
Replace their transitive limit instances by direct Mathlib imports. No declaration
signature or definition body changes. This is an import-interface change only.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.PullbackYoneda
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.SiteInverseImageTensor
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Yoneda
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.PullbackYoneda
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Types.Limits
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SiteRepresentableAlgebraicPullback | U7 | Proof completed; public imports narrowed to required limit instances. |

`python3 tools/downstream.py Sheaf.CategoryTheory.SiteRepresentableAlgebraicPullback
--uses CategoryTheory.siteRepresentableAlgebraicPullback` reports zero downstream
modules. A text search of both library roots finds no other user of either public
declaration and no importer of the module. There are no consumers to adapt.
The theorem and definition signatures and all target statements are unchanged.
The mathematical DAG parent references remain; no module is withdrawn.
The compiler accepts the module and `#print axioms` reports only the standard
three axioms for both declarations.

## Status

landed 20261021T120801-L-3946565 2026-10-21 (merge of deliver/U7/Sheaf.CategoryTheory.SiteRepresentableAlgebraicPullback)
