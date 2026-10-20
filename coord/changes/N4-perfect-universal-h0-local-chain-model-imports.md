# AlgebraicGeometry.Scheme.perfect_universalH0_local_chain_model

## Reason

The restored item is compiled against the current adopted source tree. Its public
statement mentions `derivedPullback`, whose declarations are supplied by the adopted
source module `WeilConjectures.AlgebraicGeometry.DerivedPullback`. The quarantined
version retained the public import of the withdrawn Sheaf alias, so that line remains
for compatibility while the source module is added as a public import. The proof also
uses the adopted source affine representative module. This preserves the theorem's
signature and makes the required public vocabulary available to downstream importers.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PerfectUniversalH0LocalChainModel | N4 | Public derived-pullback vocabulary is supplied by the adopted source module; theorem signature and proof compile unchanged. |

## Status

landed 20261020T221302-L-4168994 2026-10-20 (merge of deliver/N4/Sheaf.AlgebraicGeometry.PerfectUniversalH0LocalChainModel)
