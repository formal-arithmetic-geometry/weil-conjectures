# ClosedSupportStratumHom public imports

## Reason

The proof uses the module-object closed monoidal and derived-functor APIs directly.
Four public ringed-site imports supplied no declaration needed by the statements.
Pruning them reduces the proof dependency closure. Existing signatures, definitions,
visibility, coefficient conventions and universes stay unchanged. No target statement
needs semantic review: all definitions used by targets are byte-identical.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteLocallyProjective
public import Sheaf.AlgebraicGeometry.AdmissibleCondensedCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.HomComplex
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
```

## New

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteLocallyProjective
public import Sheaf.AlgebraicGeometry.AdmissibleCondensedCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
```

## Users

The earlier downstream scan counted 265 transitive consumers. The direct import boundary
has two modules. Neither is adapted; their imports provide the tensor and ringed-site
interfaces they use independently.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | E3, not adapted | Same statements and definitions; independently imports CochainTensorUniverses. |
| Sheaf.Paper.FormalClosedSupport | Q9, not adapted | Same statements and definitions; same stratum theorem signature. |

## Status

landed 20261019T034252-L-415772 2026-10-19 (merge of deliver/D3/Sheaf.AlgebraicGeometry.ClosedSupportStratumHom)
