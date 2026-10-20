# etaleFiniteTwistPullback_base import interface

## Reason

The base theorem only concerns ordinary sheaves. Its original header re-exported
additional derived tensor and shift infrastructure and imported proof-plan modules
that the completed construction does not use. Retain the statement infrastructure,
import the five proved helper modules through the two immediate proof dependencies,
and use the existing canonical monoidal-unit and composition theorems. No existing
declaration signature, visibility or definition changes. No target meaning changes.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Sheaf.Paper.RingedTopoiDerivedTensorPullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable
import WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitAwayCoverEtale
import Sheaf.AlgebraicGeometry.IsIsoIffOfJointlySurjectiveEtaleFamily
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.Paper.RingedTopoiCanonicalTensorPullback
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
```

## New

```lean
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import Sheaf.AlgebraicGeometry.FiniteEtaleTateLinePullback
import Sheaf.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionReduction
```

The proof also sets `autoImplicit false`,
`backward.isDefEq.respectTransparency false` and its `.types` option for elaboration.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullbackBase | J3 | Completed proof and imports; identical signature. |
| Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback | unclaimed | Direct consumer, compiled unchanged against the new base. It imports its own derived infrastructure. |
| Sheaf.Paper.ConnectedTateLineEndomorphisms | unchanged downstream consumer | Imports the parent; compiled unchanged against both new modules. |

`tools/downstream.py ... --uses etaleFiniteTwistPullback_base` lists the base and
parent as textual users; its downstream listing additionally names
ConnectedTateLineEndomorphisms. No consumer adaptation is needed or delivered.
The parent's public imports stay identical and its base import is private.

## Status

landed 20261020T132014-L-1401226 2026-10-20 (merge of deliver/J3/Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullbackBase)
