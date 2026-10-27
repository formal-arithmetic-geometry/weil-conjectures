# AlgebraicGeometry.ProEtale.finiteRingRelativeScalarComparison

## Reason

Prune redundant public imports and unused proof imports while proving the existing
statement. Its complete signature and the scalar-mate definition remain verbatim.
The remaining public imports supply every name in those signatures and the definition;
the additional proof imports supply only the assembly argument. The two `import all`
lines use existing proved private helpers, without adding any public declaration.
No source-library file is modified.

## Old

The original import block, verbatim:

```lean
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.FiniteConstantRingedLocalModel
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.Paper.EtaleProEtaleScalarMate
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.Paper.ScalarPullbackRepresentativeData
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import Sheaf.AlgebraicGeometry.EtaleScalarFlatModel
import Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.Paper.PurEtaleScalarMateProjection
public import Sheaf.Paper.EtaleUnboundedRestrictionComparison
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
```

## New

The new import block, verbatim:

```lean
public import Sheaf.Paper.EtaleProEtaleScalarMate
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
import all Sheaf.Paper.FiniteCoefficientDirectImage
import all Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula
import Sheaf.Paper.ProEtaleLisseFiniteModelsFromLisse
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
```

## Users

`python3 tools/downstream.py Sheaf.Paper.FiniteRingRelativeScalarComparison`
reports zero downstream modules. There are no adapted consumer modules. The DAG
parent still uses the theorem, whose statement and normalization maps are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteRingRelativeScalarComparison | K9 | Existing theorem proved; imports pruned; signatures unchanged. |

## Status

landed 20261025T202532-L-2727042 2026-10-25 (merge of deliver/K9/Sheaf.Paper.FiniteRingRelativeScalarComparison)
