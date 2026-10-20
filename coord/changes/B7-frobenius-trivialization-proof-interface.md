# absoluteFrobenius_proEtale_trivialization_pullback

## Reason

Prove the existing theorem from the normalized AbsoluteFrobeniusSite witnesses,
using geometric naturality, the module adjunction and exact derived descent.
Remove unused proof dependencies. Record the local irreducibility attributes and
two removed public imports conservatively as an interface change. No declaration
signature, definition, instance, target statement or visibility changes. Every
irreducibility attribute is local and changes no importer's reducibility settings.
The attributes keep concrete tensor adjunction and constant-sheaf constructions
folded during elaboration; without them exploratory compiles exceeded 60 seconds.

## Old

The old import header contained these now-removed lines, verbatim:

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
public import Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition
import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleTensorCompositionUnit
import WeilConjectures.CategoryTheory.SiteMorphismComposition
import Sheaf.Paper.IntegralFinitePullbackComposition
```

There were no local irreducibility attributes. The public theorem had one `sorry`.

## New

The above imports are removed. This proof-only import is added:

```lean
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
```

The proof uses this local command after its direct-image evaluation helpers:

```lean
attribute [local irreducible] CategoryTheory.constantSheaf conjugateIsoEquiv
  proEtaleRingModuleAdjunction conjugateEquiv
  proEtaleRingDirectImageMap proEtaleConstantRingComparison
  proEtaleRingModulePullback proEtaleRingModulePullbackObj proEtaleRingModulePullbackMap
```

All new helpers are proved and private. The existing public statement and docstring
are byte-for-byte identical. There is no `sorry` in the delivered Lean module.

## Users

The latest `tools/downstream.py` scan lists the following two direct and transitive
importers. Its textual-use check lists this item and SchemeGeometricFrobenius.
Earlier scans during the live repository refresh listed more modules; those files
are absent from the current source tree. No consumer is edited or delivered.
Both current direct importers already import the removed public dependencies when
needed. Unchanged copies compiled against the candidate in the sandbox:
FrobeniusStalkTrivializationNormalization in 31.0 seconds and
SchemeGeometricFrobenius in 43.3 seconds. The candidate compiled in 51.4 seconds
in that three-module check (and in 18.1 seconds in its prior single-file check).

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback | B7 | One hole closed; signature identical. |
| Sheaf.AlgebraicGeometry.FrobeniusStalkTrivializationNormalization | W7 | Same statements; no adaptation. |
| Sheaf.SixFunctors.SchemeGeometricFrobenius | X2 | Same statements; no adaptation. |

## Status

landed 20261020T131936-L-1392910 2026-10-20 (merge of deliver/B7/Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback)
