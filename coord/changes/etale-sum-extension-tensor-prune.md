# EtaleSumExtensionTensor imports and local elaboration settings

## Reason

Prove the existing theorem from the source-library projection formula and elementary monoidal
adjunction identities. Remove the unused resolution/descent imports. The five retained public
imports supply the unchanged definitions and their instances; SitePerfect is proof-only.
Generic coefficient-category helpers and local transparency settings keep concrete derived
functor data folded, so the proof compiles within the single-file limit. The small-colimit
instance priority is local, uses the existing sheaf-colimit construction, and adds no data.
No public declaration signature or definition body changes.

## Old

```lean
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Sheaf.AlgebraicGeometry.EtaleSumFlatKFlat
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Paper.EtaleSumTensorTotalization
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
set_option autoImplicit false
universe u
```

## New

```lean
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u u'
attribute [local instance 2000] Sheaf.instHasColimitsOfShape
attribute [local irreducible] Functor.mapDerivedCategory Adjunction.mapDerivedCategoryAdjunction
    leftDerivedUpperStarIsoMapDerivedCategory etaleLowerShriek upperStar
```

The two public definitions remain verbatim. The only additional declarations are proved private
lemmas. The existing theorem's statement remains verbatim and its proof is now complete.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleSumExtensionTensor | J1 | Proved; imports pruned; local elaboration settings only. |
| Sheaf.SmoothPurity.TensorMateEtalePrecomp | unchanged consumer | Uses the unchanged pullback isomorphism; no adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unchanged consumer | Direct proof importer; no adaptation. |

`tools/downstream.py --uses` found 169 transitive consumers, one external named user of the
pullback isomorphism and no external named user of the comparison or theorem. Both direct
importers are checked against the new module in an isolated sandbox overlay. Local attributes
and proof-only imports do not propagate. No target statement or definition meaning changes.

## Status

landed 20261020T051405-L-1663897 2026-10-20 (merge of deliver/J1/Sheaf.AlgebraicGeometry.EtaleSumExtensionTensor)
