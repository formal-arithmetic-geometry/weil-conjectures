# AlgebraicGeometry.Scheme.AffineProEt.affine_closed_site_functor_properties

## Reason

Remove unused proof dependencies and replace three unused public imports by the precise Mathlib import required for `Functor.IsCocontinuous`. The theorem statement and `closedSiteLiftInclusion` definition are unchanged. This removes irrelevant derived-category, cohomology, special-cocontinuity, and site-axiom exports from this module. All checked consumers compile unchanged with this interface; no target statement or definition changes meaning.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteLift
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.SpecialCocontinuousCoverings
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.RingTheory.ProEtale.ClosedLiftMap
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.RingTheory.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Sheaf.RingTheory.ProEtale.ClosedLiftAdjunction
import WeilConjectures.RingTheory.ProEtale.ClosedLift
import Sheaf.RingTheory.ProEtale.ClosedLiftUnits
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Sheaf.RingTheory.IndEtaleStability
import Mathlib.RingTheory.Ideal.Maximal
import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings
```

## New

```lean
public import Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteLift
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions
import Sheaf.RingTheory.ProEtale.ClosedLiftAdjunction
import Sheaf.RingTheory.ProEtale.ClosedLiftUnits
```

## Users

The downstream list was obtained with `tools/downstream.py` for the theorem. The second reader compiled the three current direct importers (inverse-image evaluation, closed-site adjunction, specialization restriction) and the indirect inverse-image left-adjoint consumer with `lcompile.py --all` against a freshly compiled scratch copy of the sandbox module (2.1–3.3 seconds each, no warnings). Only the item module is delivered.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.NoetherianStratumDetection` | unclaimed | Same declarations and elaborated types; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation` | D4 | Original source compiled against the pruned module; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint` | E1 | Original source compiled against the pruned module; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction` | G1 | Original source compiled against the pruned module; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation` | D2 | Same declarations and elaborated types; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection` | unclaimed | Same declarations and elaborated types; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed` | B4 | Same declarations and elaborated types; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleSpecializationRestrictionSections` | D2 | Original source compiled against the pruned module; no adaptation. |
| `Sheaf.Paper.CondensedCoefficientComparisons` | unclaimed | Same declarations and elaborated types; no adaptation. |
| `Sheaf.Paper.CondensedFinitePresentationDescent` | B3 | Same declarations and elaborated types; no adaptation. |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | A4 | Same declarations and elaborated types; no adaptation. |
| `Sheaf.Paper.CondensedOpenClosedRecollement` | D3 | Same declarations and elaborated types; no adaptation. |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | unclaimed | Same declarations and elaborated types; no adaptation. |
| `Sheaf.Paper.CondensedQbarComparisons` | unclaimed | Same declarations and elaborated types; no adaptation. |
| `Sheaf.Paper.CondensedQbarExchangeEquality` | A3 | Same declarations and elaborated types; no adaptation. |
| `Sheaf.Paper.CondensedSheafExtContinuity` | C4 | Same declarations and elaborated types; no adaptation. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | unclaimed | Same declarations and elaborated types; no adaptation. |
| `TargetsCheck` | unclaimed | Same declarations and elaborated types; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | Same declarations and elaborated types; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | unclaimed | Same declarations and elaborated types; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | B2 | Same declarations and elaborated types; no adaptation. |

## Status

landed 20261015T185310-L-894313 2026-10-15 (merge of deliver/E1/Sheaf.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties)
