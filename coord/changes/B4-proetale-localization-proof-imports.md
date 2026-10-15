# ProEtaleWeaklyEtaleLocalization imports

## Reason

The independent second reading found a proof-only module imported publicly:
`Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`. The theorem's
signature uses `PresheafOfModules.pushforward`, whose defining module is now imported
publicly instead. The sheaf pushforward equivalence is only used by private proof
helpers and is now a plain import. The redundant direct public import of
`Mathlib.CategoryTheory.Sites.Equivalence` is removed; it remains publicly available
through the retained `Mathlib.CategoryTheory.Sites.Over`.

No existing declaration signature, definition, target meaning, or proof dependency
changes. The sole original theorem is proved with its byte-for-byte original signature.
This record covers the import interface only.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
```

## New

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
lists the following 32 transitive users. No user is adapted. All existing declarations
in the changed module have identical signatures, and no underlying data definition
changes, so no user's statement or a target's meaning changes. Source import-closure
analysis finds an independent public path to Sheaf.PushforwardContinuous for 25
users; the remaining seven are checked by single-file compilation against the changed
module in a scratch overlay. Sites.Equivalence remains publicly reachable for all.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal | unclaimed | Statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.NoetherianStratumDetection | unclaimed | Statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleExtensionByZero | unclaimed | Statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleExtensionByZeroAdjunction | unclaimed | Statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison | unclaimed | Statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation | D2 | Statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover | unclaimed | Statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection | unclaimed | Statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed | B4 | Statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleShriekSpecializationZero | D2 | Statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSpecializationRestrictionSections | D2 | Statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | B3 | Statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | A4 | Statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.CondensedOpenClosedRecollement | D3 | Statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | Statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | C4 | Statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteCtfTriangulated | unclaimed | Statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteRingConstructibleSheafOrigin | unclaimed | Statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteTensorConstructibleCohomology | unclaimed | Statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteTorsionConstructibility | unclaimed | Statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.IntrinsicFiniteTorsionConstructibility | unclaimed | Statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated | unclaimed | Statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleLisseOrigin | unclaimed | Statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleResidueTorTest | unclaimed | Statements and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | A2 | Statements and definitions unchanged; no adaptation. |
| TargetsCheck | unclaimed | Statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | B2 | Statements and definitions unchanged; no adaptation. |

The seven users requiring the compilation check are
Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover,
Sheaf.Paper.CondensedCoefficientComparisons,
Sheaf.Paper.CondensedQbarComparisons,
Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp,
WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport,
WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper, and
WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit.

Validation: the changed module and five of these seven downstream sources compile
cleanly against the changed-module scratch overlay. CompactSupport fails at lines
106 and 114 with the same `preservesFiniteColimits_tensorLeft_sheaf` application-type
mismatch both against the baseline library and against the overlay; it is a pre-existing
local build/source mismatch, not a missing declaration from these import changes.
TwoColimit exceeds the 60-second single-file limit against both the baseline library
and the overlay. It contains no use of SheafOfModules.over/pushforward/overFunctor
or the equivalence helpers from the affected module. These two baseline limitations
are reported rather than called successful compilation. No downstream file was edited.

## Status

landed 20261015T183129-L-811377 2026-10-15 (merge of deliver/B4/Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization)
