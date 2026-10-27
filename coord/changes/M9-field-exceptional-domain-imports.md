# AlgebraicGeometry.ProEtale.FieldExceptionalSystem.Domains

## Reason

The definitions-only module retained four private imports of theorem proof closures.
Its declarations use none of those imports. Profiling the comparison module isolated
about 22 seconds in Mathlib's privateModule linter loading import metadata. Removing
unused private proof imports removes redundant dependencies from the domain interface.
That cleanup alone did not bring the full proof below 60 seconds; the accompanying explicit
adjunction-projection API addresses repeated dependent-type conversions.
The public imports, all declaration signatures, attributes and bodies stay verbatim.
The edited module compiled with lcompile.py in 9.1 seconds without warnings.
No existing definition or target changes its mathematical meaning. No source-library
module is edited. Domains is unclaimed in coord/claims at preparation time.

## Old

```lean
public import Sheaf.Paper.FieldShriekSystemComparison
public import Sheaf.Paper.SmoothPurityTowerGluing
public import Sheaf.SecSmoothPurity.ReductionExceptional
import Sheaf.Paper.FieldScalarNormalizedSystems
import Sheaf.Paper.SmoothPurityTowerGamma
import Sheaf.SecSmoothPurity.ReductionCompatibilities
import Mathlib.CategoryTheory.Adjunction.Mates
```

## New

```lean
public import Sheaf.Paper.FieldShriekSystemComparison
public import Sheaf.Paper.SmoothPurityTowerGluing
public import Sheaf.SecSmoothPurity.ReductionExceptional
```

## Users

The modules below are the complete downstream list from tools/downstream.py, plus
the edited module. Holders are read from coord/claims on 2026-10-26. There are no
forced adaptations to another group's module. Seven unchanged interface sources
(the six exceptional intermediates and Arrows) remain for the dependency-order compile.
The four parent consumers were checked unchanged and their temporary copies removed.
These copies produce no Git diff. LevelWords has a separate performance repair recorded
in M9-field-purity-finite-theta-type.md.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FieldExceptionalSystemDomains | unclaimed | Private imports removed; public imports and declarations unchanged. |
| Sheaf.Paper.FieldExceptionalSystemAdjoints | unclaimed | Domains needs no adaptation; separate typed projection change is recorded in M9-field-exceptional-adjunction-projection.md. |
| Sheaf.Paper.FieldExceptionalSystemComparison | M9 | Own proof delivery; public statement unchanged. |
| Sheaf.Paper.FieldExceptionalSystemComponents | unclaimed | No source edit; public interface of Domains unchanged. |
| Sheaf.Paper.FieldExceptionalSystemEvaluation | unclaimed | No source edit; public interface of Domains unchanged. |
| Sheaf.Paper.FieldExceptionalSystemFiniteAdjoint | unclaimed | No source edit; public interface of Domains unchanged. |
| Sheaf.Paper.FieldExceptionalSystemFiniteComposite | unclaimed | No source edit; public interface of Domains unchanged. |
| Sheaf.Paper.FieldExceptionalSystemIso | unclaimed | No source edit; public interface of Domains unchanged. |
| Sheaf.Paper.FieldExceptionalSystemLaws | unclaimed | No source edit; public interface of Domains unchanged. |
| Sheaf.Paper.FieldProjectionOriginWitnesses | W8 | No source edit; public interface of Domains unchanged. |
| Sheaf.Paper.FieldPuritySystemTranspose | unclaimed (C1 landed) | No source edit; public interface of Domains unchanged. |
| Sheaf.Paper.FieldPuritySystemTransposeBase | unclaimed (C1 landed) | Current original source included in the complete dependency check. |
| Sheaf.Paper.FieldPuritySystemTransposeCompatibility | unclaimed (C1 landed) | Current original source included in the complete dependency check. |
| Sheaf.Paper.FieldPurityTransposeArrows | unclaimed | No source edit; public interface of Domains unchanged. |
| Sheaf.Paper.FieldPurityTransposeLevelWords | unclaimed | Domains needs no adaptation; separate finiteTheta performance repair is recorded in M9-field-purity-finite-theta-type.md. |

The current C1 landing replaced its parent hole with Base and Compatibility modules.
All three current originals, W8's original Witnesses, Arrows and the repaired LevelWords
passed the clean six-module consumer compile against the completed API. The four parent
source copies were then removed from the packet; they contribute no Git diff. Seven
unchanged interface copies remain for the final dependency-order rebuild. Current claims
are rechecked before delivery.

## Status

landed 20261026T070331-L-3547379 2026-10-26 (merge of deliver/M9/Sheaf.Paper.FieldExceptionalSystemComparison)
