# Sheaf.TraceFormula.EtaleClosedComplementSets: public import interface

## Reason

Prove `AlgebraicGeometry.etaleClosedComplementSets` through the existing closed-immersion
site-density and induced-topology arguments. The public definitions need the continuous-site
adjunction from `UpperLowerStar.Defs`; they do not need the broader set-valued composition-unit
module. The statement and all three definition bodies are unchanged. No source-library file,
target statement, or mathematical definition is changed.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.CategoryTheory.Sites.GeometricMorphism
import Sheaf.AlgebraicGeometry.PointedEtaleStalk
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import WeilConjectures.SixFunctors.OpenClosed.Stalk
```

## New

```lean
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.SixFunctors.OpenClosed.Supported
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Complement
```

## Users

All three original direct consumers were compiled against this sandbox version using
`lcompile.py`, without edits. The complete transitive downstream list is below. A declaration
name use search found no additional users. Holders are from the shared snapshot at preparation.
No consumer adaptation is necessary; no claimed module is modified.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Sites.OrientedClosedBaseLocalization | unclaimed (shared snapshot) | Direct importer; original compiles unchanged with the new imports. |
| Sheaf.CategoryTheory.Sites.ToposComplementModuleStalks | unclaimed (shared snapshot) | Transitive importer; public signatures and definition bodies unchanged. |
| Sheaf.Paper.CoefficientChangeDualizing | unclaimed (shared snapshot) | Transitive importer; public signatures and definition bodies unchanged. |
| Sheaf.Paper.CtfHomCoefficientComparison | unclaimed (shared snapshot) | Transitive importer; public signatures and definition bodies unchanged. |
| Sheaf.Paper.CtfHomConditionB | unclaimed (shared snapshot) | Transitive importer; public signatures and definition bodies unchanged. |
| Sheaf.Paper.CtfHomLocalizationDevissage | unclaimed (shared snapshot) | Transitive importer; public signatures and definition bodies unchanged. |
| Sheaf.Paper.GaloisLocalizationUniformBounds | G1 | Transitive importer; public signatures and definition bodies unchanged. |
| Sheaf.Paper.OrientedClosedBaseRestriction | unclaimed (shared snapshot) | Direct importer; original compiles unchanged with the new imports. |
| Sheaf.Paper.OrientedConstructibleSubquotients | unclaimed (shared snapshot) | Transitive importer; public signatures and definition bodies unchanged. |
| Sheaf.Paper.OrientedSourceLocalization | unclaimed (shared snapshot) | Direct importer; original compiles unchanged with the new imports. |

## Status

landed 20261021T111415-L-112129 2026-10-21 (merge of deliver/P4/Sheaf.TraceFormula.EtaleClosedComplementSets)
