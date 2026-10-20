# AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_iff

## Reason

Retire the duplicate recorded in coord/retire-items.tsv. Its only difference from the
adopted source theorem is the shorter name and a redundant reconstruction of the same
stratification. The canonical source theorem is already fully proved with the identical
universes, hypotheses, coefficient category and conclusion. This is a zero-hole
retirement, not a new proof or a definition change.

## Old

```lean
theorem isConstructibleEtaleModuleSheaf_iff
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsConstructibleEtaleModuleSheaf F ↔
      IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ => M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ => M) F
```

The theorem was in `Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`.

## New

The duplicate module is withdrawn. Each live consumer imports
`WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`
and applies this existing source theorem instead:

```lean
theorem isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsConstructibleEtaleModuleSheaf F ↔
      IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ => M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ => M) F
```

Node `lem-weil-pbc-constructible-etale-module-sheaf-comparison` remains attached,
now to that source module (existing declaration). Its mathematical statement and
all parent dependency edges are preserved. No source-library module is modified.
No target statement or definition changes, so no target meaning changes.

## Users

The complete downstream list from `tools/downstream.py --uses` follows.
All consumers have unchanged signatures, definitions and mathematical conclusions.
Only the direct consumers need their private proof import and theorem applications renamed.
The required compile of `Sheaf.Paper.FiniteCoefficientFlatModel` initially timed out.
A profiled scratch compile with a diagnostic lower heartbeat limit located repeated
`isDefEq`/`whnf` work at the first K-flat equivalence rewrite. Its retained complete proof
now fixes the same cochain tensor structure explicitly, and supplies the complex arguments
to the equivalences instead of asking `rw` to infer them. The profiled complete file
compiled in 21.9 seconds, with no higher limit or proof splitting. This is a local proof
elaboration repair; all definitions, instances visible to importers and signatures stay fixed.

Reviewer correction (2026-10-21): after this delivery's base, a landed change rewrote
`Sheaf.AlgebraicGeometry.ProjectiveLineConstructible` (it now cites the source library's
`hasConstructibleDirectImages_projectiveLine`; the private `abelianSetPullbackIso` and
`constructibleAbelian_underlyingSets` no longer exist there), and a landed change replaced
the import `Sheaf.AlgebraicGeometry.ConstructibleModuleOfFiniteCoefficientSets` of
`Sheaf.AlgebraicGeometry.FiniteConstructibleDirectImage` by its WeilConjectures source module.
The delivered copies of these two modules reverted those landed changes. Both are now the
current live text with only this retirement's import swap and theorem rename; the earlier
`Nonempty` helper repair of `ProjectiveLineConstructible` is withdrawn as moot.

Old proof fragment:
```lean
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic]
```

New proof fragments:
```lean
  let : MonoidalCategory (CochainComplex C ℤ) :=
    HomologicalComplex.monoidalCategory C (.up ℤ)
```
```lean
    apply (HomotopyCategory.kFlat_quotient_obj_iff P).mp
    apply (HomotopyCategory.kFlat_iff_preserves_acyclic
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)).mpr
```

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.BoundarySheafConstructible | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.AlgebraicGeometry.CompactBoundedConstructibleBaseChange | unclaimed | Private proof import migrated and comparison applications renamed. |
| Sheaf.AlgebraicGeometry.ConstantFiniteComparison | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.AlgebraicGeometry.ConstructibleFiniteSurjectionCancellation | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImagesComp | unclaimed | Private proof import migrated and comparison applications renamed. |
| Sheaf.AlgebraicGeometry.ConstructibleOfFiniteDirectImage | unclaimed | Private proof import migrated and comparison applications renamed. |
| Sheaf.AlgebraicGeometry.ConstructibleSheafDevissage | unclaimed | Private proof import migrated and comparison applications renamed. |
| Sheaf.AlgebraicGeometry.CurveOpenConstructibleGeneral | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.AlgebraicGeometry.DirectImageFinitenessInputHolds | unclaimed | Private proof import migrated and comparison applications renamed. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineLisseFiniteComplement | unclaimed | Private proof import migrated and comparison applications renamed. |
| Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel | unclaimed | Private proof import migrated and comparison applications renamed. |
| Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.AlgebraicGeometry.FiniteBoundaryReconstruction | unclaimed | Private proof import migrated and comparison applications renamed. |
| Sheaf.AlgebraicGeometry.FiniteConstructibleDirectImage | unclaimed | Private proof import migrated and comparison applications renamed. |
| Sheaf.AlgebraicGeometry.FiniteConstructiblePushforwardVanishing | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.AlgebraicGeometry.FiniteEtalePushforwardConstructible | unclaimed | Private proof import migrated and comparison applications renamed. |
| Sheaf.AlgebraicGeometry.FiniteFinitePresentationPushforwardConstructible | unclaimed | Private proof import migrated and comparison applications renamed. |
| Sheaf.AlgebraicGeometry.FiniteMorphismsConstructible | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.AlgebraicGeometry.FiniteRadicialExchangeDescent | unclaimed | Private proof import migrated and comparison applications renamed. |
| Sheaf.AlgebraicGeometry.FiniteReflectsBoundedConstructible | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility | unclaimed | Private proof import migrated and comparison applications renamed. |
| Sheaf.AlgebraicGeometry.FiniteTypeSheafFiniteness | unclaimed | Private proof import migrated and comparison applications renamed. |
| Sheaf.AlgebraicGeometry.GoodCurvesPreimageConstructible | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.AlgebraicGeometry.NormalOpenLisseImage | unclaimed | Private proof import migrated and comparison applications renamed. |
| Sheaf.AlgebraicGeometry.OpenComplementKnown | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.AlgebraicGeometry.OpenDegreeZeroConstructible | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients | unclaimed | Private proof import migrated and comparison applications renamed. |
| Sheaf.AlgebraicGeometry.OpenImmersionHigherDirectImages | unclaimed | Private proof import migrated and comparison applications renamed. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibilityFromLine | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibleHigherDirectImages | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.AlgebraicGeometry.ProjectiveLineConstructible | unclaimed | Private proof import migrated and comparison applications renamed (on the current live text). |
| Sheaf.AlgebraicGeometry.ProperBoundedConstructible | unclaimed | Private proof import migrated and comparison applications renamed. |
| Sheaf.AlgebraicGeometry.ProperCaseConstructibility | unclaimed | Private proof import migrated and comparison applications renamed. |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.AlgebraicGeometry.ProperConstructibleHigherDirectImages | unclaimed | Private proof import migrated and comparison applications renamed. |
| Sheaf.AlgebraicGeometry.ProperDirectImageComparisonFinitude | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.AlgebraicGeometry.ProperFiniteTorAmplitude | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.AlgebraicGeometry.QuasiFiniteShriekConstructible | unclaimed | Private proof import migrated and comparison applications renamed. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.Paper.BoundedBelowCtfReflection | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.Paper.ComparisonTorAmplitude | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.Paper.DirectImageTorAmplitude | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.Paper.FiniteAffineDirectImageSupportBound | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.Paper.FiniteCoefficientDirectImage | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.Paper.FiniteCoefficientDualConstructible | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.Paper.FiniteCoefficientFlatModel | unclaimed | Private proof import and theorem name migrated; explicit cochain tensor structure and K-flat lemma applications avoid the observed reduction timeout. |
| Sheaf.Paper.IntegralOperationsPreserveConstructible | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.Paper.IntrinsicComparisonTorAmplitude | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.Paper.OpenComplementUnconditional | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.Paper.OpenExtensionFiniteTor | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.Paper.ProperOpenCoefficientMate | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.Paper.SfIntegralDirectImageConstructible | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.Paper.SmoothExceptionalPreservation | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.SixFunctors.AdmissibleDirectImage | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.SixFunctors.AdmissibleTensorConstructibility | unclaimed | No direct use of removed name or import; no edit needed. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekFiniteTypeDenseOpen | unclaimed | Quarantined; archive preserved. Restore with the canonical source import and comparison theorem name; identical statement and preserved DAG dependency. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | unclaimed | Quarantined; archive preserved. Restore with the canonical source import and comparison theorem name; identical statement and preserved DAG dependency. |
| Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness | unclaimed | Quarantined; archive preserved. Restore with the canonical source import and comparison theorem name; identical statement and preserved DAG dependency. |
| Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators | unclaimed | Quarantined per coord/rework.tsv; archive preserved. Its private comparison import and application in finiteRing_compactGenerators require the canonical source spelling on restoration. The replacement has the identical type, so compactness and the explicit generator family are unchanged; its DAG attachment and dependencies remain. |
| Sheaf.Paper.OrientedProperImageConstructibility | unclaimed | Quarantined; archive preserved. Restore with the canonical source import and comparison theorem name; identical statement and preserved DAG dependency. |

Quarantined consumers were also inspected. Their archives are not live Lean modules
and are left intact; their DAG dependencies continue to refer to the preserved node.
Their restoration must perform the same mechanical private-import/theorem rename
(the old spelling has an identical proved replacement, not missing mathematics):

- `quarantine/Sheaf/AlgebraicGeometry/EtaleAffineLineShriekFiniteTypeDenseOpen.lean`
- `quarantine/Sheaf/AlgebraicGeometry/EtaleAffineLineShriekSheafConstructible.lean`
- `quarantine/Sheaf/AlgebraicGeometry/EtaleProperDirectImageFiniteness.lean`
- `quarantine/Sheaf/AlgebraicGeometry/FiniteRingEtaleCompactGenerators.lean`
- `quarantine/Sheaf/Paper/OrientedProperImageConstructibility.lean`

This migration note preserves their obligation and their original archive. No archive
is deleted or replaced by an empty module. Retirement is justified by the actual
proved replacement above, not by the number of current importers.

Repair of the returned head `347e73b1f8`: the five quarantined users are now explicit
module rows in this `## Users` table, including `FiniteRingEtaleCompactGenerators`
named by the return. The previous archive-path list did not satisfy that table's
module coverage requirement. Current `tools/downstream.py --uses` still lists the
same 58 live downstream modules, all covered above. The retained 23 adapted files
were compared with the current shared sources; their differences remain the
documented migration and local proof elaboration repair.

Repair of returned head `dbbc27947d`: all 23 retained Lean files were compared
with the current shared sources and compiled successfully through `lcompile.py --all`
on the server. The canonical theorem's separate axiom probe reports exactly
`propext`, `Classical.choice`, and `Quot.sound`. The node copy was refreshed from
current sources while preserving only delivery-owned changes. The delivery tool
rebuilds the packet on freshly fetched `sheaf-dag`.

The reported landing failure read the absent live path of
`Sheaf.AlgebraicGeometry.FiniteTypeTorsionUniversalStar`. That module is quarantined
in `coord/rework.tsv`; its archive, Lean attachment and dependencies are preserved.
It is not a direct comparison consumer and requires no source edit for this retirement.
The current downstream checker checks that a live path exists before reading it.
No quarantined path has been added to `deleted.txt` or restored as an empty module.

## Status

landed 20261020T233120-L-895651 2026-10-20 (merge of deliver/D9/Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison)
