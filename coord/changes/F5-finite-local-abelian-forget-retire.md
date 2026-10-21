# AlgebraicGeometry.Scheme.finite_local_abelian_forget_iff

## Reason

Retire the duplicate Sheaf theorem in favor of its adopted, already proved upstream theorem.
This is the listed retirement in coord/retire-items.tsv. The old IsLisseEtaleSheafOfSets
predicate is an abbreviation for the upstream IsFiniteLocallyConstantSheafOfTypes predicate.
The hypotheses, universes, conclusion, and mathematical dependency route are unchanged.
The source-library tree is untouched. The DAG keeps the same node and dependency edges;
only its Lean attachment moves to the existing upstream theorem. This also serves parents
whose proof is unfinished and any archived parent: their dependency node still exists.

## Old

```lean
theorem finite_local_abelian_forget_iff {Y : Scheme.{u}}
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsLisseEtaleSheafOfSets
      ((sheafCompose Y.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G) ↔
    IsLocallyConstantSheaf G ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
        Finite (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj G)
```

## New

Use this existing declaration from
`WeilConjectures.AlgebraicGeometry.FiniteLocalAbelianForget`:

```lean
theorem finite_local_abelian_forget_iff {Y : Scheme.{u}}
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsFiniteLocallyConstantSheafOfTypes
      ((sheafCompose Y.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G) ↔
    IsLocallyConstantSheaf G ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
        Finite (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj G)
```

The duplicate module is withdrawn via deleted.txt. A compilation probe applies the upstream
theorem directly to the exact old signature, establishing definitional equality.
No target type or definition changes, so no target statement review is reopened.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FiniteLocalAbelianForget --uses
finite_local_abelian_forget_iff` lists the following 14 downstream modules. All six remaining direct
importers are migrated; five mention the theorem and TorsionFiniteSubsystem imports it for
proof dependencies. The downstream scan has no additional users outside these modules.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.ConstructibleCurveSubPart` | unclaimed | Transitive consumer; no source edit or statement change. |
| `Sheaf.AlgebraicGeometry.ConstructibleCurveSubQuotient` | unclaimed | Transitive consumer; no source edit or statement change. |
| `Sheaf.AlgebraicGeometry.ConstructibleIntegralCoefficientsBackward` | unclaimed | Replace its private proof import only; all declarations unchanged. |
| `Sheaf.AlgebraicGeometry.ConstructibleTorsionModulesAgree` | unclaimed | Replace its private proof import only; all declarations unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.FinitePushforwardAssertions` | unclaimed | Transitive consumer; no source edit or statement change. |
| `Sheaf.AlgebraicGeometry.Curve.FinitePushforwardCoefficientControl` | unclaimed | Transitive consumer; no source edit or statement change. |
| `Sheaf.AlgebraicGeometry.Curve.FinitePushforwardConstructibleDescent` | unclaimed | Transitive consumer; no source edit or statement change. |
| `Sheaf.AlgebraicGeometry.FrobeniusVectorBundleKernel` | unclaimed | Replace its private proof import only; all declarations unchanged. |
| `Sheaf.AlgebraicGeometry.LisseStratumInteriors` | unclaimed | Replace its private proof import only; all declarations unchanged. |
| `Sheaf.DeligneLaumon.TorsionFiniteSubsystem` | unclaimed | Migrate comparison import and remove unused route-pivot-dropped SetLocalSystemCalculus import; declaration and existing hole unchanged. |
| `Sheaf.Paper.EtaleLocalMonodromyRealization` | unclaimed | Transitive consumer; no source edit or statement change. |
| `Sheaf.Paper.EtaleLocalMonodromyRealizationBase` | unclaimed | Transitive consumer; no source edit or statement change. |
| `Sheaf.Paper.LatticeNormalizationRationalExact` | unclaimed | Replace its private proof import only; all declarations unchanged. |
| `Sheaf.Paper.NormalizedMonodromyExact` | unclaimed | Transitive consumer; no source edit or statement change. |

The first dry run refused the baseline SetLocalSystemCalculus import in
TorsionFiniteSubsystem because that module is on route-pivot-dropped-modules.txt.
It is not used by any declaration in the consumer, so its private import is removed.
This cleanup does not change the consumer theorem, its old hole, or its DAG proof plan;
the mathematical dependency is not claimed as eliminated.

## Returned packet repair

The current ProjectiveLineConstructible module already uses the adopted upstream
projective-line theorem and has no import of FiniteLocalAbelianForget. The stale sandbox
version is removed from the packet entirely; the current module is preserved verbatim.
The downstream list above was rerun against current source after this change.

Return C-73e81 (head 73e817eac) reported a landing failure while reading the unrelated
FlatConvolutionGradedIso module. The refreshed packet also preserves the current upstream
EtaleStratifiedFinite import in FrobeniusVectorBundleKernel, instead of restoring the stale
Sheaf import from the returned head. All consumer changes are reconciled against current
sheaf-dag before server compilation and redelivery.

## Status

landed 20261021T003506-L-1643472 2026-10-21 (merge of deliver/F5/Sheaf.AlgebraicGeometry.FiniteLocalAbelianForget)
