# SheafOfModules.inverseImage_underlying_of_ring_presentation

## Reason

Transporting scalar graphs needs a module comparison compatible with the actual
module-pullback unit. A bare `Nonempty` isomorphism does not supply this fact.
The existing construction already restricts the abelian adjunction to linear maps;
retain its unit equation, then apply the unit equation for `leftAdjointUniq`.
This strengthens a proved theorem under identical assumptions, with no new hole.
The private helper `inverseImage_underlying_of_actions` retains the same unit equation
in its conclusion so that the public theorem can expose it; it is fully proved.
Both edited existing modules were unclaimed at preparation time. No target statement,
public definition, or meaning of a downstream statement changes.

The generic proof no longer needs its three file-wide backward-elaboration options.
The scalar graph proof treats `proEtaleModelRingUnit` and `SheafOfModules.pullback`
as locally irreducible and uses their unit APIs. This avoids repeatedly unfolding
large chosen adjunction terms. All modules remain individually below the 60 s limit.

## Old

```lean
theorem inverseImage_underlying_of_ring_presentation
    [RepresentablyFlat F] [PreservesFiniteLimits (sheafPullback F (Type u) J K)]
    (pr : SheafPullbackUnitPresentation (F := F)
      ((sheafCompose J (CategoryTheory.forget RingCat.{u})).obj A)
      ((sheafCompose K (CategoryTheory.forget RingCat.{u})).obj B))
    (hr : pr.unit = (sheafCompose J (CategoryTheory.forget RingCat.{u})).map φ) :
    Nonempty (pullback.{u} φ ⋙ toSheaf B ≅
      toSheaf A ⋙ sheafPullback F AddCommGrpCat.{u} J K)
```

## New

```lean
theorem inverseImage_underlying_of_ring_presentation
    [RepresentablyFlat F] [PreservesFiniteLimits (sheafPullback F (Type u) J K)]
    (pr : SheafPullbackUnitPresentation (F := F)
      ((sheafCompose J (CategoryTheory.forget RingCat.{u})).obj A)
      ((sheafCompose K (CategoryTheory.forget RingCat.{u})).obj B))
    (hr : pr.unit = (sheafCompose J (CategoryTheory.forget RingCat.{u})).map φ) :
    ∃ e : pullback.{u} φ ⋙ toSheaf B ≅
      toSheaf A ⋙ sheafPullback F AddCommGrpCat.{u} J K,
      ∀ M : SheafOfModules.{u} A,
        (toSheaf A).map ((pullbackPushforwardAdjunction φ).unit.app M) ≫
          (F.sheafPushforwardContinuous AddCommGrpCat.{u} J K).map (e.hom.app M) =
            (sheafAdjunctionContinuous F AddCommGrpCat.{u} J K).unit.app
              ((toSheaf A).obj M)
```

The private helper `SheafOfModules.inverseImage_underlying_of_actions` was also
strengthened from its old conclusion

```lean
Nonempty (pullback.{u} φ ⋙ toSheaf B ≅
  toSheaf A ⋙ sheafPullback F AddCommGrpCat.{u} J K)
```

to the corresponding existential comparison together with the normalized
adjunction-unit equation.  It is private, but the change is recorded here because
the delivery checker reports all changed declaration statements.

`Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying` changes only its last
proof step: destruct the new existential as `⟨e, _⟩`, then return `⟨e⟩` to its original
`Nonempty` conclusion. Its signature and public imports remain identical.

## Users

The declaration-name scan finds only the generic module itself and the adapted
underlying-comparison module. All transitive users reported by `tools/downstream.py`
are listed below. The original statements of all these modules retain their meaning;
no definition or instance is changed. The new scalar-graph module uses the added
normalization directly. Holders are a preparation-time snapshot.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph` | D2 (new) | Uses the normalized unit equation to prove scalar-action compatibility. |
| `Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageComparison` | D2 (new) | Uses the proved scalar graph through its proof-only import. |
| `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation` | D2 | Uses the proved comparison; its original statement is unchanged. |
| `Sheaf.CategoryTheory.ModuleInverseImageAdjunction` | unclaimed | Strengthened normalized unit comparison; same assumptions; fully proved. |
| `Sheaf.AlgebraicGeometry.NoetherianStratumDetection` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleModuleCohomologyCoproducts` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying` | unclaimed | Proof obtains the comparison and discards normalization; existing signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleOperations` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleRingedClosedCounit` | G4 | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleRingedLocalizationSequence` | H1 | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.Paper.CondensedCoefficientComparisons` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.Paper.CondensedFinitePresentationDescent` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | G2 | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.Paper.CondensedLocalPieceHomContinuity` | H3 | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.Paper.CondensedQbarComparisons` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.Paper.CondensedQbarExchangeEquality` | A3 | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.Paper.CondensedQcqsPushforwardContinuity` | D4 | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.Paper.CondensedSheafExtContinuity` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.Paper.CondensedStratumModelAssembly` | XR1b27919aec52b018 | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.Paper.ContinuousExchangeIntegralModel` | A2 | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.Paper.FiniteCtfTriangulated` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.Paper.FiniteRingConstructibleSheafOrigin` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.Paper.FiniteTensorConstructibleCohomology` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.Paper.FiniteTorsionConstructibility` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.Paper.ProEtaleConstructibleSheaf` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.Paper.ProEtaleResidueTorTest` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `TargetsCheck` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | unclaimed | No direct use of changed declaration; all existing statements and definitions unchanged. |

## Status

landed 20261015T233748-L-3369032 2026-10-15 (merge of deliver/D2/Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation)
