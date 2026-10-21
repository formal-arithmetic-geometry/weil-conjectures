# BoundedConstructiblePullback restoration

## Reason

The assigned rework row records a cluster-restore removal of this source module.
Restore its complete archived implementation to its original library path. The archive
already contains complete proofs: its absence, rather than an unproved theorem, is the
assigned defect. The restored file compiles against the current dependencies in 11.9 seconds.
This is a source restoration, with zero proof holes closed or added.

## Old

The library path is absent. The exact previous implementation remains at
`quarantine/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/BoundedConstructiblePullback.lean`.
Its two identity-isomorphism signatures are:

```lean
noncomputable def boundedConstructibleUpperStarId :
    boundedConstructibleUpperStar Λ ℓ (𝟙 X) ≅ 𝟭 (Dᵇc(X.left)⟦Λ⟧) :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (boundedConstructibleUpperStarCompatibility Λ ℓ (𝟙 X) ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarId Λ X.left) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

noncomputable def boundedConstructibleLowerStarId [IsFinitenessCoefficient ℓ Λ] :
    boundedConstructibleLowerStar Λ ℓ (𝟙 X) ≅ 𝟭 (Dᵇc(X.left)⟦Λ⟧) :=
  conjugateIsoEquiv (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ (𝟙 X)) Adjunction.id
    (boundedConstructibleUpperStarId Λ ℓ X).symm
```

## New

Restore the entire archived file byte for byte at
`lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/BoundedConstructiblePullback.lean`.
The definitions above, every theorem signature and proof, both public imports and all
attributes are identical to the archive. No mathematical interface changes.

## Users

The downstream source scan finds these eight live consumers; none requires adaptation
because the restored API is the archived API. Three quarantined direct importers are
also included so that this restoration preserves their planned interface.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Restores imported identity API. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Preserves transitive API. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Restores identity components. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Preserves transitive API. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Preserves transitive API. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Restores cocycle and unit laws. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Restores associativity and unit laws. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Restores transport and commutation laws. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Quarantined; archived API preserved. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | Quarantined; archived API preserved. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed | Quarantined; archived API preserved. |

## Status

landed 20261021T014219-L-2388436 2026-10-21 (merge of deliver/F3/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback)
