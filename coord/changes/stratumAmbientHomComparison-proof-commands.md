# AlgebraicGeometry.ProEtale.stratumAmbientHomComparison

## Reason

The proof needs additional namespace openings and two elaboration transparency options.
Preflight classifies these file-level commands as an interface change and requires this
record. They control name resolution and elaboration within this module. The existing
public theorem signature and all four public imports remain verbatim; every helper is
private and proved, and the additional proof imports use `import` or `import all`.
No public definition, instance, notation or attribute is added. No target meaning changes.

## Old

```lean
set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped CategoryTheory.Functor
```

The old theorem signature is:

```lean
theorem stratumAmbientHomComparison
    (A : Type u) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} [IsNoetherian X]
    (i : S ⟶ U) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] :
    ∃ α :
      ((((sfConstantModuleDirectImage i A).rightDerivedFunctor ⋙
          (sfIntrinsicExtensionByZero j A).mapDerivedCategory).op.prod
          (𝟭 (proEtaleDerivedCategory X A))) ⋙
          derivedInternalHomOfUniverses.{u + 1, u, u}
            (ProEt.topology X) (proEtaleConstantRing X A)) ⟶
        (((𝟭 (proEtaleDerivedCategory S A)ᵒᵖ).prod
          ((sfConstantModulePullback j A).mapDerivedCategory ⋙
            (sfIntrinsicClosedUpperShriek i
              (Scheme.Opens.ι (X := U) (⟨(Set.range i)ᶜ,
                (IsClosedImmersion.isClosedEmbedding i).isClosed_range.isOpen_compl⟩ :
                  U.Opens)) A).rightDerivedFunctor)) ⋙
          derivedInternalHomOfUniverses.{u + 1, u, u}
            (ProEt.topology S) (proEtaleConstantRing S A) ⋙
            (sfConstantModuleDirectImage (i ≫ j) A).rightDerivedFunctor),
      ∀ p, IsIso (α.app p)
```

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
open scoped CategoryTheory.Functor
```

The new theorem signature is verbatim the signature in Old. Its proof now composes
proved support projection formulas with the existing tensor-Hom adjunctions.
The file compiles in 26.5 seconds through the required server compile interface.

## Users

`tools/downstream.py Sheaf.Paper.StratumAmbientProjectionData --uses
AlgebraicGeometry.ProEtale.stratumAmbientHomComparison` lists 21 downstream modules
and identifies the parent and item as the two textual users. All are recorded below.
No consumer needs adaptation; the existing theorem type and visibility are preserved.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed | unclaimed | Transitive consumer: unchanged theorem type; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Transitive consumer: unchanged theorem type; no adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Transitive consumer: unchanged theorem type; no adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Transitive consumer: unchanged theorem type; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Transitive consumer: unchanged theorem type; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDualConstructible | unclaimed | Transitive consumer: unchanged theorem type; no adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Transitive consumer: unchanged theorem type; no adaptation. |
| Sheaf.Paper.FiniteFieldHomEtaleWitness | unclaimed | Transitive consumer: unchanged theorem type; no adaptation. |
| Sheaf.Paper.FiniteFieldInternalHomFiniteness | unclaimed | Transitive consumer: unchanged theorem type; no adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Transitive consumer: unchanged theorem type; no adaptation. |
| Sheaf.Paper.IntegralAdicHomResidueOrigin | unclaimed | Transitive consumer: unchanged theorem type; no adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Transitive consumer: unchanged theorem type; no adaptation. |
| Sheaf.Paper.IntegralGeneralLfpHomFiniteness | unclaimed | Transitive consumer: unchanged theorem type; no adaptation. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Transitive consumer: unchanged theorem type; no adaptation. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Transitive consumer: unchanged theorem type; no adaptation. |
| Sheaf.Paper.ResidueControlledFiniteHoms | unclaimed | Transitive consumer: unchanged theorem type; no adaptation. |
| Sheaf.Paper.StratumAmbientHom | unclaimed | Direct consumer: unchanged theorem type; no adaptation. |
| Sheaf.Paper.WeilInternalHomWeil | unclaimed | Transitive consumer: unchanged theorem type; no adaptation. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Transitive consumer: unchanged theorem type; no adaptation. |
| Sheaf.SixFunctors.CoefDualizingSiteMates | unclaimed | Transitive consumer: unchanged theorem type; no adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Transitive consumer: unchanged theorem type; no adaptation. |
| Sheaf.Paper.StratumAmbientProjectionData | M8 | Item: fill its proof; preserve its signature and public imports. |

## Status

landed 20261023T135051-L-2830910 2026-10-23 (merge of deliver/M8/Sheaf.Paper.StratumAmbientProjectionData)
