# AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_closedPoint_eq

## Reason

The human-approved retirement queue lists
`Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberBackward` as a zero-hole
retirement item. Its public theorem is used only by the singleton-fibre consumer.
The duplicate module is withdrawn, while the theorem is retained verbatim in that
consumer so all existing downstream statements and calls keep their signatures.
The adopted upstream twin uses the all-neighbourhood `strictLocalization` interface;
this is not definitionally the same interface as the small-model
`strictHenselizationScheme` used by the remaining Sheaf consumer, and importing both
would also duplicate `strictHenselizationStructuralMap_eq`. The consumer therefore
keeps the existing proof through the existing Sheaf functoriality theorem.

## Old

```lean
theorem strictHenselizationStructuralMap_closedPoint_eq
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω]
    [CommRing A] [IsLocalRing A]
    (s : Spec (.of Ω) ⟶ S) (e : Spec (.of A) ≅ strictHenselizationScheme s) :
    (e.hom ≫ strictHenselizationStructuralMap s) (IsLocalRing.closedPoint A) =
      s (IsLocalRing.closedPoint Ω)
```

The declaration was in
`Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberBackward`.

## New

The same declaration and proof are in
`Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiber`; only its private proof
import changes from the withdrawn module to
`Sheaf.Paper.StrictHenselizationFunctoriality`. The public theorem signature is
unchanged. The withdrawn file is listed in `deleted.txt`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiber | unclaimed | Retains the theorem in place and removes its import of the withdrawn module. |
| Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationCoreCompletion | unclaimed | Existing theorem call remains unchanged through the consumer. |
| Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationCoreData | unclaimed | Existing theorem call remains unchanged through the consumer. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux | unclaimed | Existing theorem call remains unchanged through the consumer. |
| Sheaf.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResidues | Q1 | Existing imports remain valid. |
| Sheaf.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResiduesCore | unclaimed | Existing imports remain valid. |
| Sheaf.AlgebraicGeometry.StrictHenselizationModuleFibreFactorization | unclaimed | Existing theorem call remains unchanged through the consumer. |

## Status

landed 20261020T162310-L-3588055 2026-10-20 (merge of deliver/J4/Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberBackward)
