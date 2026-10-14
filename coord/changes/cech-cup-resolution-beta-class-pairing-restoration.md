# cupCechResolution_beta_class_pairing

## Reason

The returned delivery reported a concurrent source change after its base. After the authorized
dry-run tool fetched the current branch, the item module and its node were absent. The live
server source read confirms the absence. Restore the previously reviewed interface unchanged
and prove its theorem from the signed-axis construction and explicit comparison glue. This
record makes the restoration visible to the independent reader; it is not a signature change.

## Old

No source module or declaration is present at the current fetched base
`24e53817915f203a97884f8c6ec998f44e30ae4c`.

## New

Restore `Sheaf.Paper.CechCupResolutionBetaClassPairing` with the reviewed declaration
`AlgebraicGeometry.Scheme.Modules.cupCechResolution_beta_class_pairing` and its original
signature below. Its public imports
remain `Sheaf.Paper.CechCupResolutionComparisonData` and `Sheaf.Paper.CechCupProduct`.
The proof-only import `Sheaf.Paper.CechCupSignedAxisPairing` supplies the named lower-level
signed-axis construction. Three private proved helpers and the main proof supply the cycle
lifting and comparison calculation. No definition or existing target statement changes.

```lean
theorem cupCechResolution_beta_class_pairing {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {F G : X.Modules} (D : CupResolutionPairing F G)
    (A : CupCechResolutionComparison U D.left)
    (B : CupCechResolutionComparison U D.right)
    (C : CupCechResolutionComparison U D.target) (p q : ℕ)
    (cup : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
        (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj
          (@id X.Modules (F ⊗ G)))
    (hcup : IsModuleCupProduct F G p q cup)
    (a : (((cechComplexFunctor U).obj F.presheafModuleCat).sc
      p).moduleCatLeftHomologyData.K)
    (b : (((cechComplexFunctor U).obj G.presheafModuleCat).sc
      q).moduleCatLeftHomologyData.K)
    (c : (((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).sc
      (p + q)).moduleCatLeftHomologyData.K)
    (hc : c.val = cechCupCochain U F G p q a.val b.val) :
    cup ((A.iso p).inv (HomologicalComplex.homologyMap A.beta p (cupCycleClass _ p a)))
      ((B.iso q).inv (HomologicalComplex.homologyMap B.beta q (cupCycleClass _ q b))) =
        (C.iso (p + q)).inv
          (HomologicalComplex.homologyMap C.beta (p + q) (cupCycleClass _ (p + q) c))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CechCupResolutionBetaClassPairing | S2 | Restore reviewed interface and prove its reduction. |
| Sheaf.Paper.CechCupSignedAxisPairing | new in this delivery | Supplies signed-axis construction without importing the item. |

A search of the current branch found no source importing the absent item module or using
its declaration. No other module requires adaptation. Its former downstream total-pairing
module is also absent from the current branch.

## Status

landed 20261014T013045-L-3417478 2026-10-14 (merge of deliver/S2/Sheaf.Paper.CechCupResolutionBetaClassPairing)
