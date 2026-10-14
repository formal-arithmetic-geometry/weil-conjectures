# cupCechResolution_beta_class_pairing

## Reason

The assigned module and its node are absent from the source checkout. The repair
record contains their previous complete interface. Restore that interface and use
the now-proved signed-axis pairing; its lightweight dependency repair has landed.
The original duplicate-instance batch failure no longer occurs in local compilation.

## Old

The module and node are absent. Their former public signature is recorded in
coord/repair-notes/Sheaf.Paper.CechCupResolutionBetaClassPairing.json.

## New

Restore the recorded public theorem without a signature or visibility change:

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

Preserve both recorded public imports. Use the proof-only import
Sheaf.Paper.CechCupSignedAxisPairing. Three proved private helpers supply
surjectivity of cycle classes, surjectivity of alpha classes, and the actual
paired cycle. The proof combines the two axis equations with the existing
IsModuleCupProduct characterization. No sorry or definition is added.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CechCupResolutionBetaClassPairing | P3 | Restore assigned theorem and prove it. |

A source search found no current importer of this absent module. No other module
is adapted. No target statement or definition changes.

## Status

landed 20261014T124243-L-2999273 2026-10-14 (merge of deliver/P3/Sheaf.Paper.CechCupResolutionBetaClassPairing)
