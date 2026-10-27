# finiteFreeQuotientRoosComparison

## Reason

Repair red-build return ef5b5e60103800ab (H8 landing de116fdce4).
Restore its complete finite-power/cokernel/Roos proof, but remove the private
import of `Sheaf.Paper.CompletedIntegralPrincipalUnitCriterion`. That implementation
and its transitive dependencies remove sheafification and tensor instances globally,
which broke typeclass search in `WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights`.
Prove the two small required tensor identities privately from their existing
sheafification and single-tensor APIs. Keep the concrete monoidal and Roos constructions behind local reducibility
interfaces. The theorem statement respects those interfaces; its proof uses
explicit functor-composition conversions in the final structure assembly.
No instance is added or removed by this module.

No public declaration, public import, target statement, or definition is changed.
All helpers are private and proved or concretely constructed. The existing
local transparency hints keep the concrete tensor and cone definitions behind
typed interfaces.

## Old

```lean
theorem finiteFreeQuotientRoosComparison
    (F : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
    (hfree : ∃ d : ℕ, Nonempty
      ((SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)).obj
          (SheafOfModules.unit (SheafOfModules.derivedChangeRingIndependentCoefficients J S)) ≅
        ∐ (fun _ : Fin d ↦ SheafOfModules.unit
          (SheafOfModules.derivedChangeRingIndependentCoefficients J R))))
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (vS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections)
    (uS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections)
    (hu : ∀ U : Cᵒᵖ, IsUnit (@id (S.obj.obj U) (uS.val U)))
    (e : ℕ) (he : 1 ≤ e)
    (hrelation : ∀ U : Cᵒᵖ,
      φ.hom.app U (@id (R.obj.obj U) (t.val U)) =
        (@id (S.obj.obj U) (uS.val U)) * (@id (S.obj.obj U) (vS.val U)) ^ e)
    [HasExactLimitsOfShape (Discrete ℕ)
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J S))] :
    Nonempty (QuotientRoosExchange F t vS e)
```

The body was `by sorry`.

## New

```lean
theorem finiteFreeQuotientRoosComparison
    (F : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
    (hfree : ∃ d : ℕ, Nonempty
      ((SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)).obj
          (SheafOfModules.unit (SheafOfModules.derivedChangeRingIndependentCoefficients J S)) ≅
        ∐ (fun _ : Fin d ↦ SheafOfModules.unit
          (SheafOfModules.derivedChangeRingIndependentCoefficients J R))))
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (vS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections)
    (uS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections)
    (hu : ∀ U : Cᵒᵖ, IsUnit (@id (S.obj.obj U) (uS.val U)))
    (e : ℕ) (he : 1 ≤ e)
    (hrelation : ∀ U : Cᵒᵖ,
      φ.hom.app U (@id (R.obj.obj U) (t.val U)) =
        (@id (S.obj.obj U) (uS.val U)) * (@id (S.obj.obj U) (vS.val U)) ^ e)
    [HasExactLimitsOfShape (Discrete ℕ)
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J S))] :
    Nonempty (QuotientRoosExchange F t vS e)
```

The body constructs all fields of `QuotientRoosExchange` using finite free scalar
exactness and product preservation, balanced cokernel isomorphisms, the actual
additive Roos comparison, and the cofinal arithmetic restriction quasi-isomorphism.
The existing structure remains verbatim. The two formerly imported identities
are proved as private `regularTensorIso_eq` and `single_tensor_quotient_component`.
All new reducibility attributes are local. There are no instance removals or
added public attributes. No tensor definitions are changed.

## Users

Declaration consumers returned by `tools/downstream.py --uses` and the historical
failing consumer, rechecked against the refreshed source tree:

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Algebra.Homology.FiniteFreeCompletionExchange` | unclaimed | Public declarations unchanged; no adaptation. |
| `Sheaf.Algebra.Homology.FiniteFreeQuotientRoosComparison` | D3 | Assigned proof restored and import regression repaired. |
| `Sheaf.Paper.FiniteFreeCompletedScalarComparison` | unclaimed | Public declarations unchanged; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights` | unclaimed | Historical failing consumer, now restored upstream; no adaptation. |

Textual declaration users are `FiniteFreeCompletionExchange` and
`FiniteFreeCompletedScalarComparison`, plus the item itself. No consumer adaptation
is required because public signatures and definitions are unchanged.

## Status

landed 20261024T184819-L-3199220 2026-10-24 (merge of deliver/D3/Sheaf.Algebra.Homology.FiniteFreeQuotientRoosComparison)
