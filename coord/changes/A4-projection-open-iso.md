# AlgebraicGeometry.ProEtale.CondensedRing.isIso_openImmersionProjectionComparison

## Reason

The open immersion projection comparison had an existing proof hole. This delivery closes
that hole by proving the underlying module extension-by-zero adjunction has invertible unit,
showing tensoring remains in the essential image, and transporting the comparison through
K-flat derived tensor resolutions. The proof requires local helper instances and a proof-only
import for the derived tensor API.

## Old

```lean
instance isIso_openImmersionProjectionComparison
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)))
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    IsIso (openImmersionProjectionComparison Λ j M N) :=
  sorry
```

## New

The declaration has the same signature and is proved by
`derivedOpenProjectionIsoAux Λ j M N`. Private helper lemmas establish the required
underived support and K-flat comparison facts.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Existing use remains valid; the instance is now proved. |
| WeilConjectures.PoincareDuality.Poincare | B3 | Existing use remains valid; no adaptation. |
| TargetsCheck | unclaimed | Existing interface remains valid; no adaptation. |

## Status

landed 20261017T201725-L-79673 2026-10-17 (merge of deliver/A4/WeilConjectures.PoincareDuality.ProjectionFormula)
