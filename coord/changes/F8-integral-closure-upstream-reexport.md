# Retirement of IntegralClosureDedekindSurjectiveFibres

## Reason

The human's retirement hand-off of 2026-10-20 requires full withdrawal of the Sheaf
copy in favour of its official upstream twin. The earlier re-export packet is
superseded. The main theorem is already proved upstream; the one additional public
helper in the copy is used by a single remaining consumer and is private upstream.

## Old

The two remaining consumers import:

```lean
import Sheaf.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres
```

`Sheaf.RingTheory.FiniteAlgebraExtremallyDisconnected` calls:

```lean
  apply AlgebraicGeometry.finite_spec_residueFieldMap
```

The copy exports the same main theorem as the upstream twin and this additional helper:

```lean
theorem finite_spec_residueFieldMap {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (x : PrimeSpectrum S)
    (h : (Ideal.ResidueField.map (x.comap φ.hom).asIdeal x.asIdeal φ.hom rfl).Finite) :
    ((Spec.map φ).residueFieldMap x).hom.Finite
```

## New

Both remaining consumers import:

```lean
import WeilConjectures.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres
```

The helper's complete existing proof is moved into
`Sheaf.RingTheory.FiniteAlgebraExtremallyDisconnected` as a private helper with the
same type and short name; its single use becomes `apply finite_spec_residueFieldMap`.
No consumer public signature or definition changes. The Sheaf copy is withdrawn via
`deleted.txt`; node `lem-sc-integral-closure-dedekind-surjective-fibres` points at the
upstream main theorem with unchanged mathematical statement and proof dependencies.

## Users

The retirement instruction authorizes these consumer adaptations. Neither current
consumer has a module claim in the shared repository at the time of preparation.
Only the import and the private helper/call needed by full retirement are changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.FiniteAlgebraExtremallyDisconnected | unclaimed | Import twin; retain required helper privately; update its one call. Compiled in 6.3 s. |
| Sheaf.TraceFormula.CurveNormalizationCompletion | unclaimed | Import twin; unchanged theorem statement and proof. Compiled in 3.8 s. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | absent | Already removed from current sources; no adaptation. |
| Sheaf.RingTheory.SemilocalNormalizationDimOne | absent | Already removed from current sources; no adaptation. |

A whole-library search finds no further Lean references to the withdrawn module or
its public helper. Both adapted consumer import closures exclude the withdrawn copy
and contain no Sheaf/upstream twin pairs. No upstream file or target is changed.
No proof becomes sorry, no new sorry is added, and no definition is hollowed.

## Status

landed 20261020T144248-L-2259467 2026-10-20 (merge of deliver/F8/Sheaf.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres)
