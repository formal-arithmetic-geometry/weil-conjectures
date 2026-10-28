# WeilConjectures.RationalVerdier.datum_exists

## Reason

The previous `datum_naturality_of_kflat` statement asserted naturality for the input
`Datum` itself.  `SignedSymmetry.representative` constrains `swap` only on literal
K-flat representatives, so changing a non-K-flat component by an automorphism preserves
`hflat` and the stored fields while changing the asserted conclusion.  The theorem is
corrected to produce a replacement datum with the same ordinary tensor presentation and
with its dependent biduality isomorphism re-chosen for the transported swap.

## Old

The parent proof destructured `datum_naturality_of_kflat D ... A hflat` as a direct
naturality proof for `A`:

```lean
obtain ⟨A, hflat⟩ := datum_of_integral_kflat D l hl X E wE
  (integral_verdier_biduality D l hl E X wE.omega wE.reduction)
exact ⟨A, datum_naturality_of_kflat D l hl X E wE A hflat⟩
```

## New

The parent proof unpacks the corrected transport existential and returns the replacement:

```lean
obtain ⟨A, hflat⟩ := datum_of_integral_kflat D l hl X E wE
  (integral_verdier_biduality D l hl E X wE.omega wE.reduction)
obtain ⟨A', _, hnatural⟩ := datum_naturality_of_kflat D l hl X E wE A hflat
exact ⟨A', hnatural⟩
```

The public signature of `datum_exists` is unchanged.  The item node
`lem-coef-rational-verdier-datum-naturality` records the corrected statement.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.SixFunctors.RationalVerdierDatum` | B6 | Forced proof adaptation only: unpack `A'`, its ordinary equality, and its arbitrary-derived naturality. |

## Status

landed 20261028T055608-L-772182 2026-10-28 (merge of deliver/B2/Sheaf.SixFunctors.RationalVerdierDatumNaturality)
