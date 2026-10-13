# picardScalarCech_externalCup_core

## Reason
The core declaration previously omitted the cover equalities required by the
natural-degree comparison theorem. This made the declared core statement stronger
than the supported route and prevented the wrapper from applying the final theorem.
The cover hypotheses are restored and the proof now applies the final theorem pointwise.

## Old
The core theorem had arguments `U`, `V` followed immediately by `c`, with no
hypotheses `iSup U = ⊤` or `iSup V = ⊤`.

## New
The core theorem has arguments `U`, `V`, `(hUc : iSup U = ⊤)`, and
`(hVc : iSup V = ⊤)` before `c`; its cycle compatibility conclusion is unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup | R1 | wrapper proof supplies the restored cover hypotheses |

## Status

landed 20261013T234518-L-2165947 2026-10-13 (merge of deliver/R1/Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup)
