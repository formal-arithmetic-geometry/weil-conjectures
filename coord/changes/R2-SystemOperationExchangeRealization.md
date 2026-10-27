# WeilConjectures.FrobeniusExchange.systemOpenScalarInv_isIso

## Reason

Close the natural-transformation invertibility hole by reducing it to the
componentwise criterion. The component calculation is a strictly smaller named
obligation and remains available for a follow-up proof.

## New

`systemOpenScalarInv_isIso` now applies `NatIso.isIso_of_isIso_app` to
`systemOpenScalarInv_app_isIso`. The new component theorem has the same
open-immersion and coefficient hypotheses and asserts invertibility only at one
coefficient-sequence object.

## Users

No existing module is changed. The parent DAG node records the new proof
dependency and the new component node.

## Status

pending delivery
