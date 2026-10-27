# nativeOpenTensor_ordinary_counit_isIso

## Reason

The target proof needs the localized projection-formula step as a named,
strictly simpler intermediate theorem. It records invertibility of the native
extension counit on the tensor object, from which essential-image membership is
obtained categorically.

## Old

No declaration existed.

## New

`nativeOpenTensor_ordinary_counit_isIso` states that the counit of
`moduleJAdj (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j`
at the ordinary tensor of the native extension of `M` with `N` is `IsIso`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CoefNativeOpenTensorOrdinarySupported | H9 | Uses the theorem to construct the essential-image witness. |

## Status

landed 20261027T234008-L-4159267 2026-10-27 (merge of deliver/H9/Sheaf.Paper.CoefNativeOpenTensorOrdinarySupported)
