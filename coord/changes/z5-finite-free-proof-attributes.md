# finiteFreeConstructibleScalarTransport proof elaboration attributes

## Reason

The proof fixes the coefficient universe and uses bounded site-flatness, actual scalar
adjunctions, and their normalized sections. The static preflight treats new attribute
commands, including local reducibility commands, as an importer-visible change. This
record covers them; all public declaration signatures and definitions are unchanged.

## Old

```
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
```

## New

```
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
```

Additionally, the proof locally marks `balanceIso`, `finiteFreeConstantTensor`, and
`pbcTensorSection` irreducible while checking the normalization on arbitrary pro-etale
objects. This local attribute does not escape the module. Three private local instances
fix essential smallness and additive sheafification at the original coefficient size.
They expose no new names or signatures to importers.

The removed generic instance is replaced during this proof by the existing canonical
fixed-universe instances. This is the same elaboration discipline already used by
`StrictPerfectCoefficientPackageOfUniverses`, the former proof import. It prevents
underdetermined max-universe constraints; no mathematical coefficient construction changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteFreeConstructibleScalarTransport | Z5 | Proves both original holes; private proof helpers and elaboration attributes. |
| Sheaf.Paper.PerAdicCommonStageTruncations | unclaimed | No signature or definition change; no source adaptation. |

`tools/downstream.py Sheaf.Paper.FiniteFreeConstructibleScalarTransport` lists the single
downstream module above. No module held by another group is adapted.

## Status

landed 20261021T144030-L-38746 2026-10-21 (merge of deliver/Z5/Sheaf.Paper.FiniteFreeConstructibleScalarTransport)
