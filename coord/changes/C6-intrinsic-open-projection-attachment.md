# C6: isolate the existing general open projection data

## Reason

`PurCompactSupport.openProjectionInverse_isIso` already states exactly the
componentwise invertibility needed to construct this item's normalized projection.
Its broad DAG owner `def-pur-integral-compact-support-coefficient-data` also depends
on Frobenius/convention data. Adding that owner as a proof dependency produced the
cycle

```
lem-fix-open-scalar-tensor-normalization
→ def-pur-integral-compact-support-coefficient-data
→ def-pur-conventions
→ lem-pur-twist-frobenius-scalar
→ def-weil-global-geometric-frobenius
→ def-weil-frobenius-cohomology-transport
→ def-weil-frobenius-square-exchange
→ def-weil-operation-exchange-coefficient-descent
→ lem-fix-operation-reduction
→ lem-fix-compact-support-coefficient-change
→ lem-fix-reduction-open-etale-origin
→ lem-fix-open-scalar-tensor-normalization
```

The general definitions and theorem have none of those hypotheses. This is a
DAG attachment repair; no Lean file, signature, proof, definition body, attribute
or public import of the existing source module is edited.

## Old

The broad existing definition node owns the following declarations alongside its
integral/completed coefficient data:

- `WeilConjectures.PurCompactSupport.Coefficients`
- `WeilConjectures.PurCompactSupport.openExtension`
- `WeilConjectures.PurCompactSupport.openAdjunction`
- `WeilConjectures.PurCompactSupport.pull`
- `WeilConjectures.PurCompactSupport.openDerivedAdjunction`
- `WeilConjectures.PurCompactSupport.openProjectionInverse`
- `WeilConjectures.PurCompactSupport.openProjectionInverse_isIso`

## New

The first six existing definitions belong to the narrower definition node
`def-sp-open-coefficient-adjunction-data`. The organizing coefficient record has
ring sheaves and specified inverse-image identifications only; it imposes no
composition axiom. The last existing theorem belongs to
`lem-sp-intrinsic-open-projection-invertible`, whose statement is its exact existing
signature, with unrestricted coefficient families and unbounded objects.
Both attachments are `existing: true` in the unchanged module
`Sheaf.Paper.IntegralCompactSupportCoefficientData`.

The broad node retains every other declaration. Its mathematical statement and
statement dependencies are unchanged. The original theorem's existing
docstring still cites the broad data node; this packet does not edit that source
module merely to change its blueprint tag. The new attachment records this fact.

No theorem is restated in Lean and no existing hole is copied. In particular,
this adds zero Lean holes. The main proof uses this existing theorem directly.

## Users

All current DAG consumers of the broad data node are listed below. Their Lean
imports and mathematical statements stay unchanged: the old node still supplies
all the same data transitively. Its dependency list remains verbatim; the narrower data record is used directly
by the newly attached projection theorem.
No library module is adapted and no group-held Lean file is touched.

- `def-per-adic-exceptional-context`
- `def-per-adic-exceptional-scalar-data`
- `def-sf-integral-system-canonical-bridge`
- `def-sf-integral-system-operations`
- `def-sf-open-reduction-coefficient-mate`
- `def-sf-pull-completion-comparison`
- `lem-per-adic-exceptional-projection`
- `lem-sf-constructible-exceptional-coefficient-coherence`
- `lem-sf-pf-open-factor-coherence`
- `sk-thm-sf-pf-proetale`

## Status

landed 20261021T154013-L-2748125 2026-10-21 (merge of deliver/C6/Sheaf.SixFunctors.OpenScalarTensorNormalization)
