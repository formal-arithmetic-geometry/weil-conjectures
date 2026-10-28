# WeilConjectures.IntegralFiniteExtension.finiteU_isIso

## Reason

Restore the source coefficient hypothesis `l ≠ D.p`. The former section variable
`hl` was unused in the conclusion and silently omitted from the theorem's Lean
signature. The blueprint's purity coefficient conventions fix `l ≠ p`; both
finite-free coefficient extension and finite dualizing quotient comparison require
it. This does not assert the old unrestricted theorem is false: that stronger
statement is not proved here. The correction and the affine reduction are separate
parts of this packet. No target or definition changes.

## Old

```lean
theorem finiteU_isIso (n : ℕ) :
    IsIso (finiteU l E L ι X D n)
```

## New

```lean
theorem finiteU_isIso (hl : l ≠ D.p) (n : ℕ) :
    IsIso (finiteU l E L ι X D n)
```

## Users

`tools/downstream.py` found 515 downstream modules, of which exactly the following
two mention the changed name. The sole direct importer is the second row.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionFiniteUIsInvertible | J8 | Own intermediate statement corrected to the source coefficient conventions. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionUReductionIsInvertible | unclaimed | Proof-only forced adaptation: pass existing `hl` before `n`; signature and visibility stay identical. |

The original caller fails at line 46: `n : ℕ` is supplied where `l ≠ D.p` is
expected. The adapted line is `haveI : IsIso v := finiteU_isIso l E L ι X D hl n`.
The parent DAG use still holds, since its dualizing data already require `hl`.
The target statements and the meanings of their definitions stay unchanged.

## Status

landed 20261028T072425-L-1945387 2026-10-28 (merge of deliver/J8/Sheaf.SixFunctors.CoefIntegralFiniteExtensionFiniteUIsInvertible)
