# CategoryTheory.Functor.exactAdjointForgetDerivedDetection

## Reason

The exact termwise derived functor and K-injective preservation in this theorem do not use
right derived functors constructed from quasi-isomorphism resolutions. Remove the unused
public import to prune this dependency. The theorem signature and all definitions stay identical.
The private compositor-coherence import is also unnecessary: the normalized comparison and
its representative formula are already proved in the imported upstream ExactFunctor module.

## Old

```lean
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
```

## New

The unused import is removed. Every other public import and the complete theorem signature
are preserved. No declaration is added, removed, or restated.

## Users

`python3 tools/downstream.py Sheaf.CategoryTheory.ExactAdjointForgetDerivedDetection
--uses exactAdjointForgetDerivedDetection` reports no importers; its sole declaration-name hit is this module itself.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.ExactAdjointForgetDerivedDetection | H1 | Proof completed; unused import removed. |

The DAG parents still need this theorem; none is withdrawn or bypassed. No consumer adaptation
or target-statement review is required, since no statement or definition changes.

## Status

landed 20261024T185905-L-3751706 2026-10-24 (merge of deliver/H1/Sheaf.CategoryTheory.ExactAdjointForgetDerivedDetection)
