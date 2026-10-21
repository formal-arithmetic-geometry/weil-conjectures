# SfConstructibleCanonicalCompleteness public imports

## Reason

Complete the three existing proofs using the reviewed intrinsic-to-tower theorem
and the normalized Koszul/quotient comparison. Remove five unused direct public
imports. Three are already reexported by retained statement imports. The direct
completed-constant equivalence and Qbar pullback interfaces are unnecessary for
these statements and proofs. The latter imports a large unrelated coefficient
and six-functor interface.

All existing theorem signatures, universes, visibility and docstrings are unchanged.
There is no definition change and no new declaration. The four-step DAG proof is
implemented verbatim; the unit route and every stated proof dependency remain.
In particular, the completed-pullback dependency is still supplied by the retained
CompletedPullback module; no Qbar-valued pullback is used by this argument.

## Old

```lean
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.CompletedConstantCoefficientEquivalence
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.Paper.IntrinsicCompletion
public import Sheaf.Paper.WeilCompletedTensorReflector
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.Paper.CompletedPullback
import Sheaf.Paper.PbcIntrinsicTowerComplete
import Sheaf.Paper.CompletedKoszulQuotientComparison
```

## New

```lean
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.WeilCompletedTensorReflector
public import Sheaf.Paper.CompletedPullback
import Sheaf.Paper.PbcIntrinsicTowerComplete
import Sheaf.Paper.CompletedKoszulQuotientComparison
```

## Users

The read-only downstream query reports zero downstream modules. Its declaration
usage queries for all three theorem names report only this module. A direct search
for imports of this module also finds none. Unfinished DAG parents retain their
mathematical dependency on this node; its declarations and attachment are preserved.
No consumer needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SfConstructibleCanonicalCompleteness | G2 | Three proofs completed; imports trimmed. |

## Status

landed 20261021T130023-L-2494981 2026-10-21 (merge of deliver/G2/Sheaf.Paper.SfConstructibleCanonicalCompleteness)
