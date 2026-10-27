## What changed

Proved `nativeOpenTensor_finite_exists` by constructing the native finite-stage ordinary and
cochain datum. The existing unique native pullback tensor comparison supplies its exact
pure-section normalization and naturality. Ringed-topos pullback preservation supplies both
K-flatness and flat terms. The extension unit is invertible, and tensor closure of its essential
image makes the counit on the tensor invertible; hence the specified unit transpose is an
isomorphism. The proved generic totalization helper supplies the chain comparison, its summand
formula, and naturality. The public statement of the assigned theorem is unchanged.

Added the proved helper `nativeFiniteTensor_mem_essImage`: transport the existing slice tensor
formula through the native open slice presentation. Its witness is the inverse equivalence
applied to the concrete sheafified slice tensor. No tensor compatibility of that equivalence is
assumed. All geometric arguments include the empty open, zero modules, and the positive quotient
indexed by n=0. There are no changes to existing shared definitions or other existing modules.

## Proved and sorry left

Closed one original hole: `WeilConjectures.CoefSupportOpenTensor.nativeOpenTensor_finite_exists`.
Added no holes and split off no unfinished statements.

The new helper `WeilConjectures.CoefSupportOpenTensor.nativeFiniteTensor_mem_essImage` is proved.
There are zero remaining `sorry`s in both delivered modules. Existing imported declarations are
used as stated.

## No longer needed

No existing import was removed: the assigned module initially had only its public primitives
import. No existing module is withdrawn or claimed globally pruned.

The planned direct dependency `lem-sf-open-tensor-normalization`
(`Sheaf.SixFunctors.OpenTensorNormalization`) is unnecessary for this proof: invertibility of the
unit transpose follows from full faithfulness and tensor support, without a derived
normalization package. The planned weakly-etale localization and localized-module exactness
nodes are used through the existing native slice presentation and totalization helpers, so
these underlying results remain needed. The ringed-slice tensor formula and total-tensor
helpers remain needed as well. The node records the actual proof dependencies.

## Where the brief, the DAG or earlier work was wrong

No statement repair or weakening was needed. The existing
`proEtaleOrdinaryTensorPullback_existsUnique` already gives the exact native restriction tensor
comparison and section formula required by `finitePullSection`. A new restriction-comparison
obligation is therefore unnecessary. The ordinary inverse can be proved invertible by the
smaller essential-image argument; there is no need to identify it with a separately normalized
slice projection map. Its specified adjunct and all naturality equations are nevertheless
proved exactly as stated.

## New nodes

`lem-coef-native-finite-tensor-support`, realized by
`WeilConjectures.CoefSupportOpenTensor.nativeFiniteTensor_mem_essImage` in module
`Sheaf.Paper.CoefNativeFiniteTensorSupport`, is a proved ordinary support lemma. It uses the existing
native open slice presentation and ringed-slice tensor formula, adds no `sorry`, and asserts no
cochain or K-flat data. Searches and the source proof are recorded in its node and docstring.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CoefNativeFiniteTensorSupport": "8ecae7eee5379bd67ee3377b1485c02a7e3f21e5", "Sheaf.Paper.CoefNativeOpenTensorFiniteExistence": "7c6a0d776745e9a28b0396f31579cbbf71ad66fd"}, "results": {"Sheaf.Paper.CoefNativeOpenTensorCochains": {"hash": "24883058d4c98279a981a16746182cd98d71edaa", "status": "OK"}}, "seconds": 138, "time": "2026-10-28T03:43:06+0800", "transitive": 0, "version": 1}
```

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
