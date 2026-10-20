# GaloisLisseCorrespondenceData local fibre transparency

## Reason

Compiling the original GaloisLisseCorrespondenceData against the repaired fibre functor
ended with `timeout after 60 s`. A diagnostic compile with the profiler and a lower
heartbeat bound showed repeated module and torsion-free instance inference in the large
correspondence conditions. Keep the rational fibre functor irreducible locally while
elaborating those conditions, and keep the already elaborated condition predicates
irreducible locally while elaborating the two correspondence records. Its object equations already occur explicitly wherever
needed; no data construction, predicate, field or public signature changes.

The final adapted check, including compiled artifact emission, passed cleanly in 38.5 seconds. The diagnostic
options are not in the delivery. Integral and point fibre definitions retain their
original local transparency because their evaluation predicates use their definitional
projection and germ identifications. These are local transparency attributes, not a file
split or a raised compile limit. This module was unclaimed when adapted.

## Old

```lean
namespace AlgebraicGeometry.Scheme
```

## New

```lean
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] lisseRationalFiberFunctor

attribute [local irreducible] galoisYonedaComparison
  galoisFiniteEtaleAction galoisFiniteAbelian galoisFiniteKernels galoisFiniteCokernels
  galoisFiniteLimits galoisFiniteColimits galoisFiniteUnit galoisFiniteEvaluationAction
  galoisFiniteTensor galoisFiniteScalarExtension

attribute [local irreducible] galoisRationalSheavesAbelian
  galoisRationalRepresentationsAbelian galoisRationalFiniteLimits galoisRationalFiniteColimits
  galoisAlgebraicSheavesAbelian galoisAlgebraicRepresentationsAbelian
  galoisAlgebraicFiniteLimits galoisAlgebraicFiniteColimits galoisIntegralEvaluationAction
  galoisRationalEvaluationAction galoisIntegralMonoidal galoisRationalMonoidal
  galoisAlgebraicMonoidal galoisIntegralTensor galoisIntegralUnit galoisRationalTensor
  galoisRationalUnit galoisAlgebraicTensor galoisAlgebraicUnit
  galoisAlgebraicModelScalarExtension galoisIntegralScalarExtension
  galoisRationalScalarExtension
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.GaloisLisseCorrespondenceData | unclaimed | Local transparency attributes only; every existing declaration and body stays verbatim. Compiles cleanly against the repaired fibre functor. |

The attributes are local and change neither exported reducibility nor any downstream
signature or definition, so no downstream adaptation or new mathematical node is needed.
The algebraic-functor semantic review is reopened separately in
E5-canonical-algebraic-fibre-functor.md.

## Status

landed 20261020T230733-L-606316 2026-10-20 (merge of deliver/E5/Sheaf.Paper.FibreFunctorBasepointTransport)
