## What changed

Delivered a partial proof and definition interface repairs. The generic calculation
`CategoryTheory.residueTensorRoute_generic` and ordinary pullback braiding
`AlgebraicGeometry.ProEtale.CondensedRing.residueOrdinaryPullBraid` are fully proved in the
item. The former computes the canonical tensor presentation using counit normalization,
comparison naturality, the derived tensor-comparison counit equation, ordinary homotopy
braiding, cancellation and counit naturality. No coefficient flatness is assumed.

Cached the existing generic and typed derived monoidal constructions, ordinary transported
monoidal construction, and tensor-model target, with their construction bodies unchanged.
Proved their defining equations. Existing signatures and visibility are unchanged. This is
a real definition interface repair; target definition review is reopened to verify unchanged
data. Records: `coord/changes/A4-residue-derived-monoidal-cache.md`,
`coord/changes/A4-residue-ordinary-monoidal-cache.md`,
`coord/changes/A4-residue-tensor-target-cache.md`.

## Proved and sorry left

Original holes closed: 0 of 1. New holes added: 0. Split off: 0.
The sole remaining hole is the unchanged original theorem
`AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_tensorRoute_model`
(node `new-integral-residue-tensor-route-model`). Its concrete typed scalar-counit and
presentation identifications remain to be connected to the proved generic calculation.
All delivered supporting definitions have explicit data, and all new supporting theorems
and both calculation theorems are proved. No new axiom is introduced.

## No longer needed

Removed the redundant direct import `Sheaf.Paper.IntegralResidueTensorPresentation`.
No baseline module or node is withdrawn; no pruning gain is claimed.

Use the existing source-library homotopy braiding comparison directly. The attempted
relocation and the draft concrete interface split-offs are not delivered. Their files never
landed and are absent from the delivery. Importing the existing source module adds its
previously unreached geometry dependencies; this is not claimed as progress or pruning.

## Where the brief, the DAG or earlier work was wrong

The generic calculation does not need a separate derived braided-functor descent: ordinary
homotopy braiding and the Qh braiding identity suffice. No unit-level route is bypassed.

The concrete specialization repeatedly exceeded the 60-second limit when comparing the
internal-module monoidal data, including after the generic calculation was complete. The
original hole is retained honestly rather than claiming a completed specialization. No
compilation time limit was raised. The partial delivery includes the fully proved calculation
and substantial cached-definition APIs, rather than a no-op or a rebase.

The original TensorModel and ProjectionNormalization consumers compiled unchanged against
the repaired derived overlay. ScalarGeometryBridge, ScalarRouteModel, TensorGeometry and
TensorSquare also compiled unchanged. Final delivery checks validate the delivered overlay.
Single-file lcompile checks do not refresh sandbox artifacts; import-order checks are needed.

## New nodes

`new-homotopy-functor-braiding` attaches the already proved generic complex/homotopy braiding
comparisons in their existing source-library module. No declarations are moved or duplicated.

`new-integral-residue-tensor-route-calculation` records the complete generic tensor-route
calculation and ordinary pullback braiding in the item. Both declarations are fully proved;
no hole is moved into this node.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
