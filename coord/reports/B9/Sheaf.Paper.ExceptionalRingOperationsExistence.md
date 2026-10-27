## What changed

Proved `WeilConjectures.ConstructibleExceptionalCoefficients.exists_exceptional_ring_operations`
in `Sheaf.Paper.ExceptionalRingOperationsExistence` without changing its statement.
At finite stages, package `exists_sfFiniteExceptionalOperations` and compose its actual
left inclusion equality with `PurCompactSupport.finiteImageIso`. At integral stages,
use the already stated `exists_integral_support_adjoint` for the literal restricted
compact-support functor, lift its shift and exactness through the full faithful
inclusion, and obtain the right shift, exactness and unit/counit compatibility from
the adjunction. Assemble the dependent families by cases on `RingStage`.
Two proved private helpers keep composition shift structures explicit.
The existing existential binder `left` is retained verbatim; its unused-binder
linter is disabled only for this theorem. No signature or instance attribute changes.
Added private proof imports of `ExceptionalFiniteOperations`,
`ExceptionalIntegralSupportAdjoint`, and Mathlib's triangulated subcategory API.
Updated the item's node proof, proof dependencies, and proof origin to this route.
No other existing module or node is changed.

## Proved and sorry left

Closed 1 existing hole:
`WeilConjectures.ConstructibleExceptionalCoefficients.exists_exceptional_ring_operations`
(node `lem-sf-exceptional-ring-operations-existence`).
Added 0 holes; 0 holes remain in the delivered module. Both private helpers are proved.
This is a proof from existing declarations, including the named preservation and
adjunction statements below `exists_integral_support_adjoint`; those dependencies
remain separate project obligations and are not claimed to be sorry-free.

The theorem retains every hypothesis and its universe parameters. Its finite case
excludes exponent zero and includes exponent one; the existing constructors cover
empty schemes without adding any nonemptiness or absolute separatedness assumption.

## No longer needed

No existing imports removed and no modules withdrawn. The original public import
`ExceptionalIntegralScalarMates` still supplies the statement API and the inherited
inclusion shift used by this proof.
The item's direct proof no longer uses `lem-sf-exceptional-system-transport`
(`Sheaf.Paper.ExceptionalSystemTransport`) or
`lem-pur-normalized-reconstruction-adjunction-calculus`
(`Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`). The preexisting
integral restricted-adjoint result already isolates the required system argument.
These two direct proof dependencies are replaced in the node, but their modules
remain available through the preexisting public imports and are not claimed to
leave the targets' closure. No blueprint unit or unit-level proof step is bypassed.
No scalar mates, coefficient-change comparisons, rational stages, closed stages, or
refinement assembly theorem is used to construct the families.

## Where the brief, the DAG or earlier work was wrong

The plan asked this module to reconstruct the integral system adjunction again,
but `ExceptionalIntegralSupportAdjoint.exists_integral_support_adjoint` already
provides exactly the preservation and adjoint-existence input needed here.
The stronger `ExceptionalRingStageAssembly` also has analogous proved local
constructions, but importing it would create a cycle through this item; this
proof instead uses its acyclic inputs directly and supplies only the required
operation and ambient realization fields. No new intermediate statement is needed.
The current server queue lists this as a one-hole proof item, with no rework row,
return, or build-error file for the item.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalRingOperationsExistence": "12b6f37c3f38af79a030a433dc2ffb6b444cf31b"}, "results": {"Sheaf.Paper.ExceptionalRingTransportFamily": {"hash": "5960d42c061d3c3d87bda0f357d5137c36100426", "status": "OK"}}, "seconds": 85, "time": "2026-10-28T03:25:22+0800", "transitive": 0, "version": 1}
```

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
