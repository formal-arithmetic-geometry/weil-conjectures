## What changed

Proved `WeilConjectures.PurScalarProjection.compactSupportScalarProjectionIdentification`
from this module's existing `ordinaryCompletedSquare`, `gamma_identification` and
`inner_domain`. The scalar domain of K comes from gamma identification for the identity
compactification on Y, using the already available coefficient system calculus. The scalar
domain of M comes from gamma identification for c. The private proof import
`import all Sheaf.Paper.SfProEtaleProjectionFormula` reuses
the already proved `tensor_domains` and `pull_domains` helpers in place of their
verbatim duplicated proofs. This reduces whole-file elaboration cost without changing
any statement, definition or public import.

Private proved helpers derive scalar-completion naturality under isomorphisms from
unit-normalized uniqueness, finite support counit naturality from adjunction naturality,
support realization naturality under isomorphisms from its uniqueness, and completed
tensor comparison naturality from ordinary tensor and scalar-completion naturality.
The final proof conjugates the ordinary completed square by the actual chosen support
realizations. It uses gamma identification at M and at the completed inner tensor.
No reduction functor is used to detect equality of integral morphisms.

Existing public signatures, definitions, docstrings and public imports are unchanged.
The node's added final step records the assembly; the earlier steps remain the plans for
the remaining named comparison statements.

## Proved and sorry left

Closed one of the nine original holes:
`WeilConjectures.PurScalarProjection.compactSupportScalarProjectionIdentification`.
Added zero holes; this is a proof from existing named statements, not a new decomposition.

Eight existing holes remain, all attached to
`lem-pur-compact-support-scalar-projection-identification`:

- `WeilConjectures.PurScalarProjection.scalarCompletion_existsUnique`
- `WeilConjectures.PurScalarProjection.properProjection_existsUnique`
- `WeilConjectures.PurScalarProjection.openProjection_existsUnique`
- `WeilConjectures.PurScalarProjection.realization_existsUnique`
- `WeilConjectures.PurScalarProjection.native_scalar_identification`
- `WeilConjectures.PurScalarProjection.gamma_identification`
- `WeilConjectures.PurScalarProjection.diagram_projection`
- `WeilConjectures.PurScalarProjection.ordinaryCompletedSquare`

## No longer needed

Removed five direct proof imports used by the duplicated domain-helper proofs:

- `Sheaf.SixFunctors.ConstructibleTensorCompletion`
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`
- `Sheaf.Paper.OrdinaryCompletedIntegralPullback`
- `Sheaf.Paper.QcqsCompletionUnitLocality`
- `Sheaf.Paper.SfIntegralConstructibleTriangulated`

Their mathematics remains needed through the existing proved helpers in
`SfProEtaleProjectionFormula`; none of these modules or nodes is withdrawn.
The final assembly uses the existing internal comparison statements; their unproved
obligations still need their declared dependencies. The unit route is unchanged.

Validation: the complete module compiled in 23.3 seconds before removal of redundant
proof imports; final compilation and axiom/hole probes are run by the delivery tool.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The final square can already be assembled from the
module's named intermediate comparisons. Their uniqueness statements provide the
isomorphism naturality required for transport, so no new naturality assumption or
split-off theorem is needed.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
