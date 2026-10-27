## What changed

Filled `AlgebraicGeometry.Etale.etaleDirectScalarProjection` without changing its
statement or the ordered projection definitions. The archived item was restored
from its recorded quarantine path before editing; its Lean attachment and public
imports are preserved.

Added three private proof imports: the source-library
`WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat`,
`Sheaf.SixFunctors.TensorProjectionAdjunct`, and
`Sheaf.Paper.EtaleScalarPullbackTensorCoherence`.

The private `curryComparison` merely curries the existing natural scalar tensor
comparison. The private `orderedDirectProjection_flip` uses the proved
`tensorProjectionAdjunct` with the identity morphism to identify the specified
ordered projection with the generic projection for the flipped tensor bifunctors.
The main proof applies the source-library `rightAdjointProjectionMap_mate`, using
`etaleScalarPullback_tensor` for its binary compatibility hypothesis and
`mateEquiv_counit` for its counit hypothesis. It cancels direct image of the
invertible forward pullback comparison to recover precisely the inverse-comparison
formula in the assigned statement.

Updated only the item's node proof, proof dependencies, and proof origin to match
this argument. No shared definition, signature, attribute, or public import changed.
The unit's vector-bundle-purity route is retained. The already proved
`lem-amb-tensor-projection-adjunct` is used as a generic categorical tool, without
replacing a step of that unit.

Validation: the item compiled cleanly through `lcompile.py` in 18.5 seconds.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.etaleDirectScalarProjection`
(node `lem-pur-etale-direct-scalar-projection`).

Added zero holes. No `sorry` remains in the delivered module; both private helpers
are proved. This is a proof from existing declarations, including the still-open
`etaleScalarPullback_tensor`; no claim is made that its transitive axioms are
already free of `sorryAx`.

## No longer needed

No original import was removed. The proof does not directly need
`Sheaf.Paper.RingedExchangeTensorCoherence`
(node `lem-weil-pbc-ringed-exchange-tensor-coherence`): the generic projection/mate
theorem supplies the categorical assembly without constructing a ringed-topos
presentation of this square.

The original direct proof dependencies `lem-pc-kflat-resolution` and
`lem-kun-tensor-sym` are removed from `proof_deps`: representative descent and the
symmetry calculation are already encapsulated in the two existing APIs used here.
The tensor symmetry remains a statement dependency and is used by the unchanged
ordered-projection definition. No assertion is made that these modules are globally
unreachable or can be withdrawn. No module is withdrawn by this delivery.

## Where the brief, the DAG or earlier work was wrong

The old plan proposed a ringed-topos specialization and a fresh scalar/symmetry
calculation. Both can be avoided: the adopted source library already proves
projection compatibility with mates for arbitrary bifunctors, so applying it to
flipped tensors gives the requested ordering. The existing tensor-projection
adjunct theorem identifies that ordering with the archived definition.

The rework table recorded the item as quarantined. Its archive was preserved and
used as the source; no absent path was treated as a withdrawal. There was no current
item-specific numbered return in `coord/returns/U2.md`.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
