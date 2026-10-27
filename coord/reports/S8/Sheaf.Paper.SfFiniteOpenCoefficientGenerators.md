## What changed

Proved `WeilConjectures.sfFiniteOpenCoefficient_generator` in
`Sheaf.Paper.SfFiniteOpenCoefficientGenerators`, with its public statement and all
existing definition bodies and public imports unchanged. Added a proof-only import
of the new, completely proved `Sheaf.Paper.SfIntrinsicOpenUnitGenerators` module.

The auxiliary module constructs canonical section evaluation using the realization
unit and counit. It proves naturality of the intrinsic adjunction-unit generator,
its compatibility with coefficient restriction, and the transported left-adjoint
uniqueness unit equation. The item computes each supplied normalized finite left
comparison on a single direct-sum generator and combines these computations with
the intrinsic coefficient identity. Heterogeneous section identities keep concrete
quotient carriers abstract.

The complete proof compiled as one file in 41.3 seconds. A subsequent delivery
compile with the axiom scan exceeded 60 seconds. After simplifying the quotient
carrier conversion and the concrete adjunction-unit calculation, the proved
intrinsic section construction was factored into its own module under step 3a of
the current worker brief. Each file is checked separately for delivery. The checked
full theorem had exactly `propext`, `Classical.choice` and `Quot.sound` as axioms.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.sfFiniteOpenCoefficient_generator` (node
`lem-sf-finite-open-coefficient-generators`). Added no holes. Neither delivered
module contains `sorry`. Every auxiliary theorem is proved; no unfinished statement
was split off. The new node is a proved modularization of the intrinsic part of the
argument, not a replacement assumption for the item.

## No longer needed

The proof-only import of
`Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionCoherence` is located in the
auxiliary module, where it is used. No existing public import was removed and no
module is withdrawn. `lem-sf-integral-open-reduction-comparison` is not a proof
dependency of the item: the supplied operations and normalized comparisons suffice,
so neither its completed comparison nor its existence theorem is used. Its
definition interfaces remain in the existing statement dependencies. The intrinsic
realization and coefficient compatibility dependencies now sit under the new node.
No existing module is rendered unreachable by this delivery.

## Where the brief, the DAG or earlier work was wrong

The plan did not expose the actual underlying-abelian-sheaf identification needed
to evaluate the abstract adjunction equation. The new module proves it using real
realization maps and supplies the resulting intrinsic generator API. The public
item statement is unchanged. The empty open and zero module need no additional
hypotheses: all transports are isomorphisms and the proof is pointwise.

The current worker brief permits splitting a self-contained proved part after
improving the slow constructions. That updated instruction was used after the
heterogeneous carrier and generic adjunction improvements; no compile limit was
raised and no shared definition or tool was changed.

## New nodes

`lem-sf-intrinsic-open-unit-generators`, in
`Sheaf.Paper.SfIntrinsicOpenUnitGenerators`, records the canonical intrinsic unit
generator, its underlying section evaluation, its naturality and coefficient
compatibility, and the generic transported unit equation. Every declaration is
proved. Its construction uses the existing realization and normalized coefficient
square; its statement is independent of slice operations and of coefficient
towers. There are no change records because no other existing module or interface
was changed.

## Second reading by S8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
