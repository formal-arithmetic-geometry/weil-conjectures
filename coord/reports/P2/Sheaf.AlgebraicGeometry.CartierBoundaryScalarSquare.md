## What changed

Filled `AlgebraicGeometry.ProEtale.geoCartier_boundary_scalar_square` in the item module.
The statement, definitions, attributes and public import are unchanged. Private proof imports
provide the integral pole boundary, comparison of scalar-adjunct equations, normalized scalar
units, and the exact-functor Ext API. No other existing module is changed.

The proof identifies both ordinary boundaries with their integral pole-boundary adjunct
formula, then transports that formula through exact site comparison. The supported integral
generator has an unbounded derived-unit property obtained by composing the integral-to-residue
unit with the existing normalized residue-to-R coefficient unit. Its Ext map is injective.
After applying that injection, the normalized source and root identities and Yoneda
associativity prove the coefficient square. Abstract private helpers cancel the two source
isomorphisms without unfolding the concrete sheaf definitions.

A previous N3 sandbox contained this argument. P2 reused and inspected it, repaired scalar-unit
composition by explicitly typing its three objects, and replaced the failing concrete source
cancellations with abstract Ext lemmas. The scalar-unit conversion and functor transport use
existing named lemmas instead of large inline definitional conversions. No new statement is split off.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.geoCartier_boundary_scalar_square`
(node `lem-sfb-cartier-boundary-scalar-square`).

Holes closed: 1 of 1. Holes added: 0. Holes left in this module: 0.
All private helpers are proved. This is a proof from existing project declarations, including
`AlgebraicGeometry.ProEtale.geoCartier_normalized_scalar_units`, whose existing hole is outside
this delivery. It is not a claim that the entire transitive proof closure is sorry-free.

## No longer needed

No original import is removed, and no module is withdrawn. No whole module is claimed pruned
from the targets' closure. Every added proof import supplies a declaration used by the proof,
including the existing scalar-unit conversion lemma that avoids unfolding the predicates.

The item's direct proof plan no longer uses these former dependencies:
`lem-sfb-successive-derived-quotient-normalization`, `lem-geo-cartier-coeff-extension`,
`lem-asd-finite-etale-twist-line`, `lem-asd-ordinary-supported-kummer`, and
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`. Their modules need not be imported privately
for this proof: the existing normalized-unit theorem supplies the coefficient universal
property, while integral-boundary normalization and Ext injectivity prove the square.
These results may remain transitively needed by other declarations, including the normalized
units. The ordinary boundary interface remains in the unchanged statement dependencies.

## Where the brief, the DAG or earlier work was wrong

The general derived tensor-transitivity argument is unnecessary for this square once the full
relative-boundary equations and the existing normalized scalar-unit theorem are used.
The unit route is retained: integral pole boundary, positive Kummer reduction, coefficient
extension via its universal property, and exact site comparison. Empty support, zero
coefficient rings and N=1 require no extra hypotheses: the proof uses actual derived-unit
bijections, not nontriviality or flatness of the coefficient map.

The prior N3 sandbox report described a proof but its source did not compile on the current
base. The scalar-unit composition lacked explicit target objects, and concrete simplification
failed to cancel source isomorphisms. These issues are repaired inside the item module.
The private composition helper imported from `EtaleSupportedIntegralDerivedUnit` is used;
its public supported-integral theorem is not invoked. The node records that module's existing
attachment for this generic tool dependency.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
