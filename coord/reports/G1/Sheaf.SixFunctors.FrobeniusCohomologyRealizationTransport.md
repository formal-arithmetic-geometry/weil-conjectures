## What changed

Factored the canonical realization comparison into the rational cohomology
comparison and the scalar-and-size tensor comparison, using explicit composites
of the existing specified maps. No old definition or statement changes.

Proved the scalar tensor tower law for arbitrary field homomorphisms, then for
an abstract field system, and specialized it to the finite coefficient stages.
The assigned module proves the categorical pasting and common-stage cancellation
arguments and applies them to the two factor cocycles. Naturality moves the
intermediate rational comparison past the inverse tensor comparison. The two
endpoint tower equations then cancel the source and target associators in
`StageSystem.tr`, yielding the original morphism equality.

The constructed `CoefficientData` record contains the scalar factors independently
of geometry. `coefficientDataOfFields` constructs it together with the proved
tensor equation for an arbitrary field system. `coefficientParts` specializes
its data field, and `realizationParts` adds the specified rational cohomology
and comparison maps to make `FactorData`.
The generic constructor bundles the explicit coefficient data with its proved
natural-isomorphism tensor equation. Taking components gives the original
objectwise tower law; the identity components of the functor associator simplify.
Taking the proof field and using explicit functor associators keeps the large
functor constructions folded. A proved component
formula identifies the resulting comparison with the original endpoint
comparison. The final proof explicitly reduces the factored and original stage
maps to the same composite.

## Proved and sorry left

Closed the original textual hole in
`WeilConjectures.frobeniusCohomologyRealization_transport`
(node `lem-weil-frobenius-cohomology-realization-transport`).

Proved the new pure scalar-and-size law
`WeilConjectures.CohomologyRealization.coefficientComparison_cocycle`
(`lem-weil-frobenius-cohomology-coefficient-cocycle`). Its private helpers prove
the ordinary module equation by two tensor inductions, identify the canonical
factorization on complexes, extend through derived localization, and insert the
specified equalities of coefficient inclusions and embeddings. The compiler
accepted this module, and `#print axioms` reports exactly `propext`,
`Classical.choice`, and `Quot.sound` for this theorem. The proved
`WeilConjectures.CohomologyRealization.coefficientParts_cocycle` specializes it
to the constructed coefficient record. The intermediate proved
`coefficientDataOfFields_cocycle` gives this specialization for an arbitrary
preordered field system before choosing the finite coefficient fields.

Added one hole in a separate statement module:

- `WeilConjectures.CohomologyRealization.rationalComparison_cocycle`
  (`lem-weil-frobenius-cohomology-rational-cocycle`): the objectwise rational
  coefficient-tower equation before the final scalar-and-size extension.

This is a decomposition, with one original hole closed and one added, for net
zero. The assigned module and the coefficient cocycle module have zero remaining
holes. Every new definition has a complete constructed body. The remaining
obligation is stated directly on the shared canonical record; its predicate
uses only `H`, `F`, `c`, and `q`, and expands to the original objectwise rational
equation. This avoids converting between equivalent large functor expressions.
It expresses the rational operation and point-fibre part of the original
plan; it has no final extension into D(Ω) and is not the morphism transport
statement under another name. The tensor coherence, categorical pasting,
naturality and cancellation are proved in Lean.

Validation: all four delivery modules compile together in import order. A separate
compiler audit checked the public construction bodies and the original theorem
type for private constants, and found none. Both tensor cocycle formulations,
the generic component lemma, and the canonical coefficient-record cocycle have
only the three permitted axioms. The assigned transport theorem additionally
has `sorryAx` from the named rational cocycle. The audit file is outside the
delivery. The original theorem signature and docstring are preserved verbatim.

## No longer needed

None. No original import or module is withdrawn. The original operation,
rationalization, point-fibre and stage-system dependencies are still needed
transitively by the factor cocycles. The existing unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The realization-data declarations supply the normalized comparisons but do not
state the two factor cocycles needed in the parent proof. The existing
`FrobeniusExchange.stageBeta_coherence` concerns operation-side functors that
include geometric pullback; it does not directly state the rational cohomology
comparison or its final scalar-and-size realization.

Deligne's explicit iterated coefficient-extension convention is in
(1.1.1)(d); (1.1.10)--(1.1.14) describe Weil sheaves and cohomology transport.
The new node citations include (1.1.1)(d). The detailed categorical assembly of
these existing constructions is identified as agent-written.

## New nodes

`def-weil-frobenius-cohomology-comparison-factors` owns the five stage
constructions and their two generic comparison constructors in
`FrobeniusCohomologyComparisonFactors`. The same node owns the shared factor
record, its stage/comparison constructions, the rational component predicate
and coefficient natural-isomorphism predicate,
and the generic constructor that bundles explicit coefficient maps with their
proved component equation. They expose the existing normalized maps as natural
isomorphisms without adding choices. The coefficient cocycle is recorded as
an equality of natural isomorphisms, with its component formula proved explicitly.

`def-weil-frobenius-cohomology-canonical-factors` owns the constructed field-system
coefficient record with its proved tensor law, its finite-stage specialization,
and the full canonical record adding rational cohomology and comparison maps.
These definitions use explicit data and proved properties, with no existence
choice or data depending on an unfinished proof.

`lem-weil-frobenius-cohomology-rational-cocycle` is the rational operation and
point-fibre tower equation, before extension into D(Ω).

`lem-weil-frobenius-cohomology-coefficient-cocycle` is the proved balanced tensor
tower equation for arbitrary field homomorphisms and the final scalar-and-size
extension. It specializes to the coefficient inclusions and stage embeddings.
Its complete Lean proof uses ordinary module tensor normalization and then
derived localization.

The original node's proof and proof dependencies now follow the actual Lean
pasting argument. No existing public interface is changed, so no change record
or consumer adaptation is required.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
