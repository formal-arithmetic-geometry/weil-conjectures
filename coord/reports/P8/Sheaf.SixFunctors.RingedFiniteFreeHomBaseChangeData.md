## What changed

Proved `CategoryTheory.ringedFiniteFreeHomBaseChange_complex` in
`Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeData`, preserving its statement and
`ringedFiniteFreeScalarSection` verbatim. The proof obtains the existing normalized scalar
adjunction and tensor data with standard auxiliary derived-category choices, identifies
its ordinary extension with the supplied extension using the prescribed object/map
formulas, and identifies the scalar unit with the specified sheafified pure section.
A proved private helper establishes naturality of the tensor components by adjunction,
total pure-generator extensionality, unit naturality, and the given generator formula.
`NatIso.ofComponents` supplies the required natural isomorphism, and the existing
K-flat preservation field supplies the last clause.

Added one proof-only `import all` of
`Sheaf.Algebra.Homology.ScalarHomTensorCoherence` to reuse its proved private
`total_pure_hom_ext` and `tensor_generator_map` helpers. Existing public imports and
public declarations are unchanged. Updated the tensor-complex node's proof and proof
dependencies to describe this argument. No definitions, consumers or target statements
are changed; there are no new nodes.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.ringedFiniteFreeHomBaseChange_complex`
(node `lem-sf-ringed-finite-free-tensor-complex`).
Added zero holes; zero `sorry` occurrences remain in the delivered Lean module.
The private helper `scalarComparison_natural` is also fully proved.
This is a proof from existing library declarations, not a decomposition into new holes.

## No longer needed

No imports are removed and no modules or nodes are withdrawn. The existing DAG route
through `lem-sfb-dc-hom-scalar-adjunction` is retained. No additional finite-free basis,
Hom-coordinate theorem, derived tensor transport, or new K-flat lemma is needed.
The auxiliary standard derived-category choices are used only to obtain already stated
ordinary/chain data and do not occur in the conclusion. No blueprint unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned proof route works. The tensor comparison interface stores component
isomorphisms and their generator formula rather than chain-level naturality; naturality
therefore needs the explicit private helper in this delivery. The reusable generator
extensionality and tensor functoriality lemmas are private in the coherence module,
so they are accessed with Lean's supported proof-only `import all`.
A single-file server compile passed in 17.0 seconds. Final delivery preflight supplies
the module and axiom checks. No mathematical statement repair was necessary. The argument adds no nonzero,
flatness, finite-free, or boundedness hypothesis, and applies equally to zero rings,
zero complexes and arbitrary unbounded complexes.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
