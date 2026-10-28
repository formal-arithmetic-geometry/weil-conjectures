## What changed

Constructed the scalar, evaluation, and inverse-limit fields of
`coefficientDerivedSectionsCoreData` directly for the prescribed coefficient functors.
All added helpers are private and proved. They are separated into
`Sheaf.Paper.CoefficientSectionsCoreTransport` (ordinary transport and generic
derived comparisons) and `Sheaf.Paper.CoefficientScalarSectionsCoreComparison`
(the scalar specialization). The complete single-file proof typechecked but took
99 seconds; after improving the scalar conversion, these self-contained parts were
separated to meet the 60-second limit for each file. This adds no public statements
and no new proof obligations. Existing public declarations and imports
retain their signatures and visibility.

The ordinary section comparison identifies a map from the module unit with its
values at one, then with the limit of the underlying presheaf. This identification
transports the proved restriction-of-scalars acyclicity theorem to the project's
Coyoneda model of sections. The composite of exact scalar restriction and completed sections is therefore
a right derivation on finite coefficient modules. Uniqueness of right derivation
gives its comparison with finite sections and the required scalar model equation. The ordinary
scalar formula follows from linearity and the value at one.

For evaluation, the existing generic tower comparison is instantiated with the actual
right-derived functors and combined with the already proved restricted-evaluation
isomorphism and scalar comparison. For inverse limit, both composites derive the same
ordinary functor: limit preserves K-injectives by its exact constant left adjoint,
and the existing tower-image acyclicity lemma handles the other composite.
Uniqueness of right derivation transports the ordinary sections/limit isomorphism.

## Proved and sorry left

Closed: `WeilConjectures.coefficientDerivedSectionsCoreData` (one original hole).
Added: none. Remaining in all three delivery modules: none.

Ordered server compilation passed: transport 34.1 seconds, scalar comparison
51.3 seconds, and the public module 17.8 seconds. The private-only module lint
option is deliberately set at module scope for the two implementation modules.

## No longer needed

The strict-system/sequence-site transport in the original plan is unnecessary:
the generic comparison and acyclicity helpers apply directly to the actual module
categories and their existing derived functors. Both original planned dependency
modules remain used. No existing declaration or module is withdrawn, and no public
import is removed. The separate proof import of right-derived composition is
unnecessary because the pullback module already reexports it. No dependency node is claimed to be globally pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG described transport of generic packaged comparisons. Their underlying proved
lemmas give the comparisons directly for the functors already chosen in the public
interface. The node proof now records this direct construction. No statement or
definition repair was needed.

Separate downstream concern: `coefficientDerivedSectionsCoreEquations` asks for
normalization equations for every `D`, but the present data structure permits an
arbitrary global-limit isomorphism and arbitrary evaluation isomorphisms. Composing
one of those with negation preserves its type and generally changes the proposed
equations. That downstream statement should check its missing normalization
condition. This proof does not use it, and no downstream file is changed here.


## New nodes

`lem-coef-sections-core-limit-transport` records the already proved private
`WeilConjectures.sectionsLimitComparison` and its implementation module. Its proof
uses the existing tower-image acyclicity theorem and uniqueness of right derivation.

`lem-coef-sections-core-scalar-comparison` records the already proved private
`WeilConjectures.scalarSectionsComparison` and its implementation module. Its proof
uses ordinary value-at-one transport, restriction-sections acyclicity and the
universal exact-composite comparison. Both nodes have zero holes; these are file
extractions, not new proof obligations.

Change record: `coord/changes/r3-coefficient-sections-core-proof.md`. The public
signatures are identical; both unchanged direct importers compiled successfully.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.CoefficientDerivedSectionsCoreData": "f583653ccebe459dbe378985e0001cf26937633b", "Sheaf.Paper.CoefficientScalarSectionsCoreComparison": "8d240384d98c28e03d24723a7e890c688353a924", "Sheaf.Paper.CoefficientSectionsCoreTransport": "ce39b9c3a9ec7ced0c738447c8db9d2608714c2e"}, "results": {"Sheaf.Paper.CoefficientDerivedSectionsCore": {"hash": "ffff8012a1456bc980d58a81c32816f379d3b562", "status": "OK"}, "Sheaf.Paper.CoefficientDerivedSectionsCoreEquations": {"hash": "924c6e50dae31f441617dfeac7e3e0779a3b9b73", "status": "OK"}}, "seconds": 56, "time": "2026-10-28T12:50:36+0800", "transitive": 0, "version": 1}
```

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
