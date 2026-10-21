## What changed

Proved `AlgebraicGeometry.ProEtale.constructible_localTor_iff_etaleOrigin` in
`Sheaf.AlgebraicGeometry.ConstructibleLocalTorEtaleOrigin`, with its original statement,
universes, public imports and definitions unchanged. Added three proved private helpers:
`torAmplitude_iso` transports the universal K-flat Tor tests,
`cohomologyBounded_of_torAmplitude` obtains the cohomology interval from a bounded flat
model, and `boundedConstructible_iso` transports constructible cohomology and its interval.

Local-to-global Tor bounds use
`Scheme.hasFiniteCoefficientProEtaleTorAmplitude_iff_locally`. The existing
`coefficientModelTorAmplitude_iff_flatModel` supplies a representative supported in the
same interval, so homology localization gives boundedness. The finite-Tor equivalence
already supplied by `finiteTorComparisonNoetherian` then provides the etale antecedent.
Its counit and the natural identification with derived comparison give the ambient
isomorphism. The standard localization representative and its factorization through
termwise comparison produce the representative required by the statement. Conversely the
same factorization identifies the supplied representative with derived comparison; the
forward restricted equivalence supplies constructibility and finite Tor bounds, which
transport across the ambient isomorphism and then localize.

Updated the existing item's DAG proof and proof dependencies to this argument. All added
imports are private proof imports. No other modules or public interfaces change.

Validation: the delivered module compiles cleanly through `lcompile.py` in 7.1 seconds.
Both new proof-import directions pass `import_direction.py may`. The original theorem
signature is byte-identical, and all Lean lines are at most 100 characters.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProEtale.constructible_localTor_iff_etaleOrigin`
(node `lem-sfb-constructible-local-tor-etale-origin`). Added 0 holes; split off 0 statements.
There is no `sorry` left in any delivered Lean file. All three private helpers are proved.
The proof uses existing declarations with their existing transitive assumptions; it does
not assert that the full project dependency closure is already free of `sorry`.

The construction works uniformly for the empty scheme, the zero ring and zero complexes:
the existing local/global theorem supplies an ordered interval even for the empty cover,
and every subsequent operation uses localization and categorical equivalences. No
nonempty space, nonzero ring, completeness or additional boundedness hypothesis is used.
Independent coefficient universe `v` is retained.

## No longer needed

Removed the private direct imports
`Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison` and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`.
The separate bounded-constructible descent and subsequent reflection of the Tor interval
are already bundled into the restricted equivalence of
`det-pe-finite-tor-comparison-noetherian`. The source fixed-coefficient tensor is not the
coefficient-model tensor used by this proof. Its direct proof dependency
`def-weil-derived-tensor` is replaced by `lem-pe-coefficient-tor-flat-model` for boundedness.

Removed `sk-thm-pe-constructible-comparison` from the item's direct proof dependencies and
its top-level `tool_uses` list: its equivalence is used through
`det-pe-finite-tor-comparison-noetherian`, which still imports and proves its result from
that comparison. This does not withdraw that module or any source declaration. No module
is claimed to disappear from the whole targets' import closure. No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The stated plan is valid. Its boundedness step and its two comparison steps need no new
intermediate statements: the library already supplies a bounded-flat-model criterion and
the restricted finite-Tor equivalence with the exact natural comparison required here.
The updated node records these existing declarations and the explicit iso transports.
No statement, definition or unit route is changed. There are no new nodes or forced
consumer adaptations.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
