## What changed

Completed all eight remaining proofs in `Sheaf.Paper.FiniteStagePairCategory`.
The actual finite-stage tensor functors are identified with the declared
embedding-based scalar extensions. Raw scalar localization is compared with the
existing Rationalization localization; its universal property supplies functor
factorization, natural isomorphisms, uniqueness, and additivity.

Ordinary identity tensor units are mates of identity-on-sections restriction.
The universal derived counit gives their unique derived normalization. Exact-derived
composition coherence and the adjunction mate identities prove the pentagon.
K-flat resolutions identify the normalized derived unit with the restriction mate;
the diagonal unit equation and the pentagon imply both general unit laws.
Every added helper is private and proved.

Added six proof-only imports: `Sheaf.Paper.PbcScalarExtension`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom`,
`Mathlib.CategoryTheory.Adjunction.Additive`,
`Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived`, and
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`.
Updated the existing node's proof, proof dependencies, and proof origin.
All existing declaration signatures, public imports, definitions, and docstrings remain fixed.
The change record is `coord/changes/F7-finite-stage-scalar-proof-context.md`.

The full module compiled cleanly through lcompile.py in 34.6 seconds.
The required deliver3.py dry run also passed compilation and preflight, including
consumer and declaration checks; its review class is CODEX because of the node
update, private proof context commands, and change record.

## Proved and sorry left

Closed 8 of 8 baseline holes, all in namespace `AlgebraicGeometry.Scheme`:

- `pbcAmbientScalarExtension_preserves`
- `pbcRationalScalarExtension_exists`
- `pbcOrdinaryScalarUnit_exists`
- `pbcAmbientScalarUnit_exists`
- `pbcScalarAssociator_exists`
- `pbcScalarAssociator_cocycle`
- `pbcScalarSystem_units`
- `pbcScalarExtension_additive`

Zero holes remain in the item; zero holes added; zero statements split off.
These proofs use existing dependency declarations, some of which still contain
`sorry`, as required by stage 3. Their statements and modules are unchanged.
The five proofs previously landed by E5 are retained.

## No longer needed

No original import or declared proof dependency was removed; no module is withdrawn.
The node originally had an empty proof list and no proof dependencies, so the
updated node records the dependencies actually used.

No separate directed-colimit-of-abelian-groups module is needed in the proof:
the existing common-stage PairCategory quotient and its proved group operations
already implement that construction. The statement dependency
`def-weil-directed-colimit-abelian-groups` is retained, since it describes the
alternative interpretation of the Hom groups in the node's statement.
No independent tensor associativity or tensor unit lemma is assumed: the mate
coherence and unit calculations are proved privately here from the normalized
restriction and adjunction APIs. Pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The node's empty proof list did not describe the scalar coherence obligations
present in its Lean module. The new proof list records the argument actually checked.
The existing declarations suffice; no statement correction or definition repair is needed.

Earlier tool failures were temporary remote compile/provider failures. Resumed
compiles now succeed. The dispatcher refreshed the budget metadata across retries
(the preserved original attempt recorded start 1792426240.1786227; the current
launcher-owned metadata records 1792429583.4657576). No budget metadata was edited
by the worker, and elapsed time was not used to justify a split.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
