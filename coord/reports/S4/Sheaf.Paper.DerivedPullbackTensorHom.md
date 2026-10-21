## What changed

Filled six existing theorem proofs in `Sheaf.Paper.DerivedPullbackTensorHom`:
`rationalPullbackScalarComparison_existsUnique`,
`rationalTensorScalarComparison_existsUnique`,
`integralHomScalarPair_permitted`, `rationalHomScalarPair_permitted`,
`rationalHomScalarComparison_existsUnique`, and `commonStageHomPairAtStage_permitted`.
All public signatures, definitions, imports, and existing docstrings are preserved.
The additional universe names and scoped proof commands are documented in
`coord/changes/S4-derived-operations-private-proof-context.md`; no consumer is adapted.

Integral membership is transported through `scalarHomCompleted` from the scalar
extension of the permitted source Hom. Rational membership follows from the
literal object specification of the existing rational scalar functor. The rational
Hom scalar comparison is localization of the prescribed integral comparison,
transported along the existing object equalities; its specified hom proves uniqueness.
For common-stage membership a proved private helper constructs the isomorphism of
underlying integral objects for iterated versus direct stage extension, using
`sfIntegralScalarComp` and the actual coefficient-inclusion composition law. Apply
internal Hom with the inverse first-variable isomorphism and the direct second-variable
isomorphism, and transport integral constructibility. In particular no rational
isomorphism is used to infer integral constructibility.

The pullback scalar comparison is natural already on integral objects: its
components are conjugated by the recorded completion isomorphisms, and naturality
follows from the completion natural transformation and ordinary comparison.
A proved private tensor-induction helper then extends that naturality to raw
rational Hom modules. Both composite functors have the same coefficient map;
their prescribed pure-tensor formulas provide all maps needed by the helper.
Transporting the localized integral components gives the stated normalization,
and componentwise extensionality proves uniqueness.

The tensor comparison uses the same normalized completion conjugation in both
input variables. A second proved private helper performs tensor induction in each
Hom module, using the specified bilinear action of the rational tensor functors.
Its additive maps are composed through generic proved helpers to avoid unfolding
the selected functor data. Coefficient multiplication is preserved by the actual
field-induced coefficient ring homomorphism. The statement's component formula
then determines the natural isomorphism uniquely.

## Proved and sorry left

Six of the original twelve holes are closed, by the six declaration names listed
above (all in namespace `WeilConjectures`). No holes are added or split off.

Six existing holes remain, all attached to
`def-weil-derived-pullback-tensor-hom`, with their original sources and proof docstrings:

- `WeilConjectures.rationalDerivedPullback_existsUnique`
- `WeilConjectures.rationalDerivedTensor_existsUnique`
- `WeilConjectures.rationalDerivedInternalHom_existsUnique`
- `WeilConjectures.commonStageDerivedPullback_existsUnique`
- `WeilConjectures.commonStageDerivedTensor_existsUnique`
- `WeilConjectures.commonStageDerivedInternalHom_existsUnique`

This is a partial proof delivery, without a decomposition or a definition repair.
The complete module compiled through `lcompile.py` in 52.3 seconds. All 51 original
declaration signatures were compared with the shared source and are unchanged.

## No longer needed

None. No imports, declarations, modules, or DAG dependencies are removed. The node
is a definition node with empty `proof` and `proof_deps`; the six proofs implement
the existing declaration docstrings without changing their route. In particular,
the scalar-extension comparison, rationalization, and common-stage construction
remain needed, including their still-unfinished theorems.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The common-stage membership proof must use the integral
scalar associator, rather than merely the rational stage associator, because its
predicate asserts constructibility before rationalization. This is exactly the
qualification already made in the existing proof docstring.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
