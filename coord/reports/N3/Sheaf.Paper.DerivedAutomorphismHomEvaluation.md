## What changed

Only `lean/Sheaf/Paper/DerivedAutomorphismHomEvaluation.lean` changes.
The four natural isomorphisms are assembled from the existing comparison-law
statements with `NatIso.ofComponents`, with the specified component formulas.
The common-stage shift equation follows by applying its inclusion functor to the
rational equation. Realized system evaluation follows directly from the closed
adjunction's counit equation, followed by the functorial limit. A proved private
generic helper keeps that calculation independent of the large system model.

The integral, rational and common-stage permitted-pair properties and shift closure use the
already stated coefficient-descent dependency. The K-injective representative
model is the fixed resolution comparison followed by the inverse localized Hom
augmentation; cancellation proves the required uniqueness. Two private proof
imports are added: `Sheaf.Paper.PodReindexingHomCoefficientDescent` and
`Sheaf.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses`.

Local irreducibility for `Scheme.residueField` and `HasDerivedCategory.standard`
prevents repeated unfolding of these large models during elaboration, following
the same convention as the coefficient-descent dependency.

All existing declaration signatures, definitions, public imports and docstrings
are preserved. No new public statement or definition is introduced.

## Proved and sorry left

Closed 8 of the original 44 theorem holes; added 0 holes; split off 0 statements.
The closed declarations are:

- `derivedAutomorphismHomEvaluation`
- `podCommonHomComparison_shift`
- `podSystemHomComparison_realizedEvaluation`
- `podIntegralPairs_pullback`
- `podRationalPairs_pullback`
- `podIntegralPair_shift_property`
- `podKInjectiveHomModel_existsUnique`
- `podCommonPairs_pullback`

These proofs use the existing named dependencies, some of which still have
`sorry`; this does not assert an axiom-free proof of the complete mathematical
package. The following 36 original holes remain unchanged. Every listed
declaration belongs to `lem-pod-derived-automorphism-hom-evaluation`:

- `podFiniteHomComparison_laws`
- `podIntegralClosed_existsUnique`
- `podIntegralHomComparison_laws`
- `podRationalClosed_existsUnique`
- `podRationalHomComparison_laws`
- `podCommonClosed_existsUnique`
- `podCommonHomComparison_laws`
- `podSystemHomComparison_laws`
- `podCompletedRingProjection_naturality`
- `podCompletedRingMap_isIso`
- `podCompletedInverseImage_equivalence`
- `podFiniteRestrictionOrdinary_existsUnique`
- `podOrdinaryLimitReindexing_existsUnique`
- `podLimitReindexing_existsUnique`
- `podReductionReindexingMap_laws`
- `podCompletedToTower_laws`
- `podHomReductionSquare`
- `podHomComplexShift_existsUnique`
- `podDerivedHomShift_existsUnique`
- `podFiniteHomComparison_shift`
- `podFiniteHomComparison_comp`
- `podIntegralReindexedHom_shift`
- `podCompletedModuleComp_existsUnique`
- `podIntegralPullbackComp_normalization`
- `podIntegralHomComparison_comp`
- `podSystemNormalized`
- `podSystemHomComparison_fiber`
- `podArgumentFirst_integral_rational`
- `podArgumentFirst_finite`
- `podArgumentFirst_finite_transpose`
- `podArgumentFirst_common`
- `podRationalHomComparison_comp`
- `podCommonHomComparison_comp`
- `podIntegralHomShift_existsUnique`
- `podIntegralPullbackShift_existsUnique`
- `podIntegralRationalHomComparison_shift`

## No longer needed

None. No imports, nodes or modules are withdrawn. The remaining companion
proofs still need the six declared reindexing dependencies; assembling the top
natural isomorphisms does not make those dependencies unnecessary.

## Where the brief, the DAG or earlier work was wrong

The current system dependency `Sheaf.Paper.ReindexingSystemHomReductionSquare`
publicly imports this item, so it cannot also be imported by this item without
an import cycle. Its interface is therefore not used by this packet. The other
remaining companions retain their original statements and planned dependencies.

The module's main theorem is an assembly of existing companion statements;
its proof need not repeat their representative-level constructions. The system
evaluation consequence follows from the defining adjunction even before the
system comparison's invertibility and coherence laws are established.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
