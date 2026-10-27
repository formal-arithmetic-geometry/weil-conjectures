## What changed

Proved `WeilConjectures.normalizedIntegralGeometricCoherence` in the item module,
with the existing statement and public import unchanged. Added the proof import
`Sheaf.Paper.QuotientSystemMixedCoherence` and proved private adjunction calculations.
The proof transfers composition and unit equations through the actual supplied
reduction/limit adjunction. It uses effectivity and completeness already in `D`.
The node records this direct proof instead of the word-calculus route.
Local standard-derived-category priorities and irreducibility keep typeclass search
from unfolding the coefficient constructions. Making `Scheme.residueField` locally
irreducible prevents failed searches from unfolding unrelated scheme stalk colimits.
No shared definition is changed. The complete proof compiled in 12.7 seconds with
profiling enabled; those debugging options have been removed for delivery.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.normalizedIntegralGeometricCoherence`
(node `lem-trf-normalized-integral-geometric-coherence`). All seven fields are proved:
three ordinary system equations, naturality, realized associativity and both units.
No holes added; no `sorry` remains in the delivery. Existing dependencies may still
have their own holes; none of their statements or proofs is changed.

## No longer needed

The declared proof dependency `lem-trf-counit-realization-substitution` and its module
`Sheaf.TraceFormula.CounitRealizationSubstitution` are unnecessary for this proof.
Adjunction Hom naturality supplies the needed substitution square directly, and
completeness reflects equality after reduction. No word syntax, scalar normalization,
parenthesization induction or scalar associativity is needed for these geometric laws.
The module was never imported by the original item, so no existing import is removed.
The quotient-system coherence dependency remains needed. No existing module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The word-calculus route is longer than needed: the exact supplied adjunction, counit,
effectivity and completeness fields suffice to transfer the geometric laws directly.
The source file exists despite its historical quarantine/rework row and is preserved.
No statement or definition repair is necessary. No new nodes or forced adaptations.

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
