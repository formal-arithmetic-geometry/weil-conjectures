## What changed

Partial proof delivery for `Sheaf.Paper.CompactSupportCondensedRealization`.
Filled the inherited additive and integral-linear structures, the three geometric
base facts, compactification-open quasi-compactness, derived section-encoding
equivalence, and constructible shift stability. Existing public signatures and data
constructions are unchanged.

A proved private helper handles derived equivalences with independent Hom
universes. It uses the localized termwise unit and counit, avoiding instance
search across two derived-category presentations. Added the proof import
`WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed` for invariance of
constructibility under cohomology-shift isomorphisms.

Marked `encodingScalarMap` locally irreducible before registering its isomorphism instance.
Profiling found that registering `encodingScalarMap_isIso` otherwise spent about
18 seconds unfolding the large mate expression. This file-local elaboration
attribute preserves the public definition and all downstream behavior.

Validation: the complete item module compiled through `lcompile.py` with exit code 0
in 41.1 seconds, below the 60-second file limit. No new holes were introduced.

## Proved and sorry left

Original holes: 25. Holes closed: 8. Holes added: 0. Split off: 0.
This is a partial proof delivery; the simultaneous comparison theorem remains open.
All declarations below are in namespace
`WeilConjectures.CompactSupportCondensedRealization`, except the final theorem,
which is in `WeilConjectures`. Their existing node is
`lem-pur-compact-support-condensed-realization`.

Closed:

- `integralSupport_additive`
- `integralSupport_linear`
- `base_noetherian`
- `base_dimension`
- `base_primeUnit`
- `encodingDerived_isEquivalence`
- `compactification_open_quasiCompact`
- `fieldConstructible_shiftStable`

Remaining, with existing statements and documented proof plans retained:

- `fieldExtension_flat`
- `omegaExtension_flat`
- `scalarModelTransport_subsingleton`
- `scalarModelTransport_nonempty`
- `sectionFieldMap_existsUnique`
- `encodingScalarMap_isIso`
- `realizedCoefficient_square`
- `encodingRestriction_existsUnique`
- `fieldScalar_preserves`
- `omegaScalar_preserves`
- `finiteProjection_isIso`
- `omegaProjection_isIso`
- `omegaSupport_preserves`
- `systemRefinement_id`
- `systemRefinement_comp`
- `omegaRefinement_isIso`
- `compactSupport_condensedRealization`

## No longer needed

None. No modules, nodes, or existing imports are withdrawn. The remaining
reconstruction, flatness, projection, coefficient, and refinement holes still
need their recorded dependencies. No new proof dependency is substituted for
any unit step.

## Where the brief, the DAG or earlier work was wrong

The original module has 25 holes. The flatness calculus is stated for finite
intermediate fields inside the fixed algebraic closure, whereas the item uses
arbitrary finite coefficient types and field embeddings. Applying that calculus
to the untouched flatness/projection holes requires the coefficient-model
transport; it is not a direct instance application.

The standard derived-equivalence instance uses a common derived Hom universe.
The displayed section encoding has two independent Hom sizes, so its proof
instead supplies the termwise quasi-inverse and the localized unit/counit
explicitly. This preserves the existing statement and avoids unfolding the
large section-module equivalence during instance synthesis.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
