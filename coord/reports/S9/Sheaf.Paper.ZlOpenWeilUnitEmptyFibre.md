## What changed

Filled `WeilConjectures.ZlOpenUnit.rationalAlpha_natural` in
`Sheaf.Paper.ZlOpenWeilUnitEmptyFibre`, preserving every existing public declaration,
statement, data definition, and import. Private helpers prove naturality of the
specified rational compositor: identify its components with integral models, use
integral naturality on pure Hom tensors, and extend by additivity. Inverse naturality
and equality transport then give the comparison for a commutative square; specialize
to the actual Frobenius square. This follows the existing private calculations in
`Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality` without changing that module.
No replacement comparison is chosen. The private proof section temporarily
restores ordinary unfolding of the rational pullback and localization, then the
existing local unfolding controls resume. The compact-support functors and the
generic predicates remain locally irreducible at the final theorem, and elaboration
runs sequentially. These settings prevent repeated expansion of realized functors;
all existing data-definition bodies remain verbatim. The unused-section-variable linter is
disabled on the two existing theorem declarations to preserve their binders.

Replaced proof terms of `fiberFiniteType`, `fiberQuasiCompact`, `overPullFiniteType`,
`overPullQuasiCompact` by direct `MorphismProperty.pullback_snd` applications, and
`fiberOver` by its explicit `Over.w` equation. Profiling found an approximately
21-second instance search in the old `fiberFiniteType` proof; direct base change
avoids that search. These proposition-valued instances retain their signatures.

## Proved and sorry left

Closed one of the two original holes:
`WeilConjectures.ZlOpenUnit.rationalAlpha_natural`.
Added zero holes; split off zero statements.

The only remaining hole in the delivered module is
`WeilConjectures.ZlOpenUnit.openWeilUnitAndEmptyFibre`
(blueprint: `lem-zl-open-weil-unit-and-empty-fibre`). Its statement and complete
seven-step proof docstring are unchanged. This is a partial proof of a module
with several holes, as permitted by the brief.

Validation: the complete rebased module compiled cleanly through `lcompile.py`
in 43.6 seconds, below the 60-second limit. Final delivery preflight follows.

## No longer needed

None. All existing imports remain necessary for the public definitions and
statements. No dependency, node, or module is pruned. The existing DAG plan
continues to describe the remaining main theorem; no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The latest blueprint places
`lem-zl-morphism-open-closed-reduction.proof.md` under
`sec-deligne-laumon-general/sk-prop-wgen-relative-line/`; the node retains a
historical `sk-l-dl-general-excision/` path. The latest Part 2 extension-by-zero
sentence was read. A useful rational-compositor and return-comparison naturality
proof already exists privately in `LocalFrobeniusWeilMorphismNaturality`.
The earlier retained proof needed its cast simplification corrected and its
natural-isomorphism assembly replaced by an explicit arrow calculation to avoid
expensive definitional equality checks. The previous disk-space failure no longer
prevents the compiler from starting.

The current shared source includes the landed C6 independent-coefficient-universe
repair and typed scalar-transport wrappers. All those changes are preserved in
this packet; the retained sandbox predates them. No definition change or consumer
adaptation is part of this delivery. The new proof specializes to the
current signature without the former separatedness assumptions.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
