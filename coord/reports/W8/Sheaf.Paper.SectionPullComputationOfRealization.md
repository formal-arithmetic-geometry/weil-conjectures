## What changed

Replaced the proof of `section_pull_computation_of_realization` by a computation-square
pasting argument, preserving its statement and its public import. The endpoint scalar
computation is first extended from flat-term K-flat complexes to all internal complexes.
The ordinary square is identified by scalar units and conjugate adjunctions. The main
proof then pastes the two scalar and two geometric computation squares, substitutes the
supplied realization equation, and uses faithfulness of precomposition by the termwise
section equivalence. Its conclusion actually holds on every section complex, so the
original flatness hypotheses can be ignored without changing the statement.

Added the two proof imports `SectionScalarComputationAll` and
`SectionOrdinaryPullCompatibility`, and the existing
`SectionDerivedPushpullNormalization`. The two new modules publicly import only the
normalization data needed by their statements. Their other imports are private proof
imports. All helper data are explicit constructions; no existing definitions or
statement signatures are changed. No source-library file is changed.

The categorical calculation uses a generic pasting proof and a constructor that
fixes the cochain and localization interfaces before inserting the sheaf functors.
Explicit component lemmas keep cochain and localization comparison interfaces fixed,
avoiding repeated expansion of the underlying sheaf and derived functors.
A small private structure groups each category's abelian and localization data.
The cochain constructor reads these structures from the supplied derived functors
and shares the resulting pairs, retaining their specified choices.
Lifted ordinary squares are constructed using both canonical cochain composition
isomorphisms, so their interfaces use iterated functors explicitly.

The new endpoint lemma reuses the proved unbounded K-flat resolution
`lem-pc-kflat-resolution` and the existing tensor presentation
`def-pur-site-sheaf-tensor-presentation-data` as tools. The ordinary calculation reuses
`lem-sfb-equivalence-square-inverse-mate-coherence` and the defining unique-choice mate
equation of the upper comparison in `lem-sfb-internal-module-operations-transport`. These generic tools supply the
resolution and adjunction identities needed here; the assigned unit route is preserved.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.QuotientChange.section_pull_computation_of_realization`.
No holes are added or left in the three delivered modules. Both new lemmas,
`AlgebraicGeometry.ProEtale.QuotientChange.section_scalar_computation_all` and
`AlgebraicGeometry.ProEtale.QuotientChange.section_ordinary_pull_compatibility`,
are fully proved. This is a proof, not a decomposition into further obligations.

All three proofs passed server compilation through `lcompile.py`; the main file
compiled and exported in 57.8 seconds with profiling enabled and Lean's
default asynchronous elaboration. Profiling options
have been removed. The delivery tool recompiles the final packet, checks the
per-file time limit, and checks its DAG records.

## No longer needed

No original import is removed: the original normalization-data import is needed by the
unchanged statement. No existing module is withdrawn or claimed globally unnecessary.

The original proof plan's preservation of K-flatness and flat terms under geometric
pullback is unnecessary. Resolving the section image and cancelling the localized
augmentation extends scalar counit compatibility to every complex before pasting.
Thus no preservation lemma, node, module, or import for that subargument is introduced.

The existence theorem `lem-sfb-internal-section-scalar-adjunction` is not invoked:
the supplied comparison's generator equation and the scalar pair's specified unit
already determine its ordinary mate. Its module remains publicly imported by the
normalization data for the definitions used in the statement. The geometric transport
and derived normalization dependencies remain needed, through the ordinary helper and
the main computation respectively.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was needed. The DAG's geometric preservation
subargument was avoidable: naturality along a K-flat resolution gives the required
endpoint scalar identity without any assertion about pullback preserving K-flatness.
The updated proof steps and dependencies record that route.

## New nodes

`lem-sfb-section-scalar-computation-all`, realized by
`AlgebraicGeometry.ProEtale.QuotientChange.section_scalar_computation_all` in
`Sheaf.Paper.SectionScalarComputationAll`, is a unary endpoint computation lemma.
Its resolution argument uses the termwise section equivalence, transfers flatness and
K-flatness along its counit isomorphism, and cancels the localized augmentation by
naturality. It makes no geometric pullback assertion. The argument applies to
unbounded complexes, zero coefficient rings, and empty schemes.

`lem-sfb-section-ordinary-pull-compatibility`, realized by
`section_ordinary_pull_compatibility` in
`Sheaf.Paper.SectionOrdinaryPullCompatibility` and the same namespace, is the ordinary
adjunction square only. It has no internal derived comparison b, section derived
comparison d, realization equation, or complex-computation conclusion. The scalar
unit is identified at coefficient 1, the right rectangle is checked on sections,
and the existing adjunction-compositor theorem identifies the left rectangle.
No nonzero or flat-coefficient hypothesis is used. Neither new node restates the
assigned computation theorem. No change records are required.

## Second reading by W8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
