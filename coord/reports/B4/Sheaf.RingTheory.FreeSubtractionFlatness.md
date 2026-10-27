## What changed

Proved `Module.free_subtraction_flatness` in
`Sheaf.RingTheory.FreeSubtractionFlatness`, preserving its signature and public imports.
The proof applies the existing local generic-basis theorem after base localization,
with explicit transports of the fibre generic prime, generic stalk, residue field,
and basis map. Mathlib's maximal-localization injectivity criterion globalizes the
result over the base ring. Universal exactness of the localized quotient sequence
then proves the flatness equivalence using the existing flat-cokernel theorem and
the proved source-library flat-extension theorem.

All auxiliary lemmas are private and completely proved. The proof uses private
imports of `Sheaf.TraceFormula.LocalGenericBasisUniversalInjective`,
`Sheaf.RingTheory.UniversalInjectiveLocalization`,
`Sheaf.TraceFormula.LocalUIFlatCokernel`,
`WeilConjectures.Mathlib.RingTheory.Flat.Equalizer`, and Mathlib localization,
tensor, residue-field, and affine pullback APIs. Updated the existing node's proof,
proof dependencies, and proof origin to record this route. No statement or
definition changes, forced adaptations, or new nodes. The change record
`coord/changes/B4-free-subtraction-flatness-proof-environment.md` documents the
explicit universe, open, and option commands required by the private helpers;
preflight treats these commands as an interface change.

## Proved and sorry left

Closed 1 of 1 original holes: `Module.free_subtraction_flatness`
(`lem-trf-free-subtraction-flatness`). Added 0 holes; 0 `sorry` remain in the
delivered module. No intermediate open statements were split off.

The geometric local input remains an existing dependency, as intended by stage 3:
`RingHom.local_generic_basis_universal_injective` and
`RingHom.maximalIdeal_map_isPrime_of_geometricFibres`, together with its existing
universe-transport input, are supplied by the local generic-basis module. This
packet does not claim to prove those declarations. The localization and flat-cokernel
dependencies already have complete proofs in the shared library.

Compiled the complete item with the required server compiler. Checked the zero-rank
and zero-module cases: the proof uses finite products, tensor products, localization,
and exact quotients uniformly and requires no nonzero-rank hypothesis. The zero base
ring case is covered by Mathlib's maximal-localization criterion without choosing
a base prime. All tensor comparison squares are proved on generators; the final
universe restriction is proved by an explicit `ULift` equivalence.

## No longer needed

The proof does not use `lem-trf-universal-injective-check-stalks` or
`Sheaf.RingTheory.UniversalInjectiveCheckStalks`; removed this dependency from the
node and the exploratory proof import. Checking maximal localizations over the
base ring directly replaces the contracted-prime stalk comparison. This is a
pruning of this item's dependency only; no claim is made that other parents no
longer need that module, and no file is withdrawn.

No second application of the local generic-basis criterion at an arbitrary
A-prime is needed. Universal injectivity plus the localized quotient sequence
supplies the flatness equivalence. Removed the unused exploratory proof import
`Mathlib.RingTheory.Localization.Finiteness`. All original public imports remain.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The planned route works mathematically, but its
contracted-prime globalization and second generic-basis application are
unnecessary with the existing APIs. The revised node records the shorter route.
The unit's specified route is preserved: its free-subtraction assertion and its
local generic-basis input remain, with only the lower globalization and flatness
glue changed.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
