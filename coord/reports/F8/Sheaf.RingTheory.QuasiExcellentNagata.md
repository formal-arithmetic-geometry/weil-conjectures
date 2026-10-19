## What changed

Proved `isNagataRing_of_isQuasiExcellent` in
`Sheaf.RingTheory.QuasiExcellentNagata`, with its signature unchanged.
For each finite type domain algebra, the proof chooses a nonzero regular principal
open using the spectrum basis, transports regularity across Mathlib's iterated
localization equivalence, and applies the existing normality theorem. Regularity
of each maximal-local completion makes it reduced, giving local N-1 and then
global N-1. The universally Japanese criterion and prime quotients finish Nagata.
The argument follows the local Stacks source, More on Algebra Tag 07QV.
Updated the existing node's proof, dependencies and proof origin to match Lean.
Added only a proof import of `Mathlib.RingTheory.Localization.LocalizationLocalization`.
No definitions, statements, public imports, consumers or new modules changed.

## Proved and sorry left

Closed 1 of 1 holes: `isNagataRing_of_isQuasiExcellent`
(node `lem-exc-quasi-excellent-nagata`). Added 0 holes; split off 0 theorems.
There are no remaining `sorry`s in the delivered module.
The existing supporting declarations are used as the stage-3 brief requires;
this does not claim their transitive dependencies are all sorry-free.

## No longer needed

Removed proof imports:

- `Mathlib.AlgebraicGeometry.Scheme`: only the prime spectrum topology is used.
- `Mathlib.RingTheory.Localization.Away.Basic`: supplied by the local N-1 criterion.
- `Sheaf.RingTheory.AdicCompletionNoetherian`: retired compatibility module;
  the proof uses the already imported source-root completion theorem.
- `Mathlib.RingTheory.AdicCompletion.Algebra`: public through `ExcellentRing`/`GRing`.
- `Mathlib.RingTheory.Noetherian.Defs`: supplied by the statement imports.
- `WeilConjectures.RingTheory.AnalyticallyUnramified`: the N-1 lemma publicly imports the definition.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: no scheme-level regularity is used;
  the ring clause of `def-weil-regular-scheme` is Mathlib's `IsRegularRing`.
- `Sheaf.RingTheory.GRing`: public through `ExcellentRing`.

The proof no longer uses node
`lem-weil-pbc-spec-irreducible-closed-subsets-primes`: the basic-open basis
finds the required principal neighbourhood directly. Its proof-dependency edge
was removed. All other original proof-dependency nodes remain used.
The local-ring identification now cites the existing Mathlib leaf
`lem-weil-pbc-localization-of-localization` explicitly.
No claim that these shared modules can be withdrawn from other consumers.

## Where the brief, the DAG or earlier work was wrong

The main plan and statement are correct. The fraction-map construction in step 3
is already Mathlib's `IsLocalization.localizationLocalizationAtPrimeIsoLocalization`.
The explicit closed-complement ideal in step 2 is unnecessary because Mathlib
already supplies the basic-open basis. No change to the unit route.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
