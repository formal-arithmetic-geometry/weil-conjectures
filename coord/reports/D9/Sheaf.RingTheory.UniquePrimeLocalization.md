## What changed

Filled `IsLocalization.uniquePrimeLocalization` without changing its signature or any existing
public definition. The proof follows Stacks Algebra Tags 00EA and 00DK. Going-up and a maximal
ideal argument show that each denominator outside q divides an element in the image of
A minus p. The resulting cofinality proves the ring comparison and identifies module
localization with scalar base change. Tensor symmetry gives the specified canonical action;
the fraction formula proves naturality by tensor induction. All new helpers are private.

Validation: the module compiles in 5.3 seconds without errors or warnings. The original
public definitions and theorem signature are unchanged; the file contains zero sorries.

Updated `lem-trf-unique-prime-localization` to record the denominator argument and the actual
Mathlib APIs used. No consumer adaptation or interface change is needed.

## Proved and sorry left

Closed 1 hole: `IsLocalization.uniquePrimeLocalization`
(blueprint: `lem-trf-unique-prime-localization`). Added 0 holes; split off 0 statements.
There are no remaining sorries in the delivery.

## No longer needed

The proof does not need `lem-weil-pbc-localization-prime-residue-field-iso` or the proof import
`WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso`. It uses the localization unit
criterion and uniqueness directly, so no residue-field or iterated-localization comparison
is needed. Removed that node from `proof_deps` and its obsolete `tool_uses` entry.
No module is withdrawn: the source theorem remains available to its other consumers.

Replaced the explicit proof import `Mathlib.RingTheory.Ideal.Maximal` with
`Mathlib.RingTheory.Ideal.Nonunits`, whose maximal-ideal corollary is used in the proof.
The node `lem-weil-pbc-proper-ideal-contained-in-maximal` remains a dependency through that
Mathlib corollary. All other declared mathematical dependencies remain needed.

## Where the brief, the DAG or earlier work was wrong

No statement correction was necessary. The planned residue-field comparison was stronger than
the proof needs. Denominator cofinality handles the ring and module comparisons directly.
The explicitly selected localized-module action needs a local SMul instance because Lean's
default quotient scalar action is a different instance. The original definitions are preserved.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
