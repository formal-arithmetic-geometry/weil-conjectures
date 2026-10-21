## What changed

Proved `AlgebraicGeometry.effective_cartier_affine_dimension_drop` with its original
statement. A maximal ideal containing f has full height by the existing finite-type
domain localization theorem. Mathlib's principal quotient theorem for a regular element
in such a prime gives the equality immediately. Spectrum dimensions are converted to
ring dimensions by Mathlib. Replaced the proof-only import
`WeilConjectures.AlgebraicGeometry.Dimension` with
`Mathlib.RingTheory.KrullDimension.Regular`; preserved all public imports.
Updated the item's proof, proof dependencies and proof origin to this shorter argument.
No definitions, public interfaces, targets or source-library files changed.
Local parser checks confirm identical declaration signatures and public imports;
the import-direction check accepts the new Mathlib proof import.
The item compiles cleanly through lcompile.py (3.3 seconds, exit code 0).

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.effective_cartier_affine_dimension_drop`
(node `lem-sc-effective-cartier-affine-dimension-drop`). Added 0 holes; split off 0.
There are no remaining sorries in this delivery. The proof uses the project's existing
`finiteTypeDomain_ringKrullDim_localizationAtMaximal`; its proof dependencies remain
unchanged and are outside this delivery.

## No longer needed

Removed the proof-only import `WeilConjectures.AlgebraicGeometry.Dimension`.
The item no longer uses `lem-pc-scheme-dimension-local-rings`,
`lem-weil-pbc-dimension-quotient-nonzerodivisor`, `pqf-lem-locnoeth-lft`, or
`def-weil-finite-type-morphism` as proof dependencies. The ring-theoretic
Noetherianity theorem replaces the scheme-theoretic Noetherianity detour.
The Mathlib full-height principal quotient theorem replaces the local quotient
argument and subsequent supremum over local rings. Removed their obsolete
entries from the item's top-level `tool_uses`; retained the finite-type domain tool.
These nodes may still serve other users; no declaration or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement and existing dependency statements are correct.
The planned local-to-global argument was longer than necessary: Mathlib already
packages the needed two principal-ideal dimension inequalities for a full-height
prime. The unit's statement and route are preserved; only the proof of this
auxiliary affine dimension lemma changes.

## New nodes

`lem-sc-principal-quotient-dimension-full-height` is a Mathlib leaf attached directly
to `Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors`. It adds no Lean
module or hole. Its hypotheses and conclusion were checked against the installed
Mathlib source and semantic searches. A unit cannot belong to a proper prime, and
zero is excluded by regularity in a nontrivial ring; the zero-dimensional field
case has no admissible element and prime. The theorem also supports infinite
Krull dimension through WithBot ENat. No change record is needed for a proof-only
change with identical public imports and declaration signature.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
