## What changed

Proved `CategoryTheory.strictRoosShiftLocalization` with its signature unchanged.
The proof uses the existing coherent product shift and signed mapping cocone shift,
and identifies their concrete functor with `roosF`. Private proved helpers establish
both coordinate formulas, their inverse formulas, the degreewise limit comparison,
and compatibility of `roosι`. Mathlib's `Functor.commShiftOfLocalization` descends
through the prescribed `κ`; localization extensionality proves uniqueness, and
naturality of the `QA` shift gives the localized inclusion equation.

Added private proof imports of `Mathlib.CategoryTheory.Shift.Localization`,
`Sheaf.CategoryTheory.ProductCommShift`, and
`Sheaf.Algebra.Homology.SignedMappingCoconeShift`.
Updated the existing node's proof and dependency list to record these reused results.
All helper data are explicit constructions from limits, products, and isomorphisms.
The static command-visibility gate requires a change record for the proof namespace,
opens, local attributes and elaboration option; see
`coord/changes/strict-roos-shift-proof-environment.md`. There are no external Lean
importers or name users to adapt. Existing public signatures and imports are unchanged.

## Proved and sorry left

Closed 1 hole: `CategoryTheory.strictRoosShiftLocalization`
(node `lem-a1-strict-roos-shift-localization`). Added 0 holes. No `sorry` remains
in the item or is introduced elsewhere. This is a proof, with no decomposition.
The reused product and signed cocone modules contain no `sorry`.
The saved candidate previously passed a single-file compile in 10.8 seconds;
a fresh compile and delivery preflight are being run for this resumed session.
The existing theorem signature is byte-for-byte unchanged, and all lines meet
the width limit.

## No longer needed

Removed the redundant private import `Mathlib.CategoryTheory.Localization.Predicate`;
`Mathlib.CategoryTheory.Shift.Localization` supplies that API. Removed unused private
coordinate helpers from the interrupted working copy and its unused evaluation
adjunction import. No declared mathematical dependency or library module is pruned:
the original three dependencies remain used, with the two existing shift lemmas added.
No new split statements or modules are needed. The two reused shift lemmas are
proved generic tools from another unit; they supply product preservation and
signed cone coherence without bypassing this unit's route.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was necessary. The DAG's six-step argument is
implemented using the existing general coherent shift constructions instead of
repeating their naturality and zero/addition proofs. The saved working copy needed
the tower-limit hypothesis in its augmentation helpers and referred to a nonexistent
`roosι_fst`; that equation is now proved directly from the existing cocone lift API.
The inverse formulas follow by cancellation, including for negative or zero shifts;
no exactness of countable products is used. No target or public definition changes.
The resumed compiler check also found two final proof errors in the saved candidate:
the localized inclusion needed explicit reassociation, and the uniqueness proof
needed structure extensionality before unfolding the chosen localization shift.
Both are corrected in the delivered proof.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
