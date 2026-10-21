## What changed

Filled the three theorem proofs in
`lean/Sheaf/CategoryTheory/KInjectiveFiberTriangleComparison.lean`, retaining every public
signature and definition. Added proved private helpers for universal extensions, K-injective
cone closure, cone-map isomorphisms and naturality, and inverse-unit naturality.

The shift isomorphism comes from uniqueness of Kan extensions and transport along shift
equivalences. Its factorization equation is the normalization for every complex; hom-ext
proves uniqueness. K-injective cone closure follows from Mathlib's triangulated right
orthogonal to acyclic complexes. The triangle comparison is the inverse of the triangle map
with components eta, followed by the localized canonical chain comparison. Its connecting
square uses the stated normalization, with both localization shift comparisons explicit.
Naturality follows from the two cone coordinates and naturality of eta.

Replaced the private proof import of `Sheaf.CategoryTheory.KInjectiveTotalDerived` by
`Mathlib.CategoryTheory.Functor.KanExtension.Basic`. Updated the item's DAG proof,
proof dependencies and proof origin to match these arguments. No consumer adaptation or
change record is necessary: all public interfaces and the fixed unit route are preserved.

## Proved and sorry left

Closed all three original holes:

- `CategoryTheory.existsUnique_unitNormalizedKInjectiveShift`.
- `CategoryTheory.kInjectiveFiberTriangle_comparison`.
- `CategoryTheory.kInjectiveFiberTriangle_comparison_naturality`.

No holes added, no split-off statements, and no `sorry` remains in the delivery.
Compilation and axiom verification are recorded by the delivery checks.

## No longer needed

Removed the proof import `Sheaf.CategoryTheory.KInjectiveTotalDerived`. The proof does not
use `lem-weil-pbc-kinjective-total-derived` or `lem-weil-pbc-kinjective-hom-derived`:
the universal unit and its computing-object isomorphisms are already hypotheses, and
Kan-extension uniqueness constructs the shift without Hom lifts or replacements.
These two nodes were removed from this node's `proof_deps` and proof-step `uses`.
Their declarations remain available to other consumers; no module is withdrawn.

The remaining planned dependencies (the abstract derived category, additive functors,
triangulated categories and K-injective shifts) are used. No other module or node is
claimed to be globally pruned. The unit's own statement and proof steps remain intact.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The DAG's representative-and-Hom-lifting construction of
the normalized shift is unnecessary once the full natural-transformation universal
property is a hypothesis. The abstract Kan-extension proof is shorter. The explicit
componentwise null-homotopy for cone closure can also be replaced by Mathlib's
right-orthogonal closure, which follows the homological-functor proof of Stacks Tag 090X.

Read Stacks `derived.tex`, `lemma-triangle-K-injective` (090X) and
`lemma-derived-shift` (05SU), the item's full node and all six declared dependency records,
their Lean signatures, and the proper-base-change unit record and current blueprint.
Searched Mathlib with LeanFinder, Loogle and grep, and both project library roots with rg.
No additional hypothesis (in particular exactness of G) is used. All constructions remain
valid for zero objects, zero endomorphisms, identity endomorphisms and the zero functor;
no proof step cancels an endomorphism or a non-computing component of eta.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
