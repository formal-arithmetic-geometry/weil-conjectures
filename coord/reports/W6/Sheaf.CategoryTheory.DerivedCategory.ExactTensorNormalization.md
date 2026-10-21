## What changed

Proved `CategoryTheory.Functor.exactDerivedTensorComparison_normalization` without changing its
statement or the explicit definition `exactDerivedTensorUnitIso`.

The proof uses the existing source-library `OplaxMonoidal.ofLaxSquare`, restricted to the monoidal
full subcategory of native K-flat complexes. On this subcategory the assumed model normalization
is exactly its compatibility hypothesis. Functorial flat resolutions supply every derived
object with a K-flat representative. The native localization tensorator is invertible on these
representatives, and naturality transfers invertibility of the prescribed tensor comparison to
all derived objects. Expanding the native unit model identifies the induced unit with the
prescribed composite, including its orientation. `CoreMonoidal.ofOplaxMonoidal` gives the strong
structure with precisely the required maps. The proof uses no braiding compatibility for F.

Added proved private interface lemmas and one private proof import:
`WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare`.
Updated the item's DAG proof and proof origin to describe this implementation.
Elaboration transparency options are scoped to individual proofs; no public API is changed.

Searches: LeanFinder found the exact-derived factorization API and monoidal localization
constructors; Loogle found `CoreMonoidal.mk'`; local source searches found the more directly
applicable `OplaxMonoidal.ofLaxSquare` and the native K-flat model/counit API. No new public intermediate
statement was required. Read the source's complete square proof and Stacks
`sites-cohomology.tex`, `lemma-symmetric-monoidal-cat-complexes` and
`lemma-symmetric-monoidal-derived` (Tags 0FPQ and 0FPT). These Stacks results concern ringed sites
and omit the diagrams; the abstract cross-functor argument is the existing source-library proof.

## Proved and sorry left

Closed one hole: `CategoryTheory.Functor.exactDerivedTensorComparison_normalization`
(node `lem-sfb-exact-tensor-functor-derived-normalization`).
Added zero holes; split off zero statements. No `sorry` remains in the item.
`exactDerivedTensorUnitIso` retains its original explicit construction.
The server compile completed in 33.3 seconds; the theorem uses exactly `propext`,
`Classical.choice`, and `Quot.sound`. Removed the redundant `change` noted by its linter
before the final delivery compile and probe.

## No longer needed

Removed redundant private imports `Mathlib.CategoryTheory.Adjunction.Limits` and
`WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal`; their APIs remain
available from the retained public dependencies. No mathematical dependency or node is withdrawn.
All declared DAG proof dependencies are used.
The generic square construction supplies the planned coherence calculations and transport to
arbitrary objects. No blueprint unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was necessary. The stated hypotheses and all independent
universes are preserved. The original diagram plan is realized using an existing proved generic
square theorem instead of repeating its diagram calculations.

## New nodes

`lem-sfb-oplax-monoidal-of-lax-square` attaches the already proved source-library construction
`CategoryTheory.Functor.OplaxMonoidal.ofLaxSquare`, used for the three coherence equations.
It creates no Lean module, declaration or hole. Its complete cancellation proof is recorded
from the existing source, and its hypotheses apply on the K-flat monoidal full subcategory.
The identity square recovers the original oplax maps; an empty model class cannot satisfy
the representation premise because a monoidal target contains its unit. The argument needs
only lax structure on the source localization, and uses no symmetry of the functor.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
