## What changed

Proved `CategoryTheory.exactOpenClosedUnboundedCalculus` in
`Sheaf.CategoryTheory.ExactOpenClosedUnboundedCalculus`, without changing its signature.
The actual termwise adjunctions are localized with Mathlib `Adjunction.localization`;
its component lemmas give all four required equations with the specified factorization
isomorphisms. Componentwise invertibility and localization essential surjectivity prove
invertibility of the open unit and closed counit. Existing exact-derived cohomology
comparisons prove the mixed zero statements. A diagram of the assumed short exact rows,
the short five lemma, and the unbounded cohomology criterion prove joint reflection.
The support unit follows from joint reflection and the triangle identity. The explicit
inverse on Hom sets is the unit, followed by the image of the given morphism, followed
by the inverse unit; naturality and the closed triangle identity prove both inverse laws.

Added two completely proved private helpers for invertibility after localization and
vanishing of mixed derived composites. Replaced the proof import of
`Sheaf.SixFunctors.OpenTensorNormalizationData` with
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` for its existing
proved cohomology comparison and zero-object criterion. Updated the node proof to match.
All existing public imports, declarations, signatures, and docstrings are preserved.

Validation: the final module compiles through `lcompile.py` without warnings. Import-cycle
checking accepts the new private import. Read the cited blueprint proof (2) and the local
Stacks statements for exact descent, localization, exact functors, the five lemma and the
unbounded derived category. The proof never uses boundedness or resolutions.

## Proved and sorry left

Closed one hole: `CategoryTheory.exactOpenClosedUnboundedCalculus`
(node `lem-sfb-exact-open-closed-unbounded-calculus`).
Zero holes remain in the item; zero holes added; zero statements split off.
Both private helpers are proved, and no definitions or instances were changed.

## No longer needed

Removed proof import `Sheaf.SixFunctors.OpenTensorNormalizationData` and the dependency
`def-weil-exact-derived-adjunction` from this node's proof dependencies: its specialized
wrapper is unnecessary because Mathlib's localization construction supplies precisely
the same specified maps with independent category universes.

Removed redundant private imports
`Mathlib.Algebra.Homology.DerivedCategory.HomologySequence` and
`Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`: the required facts are already
available through the retained imports and the new exact-derived comparison import.
Their corresponding mathematical dependencies remain used and remain in the DAG.
No other declared proof dependency is pruned. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The attached `exactDerivedAdjunction` wrapper uses common object, morphism and localization
universes, whereas this item allows independent universes. Its underlying Mathlib
construction works directly, so no interface repair or consumer adaptation is needed.
The mathematical argument of the node is valid and is now fully formalized.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
