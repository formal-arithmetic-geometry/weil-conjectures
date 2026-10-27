## What changed

Proved `CategoryTheory.Functor.additive_exact_finite_preservation_of_conservative_square`
in `Sheaf.CategoryTheory.ExactConservativeSquareFinitePreservation` without changing
its signature or its public imports. Transport additivity along `eta.symm` and
reflect it through the faithful additive functor `q`. Map a short exact complex
through `p` and `L`, transport it back along `S.mapNatIso eta.symm`, and use
Mathlib's `CategoryTheory.ShortExact.reflects_shortExact_of_faithful q`.
Finally `(H.exact_tfae.out 0 3).mp` gives finite limit and colimit preservation.

Replaced the private import `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
with `Mathlib.CategoryTheory.Abelian.ShortExact`, which supplies reflection of
short exactness. Updated the existing node's proof and proof origin to match.
The unchanged hypothesis `hq` is unnecessary for this shorter proof, so the
unused-variable linter is disabled locally for this theorem only.

The remote single-file compiler accepts the final file without warnings.
A separate `#print axioms` check reports only `propext`, `Classical.choice`, and
`Quot.sound`. All eight category/object/morphism universes stay independent.

## Proved and sorry left

Closed one of one original holes:
`CategoryTheory.Functor.additive_exact_finite_preservation_of_conservative_square`
(node `lem-sf-exact-conservative-square-finite-preservation`).
Zero holes remain; zero holes added; zero statements split off.

## No longer needed

Removed the direct private import
`Mathlib.Algebra.Homology.ShortComplex.PreservesHomology` (still available
transitively through `ExactFunctor`). The explicit image-to-kernel comparison,
its preservation under `q`, and the conservativity argument of the original
plan are unnecessary: Mathlib already reflects short exactness through faithful
zero-preserving functors between abelian categories. The hypothesis `hq` and
`q.ReflectsIsomorphisms` are retained unchanged but are unnecessary.

No entire declared dependency node or project module is pruned. In particular
`lem-sp-exact-functor-preserves-homology` remains used through its recorded
`exact_tfae` equivalence, and all five definition dependencies still describe the
notions used by the proof. No unit statement or step is bypassed; the unit's
`realized` record does not assign this auxiliary node a unit-level step.

## Where the brief, the DAG or earlier work was wrong

The six-step docstring and original DAG proof plan are valid but longer than
necessary. Mathlib's faithful reflection theorem removes the need to construct
and transport the image-to-kernel comparison. The statement remains exactly as
assigned, including its stronger hypotheses. The DAG now records the shorter
proof; the existing docstring is retained as the original proof plan.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
