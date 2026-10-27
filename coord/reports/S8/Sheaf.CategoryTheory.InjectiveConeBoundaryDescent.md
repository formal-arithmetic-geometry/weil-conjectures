## What changed

Proved `CategoryTheory.Functor.exists_injectiveConeBoundaryDescent` in
`Sheaf.CategoryTheory.InjectiveConeBoundaryDescent`, retaining all existing public
signatures and definitions. Private helpers verify the cone differential and
negative projection, compare the cone roof with the snake boundary, prove the
positive cocycle-lift formula, and descend the roof through injective models.
All original public imports are retained; no imports were added or removed.
The K-injective Hom bijection supplies every derived morphism and proves
uniqueness up to homotopy. The explicit cone homotopy has diagonal components
`F(k)` and `-S(k)`; naturality cancels its cross terms.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.Functor.exists_injectiveConeBoundaryDescent`
(node `lem-pur-injective-cone-boundary-descent`). No holes added or split off.
No `sorry` remains in the delivered module. The complete file compiles without
errors or warnings through `lcompile.py` (19.4 seconds on the compile server).

## No longer needed

No DAG dependencies or modules are pruned. The proof follows the existing six
steps using the recorded Mathlib declarations and the already proved
`CategoryTheory.Functor.exists_injectiveBoundary`.

## Where the brief, the DAG or earlier work was wrong

None. The cone-to-snake comparison and elementwise positive lift formula are
already provided by Mathlib's `homologySequenceδ_triangleh` and `ShortExact.δ_apply`;
the proof uses these rather than repeating their diagram chases. The unit route
is retained. The static interface checker flags scoped `omit ... in` commands
on private helpers; the change record explains their scope and confirms that
no existing public declaration changes. See
`coord/changes/injective-cone-boundary-descent-private-helpers.md`.

## Second reading by S8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
