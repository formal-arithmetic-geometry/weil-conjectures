## What changed

Filled `AlgebraicGeometry.ProEtale.BoundedSiteConjugates.boundedSiteCompositorConjugates`
using private proved helpers for the word Hom bijections, the boundary comparison, and
induction on the pasted diagram. The definitions and the public theorem statement are
unchanged. The node proof, proof dependencies, and proof origin were updated to match
the explicit calculations. The proof checks the full pasting assertion, including both kinds of
whiskering, vertical composition, identity words, associators, and unitors.

The etale argument first proves a transpose formula for an arbitrary arrow following
the pasted map, then specializes it to the target-word counit. The site argument
compares the entire conjugate using the actual left site-coherence square. A separate
induction compares the recursively pasted right arrows; cancellation of the invertible
target comparison gives equality with the entire pro-etale conjugate.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.BoundedSiteConjugates.boundedSiteCompositorConjugates`
(1 of 1 original holes). Added: none. Remaining in delivered modules: none.
All helpers are private and proved; no new public theorem or module is introduced.
The final module compiled through `lcompile.py` with exit code 0 and no warnings.

## No longer needed

Removed imports:

- `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`: the definitions retain their explicit
  chosen etale adjoints; none of this module's declarations is used.
- `Mathlib.CategoryTheory.Adjunction.Mates`: the needed pasting laws are proved directly
  from source/target naturality of the recursive Hom bijections. No generic mate theorem
  or conjugate equivalence is invoked.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: the supplied
  `Stage.dimension` and `Stage.dimension_le` already retain the finite bound.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: no local-dimension construction is
  used; the underlying `topologicalKrullDim` definition comes from the transpose module.

Removed proof dependencies `lem-kun-dimension-finite-type`, `def-kun-dimension`,
`def-kun-topological-krull-dimension`, `def-weil-pbc-adjunction-conjugate`, and
`lem-weil-pbc-mate-pasting`. The topological-dimension declaration remains needed by the
unchanged `Stage` statement, and the ordinary conjugate remains the semantic description
of the unchanged definitions. Only the unused proof edges were removed; all existing
statement dependencies are retained. The updated
node records the explicit Hom calculations actually used. No module is withdrawn; this
delivery does not delete or alter anything in the adopted source tree.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed. The primitive boundary comparison includes the
bounded-to-ambient etale compact-support compatibility isomorphism; it must be included
when comparing `Word.homEquiv` with the published bounded-origin transpose.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
