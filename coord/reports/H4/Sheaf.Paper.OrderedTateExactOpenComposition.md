## What changed

Replaced the proof hole in `AlgebraicGeometry.Etale.orderedTateExactOpenComposition`
with ordered tensor induction. Private proved helpers establish normalized roots and
line composition, carry it through exact degree-zero and shift comparisons, and combine
the tensor factors. The exact-comparison calculations adapt the existing private
`LineComparisons` proof in `Sheaf.AlgebraicGeometry.SfP1ChartExchange`.
The final calculation conjugates the derived compositor by the exact comparison and
identifies it with `DegreeZeroMapGluing.openComp`. Public definitions, signatures and
public imports are unchanged. Only the assigned module and its own node are changed.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.orderedTateExactOpenComposition` (one original hole).
Added: none. Remaining: none. Split off: none.
Validation: the cleaned module passed a single-file server compile in 22.3 seconds.
`#print axioms AlgebraicGeometry.Etale.orderedTateExactOpenComposition` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`. The complete type/body traversal and axiom scan, with per-declaration diagnostics,
also passed in 23.7 seconds after the local caching adjustments. Local irreducibility of the sheaf and derived functor constructions
and reuse of the cached category instances keep the comparison calculations small.
Both original public declaration
signatures and the complete body of `orderedTateExactPullback` were checked unchanged.

## No longer needed

No original dependency was pruned. The three original declared dependencies remain needed. The proof additionally
uses the proved constant-unit composition and derived tensor composition equations.
No existing module or node is withdrawn. The unused proof import
`WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle` from the
initial draft was replaced by the generic derived-single comparison module actually used.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The existing finite-Tate-line comparison API assumes
positive N; this statement allows N = 0. The private generator-normalization argument
establishes the required composition equation without adding positivity, nonemptiness,
or assumptions on the coefficient ring. It applies to empty opens and degree zero.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
