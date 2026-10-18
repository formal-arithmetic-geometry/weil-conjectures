## What changed

Proved `AlgebraicGeometry.Etale.derivedMapRestriction_laws` in
`Sheaf.AlgebraicGeometry.EtaleDerivedMapPresheaves`, following its existing docstring:
lift the identity and associativity coherence of etale pullback to derived categories,
then cancel the comparisons in the conjugation formulas. The isomorphism laws follow
from the morphism laws by `Iso.ext`.

Added the proof-only import `WeilConjectures.SixFunctors.BaseChange.Pasting` for
`upperStarComp_assoc'` and the underived unit coherence. The private helpers prove
the localization calculations for arbitrary exact functors and then specialize to
arbitrary coefficient categories before using `ModuleCat B`. This avoids the expensive
kernel reductions encountered when defining the same comparisons directly for module
coefficients. All helper definitions are explicit constructions and all helper lemmas
are proved. Existing public statements and definition bodies are unchanged.

The complete module compiled through `lcompile.py` in 8.4 seconds. The unchanged
consumer compiled against it in 6.4 seconds; both are within the single-file limit.
No consumer adaptation or definition change is needed. The unchanged consumer
`Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy` is also checked against
the proved module. The local proof-support commands are documented in
`coord/changes/E1-etale-derived-map-private-coherence.md`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.derivedMapRestriction_laws`
(node `def-weil-pbc-etale-derived-map-presheaves`). This proves all four conjuncts,
for identity and composite restriction of both morphisms and isomorphisms.

Added holes: 0. Remaining holes in the delivered module: 0.
`#print axioms AlgebraicGeometry.Etale.derivedMapRestriction_laws` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.
No theorem is split off and no new module is added.

## No longer needed

None. No imports were removed. The node has no declared proof dependencies or proof-step
uses to prune. The two original public imports are retained, and the added private import
is used for pullback coherence. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The node's JSON proof array is empty; the module's existing theorem docstring supplies
the identity/coherence argument, which this proof follows. No change to that route,
public statement, or definition was necessary. The existing source library provides the
underived coherence and the localization characterizations needed to prove the derived
coherence without new obligations.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
