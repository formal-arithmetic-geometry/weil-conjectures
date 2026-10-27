## What changed

Proved `AlgebraicGeometry.Etale.etaleGraphFromOpen_baseChange` by pasting the
specified proper/open exchange cube along the explicit product graph construction.
Private exchange-word and compatible-isomorphism helpers keep track of associators,
inverses, and horizontal composition. Pullback universal properties construct the
base changes of both graph neighborhoods and their intersection.

The proof uses the existing `sfExactExchangePasting` composition equations and the
Cartesian normalization of `etaleProperOpenExchangeCube`. The identity normalization
for open extension is identified with the actual derived identity comparison by
adjunction conjugacy. No public signatures, definitions, or public imports change.

Validation: the complete module compiled through `lcompile.py` in 22.8 seconds.
The original theorem signature and public imports were checked byte-for-byte.
The module contains zero `sorry` tokens; no new modules or nodes were introduced.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.etaleGraphFromOpen_baseChange` (one original hole).
Added: none. Remaining holes in the delivered module: none.

## No longer needed

No modules are withdrawn and no existing imports are removed. The proof uses the
existing exact-exchange-pasting API instead of separately rebuilding the direct-image
and open-extension compositor coherence proofs. The old node dependencies
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`,
`lem-sfb-ringed-derived-monoidal-comparisons`,
`lem-kun-derived-pullback-composition-monoidal`,
`lem-cbc-extension-zero-composition`, and
`lem-weil-pbc-extension-by-zero-exact` are therefore not separate steps of this proof;
their interfaces remain available through the imported library. They are not claimed
to be globally prunable.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface repair was required. The planned cube argument
works. Its composition-coherence steps are already packaged by
`sfExactExchangePasting`; the node proof is updated to record that API and the
explicit pullback construction used here.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
