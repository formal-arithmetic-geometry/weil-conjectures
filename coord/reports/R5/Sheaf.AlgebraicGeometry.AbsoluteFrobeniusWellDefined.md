## What changed

Proved `AlgebraicGeometry.absoluteFrobenius_well_defined` in
`Sheaf.AlgebraicGeometry.AbsoluteFrobeniusWellDefined`, preserving its signature and
all existing imports. Added three proved private helpers: naturality of the scheme
Frobenius, its identification with `Spec.map` on an affine scheme, and the equality
between its n-th categorical power and the published n-th iterate.

The proof follows the existing node's nine steps. Prime-ideal inverse images use
`Ideal.IsPrime.pow_mem_iff_mem`; locality uses `isUnit_pow_iff`. Naturality is the
ring-map power identity. The affine calculation uses `ext_to_Spec` and naturality
of `Scheme.ΓSpecIso`. Stalks are computed on germs, restrictions are checked after
composition with the open immersion, and categorical iteration is proved by
induction. The same calculations include n = 0, zero rings and empty opens.

Searches already recorded in `searches.jsonl` found the prime-ideal power lemma
through Loogle; LeanFinder and grep did not find the entire multi-clause statement.
No definition, public signature or consumer was changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.absoluteFrobenius_well_defined`
(blueprint node `lem-weil-absolute-frobenius-well-defined`).

Holes added: 0. Holes remaining in the delivered module: 0. No result was split off.
All three private helpers are proved.

## No longer needed

None. No imports, dependency nodes or modules are removed. The proof uses all
five recorded proof dependencies through their existing interfaces, and retains
the original route. The private helpers implement the existing affine,
restriction and iteration steps rather than introducing additional assumptions.

## Where the brief, the DAG or earlier work was wrong

None. The theorem includes the categorical-power equality required by the earlier
statement review; this equality is proved, including its zeroth-iterate case.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
