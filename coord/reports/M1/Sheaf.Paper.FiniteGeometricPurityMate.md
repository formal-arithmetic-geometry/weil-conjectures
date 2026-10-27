## What changed

Changed only `lean/Sheaf/Paper/FiniteGeometricPurityMate.lean` and its existing DAG node
`lem-pur-finite-geometric-purity-mate`. All public signatures and all existing definitions are
unchanged. No source-library file is modified.

The geometric fiber and morphism properties now use Mathlib's base-change API. Retagging
uses the ring-equivalence isomorphism and the second Galois projection equation. The
Cartesian assertion is the existing Frobenius square; the retained constructions agree
definitionally in the fixed presentation. Fixed-coordinate purity invertibility follows
by reflecting the published smooth-purity isomorphism and cancelling reassociation.

Added private proof imports of `Sheaf.Paper.PullbackTorAmplitude`,
`Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`, and
`Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`. The first proves preservation of the
input class along the retagged Frobenius morphism, with canonical realization comparisons.
The second supplies bounded etale-origin witnesses, and the third supplies isomorphism
closure of intrinsic bounded constructibility. Exact pullback preserves those
witnesses. The published compact-support base-change theorem and the existing
compactification comparison prove invertibility of the actual specified B. Finally the
published bounded-class Hom equivalence constructs the mate from inv(B) followed by the
pulled-back counit, and its inverse formula and injectivity prove existence and uniqueness.
Every new private helper is completely proved.

The existing DAG retains its still-open purity-factor argument and records these proved
prerequisites and their additional declared proof dependencies. The six-operations unit
route is unchanged. The scoped unused-section-variable linter setting on
`geometricPurityMapProperties` preserves its original, stronger list of domain binders
while allowing its proof to use only relative base change.

## Proved and sorry left

Closed eight of the ten original holes, with no holes added and no split-off statements.
The proved declarations in `WeilConjectures.PurityFiniteSetting` are:

- `geometricPurityFiberProperties`
- `geometricPurityMapProperties`
- `geometricPurityMapIsIso`
- `geometricPurityRetagProperties`
- `geometricPurityRetagging`
- `geometricPurityInput`
- `geometricPurityBIsIso`
- `existsUnique_geometricPurityMate`

The two remaining sorries are unchanged named statements, both attached to
`lem-pur-finite-geometric-purity-mate`:

- `WeilConjectures.PurityFiniteSetting.existsUnique_geometricPuritySource`
- `WeilConjectures.PurityFiniteSetting.finiteGeometricPurityMate`

The remaining work is independence of the root-chart source comparison, and comparison
of the normalized orientation and tensor-purity base-change factors with that source
comparison and the specified counit mate. The inverse-purity formula then follows by
cancelling the now-proved invertible geometric purity map.

## No longer needed

No modules, imports, or DAG dependencies are withdrawn. All existing public imports are
retained for the existing interface. The proof import of finite smooth purity is used.
The original purity-factor dependencies remain for the two unfinished assertions.

For the proved mate construction, an additional assertion that the exceptional image
has finite Tor amplitude is unnecessary: its bounded-below etale origin, as supplied by
the published exceptional-image theorem, suffices for both compact-support exchange and
the Hom equivalence. This is a local simplification and does not withdraw the general
exceptional-preservation results from the library.

## Where the brief, the DAG or earlier work was wrong

No statement is changed or disputed. The fixed-scalar retagging assertions are
stronger in presentation than their informal explanation suggests: their underlying
constructions are definitionally equal, so no new right-adjoint or orientation transport
lemma is needed to prove `geometricPurityRetagging`. The mate's domain can also be
verified with bounded-below etale-origin witnesses, as explained above.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
