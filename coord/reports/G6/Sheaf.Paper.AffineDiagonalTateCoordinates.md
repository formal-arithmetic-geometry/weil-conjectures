## What changed

Filled all three theorem proofs in `Sheaf.Paper.AffineDiagonalTateCoordinates` without
changing any declaration signature, definition body, attribute, or public import.
Added private proof imports of `Sheaf.AlgebraicGeometry.FiniteEtaleTateLinePullback`
(with `import all` to use its proved scalar-extension Hom equivalence) and
`WeilConjectures.AlgebraicGeometry.Curve.KummerTransition`.

`projectionRootTransition_existsUnique` obtains existence from the stated exponent-transition
clause of `finite_tate_site_descent`. Its uniqueness proof uses the scalar-extension and
sheafification adjunctions: maps agree if they agree on `1 tensor z`. The existing
`rootsOfUnityPowMap` supplies the smaller root, and its kernel-inclusion equation supplies
the normalization hypothesis. Thus uniqueness requires no additional comparison-square
assumption. The two endpoint-transport results choose their literal raw isomorphisms;
these have definitionally equal endpoint types, so `HEq.rfl` gives existence and
`eq_of_heq` gives uniqueness.

Updated the existing coordinate node's proof, proof dependencies, and proof origin to
record this argument. The unit route is preserved; these are only coefficient coordinate
identifications, independent of either purity orientation. The proof includes n=0 (positive
coefficient level one), the empty scheme, and arbitrary ramification without a divisibility
condition.

Searches ran through the launcher: LeanFinder for normalized finite Tate root transitions,
Loogle for `HEq, ExistsUnique`, and grep for `IsFiniteTateEtaleTransition` and generator
extensionality. No Mathlib result replaces the existing project descent theorem. Repository
search located the existing Hom equivalence and root-power map, which the proof reuses.

## Proved and sorry left

Closed three of three holes, all in namespace `WeilConjectures.PurityFiniteSetting`:

- `projectionRootTransition_existsUnique`.
- `projectionLineIso_existsUnique`.
- `projectionDiagonalUnit_existsUnique`.

No holes remain in the item, no holes were added, and no statements were split off.
The complete module compiled cleanly through `lcompile.py` in 31.4 seconds.
The root-transition proof uses already stated library dependencies, including
`AffineLinePurity.primeUnit` and `finite_tate_site_descent`; their remaining dependency
proofs are outside this delivery. This is a proof from existing declarations.

## No longer needed

None. All existing public imports are retained because they supply the published interface.
No modules or nodes are withdrawn. The node previously had no numbered proof steps or
proof dependencies to prune. No intermediate statements or modules were introduced.

## Where the brief, the DAG or earlier work was wrong

The coordinate node had no proof steps despite its three named theorem obligations.
Those steps are now recorded. The descent theorem's uniqueness clause includes a
comparison square as well as the root formula; it cannot alone establish uniqueness
for this item's weaker predicate. The generator argument explicitly fills that gap.
No statement correction or definition repair was needed.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
