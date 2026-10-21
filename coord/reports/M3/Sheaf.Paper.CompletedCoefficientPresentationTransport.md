## What changed

Implemented the normalized commutative coefficient lift, ordinary restriction round trip,
exact derived equivalence, bounded constructibility comparison, and scalar comparisons in
`Sheaf.Paper.CompletedCoefficientPresentationTransport`. The private restriction equivalence
uses identity maps on sections. A generic private tensor-comparison lemma keeps the
adjunction argument abstract over its ring sheaves, avoiding repeated unfolding of
the concrete completed-ring constructions. The scalar comparison is obtained from the normalized
extension/restriction adjunctions; its derived version is fixed by the universal tensor
counits and localization factors.

The completeness proof uses the separate unit-compatible completion Roos triangle in
`Sheaf.Paper.CompletedCoefficientCompletionRoosTransport`. It transports the triangle when
the unit is invertible; conversely, uniqueness of the third vertex of the rotated triangle
gives an isomorphism to a complete object. The existing sf/legacy comparison supplies the
slice predicate. The new theorem is a genuine comparison of completion objects before any
completeness condition is imposed.

All existing public signatures, docstrings and public imports are preserved. Two exactness
proof bindings in `purDerivedCoefficientRoundTrip` use `have` instead of reducible `letI`;
all data and maps of the definition are unchanged.
Additional imports are private proof imports. No consumer requires adaptation. Local proof
transparency commands are recorded in
`coord/changes/M3-completed-coefficient-proof-transparency.md`.

## Proved and sorry left

Seven original hole bodies are closed. Six are proved from existing declarations:

- `WeilConjectures.purCoefficientIso_existsUnique`.
- `WeilConjectures.purOrdinaryCoefficientRoundTrip_existsUnique`.
- `WeilConjectures.purDetailedTransport_isEquivalence`.
- `WeilConjectures.purCoefficientModel_bounded_predicate`.
- `WeilConjectures.purOrdinaryScalarModel_existsUnique`.
- `WeilConjectures.purScalarModel_existsUnique`.

`WeilConjectures.purCoefficientModel_predicates` is a decomposition through the new,
strictly separate completion-object comparison. Its Lean proof combining that comparison
with the rotated-triangle and legacy-predicate arguments is complete.

The only new hole is
`WeilConjectures.completedCoefficientCompletionRoosTransport`, node
`lem-pur-completed-coefficient-completion-roos-transport`. No hole remains in the item
module; none is introduced inside a definition or private declaration. Thus the packet
closes seven old hole bodies and adds one hole: six net closures and one decomposition.

The full item compiles through `lcompile.py` in 44.6 seconds, with no warnings or
errors. The new completion-comparison module also compiled through `lcompile.py`.

## No longer needed

None. No existing import, module, declaration or DAG dependency is withdrawn. The original
node had no proof steps or proof dependencies; its statement dependencies remain intact.
The unit statement and its route are preserved.

## Where the brief, the DAG or earlier work was wrong

The item node supplied no numbered proof plan (`proof` and `proof_deps` were empty).
Its coefficient and bounded interfaces are already stated in the landed integral
stratified-perfect characterization and are reused. That interface does not provide the
unit-compatible completion triangle for an arbitrary input. This missing comparison is
recorded separately, with the source's Koszul-to-quotient reconstruction route.

The generic pushforward-equivalence construction caused expensive reduction. The private
identity-on-sections restriction equivalence avoids that cost without changing the mathematical data of a public
definition or splitting the item module for compilation.

## New nodes

`lem-pur-completed-coefficient-completion-roos-transport` states the comparison of the actual
completion reflector, its unit and the canonical intrinsic quotient Roos triangle for any
derived input. Its source is Stacks 099M, 099N and 06YY, in the coefficient comparison of
Step 1 of `fix-prop-adjunctions`. Its full proof in words and dependency route are recorded in
the node and theorem docstring. The zero object, empty scheme and first positive quotient
use the same maps. All three required search kinds (LeanSearch, Loogle/LeanFinder and source grep) and
the blueprint ancestor search found no existing
statement with this normalization. The local proof-transparency change record above covers the command-level preflight
flag and the two exactness proof bindings; no existing statement changes.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
