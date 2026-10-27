## What changed

Filled `WeilConjectures.qcqsCompactSupport_strictReductionGamma` by assembling
representative independence, normalized right-derived-limit uniqueness, and a separate
comparison of whole derived strict towers. The original public signature and public
imports are unchanged. Added private proof imports of
`CompactSupportRepresentativeIndependence` (with private proof API) and
`QcqsCompactSupportNativeTowerComparison`. The private `recordedTowerLimit` and its
generic categorical helpers adapt the fully proved argument already present in
`CompactSupportNormalizedTowerLimit`, using the original assigned dependencies directly.

The proof composes the recorded comparison with the total limit of the strict-tower
isomorphism. Naturality moves that isomorphism across the actual limit projection.
Its specified finite coordinates identify the result with the recorded Roos projection.
Proved private categorical helpers handle equality transport, projection composition,
and adjunction transport. The finite scalar-adjunction Hom equivalence gives the required
finite reduction isomorphism, including its existing object-transport factor.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.qcqsCompactSupport_strictReductionGamma`
(node `lem-qcqs-compact-support-strict-reduction-gamma`).

Added one hole, the complete proof of
`WeilConjectures.qcqsCompactSupport_nativeTowerComparison`
(node `lem-qcqs-compact-support-native-tower-comparison`). It compares the recorded
coherent tower with native proper/open reduction **before** total inverse limit,
on the ambient derived input category. It does not assert the recorded integral
compact-support functor, a limit comparison, or the scalar-adjunction projection formula.

This is a decomposition: one original hole closed and one strictly earlier tower
comparison left, for a net hole reduction of zero. The original module has zero
remaining holes. All private categorical helpers, including `recordedTowerLimit`,
are proved. The revised main module compiled cleanly in 44.3 seconds, and the new
statement module compiled in 38.1 seconds. The instance-priority adjustment is local. A local unused-variable
linter setting preserves the existing unused `SY` binder unchanged.

## No longer needed

No existing public import or declaration is removed, and no module is withdrawn.
The assigned representative-independence and strict-tower homotopy-limit nodes remain
needed. `CompactSupportNormalizedTowerLimit` is not imported: its argument is assembled
locally from those assigned declarations, so its later public theorem is not a proof
dependency of this earlier DAG item. The coefficient calculus remains needed by the
signature and the native tower comparison. No global pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The original plan names representative independence and total-limit uniqueness, but
those do not themselves expose an isomorphism from the **chosen** recorded coherent
tower to an arbitrary native reduction calculus. The former's Lean package records
evaluations and quotient transitions; finite evaluation alone does not provide a
whole-system comparison or detect equality of derived morphisms. The new lemma names
that missing step explicitly. Its eventual proof must retain the construction on
strict resolutions and its universal normalization; it cannot be proved merely by
matching evaluated diagrams. Exposing the construction-owned normalization of the
recorded tower may be needed to finish this step.

The normalized-limit argument is already proved in the library and is assembled
here from its underlying declarations, so no new limit or integral-action obligation
is introduced. The
unit and chapter routes are unchanged. The new statement includes zero inputs,
empty schemes and opens, and all positive coefficient levels indexed by n+1; its
construction requires neither a finite base field nor extra separatedness of X or Y.

The first preflight refused adding the packaged normalized-limit theorem as a DAG
proof dependency: representative independence and the finite action already lie in a
150-node cyclic component reaching this item, while that packaged theorem lies outside
it. Adding the wrapper would enlarge that component. The revised proof follows the
original assigned route directly, with proved private categorical assembly, and does
not change any existing shared node or dependency to remove the cycle. This pre-existing
DAG issue remains visible for the maintainer; no Lean import cycle is introduced.

## New nodes

`lem-qcqs-compact-support-native-tower-comparison`, in
`lean/Sheaf/Paper/QcqsCompactSupportNativeTowerComparison.lean`, isolates the comparison
of whole derived strict towers and its finite evaluation normalization. Its source is
the coherent compact-support quotient construction and the compatible coefficient
comparisons in the current blueprint's integral compact-support proof. It is strictly
before applying any total limit. No existing shared interface is changed and no change
record is required.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
