## What changed

Implemented `nativeWeil_induction_summands` with its signature unchanged. Private helpers
construct the actual integer exchanges, prove naturality and the successor equation, and
prove the summand formula by integer-recursive uniqueness. The natural transformation is
constructed by transposing the specified `F(eta)` followed by beta inverse, with the actual
derived free adjunction, rather than choosing an arbitrary isomorphism.

The inverse Frobenius preserves the constructible localizing hull by comparison with the
exact derived inverse of the native geometric-Frobenius equivalence. After geometric base
change of the given compactification, the existing native compact-support coproduct theorem
shows that the image of the free cofan is colimiting. The proof constructs an inverse using
its universal property and the inverse integer exchanges, verifies both inverse equations
on coprojections, and uses conservative derived forgetting.

Added `Sheaf.Paper.NativeWeilComparisonStructure`, isolating the one unresolved common-model
compatibility equation for the specified beta. It contains neither integer exchanges,
induction, a transpose, a coproduct assertion nor an invertibility assertion. This is step 6
of the existing argument, strictly smaller than the assigned theorem. Its full proof in
words is in both its docstring and its new node.

Validation: `lcompile.py --all` compiled both delivered modules. The only warning
requested an explanation of the scoped heartbeat allowance; that explanation is now
included. Profiling options were removed. The delivery tool performs the final compile
and packet checks.

All added imports in the item are private proof imports. No existing shared module,
statement, definition, public import, attribute, or instance is changed. The unit route is
unchanged; its recorded `realized` lists are empty.

## Proved and sorry left

Closed the hole in
`AlgebraicGeometry.NativeWeilInduction.nativeWeil_induction_summands`
(node `lem-sf-native-weil-induction-summands`).

Added one hole:
`AlgebraicGeometry.NativeWeilInduction.nativeWeil_comparison_structure`
(node `lem-sf-native-weil-comparison-structure`).

This is a decomposition: one original hole closed and one strictly smaller hole added,
net zero holes. The item itself has zero holes. Every private helper is proved; no
construction obtains data from an unproved existence theorem.

## No longer needed

No original import was removed: the item originally imported only its shared data module.
No module is withdrawn or claimed globally pruned.

Removed direct proof dependencies from the item node:

- `lem-sf-native-weil-proper-normalization`
- `lem-derived-exact-equivalence-squares`
- `lem-sfb-exact-derived-natural-iso`
- `lem-sf-exact-adjoint-forget-derived-detection`
- `lem-sf-fixed-pair-common-derived-resolution`
- `lem-sf-kinjective-derived-map-computation`
- `def-weil-exact-derived-adjunction`
- `lem-sf-fixed-pair-free-integer-adjunction`
- `lem-kun-grothendieck-derived-coproducts`
- `lem-sfb-finite-type-composition-base-change`

The new compatibility node retains proper normalization, exact-equivalence squares,
common resolutions and K-injective map computation. These model-calculation dependencies
are delegated, not globally pruned. The actual localized free adjunction and conservative
forgetting are already supplied by the shared data and heart properties, so their generic
adjunction/detection constructions need not be invoked again.

The integer recursion uses the proved `IsoAlgebra.Free` API directly; it does not need the
large conjunction `fixedPairFreeIntegerAdjunction`, its full adjunction characterization,
or the free-resolution cyclic map and distinguished triangle. The free cofan is supplied
by heart properties. The exact-derived coproduct preservation and the separate
`lem-grothendieck-derived-has-coproducts` API are used directly and retained; the older
Kunneth coproduct conjunction is unnecessary. Finite-type composition is unnecessary here:
the native sums theorem takes the geometric compactification and proves its own
intermediate-scheme finiteness. Its base-change hypotheses are discharged directly.

## Where the brief, the DAG or earlier work was wrong

The old proof bundled integer exchange, beta normalization, transpose summands and
coproduct invertibility into one step. The generic recursion and the coproduct inverse can
be proved independently of the common K-injective model calculation; the revised proof
records that separation. HeartProperties states forward Frobenius stability, so inverse
stability required an additional proved argument, included privately in the item.

The source `lem-fix-weil-operations.proof.md` is currently in
`sk-rem-sf-pf-done`, rather than `sk-thm-sf-package`; the new node cites its current location.
Read that source's first two paragraphs, the equivariance corollary's final sentence, the
existing comparison-data constructions, and the unit record. The structure equation has
the correct orientation: apply target Frobenius to beta, then the native exchange and the
image of the source structure. Identity morphisms and zero complexes reduce to the expected
naturality and zero equations; the equation does not assume constructibility or a choice
of fixed-pair interpretation for derived objects.

## New nodes

`lem-sf-native-weil-comparison-structure`: compatibility of the actual native beta with
localized structure and the first Frobenius exchange. Its proof uses the common proper
K-injective model and the exact open comparison, followed by derived-map normalization.
LeanSearch, LeanFinder, Loogle and Mathlib grep found generic comparison/naturality APIs but
no statement of this specified compatibility. Local source search read the canonical
comparison and structure definitions; the upstream Frobenius-on-global-sections theorem
requires an invariant auxiliary functor and does not assert this equation. No change record
is needed because existing interfaces are unchanged.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
