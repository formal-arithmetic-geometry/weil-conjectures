## What changed

Completed `AlgebraicGeometry.Scheme.UniversalCover.pointedCover_compatible_unit_roots` with its existing signature and definitions unchanged. All added helpers and the divisibility index are private and fully proved in the item module. The public cover import now names its actual defining source module, replacing the larger `PointedLimitCech` package. The import change is recorded in `coord/changes/pointed-cover-unit-roots-imports.md`; there are zero current Lean consumers to adapt.

Finite nonempty inverse systems provide compatible primitive and scalar labels. Monic root algebras are finite and the source theorem `AdjoinRoot.etale_X_pow_sub_C` proves they are etale. The existing `UniversalCover.toObj` construction lifts each geometric root. A divided-polynomial idempotent argument proves that two simple roots in a connected ring are equal or have unit difference; this yields marked uniqueness and the primitive-power unit differences. Quotient-ring extensionality proves uniqueness of the entire homomorphism. Elementary power calculations and marked uniqueness give both power identities and the full naturality clause.

Updated the existing node's proof, proof dependencies, proof origin, and removed its obsolete root-split-away tool approval. The generic standard-etale source helper is audited under the already closed `lem-sc-kummer-exact`; `lem-pc-scheme-connected-iff-idempotents` is another already closed generic tool. Neither replaces any unit-level step.

Validation: single-file compilation through `lcompile.py` succeeded cleanly in 14.7 seconds. `#print axioms` for the completed theorem reports exactly `propext`, `Classical.choice`, and `Quot.sound`. Edge cases checked in the argument include n=1, n=m, k=0, p=2, an empty finite family, scalar zero, and nonreduced connected base rings. The main prime hypothesis stays in the original statement although the proof needs only coprimality and the geometric point.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.Scheme.UniversalCover.pointedCover_compatible_unit_roots` (node `lem-sfb-pointed-cover-compatible-unit-roots`). Added 0 holes and split off 0 statements. No `sorry` remains in the delivered module. Every private helper is proved.

## No longer needed

- `lem-sfb-residue-unit-reduction-surjective`: finite inverse-system nonemptiness requires no surjectivity of transitions, so the residue-unit lifting argument is unnecessary.
- `lem-sbc-root-split-away-cover-etale` and its proof import `WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitAwayCoverEtale`: its obsolete top-level `tool_uses` approval is also removed. Replaced by the already proved direct root-algebra etaleness theorem `AdjoinRoot.etale_X_pow_sub_C`.
- Removed proof imports `Mathlib.Data.ZMod.Units`, `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`, `WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed`, and `WeilConjectures.Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots`. Primitive existence uses Mathlib's `HasEnoughRootsOfUnity.exists_primitiveRoot` and its algebraically closed field instance directly.
- No finite split-product algebra or lifted split idempotent is required. The direct divided-polynomial calculation proves the difference assertion, and the existing cover construction already provides the normalized sections and connectedness. Removed the public `Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitCech` import, replacing it with `WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCoverConstruction`. The theorem `nonempty_pointedLimitCechCoordinates` and its companion Cech statements are not invoked by this proof. The conceptual pointed-cover dependency node stays, since its existing source construction is essential.

These nodes and imports are unnecessary for this item's proof; this report does not claim that their modules have no other consumers. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The nine-step plan contains unnecessary surjectivity work for compatible labels: the finite inverse-limit theorem only assumes finite nonempty terms. Its difference-of-roots step is correct but can be replaced by the shorter connected-ring argument, valid without reducedness. The existing declarations and source library suffice; no new public theorem or definition repair is needed beyond the documented import pruning. The source's existing pointed cover, rather than the still-holed package of extra Cech coordinates, suffices for this result.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
