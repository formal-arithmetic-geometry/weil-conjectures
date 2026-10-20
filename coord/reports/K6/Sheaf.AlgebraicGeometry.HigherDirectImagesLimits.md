## What changed

`AlgebraicGeometry.higherDirectImage_baseChange_of_limit` follows the two-continuity
argument of Tags 0EZT and 0EYM. Construct the canonical higher-image diagram, use
continuity to make its projection cocone a colimit, and preserve that colimit by
inverse image. Present the same pulled diagram using the assumed stage exchange
isomorphisms. The proved coefficient-cube theorem verifies its transition and
projection-leg equations. The second continuity comparison is the limit exchange,
by the colimit universal property. Removing its invertible cohomology and
single-functor comparison factors gives the original conclusion. The item's
signature is preserved verbatim.

The new `RelativeHigherImageConeLaws` module constructs the diagram data and proves
its functor/cocone laws from derived horizontal pasting, exact inverse-image
cohomology, single-functor compatibility and inverse-image coherence. Its generic
presentation constructor is explicit and irreducible: users work through its
specified equations instead of unfolding the concrete diagram.

The new `RelativeHigherImageContinuityPreorder` module proves the needed preorder
extension of the existing partial-order continuity theorem. It reindexes all data
along the thin-skeleton equivalence, applies the existing theorem, and identifies
the two descent maps by their colimit legs. Its exchange abbreviation is exactly
the existing exchange map, with its derived-functor endpoints written explicitly.
No existing definition, statement or module besides the item is changed.

The proof uses explicit functor endpoints, local transparency settings and generic
categorical comparison lemmas to avoid expanding the concrete sheaf and derived
functor constructions during endpoint comparison. The fixed statement's torsion
assumption is unnecessary for relative continuity on abelian sheaves; its unused
variable lint is disabled only for that declaration. All three delivered modules
passed delivery compilation and the axiom probes; the earlier preflight required
the search and elaboration-command records now included in this packet.

## Proved and sorry left

Original holes closed (1 of 1):

- `AlgebraicGeometry.higherDirectImage_baseChange_of_limit` (`lem-kun-0ezt`).

New results proved, with zero new holes:

- `AlgebraicGeometry.Etale.relativeHigherImage_cone_laws`
  (`lem-kun-relative-higher-image-cone-laws`), including composition, identity and
  canonical projection-leg compatibility.
- `AlgebraicGeometry.Etale.higherDirectImage_relative_continuity_preorder`
  (`lem-kun-relative-continuity-preorder`), by reindexing the existing theorem.

The delivered modules contain no `sorry`. No unfinished statement is split off.
The proof uses the existing stated dependency
`AlgebraicGeometry.Etale.higherDirectImage_relative_continuity` (`lem-kun-0eym`),
whose original hole remains outside this delivery. It does not claim to prove it.

## No longer needed

Private proof imports removed from the item:

- `Mathlib.CategoryTheory.Adjunction.Mates`.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`.
- `Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`.
- `Sheaf.Paper.KunBcMapOnCohomology`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact`.

The standalone derived cube (`lem-kun-derived-exchange-cube`) is not needed by this
argument: the proved coefficient cube gives both required equations directly.
The conjunction in `lem-weil-pbc-derived-inverse-image-composition` is not a direct
dependency of this proof; ordinary inverse-image coherence and derived pasting
supply its equations. Its obsolete top-level `tool_uses` entry is removed, with
remaining approvals in their original order. These are removals from the item's
route, not global withdrawals: the existing continuity module still imports its
own proof dependencies, including derived inverse-image composition.

`KunBcMapOnCohomology` is unnecessary because invertibility of the two comparison
factors directly identifies the stated derived-exchange condition with the abelian
exchange. The limit square is supplied as `sq`, so no separate construction of its
cartesian property is needed. No existing module or source declaration is withdrawn.

The inherited `higherDirectImage_baseChange_core` restatement and its node were
rejected by the initial delivery check and removed from the sandbox; they never
landed.

## Where the brief, the DAG or earlier work was wrong

The inherited packet moved the whole goal to a renamed theorem and included a
`True` placeholder. That was not a reduction. The current argument constructs the
actual diagrams and proves their compatibility equations instead.

The existing continuity theorem accepts a partial order, while the item accepts a
preorder. The new proved extension resolves this through an equivalent partially
ordered indexing category. The original module is held by H5 and is preserved
unchanged; an earlier proposed signature repair was refused by preflight and is
absent from this packet.

The continuity interface assumes a higher-image diagram and its legs; it does not
construct their laws. The new cone-law node supplies precisely the separate first
paragraph of Tag 0EYM. It has no limit, affine, qcqs, torsion or stage base-change
hypothesis. Empty indexing categories give vacuous laws; identity maps, zero
coefficient maps and q=0 are covered by the same proved formulas. The unit route
through relative continuity is retained.

## New nodes

`lem-kun-relative-higher-image-cone-laws`, in
`dag/nodes/sec-smooth-purity/lem-kun-relative-higher-image-cone-laws.json`, records
the canonical transition and projection-leg laws from Tag 0EYM. Its theorem is
proved in `Sheaf.AlgebraicGeometry.RelativeHigherImageConeLaws`.

`lem-kun-relative-continuity-preorder`, in
`dag/nodes/sec-smooth-purity/lem-kun-relative-continuity-preorder.json`, records the
proved extension by equivalence of indexing categories, in
`Sheaf.AlgebraicGeometry.RelativeHigherImageContinuityPreorder`.

Both new nodes are proved. The existing item node records the actual
two-continuity proof and direct coefficient-cube applications. The elaboration commands in the item are recorded in
`coord/changes/K6-higher-image-limit-elaboration.md`; existing statements,
definitions and public imports are preserved.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
