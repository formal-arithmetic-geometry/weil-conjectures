## What changed

Reduced `AlgebraicGeometry.AlgebraicSpace.strictLocalChartComparison` to two genuine
steps of its existing pointed-neighbourhood argument. The assigned module now contains
a complete Lean proof of the comparison from the two new declarations. It obtains a
normalized scheme-chart cocone, applies its colimit property, compares it with the
existing affine scheme colimit, and composes with the existing small/full comparison.
The coprojection formula proves the required germ equation. For uniqueness, compatible
small refinements detect every affine scheme-colimit leg, so colimit hom-ext proves
equality of the underlying ring maps and hence of the ring equivalences.

The new modules are `Sheaf.AlgebraicGeometry.SchemeChartGermCocone` and
`Sheaf.AlgebraicGeometry.SchemeChartGermCoconeIsColimit`. They state, respectively,
extension and normalization of an arbitrary cocone, and universality for an already
specified normalized cocone. Neither asserts the comparison ring equivalence. The
first does not assume or conclude a colimit property; the second does not construct
the germ cocone or the refinement witnesses. The original theorem's categorical
assembly and uniqueness are proved in Lean, rather than moved to a renamed theorem.

Both new statements quantify an arbitrary cocone on the actual regular-function
diagram, not a replacement ring or an unspecified structure-sheaf model. Their
sources are spaces-properties.tex, Tag 04KF and the direct proof of Tag 04K2(4).
The docstrings and DAG nodes give the corresponding complete arguments on pointed
neighbourhoods. Searches found generic colimit comparison APIs, which the proof uses,
but no existing chart comparison for these algebraic-space diagrams.

No existing signature, definition, public import, attribute, or docstring is changed.
No source-library module or other existing module is changed. The unit route is kept.
The node's first proof step and proof dependencies record the actual decomposition;
the other strict-local obligations retain their existing argument.

## Proved and sorry left

Closed the body hole of `AlgebraicGeometry.AlgebraicSpace.strictLocalChartComparison`
from the two new supporting statements: 1 of the 3 original holes is decomposed,
2 holes are added, and 2 original holes remain. This is a decomposition, not a net
proof gain. The packet has 4 remaining holes in total.

The two unchanged holes in the assigned module, both attached to
`lem-sfb-space-strict-local-flatness`, are:

- `AlgebraicGeometry.AlgebraicSpace.schemeStrictLocal_presentation`.
- `AlgebraicGeometry.AlgebraicSpace.geometricStalk_flat_iff`.

The two added whole-proof holes are:

- `AlgebraicGeometry.AlgebraicSpace.schemeChart_germCocone`, node
  `lem-sfb-space-chart-germ-cocone`, in `SchemeChartGermCocone.lean`.
- `AlgebraicGeometry.AlgebraicSpace.schemeChart_germCocone_isColimit`, node
  `lem-sfb-space-chart-germ-cocone-is-colimit`, in `SchemeChartGermCoconeIsColimit.lean`.

`flatAt_iff_chart_stalk` and its six private helpers retain their previously proved
bodies. There is no partial-proof sorry, new definition, axiom, or arbitrary data
construction. The proof of strictLocalChartComparison compiled in 16.1 seconds;
the two new statements separately compiled in 6.8 and 6.7 seconds before their
public imports were narrowed to the defining scheme-diagram module. The final
three-file packet is checked again after that import cleanup.

## No longer needed

No existing Lean import is removed. Two private imports of the new supporting
modules are added. The new modules publicly import only the existing geometric
stalk model and the upstream scheme pointed-neighbourhood diagram they state.

The chart comparison does not use `schemeStrictLocal_presentation`,
`geometricStalk_flat_iff`, ordinary scheme local rings, residue-field choices,
strict-henselization module flatness, or faithful-flat descent. Those theories
remain required by the two untouched original obligations; no global withdrawal
or deletion is claimed for them.

Removed the following dependencies of the old first proof step from this item's
`proof_deps`:

- `lem-sfb-stack-chartwise-smooth-etale-calculus`, module
  `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`: the definition module's
  proved `isEtale_comp` gives the only composition operation required here.
- `lem-trf-space-fibre-products-etale-covers`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`: the scheme tests
  in `IsEtale e` already represent the pullbacks with the fixed chart needed for
  the inverse germ construction. General fibre products of algebraic spaces and
  permanence of their covers are not required.

The obsolete top-level tool approval for the latter dependency is removed;
no approval is added or reordered. Their uses in other modules are unaffected.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The chart comparison needs neither the full stack
chartwise calculus nor general algebraic-space fibre-product permanence. The
smaller scheme-test and cocone arguments suffice for this clause.

Edge cases checked: a geometric lift t excludes an empty T; the chosen chart e
need not be surjective; identity charts give ordinary reindexing by the affine
small skeleton; arbitrary cocone vertices, including the zero ring, are allowed
in the extension step; a fixed normalized cocone is universal only under the
explicit IsColimit hypothesis on the original cocone. No separation, finiteness,
Noetherian, or extra field-extension hypothesis is introduced.

## New nodes

`lem-sfb-space-chart-germ-cocone` states the extension of an arbitrary cocone from
small pointed affine X-charts to affine pointed neighbourhoods of a fixed etale
scheme chart, including existence of compatible small refinements and the
normalization on every such refinement. Its missing proof is the forward germ
construction and choice-independence part of the source's argument.

`lem-sfb-space-chart-germ-cocone-is-colimit` states the universal property of a
specified normalized germ cocone. Its missing proof is the reverse construction
by pointed scheme pullback and affine refinement, with factorization and uniqueness.
The final comparison isomorphism and its uniqueness are proved in the assigned
module. Both new nodes retain the parent's chapter, unit, and blueprint ancestry.
No change record is needed because no existing interface or definition changes.

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
