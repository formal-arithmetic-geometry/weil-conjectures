## What changed

Replaced the original `diagonalOrientationRefinement` sorry with a complete assembly proof. It chooses normalized charts, uses their four comparison equations, proves restriction transitivity by cancellation, and covers overlaps with the affine-open basis. The original data definitions were moved verbatim to `DiagonalOrientationRefinementData` and publicly reexported; the original theorem signature is unchanged.

The chart choice is made only after proving normalized chart existence. Its only
downstream use is the orientation specified by `BetaNormalized`; compatibility for
arbitrary normalized charts proves independence of this choice. No definition is
filled by an arbitrary witness from a mere unproved existence statement.

Added complete categorical helper modules for comparison pullback coherence, smooth section exchange composition, compared exchange composition, and dualizing exchange naturality. The zero-section integration equation is isolated as a separate sourced theorem. All nine delivered modules compile together through `lcompile.py --all`. The original theorem retains two redundant finite-type binders in its restriction clause; a declaration-local unused-variable linter option preserves that signature without warnings. No mathematical statement or definition changes.

This repairs the landing failure of reviewed head `655d4762876`. The retained packet
was compared with the current shared base: all 29 original declaration signatures and
all 28 relocated definition bodies remain identical. The change record now lists the
new direct consumers as well as the unchanged existing consumers. No Lean proof edit
was requested by the return.

The landing failure came from the reviewer-fix filename. The delivered file is
`coord/changes/T8-diagonal-orientation-data-relocation.md`; `tools/batch_land.py`
requires its flat `--apply-fixes` alias to be
`T8-diagonal-orientation-data-relocation.change.md`, not the ordinary `.md` basename.
The record now explicitly documents both names. Its delivery path is unchanged.
The refreshed packet is compiled and delivered against the current shared base.

## Proved and sorry left

The original module had one hole, in
`WeilConjectures.PurityFiniteSetting.diagonalOrientationRefinement`.
Its body is now a complete assembly proof with the original signature.

One hole is added, in
`WeilConjectures.PurityFiniteSetting.OrientationRefinement.vector_zero_section_integration_baseChange`
(node `lem-pur-vector-zero-section-integration-base-change`). It is precisely the
integration-normalized zero-section equation for a Cartesian change of bundle model.
It supplies neither the Rees geometry, the alpha and delta comparisons, the chart
construction, nor the gluing argument. The net hole count of this reduction is zero:
one original hole closed and one strictly smaller hole added. This is a decomposition,
not a claim of a sorry-free target proof.

The following public categorical lemmas have complete proofs:

- `WeilConjectures.PurityFiniteSetting.Dnc.section_baseChange_comp`,
  `section_baseChange_comp_over_id`, `section_baseChange_id`,
  `section_baseChange_congr`, `section_baseChange_comp_right_id`, and
  `section_baseChange_comp_left_id`;
- `WeilConjectures.PurityFiniteSetting.Dnc.pullComparison_comp` and
  `pullComparison_naturality`;
- `WeilConjectures.PurityFiniteSetting.OrientationRefinement.exchange_congr` and
  `exchange_comp`;
- `WeilConjectures.PurityFiniteSetting.dualizing_base_rectangle` and
  `section_inverse_exchange_naturality`.

The new public chart and compatibility theorems are
`WeilConjectures.PurityFiniteSetting.OrientationRefinement.diagonalOrientationChart_exists`
and `WeilConjectures.PurityFiniteSetting.OrientationRefinement.diagonalOrientationCompatible`.
All private helpers in these modules are proved; their complete declarations are included in the packet. The isolated integration theorem is the only remaining explicit `sorry`.

## No longer needed

The planned nodes `lem-weil-pbc-spec-localization-away-basic-open` and `lem-weil-pbc-affine-open-section-vanishing-prime` are unused because the Mathlib affine-open basis and the finite-type appTop criterion suffice. Their old tool-use entries are removed from this node. This does not assert that other project consumers no longer need those modules. Removed these private imports from the original module: `Sheaf.Paper.CohomologicalSmoothnessTheorem`, `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`, `Sheaf.Paper.PurityDiagonalBaseChangeCompared`, `Mathlib.CategoryTheory.Adjunction.Mates`, `Mathlib.RingTheory.Spectrum.Prime.Topology`, `Mathlib.AlgebraicGeometry.ResidueField`, `Sheaf.Paper.ExchangeFunctoriality`, `Sheaf.Paper.IntegralFinitePullbackComposition`, `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`, and `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`. The diagonal base-change comparison is used privately by `DiagonalExchangeNaturality`; the others are not direct imports of the delivered files. `Mathlib.AlgebraicGeometry.AffineScheme` remains a proof import of the assembly theorem. The old direct appeals to `thm-pur-cohomological-smoothness` and
`def-pur-co-smoothness` are also unnecessary: the proof uses the ordinary smooth
exceptional exchange and the actual normalized DNC coherence directly. Other original
dependencies remain through the unchanged definitions or through the new helper nodes.
No source declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The blueprint route’s localization subargument is unnecessary. The normalization predicate quantifies over arbitrary Cartesian bundle presentations, so linear frame naturality alone cannot prove it; the missing integration naturality component is recorded explicitly, while the chart and compatibility constructions are proved from it. The exponent-transport theorem cannot be imported because its current dependency graph reaches this item; the base-change node records the direct diagonal-exponent route instead.

## New nodes

`def-pur-diagonal-orientation-refinement-data` records the relocated, unchanged data API.
The existing comparison and Tate-pullback nodes now attach to its module.

`lem-pur-smooth-section-exchange-composition` records the proved section-exchange
composition, identity, congruence, and one-sided identity equations.

`lem-pur-comparison-pullback-derived-coherence` records the proved composition and
naturality laws of the actual finite-coefficient site comparison.

`lem-pur-compared-smooth-exchange-composition` records the proved pro-etale comparison
coordinates of smooth exchange composition.

`lem-pur-diagonal-exchange-naturality` records the proved dualizing rectangle and its
restriction along compatible sections.

`lem-pur-vector-zero-section-integration-base-change` is the remaining sourced lemma:
transpose the trace base-change equation at the fixed diagonal exponent and pull it to zero.
It includes arbitrary Cartesian bundle presentations, not only linear trivializations.

`lem-pur-diagonal-orientation-chart-existence` records the Rees normal-bundle model and
construction of its integration-normalized chart from the zero-section equation.

`lem-pur-affine-diagonal-orientation-chart-compatibility` records the four comparison equations on
nested affine opens, with the actual Rees-constrained normal map.

Change record: `coord/changes/T8-diagonal-orientation-data-relocation.md`.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
