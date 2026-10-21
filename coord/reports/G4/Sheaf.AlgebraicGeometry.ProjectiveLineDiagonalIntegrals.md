## What changed

Proved `projectiveLine_diagonal_ker_isInvertible` using the regular immersion
criterion for the smooth projective line. The target theorem now constructs this
Cartier witness, obtains the normalized supported Kummer class, and reduces its
integral identity to the Chern-component statement and the (proved) trace calculation.
Change record: `coord/changes/projective-line-diagonal-data.md`. The existing
diagonal data definitions are exported from `ProjectiveLineDiagonalData`; the
parent module publicly re-exports that data.

Reviewer fix (2026-10-21): the chart pushforward `projectiveLineDiagonalChartPushforward`
moved from the Chern-components module into `ProjectiveLineDiagonalData` (it is a
definition and is owned by the definition node `def-amb-p1-diagonal-data`, not by a
theorem node). `ProjectiveLineDiagonalData` also gets the factorization lemma
`projectiveLineDiagonalTrace_eq`: trace = chart pushforward ≫ projective-line trace.
`projectiveLine_diagonal_trace_calculation` is now proved. Unused imports of the Chern
module were dropped. The node records were made to agree with the Lean.

## Proved and sorry left

Closed the original `projectiveLine_diagonal_integrals` sorry. Proved:

- `projectiveLine_diagonal_ker_isInvertible` (`ProjectiveLineDiagonalCartier.lean`);
- `projectiveLine_diagonal_trace_calculation` (`ProjectiveLineDiagonalTraceCalculation.lean`):
  the trace `pr₂ ∘ b⁻¹` sends the relative Chern adjunct to one
  (`projectiveLineTrace_chern`) and kills the twisted-unit summand, because `b` restricts
  to the unit on the first summand;
- `projectiveLineDiagonalTrace_eq` (`ProjectiveLineDiagonalData.lean`).

One `sorry` is left:

- `projectiveLine_diagonal_chern_components` in
  `ProjectiveLineDiagonalChernComponents.lean`.

## No longer needed

The original target proof's direct affine-chart and stalk argument is no longer
needed in this module: the proof uses the regular-immersion criterion, the
supported-Kummer interface, the Chern decomposition, and the projective-line
trace decomposition. The chart-calculation, geometric-fibre and stalk-detection
dependencies dropped from the item's `proof_deps` are
`lem-weil-pbc-projective-space-standard-charts`,
`lem-weil-pbc-fibre-product-affine-spectra`, `cor-weil-pbc-geometric-fiber-finite`,
`def-kun-unbounded-exchange`, `def-pc-divisor-line-bundle`, `def-sc-p1-standard`,
`def-weil-pbc-composite-adjunction`, `def-weil-proper-morphism`,
`def-weil-sheaf-of-modules-category`, `lem-asd-ordinary-finite-p1-adjunction`,
`lem-weil-pbc-closed-immersion-finite`, `lem-weil-pbc-derived-single-fully-faithful`,
`lem-weil-pbc-finite-type-over-noetherian`,
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`,
`lemma-nagata-projective-space-base-change-proper`,
`lemma-nagata-projective-space-base-change-pullback`,
`lemma-weil-pbc-finite-direct-image-exact`, `lemma-weil-pbc-geometric-stalk-conservative`,
`prop-weil-pbc-geometric-stalks-exact`. The target also no longer directly
imports the derived-category, site-point, noetherian, finite-morphism, and
projective-space support modules that were present only for the old monolithic
proof; they remain transitively available through the public data module, which
keeps the imports of the unchanged definitions.

## Where the brief, the DAG or earlier work was wrong

The original DAG route treated the full Chern and trace calculation as one
undivided theorem. The trace part is formal once the decomposition of
def-amb-p1-trace is known, so the only geometric statement left is the Chern
decomposition. The definitions also had to be moved to a public data module to let
the split statements import them without a cycle; signatures and public visibility
are unchanged.

Overlap: the existing, still-sorry
`ordinaryFiniteP1_diagonal_kummer_component_formula`
(lem-sp-finite-p1-diagonal-kummer-component-formula) states the same decomposition
with the base class only existential, for arbitrary twist transports and Chern arrows.
It lives downstream of this item, so the item cannot use it.

## New nodes

- `def-amb-p1-diagonal-data`
- `lem-amb-p1-diagonal-cartier`
- `lem-amb-p1-diagonal-chern-components`
- `lem-amb-p1-diagonal-trace-calculation`

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
