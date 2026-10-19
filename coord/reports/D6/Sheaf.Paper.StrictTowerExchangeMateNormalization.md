## What changed

Proved four of the six existing theorem holes in
`Sheaf.Paper.StrictTowerExchangeMateNormalization`, without changing any existing
signature, definition, visibility, or import.

- `exchangeConstant_coherent`: the general constant-section composition formula
  identifies each composite coefficient isomorphism with the comparison for the
  composite scheme morphism; commutativity of the chosen square gives the required HEq.
  Two proved private helpers reproduce the general adjunct-composition calculation
  and the constant-section calculation already proved privately in
  `ProfiniteCoefficientInverseImage`; the finite-tower public theorem cannot be
  specialized to the possibly infinite ring A.
- `exchangeScalar_comm`: compare both maps after every finite projection, use the
  defining residue equations of `adicDatumScalar`, transport through the canonical
  constant-system comparison, and apply naturality of `proEtaleConstantComparison`.
- `exchangeTowerModuleRes_exact`: apply the existing restriction-of-scalars
  preservation instances and pointwise preservation for right whiskering.
- `exchangeStrict_naturality`: package the projection maps into natural isomorphisms
  using `towerProjection_properties`; compose their inverses with the reduction of
  the natural ambient exchange and the right projection comparison. Its naturality
  equation is definitionally the required strict-tower equation.

## Proved and sorry left

Closed four original holes:
`AlgebraicGeometry.Scheme.exchangeConstant_coherent`,
`AlgebraicGeometry.Scheme.exchangeScalar_comm`,
`AlgebraicGeometry.Scheme.exchangeTowerModuleRes_exact`, and
`AlgebraicGeometry.Scheme.exchangeStrict_naturality`.
Added zero holes; split off zero statements.

Two original holes remain, both attached to
`lem-weil-pbc-strict-tower-exchange-mate-normalization`:

- `AlgebraicGeometry.Scheme.exchangeResPush_existsUnique`: still needs the
  normalized universal right-derived comparison on the strict diagram category.
- `AlgebraicGeometry.Scheme.strictTowerExchangeMateNormalization`: still needs the
  diagram-site tensor/exchange coherence and its compatibility with the specified
  coefficient-restriction comparisons. The first conjunct expands the specified
  conjugate; the finite evaluation clause is available from
  `AdicCoefficientDatum.fourTowers_compatibility`. The strict mate equality must
  come from the diagram-site argument, not faithfulness of derived evaluations.

## No longer needed

None. No imports or modules are pruned: the remaining main theorem retains its
original diagram-site proof plan and dependencies. The four proved auxiliary
obligations use the existing interfaces and do not introduce a different route.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The published finite-ring composition clause
cannot prove constant-coefficient coherence for an arbitrary possibly infinite A;
its source module already proves the required general formula privately. Reusing
that proof locally avoids a stronger statement or a change to the dependency's API.

The resumed compiler check exposed an ambiguous high-priority locally bijective
instance with a free coefficient-universe parameter. The exactness proof now uses
`WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0}` explicitly,
then constructs the colimit instance at the specified sheaf and diagram universes.
No launcher scripts or shared repository files were changed.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
