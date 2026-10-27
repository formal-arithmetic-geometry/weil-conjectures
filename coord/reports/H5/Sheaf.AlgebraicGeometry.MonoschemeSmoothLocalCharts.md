## What changed

Filled two theorem proofs in Sheaf.AlgebraicGeometry.MonoschemeSmoothLocalCharts.

- `AlgebraicGeometry.Monoscheme.affine_smallest_neighborhood_formula`: apply
  `FineFan.monoidPrime_minimal_neighborhood` to the selected product, including its
  empty case. Prove that sheafification is bijective on a smallest neighborhood
  from local bijectivity and the fact every covering sieve contains the identity.
  Evaluation at the distinguished prime is an explicit equivalence from compatible
  fraction families to the face localization. Naturality of the sheafification
  unit proves the canonical numerator formula.
- `AlgebraicGeometry.Monoscheme.realized_smallest_product_chart`: construct the
  polynomial/Laurent algebra equivalence using domain transport, product currying,
  finite exponent functions, and the multiplicative/additive notation equivalence.
  Verify the basis formula and use additive induction for the coefficient map.
  Prove Laurent algebra smoothness over every commutative ring by induction on
  the rank, using localization of A[X] at X for each Laurent variable. Transport
  the coefficient inclusion along the actual algebra equivalence and apply the
  affine criterion for smoothness.

Search used leanfinder (smallest affine monoscheme neighborhoods), loogle
(`MonoidAlgebra, MvPolynomial`), msearch grep for product monoid algebras and
smoothness, and direct searches of Mathlib, WeilConjectures and Sheaf. No exact
replacement for these clauses was found; existing Mathlib algebra equivalences
and Laurent localization supplied the shorter realized-chart route.

All added imports are private proof imports. Existing public signatures and public
imports are unchanged. Existing restriction and covering proofs are preserved.
The node's proof route and dependencies now reflect these arguments. No other
existing module or node is changed, and no new module or public statement is introduced.
Edge cases retained: empty finite products, r=t=0, repeated monoid generators,
torsion in the coefficient monoid, and arbitrary field characteristic.

Validation: lcompile.py compiled the file without warnings or errors in 9.3 s.
The axiom audit for `realized_smallest_product_chart` shows only `propext`,
`Classical.choice`, and `Quot.sound`. The audit for the finite-generator formula
also shows `sorryAx` through the existing minimal-neighborhood dependency.
Temporary axiom-print commands were removed before delivery. A source comparison
confirms that all five public signatures and all public imports are identical.

## Proved and sorry left

Original item: 3 holes. Closed 2; added 0; left 1. No decomposition or split-off holes.

Closed:
- `AlgebraicGeometry.Monoscheme.affine_smallest_neighborhood_formula`.
- `AlgebraicGeometry.Monoscheme.realized_smallest_product_chart`.

Left unchanged:
- `AlgebraicGeometry.Monoscheme.exists_smallest_affine_neighborhood`, node
  `lem-trf-monoscheme-smooth-local-charts`.

The finite-generator formula uses the existing named theorem
`AlgebraicGeometry.FineFan.monoidPrime_minimal_neighborhood`, whose proof is still
sorry in its own module. This is an existing planned dependency, not an added hole.
All new private helpers are proved, including the explicit section equivalence.

## No longer needed

The realized-chart proof does not require:
- `def-sbc-affine-space` (Mathlib AlgebraicGeometry.AffineSpace): no comparison
  with relative affine space is needed.
- `sbc-lem-affine-space-smooth`
  (WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth): polynomial
  smoothness and Laurent localization are used directly as ring algebra facts.
- `lem-weil-pbc-principal-localization-open-immersion`: the algebra-level
  principal-localization smoothness theorem suffices.
- `lem-pc-open-immersion-smooth-composition`: smooth ring homomorphisms compose
  directly before applying Spec.

These nodes are removed from proof_deps and the obsolete affine-space tool_use
is removed. None was imported in the starting item, so no original Lean import
is removed. The public Mathlib scheme Smooth import remains necessary for the
statement and affine criterion. The minimal-neighborhood and fine-monoid-chart
nodes remain dependencies of the still-open first clause. No module withdrawal
or unit-route change is proposed.

## Where the brief, the DAG or earlier work was wrong

The node `lem-trf-fine-monoid-local-smooth-charts` records the module
`Sheaf.AlgebraicGeometry.FineMonoidLocalSmoothCharts`, but that file is absent
from this checkout. No corresponding rework/quarantine row was found. Its
`Monoscheme.exists_smallest_stalk_chart` declaration is the planned affineness
input for the first clause. I left that clause and its dependencies unchanged,
and did not duplicate the missing theorem or replace it by another hole.

The original realized-chart docstring and node proposed a single localization
at the product of all Laurent variables followed by a relative affine-space
comparison. Repeated one-variable Laurent localization gives a shorter proof
from existing Mathlib equivalences and smooth algebra facts. This changes only
the route below the unit level. The unit sk-i-curve-zero has no realized steps
attached to this auxiliary node, and no unit record is changed.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
