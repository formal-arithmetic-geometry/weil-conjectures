## What changed

Reduced `AlgebraicGeometry.isOpen_fibre_depth_eq_ringKrullDim_of_isAffine` without changing
its signature or its existing docstring. The proof now chooses a quasi-finite polynomial
chart, takes its open stalk-flat locus, and maps that locus into the original scheme.
The chosen point lies in this open image, and the pointwise criterion proves containment
in the desired locus. The assigned module contains no remaining `sorry`.

The two private flat-locus helpers are fully proved from
`Module.isOpen_setOf_flat_localizedModule`. They identify scheme stalk flatness with
flatness of prime localizations, transfer flatness along `IsLocalizedModule.iso`, and
pull openness back through affine scheme isomorphisms. In particular, they use the
finitely presented flat-locus theorem over arbitrary rings, rather than the existing
Noetherian-base variant in `FiniteFlatTargetLocus`.

Added proof-only imports of `QuasiFinitePolynomialChart`,
`PolynomialChartFibreFlatCriterion` and `OpenFlatLocus`. All original public imports and all existing signatures remain identical.
No definitions, target statements, or other existing Lean modules were changed.

## Proved and sorry left

Closed the assigned module's one hole:
`AlgebraicGeometry.isOpen_fibre_depth_eq_ringKrullDim_of_isAffine`
(node `lem-sbc-affine-fibre-cohen-macaulay-locus-open`).

Added two holes, each a whole proof of a named public theorem in its own new module:

- `AlgebraicGeometry.exists_quasiFinite_polynomial_chart`
  (`lem-sbc-quasi-finite-polynomial-chart`): the polynomial chart and affine transport,
  independently of flatness or Cohen-Macaulayness.
- `AlgebraicGeometry.polynomial_chart_flat_stalk_iff_fibre_depth_and_dimension`
  (`lem-sbc-polynomial-chart-fibre-flat-criterion`): a pointwise criterion on an already
  supplied chart, including the fibre-dimension condition, with no openness conclusion.

This is a decomposition: one hole closed, two holes added, net -1 before any pruning.
Neither remaining theorem restates openness. The entire passage from these two
statements and the existing flat-locus theorem to openness is real, compiling Lean.

The new statements were checked against Stacks Tags 00QE, 00RE, and 00RH. In particular,
Tag 00RE has a dimension condition. The chart supplies precisely this condition at the
starting point. Empty X has no y; an empty chart has no x; n = 0 is allowed. For a useful
negative test, Spec k mapping to affine 1-space by t = 0 is quasi-finite and has a
Cohen-Macaulay stalk but is not flat; its dimension is 0 rather than 1, so the new
criterion correctly has false right-hand side. For the identity chart on affine
n-space the fibre dimensions and flatness agree, including generic points, whose local
ring dimension is not the topological dimension at the point. No arbitrary data is
chosen from an unproved existence theorem inside a definition.

## No longer needed

No original import or transitive plan dependency was pruned. An experimental direct import
of `Mathlib.RingTheory.Localization.Module` was removed after compilation showed it was
unnecessary; the needed localization interface is already visible. The original algebraic tools remain needed in
the plans of the two new nodes: quasi-finite polynomial normalization, miracle
flatness, the fibrewise flatness criterion, and the flat local depth formula.
Openness of flatness is used directly by the assigned module. The original node's
immediate proof dependencies now name the two reductions and openness of flatness;
this is regrouping, not pruning their transitive dependencies.

For completeness, the old immediate `proof_deps` no longer directly invoked by the
assigned Lean proof are:

- `def-pc-scheme-fibre`, `def-weil-affine-spectrum`: retained in the chart and criterion
  plans and used by the imported scheme definitions.
- `def-weil-pbc-depth`, `def-weil-pbc-krull-dimension-ring`: retained as statement
  dependencies; their definitions occur in the unchanged target and the criterion.
- `lem-weil-pbc-quasi-finite-over-polynomial-algebra`: retained in the chart plan.
- `lem-weil-pbc-miracle-flatness`, `lem-weil-pbc-criterion-flatness-fibre`,
  `lem-weil-pbc-flat-local-depth-formula`: retained in the pointwise criterion plan.

`lem-weil-pbc-openness-of-flatness` remains directly used. No library module is claimed
as pruned by this delivery.

## Where the brief, the DAG or earlier work was wrong

No false original statement was found. The existing algebraic dependencies do not
expose the scheme-level chart or pointwise criterion with all fibre transports, so
those two parts of the existing plan are the remaining statements. The source's
pointwise criterion requires both Cohen-Macaulayness and the dimension of the fibre
at the point; the dimension is not the dimension of the local ring alone. The
new statements explicitly preserve this distinction.

The existing module does not yet import its DAG's proof-dependency modules. The proof
uses `OpenFlatLocus` directly; the other original dependencies appear in the new
nodes' proof plans. The polynomial-regular-ring node has no `lean` record, but already has an exact
`mathlib_match` for `MvPolynomial.isRegularRing_of_isRegularRing` in
`Mathlib/RingTheory/RegularLocalRing/Polynomial.lean:108`. No attachment or duplicate
statement is needed.
The generic algebra results of the proper-base-change and curve-estimates units are
used as tools for this same polynomial-chart route; no step of the unit is bypassed.
No change record or forced adaptation is needed.

LeanSearch returned Internal Server Error for both new-node queries. This is recorded
as unavailable. LeanFinder, logged Mathlib grep, and searches in both library roots
found no exact theorem. Blueprint searches for quasi-finite polynomial charts and
Cohen-Macaulayness found no imported blueprint node with these scheme-level statements.

## New nodes

`lem-sbc-quasi-finite-polynomial-chart`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-quasi-finite-polynomial-chart.json`, records
`Sheaf.AlgebraicGeometry.QuasiFinitePolynomialChart`. It isolates existence and
transport of the polynomial chart from the openness problem. Its proof uses the
existing ring-level polynomial-chart theorem and finite-type field dimension formula.

`lem-sbc-polynomial-chart-fibre-flat-criterion`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-polynomial-chart-fibre-flat-criterion.json`,
records `Sheaf.AlgebraicGeometry.PolynomialChartFibreFlatCriterion`. It isolates the
pointwise equivalence using miracle flatness, the fibrewise criterion, and the depth
and dimension comparisons. The statements, hypotheses, source, proof steps, actual
search results and Lean signatures are recorded in both nodes.

Validation: all three modules compile together without warnings. The dry run passed
compilation, declaration/signature checks, the axiom probe and preflight except for
the independent second reading, which is intentionally left to the next worker.


## Second reading by K3

1. **Existing interface: PASS.** Read the complete diff against the repository version.
   The sole existing theorem's signature and docstring are byte-for-byte unchanged;
   the additions are two private proved helpers, three plain proof imports, and the
   replacement proof. The existing node differs only in `proof`, `proof_deps`, and
   `proof_origin`. There are no changed definitions or forced adaptations.
2. **Proof and axioms: PASS as a decomposition.** Independently compiled all three
   modules with `lcompile.py --all`, without errors or warnings. Scratch copies with
   `#print axioms` checked both private helpers, the assigned theorem, and both new
   theorems. All five declarations use only `propext`, `Classical.choice`, `Quot.sound`,
   and `sorryAx`. The fully written helpers still depend on existing upstream holes
   through `OpenFlatLocus`; the assigned theorem also depends on the two newly
   reported supporting holes. Thus the helpers are proved reductions, not axiom-free
   closure results. Exactly two `sorry` occurrences remain, each the entire proof of its named
   public theorem. No forbidden declarations, hollow definitions, or data definitions
   choosing arbitrary existence witnesses occur.
3. **Split statements: PASS.** Read both signatures and their full docstring proofs
   against [00QE](https://stacks.math.columbia.edu/tag/00QE),
   [00RE](https://stacks.math.columbia.edu/tag/00RE), and
   [00R7](https://stacks.math.columbia.edu/tag/00R7). Checked empty-source cases,
   the zero-variable chart, the identity on affine space at a generic point, and the
   nonflat closed point of affine one-space. In the last case the Cohen-Macaulay
   condition alone holds while the dimension condition fails, as required. The chart
   concerns existence and transport; the criterion concerns one supplied chart at
   one point. Neither asserts openness or restates the assigned theorem. Independent
   LeanFinder queries used local Noether normalization and miracle flatness wording;
   logged Mathlib grep and searches in both Lean roots found no exact replacement.
   The available normalization result is ring-level, over a field, and the existing
   polynomial-chart theorem is ring-level; neither closes the scheme transport in
   a few minutes. No supporting hole was closed during this reading.
4. **Route and pruning: PASS.** Read the flat-locus helpers and the open-image
   neighborhood assembly. The helpers genuinely transfer localized-module flatness
   to scheme stalks over an arbitrary base; the Noetherian-base result in
   `FiniteFlatTargetLocus` cannot replace them. Each new proof import is used and is
   plain `import`; public imports supply the statement interfaces. The original
   [00RH](https://stacks.math.columbia.edu/tag/00RH) polynomial-chart route is kept.
   Read `dag/units/sk-prop-normal-form.json`: this node is an input below its slicing
   step, not a replacement of either unit step; the unit's `realized` fields are
   unchanged. The report now enumerates every original immediate dependency that
   was regrouped, with its retained use; there is no pruning claim.
5. **Nodes: PASS.** Checked every delivered node, the union of its proof-step `uses`
   against `proof_deps`, and the exact Lean signatures recorded in `lean.statement`.
   Both new nodes have the required source, searches, creation, blueprint, chapter,
   unit, and Lean records. Existing dependency nodes resolve to a Lean declaration
   or a Mathlib match. The assigned node describes the compiled reduction accurately.

**Changes by this reader:** corrected the report's stale suggestion to attach the
polynomial regular-ring theorem: its existing node already has the exact Mathlib
match. Expanded `## No longer needed` to list all regrouped old immediate dependencies,
logged independent searches, and added this review. Lean proofs and signatures and
DAG nodes needed no repair. Accounting remains one assigned hole closed and two
supporting holes added, net -1; this is a decomposition, not a complete proof.
