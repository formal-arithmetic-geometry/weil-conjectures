## Worker report

The module `Sheaf.AlgebraicGeometry.ComponentwiseNormalizationSmoothPullback` states
`AlgebraicGeometry.Scheme.reducedNormalization_smooth_pullback` and the explicit étale
specialization `AlgebraicGeometry.Scheme.reducedNormalization_etale_pullback`. Both proofs
are `sorry`; no definition or proof is added. The node is unchanged except for `lean`.

Hypothesis and conclusion correspondence:

- Schemes and morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`, with explicitly bound universe `u`.
- Both schemes locally Noetherian: `[IsLocallyNoetherian X] [IsLocallyNoetherian Y]`.
- Smooth morphism: `[Smooth f]` in the main theorem.
- Componentwise normalizations and canonical maps: the existing `X.reducedNormalization`,
  `Y.reducedNormalization`, `X.fromReducedNormalization`, `Y.fromReducedNormalization`.
- Right-hand scheme: `pullback f Y.fromReducedNormalization`, namely `X ×_Y Y^ν`.
- Isomorphism: `e : X.reducedNormalization ≅ pullback f Y.fromReducedNormalization`.
- Over X, with the first projection as structure map:
  `e.hom ≫ pullback.fst f Y.fromReducedNormalization = X.fromReducedNormalization`.
- Existence and uniqueness of isomorphisms over X: `∃! e : ..., ...`. This quantifies over
  all underlying scheme isomorphisms satisfying the structure-map equation, exactly the
  isomorphisms of X-schemes. The inverse compatibility follows from that equation and
  the isomorphism identities and is not a separate hypothesis.
- Étale case: the second theorem replaces `[Smooth f]` by `[Etale f]`, retaining every
  other binder and exactly the same unique isomorphism conclusion.
- No finiteness, excellence, reducedness, nonemptiness, integrality, quasi-compactness,
  or separatedness condition is imposed. No Noetherianity of either normalization or
  of the pullback is assumed.

Dependency declarations read and used:

- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth` (affine-locally smooth ring maps, as its recorded equivalence
  with formal smoothness and local finite presentation specifies).
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian` (the affine-open definition, equivalent to an
  affine Noetherian cover by the recorded cover theorems).
- `def-weil-pbc-reduced-normalization`: `Sheaf.AlgebraicGeometry.ReducedNormalization`,
  `AlgebraicGeometry.Scheme.reducedNormalization` and `fromReducedNormalization`.
  Read the full component construction: vanishing-ideal reduced components, their
  function-field normalizations, coproduct, and canonical coproduct-desc map.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback` and `pullback.fst`; the imported normalization module
  supplies the actual scheme limits.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`; read also its equivalence with flat, formally unramified,
  locally finitely presented and its smoothness instance.

Available proof dependencies are plain imports: Integral (integral base-change instances),
Proper (proper base-change instance), Flat (flat scheme morphisms), ResidueField (residue
fields and induced maps), GoingDown (`Algebra.HasGoingDown.of_flat`), and
`Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`
(`AlgebraicGeometry.smooth_and_fibre_dimension_zero_of_etale`). Smooth base change and
smooth implies flat are already provided by the public Smooth import. The three proof-only
nodes `lem-sfb-componentwise-normalization-generic-properties`,
`lem-sfb-smooth-normal-ascent`, and `lem-sfb-integral-normal-generic-recognition` have no
recorded Lean declaration at the time of reading; therefore no module can yet be imported
for them. They supply no object needed to type this statement; their proof uses are retained
in the docstring and the unchanged DAG for stage 3.

Source checked: `literature/stacks-project/more-morphisms.tex`, lemma-normalization-and-smooth,
Tag 07TD, lines 5410 onward. This says there is a unique isomorphism over X under smoothness
and local finiteness of irreducible components; local Noetherianity implies that hypothesis.
Its proof expressly reduces nonreduced schemes and imposes no finite normalization.
The docstrings reproduce all six proof steps from this node, including the generic-fibre
and going-down argument and the recognition theorem with no Noetherian source assumption.

Edge cases checked: X empty (normalization is the empty coproduct and both sides empty);
Y empty (a morphism to it forces X empty); nonreduced schemes (component construction
uses reduced induced structures; smooth pullback over reduction is reduced); identity
and open immersions; disconnected schemes and multiple components; arbitrary smooth
relative dimension and arbitrary characteristic; nonexcellent bases and nonfinite
normalizations. The statement adds no exclusion for any of these cases. Uniqueness is
over X, so generic normalization field automorphisms over X are forced to be identity.

Searches for an existing declaration:

- `msearch.py ... leanfinder "Componentwise normalization of locally Noetherian schemes
  commutes with smooth pullback, uniquely over the source"`: eight results, all relative
  normalization machinery (`Scheme.Hom.normalizationDesc`, its composition identities,
  `normalizationDiagramMap`, etc.), no componentwise absolute normalization theorem.
- `msearch.py ... loogle '"normalizationPullback"'`: seven results, including
  `Scheme.Hom.instIsIsoNormalizationPullbackOfSmooth`. Read Mathlib Normalization.lean
  lines 582–611: this is relative normalization of a supplied qcqs morphism and its
  base change. It does not identify the absolute componentwise normalizations here.
- `msearch.py ... grep 'reducedNormalization|normalizationPullback|normalization.*[Ss]mooth'
  AlgebraicGeometry`: seven results, relative normalization and its use in Zariski main.
- `rg` on `lean/WeilConjectures`, `lean/Sheaf`, `dag/lean_names_upstream.json`, and Mathlib
  for reducedNormalization, smooth/étale normalization, normalizationPullback, and the
  proposed declaration names: no exact existing statement or name collision.
  Upstream has finite étale curve-relative results; the Sheaf field-change module has
  separable field-extension and open-restriction cases, not arbitrary smooth morphisms
  of locally Noetherian schemes. The item id has no upstream declaration.

No statement fault or disputed assertion was found. No new nodes or dependency modules.

## Second reading by N9

This was a separate second pass by the same dispatcher-started worker; the brief forbids
starting other agents. The maintainer's independent delivery review remains required.
Reopened the node, source lemma, normalization definitions, and final module. Checked both
locally Noetherian binders, the smooth binder, both normalization objects, pullback order,
first projection equation, and unique quantifier against the statement. The étale theorem
has the same conclusion and uses the established étale notion. All universes and variables
are explicitly bound. No stronger existence claim or extra geometry hypothesis occurs.
The two proofs are `sorry` and have source/blueprint/proof docstrings. No mismatch was found.
