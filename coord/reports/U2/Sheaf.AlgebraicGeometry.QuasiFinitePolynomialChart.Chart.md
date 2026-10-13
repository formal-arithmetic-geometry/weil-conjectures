## What changed

Proved `AlgebraicGeometry.exists_quasiFinite_polynomial_chart_data` with its original
signature, universes and visibility. The proof equips the coordinate rings with the
algebra structure induced by `f.appTop`, transfers the supplied local fibre dimension,
applies the already proved `Algebra.exists_quasiFinite_over_polynomial_algebra`, and
realizes its localized polynomial map on the affine basic open containing y.

Added two fully proved bridge modules, imported only for the proof:

- `Sheaf.AlgebraicGeometry.QuasiFinitePolynomialChart.CoordinateFibreDimension`:
  `AlgebraicGeometry.affine_coordinate_fibre_dimension_eq`. Three homeomorphisms compare
  the specified fibre points. Two private proved helpers establish local-dimension
  invariance directly from inducing maps and the infimum defining local dimension.
- `Sheaf.AlgebraicGeometry.QuasiFinitePolynomialChart.LocalizedChart`:
  `AlgebraicGeometry.exists_chart_of_localized_polynomial_map`. It explicitly constructs
  the spectrum morphism from the canonical localization equivalence and polynomial
  variable renaming. It proves finite presentation, local quasi-finiteness and the
  composite identity. Its private `quasiFinite_of_primewise` proves that the supplied
  isolated-point conditions give finite contraction fibres, using compactness and
  discreteness of fibre spectra.

Updated the item's proof, proof dependencies and proof origin to match this route.
No existing statement or definition changed, and no consumer adaptations are required.
The declaration-local unused-variable linter setting preserves the original unused
existential binder `hy` verbatim.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_quasiFinite_polynomial_chart_data`
(node `lem-sbc-quasi-finite-polynomial-chart-chart`).

Also fully proved `AlgebraicGeometry.affine_coordinate_fibre_dimension_eq`
(node `lem-sbc-affine-coordinate-fibre-dimension`) and
`AlgebraicGeometry.exists_chart_of_localized_polynomial_map`
(node `lem-sbc-localized-polynomial-map-chart`), including every private helper.

Holes closed: 1. Holes added: 0. Sorries left in delivered modules: none.
This is a proof, not a decomposition into new holed statements.

All three modules compile cleanly together in dependency order through `lcompile.py`.
Individual `#print axioms` checks for all three public theorems show exactly
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

Edge cases were checked in the argument: the dimension comparison does not assume finite
or positive dimension; the realization lemma works for n = 0 and g = 0. The final
application obtains g outside the prime of y, so y belongs to its basic open. No
injectivity of the polynomial map, domain hypothesis, flatness hypothesis, or arbitrary
witness chosen from an unproved existence theorem is used.

## No longer needed

The original direct proof dependencies
`lem-weil-pbc-fibre-product-affine-spectra` and
`lem-weil-pbc-spec-localization-away-basic-open` are removed from the item's route.
The dimension comparison uses `Scheme.Hom.fiberHomeo`, affine naturality and
`PrimeSpectrum.preimageHomeomorphFiber`, rather than `pullbackSpecIso`. The geometric
realization uses the actual ring-of-sections localization instance and
`IsLocalization.algEquiv`, rather than separately transporting the spectrum along the
basic-open homeomorphism.

No original import was removed: the original five public imports supply the unchanged
statement's API. No existing Sheaf or WeilConjectures module is claimed to become globally
unreachable. The two removed nodes are Mathlib-backed dependencies; their underlying
Mathlib modules remain available transitively.

Removed the exploratory proof imports `Mathlib.Topology.LocalAtTarget` and
`Mathlib.RingTheory.Localization.Away.AdjoinRoot` from the new modules after verifying
that their proofs compile without them. The only new proof imports of the item are
the existing ring theorem and the two delivered bridge modules.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's failure to state the affine transport was not a mathematical
obstruction. Both geometric bridges now have complete proofs in Lean. In particular,
transport need not choose an affine presentation or a noncanonical witness: the
canonical global-sections localization equivalence constructs the required map.

The existing docstring calls Tag 00RH an "affine translation". More precisely,
[Tag 00RH](https://stacks.math.columbia.edu/tag/00RH) is the algebraic Cohen-Macaulay-locus
lemma whose first reduction applies [Tag 00QE](https://stacks.math.columbia.edu/tag/00QE).
The original docstring is preserved; the new modules state this attribution precisely.
The fibre-topology comparison is the one described by
[Remark 00E6](https://stacks.math.columbia.edu/tag/00E6).

The unit record `sk-prop-normal-form` has no realized binding for this item. The delivery
retains the planned polynomial-chart argument and its ring theorem; it does not bypass
the unit's normal-form or slicing steps. Blueprint searches for the proposed bridge
statements found no matching imported blueprint node. The ancestor tool returned None
for this previously created item; the new nodes retain its recorded parent
`lem-sbc-quasi-finite-polynomial-chart` and identify the precise affine-chart steps.

## New nodes

`lem-sbc-affine-coordinate-fibre-dimension`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-affine-coordinate-fibre-dimension.json`, records
the fully proved dimension bridge. Its statement has no finite-presentation or finite-type
hypothesis, and its conclusion is only the equality of the two local fibre dimensions.

`lem-sbc-localized-polynomial-map-chart`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-localized-polynomial-map-chart.json`, records the
fully proved realization bridge. It assumes a supplied polynomial map and concludes a
chart on the fixed basic open; it has no chosen point or fibre-dimension hypothesis.

Both nodes carry source references, complete proofs in words and exact Lean signatures.
LeanFinder/Loogle and Mathlib source searches supplied the components used. LeanSearch
returned an HTTP 500 and is recorded as unavailable, rather than as evidence of absence.
There are no change records because no existing interface changed.

## Second reading by U2

1. **Interface and statements.** Compared `Chart.lean` with the repository version: the
   existing theorem signature is byte-for-byte unchanged. The two added public bridge
   theorems match their DAG node signatures, and no target statement or definition was
   changed. Verdict: pass.
2. **Proof and axioms.** Compiled all three modules with `lcompile.py --all`; there are no
   `sorry`, forbidden declarations, or hollow definitions. The public theorem proofs use
   only the permitted constructions; individual axiom checks report `propext`,
   `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. **New statements.** Checked both bridge statements against their edge cases (including
   empty basic opens and zero variables) and searched Mathlib and the local library for
   duplicates. They are true, strictly intermediate, and needed by the chart proof.
   Verdict: pass.
4. **Pruning and route.** The proof follows the planned affine fibre-dimension, localized
   polynomial map, and ring quasi-finiteness route. Proof-only imports are plain `import`,
   and the exploratory imports removed by the worker are recorded above. Verdict: pass.
5. **DAG and unit records.** The item and both new node records agree with the Lean
   declarations, dependencies, sources, and proof route; the planned unit route is retained.
   Verdict: pass.

I changed only this report section; no Lean code, declarations, imports, or DAG statements
were altered during second reading.
