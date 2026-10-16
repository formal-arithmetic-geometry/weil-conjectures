## What changed

Reduced `finiteDiscreteCoefficient_coefficientUnit_pushforward` to its strict specialization at the
pullback of the terminal object over Spec Z. The item proves propagation to arbitrary V by two
constant-presheaf naturality equations and naturality of the coefficient pushforward map.

`FiniteDiscreteSchemeRing` and `ModuleObject.Basic` retain the exact original constructions through
proved equality APIs. Each chosen witness is uniquely specified by equality to the original explicit
data, with a proved existence theorem. The coefficient pushforward composition-unit API is proved.
Four unclaimed consumers adapt only proofs; every existing signature and visibility is unchanged.
All four adaptations compile against the changed dependencies.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteCoefficient_coefficientUnit_pushforward`
(node `lem-weil-pbc-finite-discrete-coefficient-sections`).

Added and remaining: `AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteCoefficient_coefficientUnit_pushforward_terminal`
(node `lem-weil-pbc-finite-discrete-coefficient-terminal`). This is a decomposition: one upper hole
closed, one strictly smaller terminal obligation added, net zero holes closed. Zero other holes are
added by the definitions, their equality APIs, the composition-unit API, or adapted consumers.

The terminal obligation still needs the conjugation-unit formula for constantSchemeIso, its
naturality in eR, and the evaluation of the composition-unit equation followed by two restriction
naturality equations. A complete natural-language proof is in its docstring. A complete elaborating
attempt was developed, but kernel checking of its terminal conversions remains too expensive.

## No longer needed

No planned dependency modules are pruned. The sole public import remains necessary for the statement.
The proof imports the new terminal module privately. Unused private terminal-conjugation helpers from
the exploratory proof are omitted from the delivery; no additional imported obligations are added.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is sufficient and the statement includes the empty-scheme and zero-ring cases.
The practical obstacle was kernel conversion of concrete inverse-image and scheme-pullback data.
The exact defining-equation APIs remove expensive implicit unfolding in downstream consumers and
in the final naturality argument. The remaining terminal conversion requires further work.

## Forced adaptations

All adapted consumers are unclaimed. Original `ContinuousChartSchemeNaturality`,
`CondensedQbarScalarPullback`, `CondensedFieldGeometricRegularCoefficient`, and
`IntegralMatrixCoefficientTransport` failed against the changed coefficient map: unfolding exposed
`Classical.choose` instead of the unit composite, causing failed simplification or conversion.
The delivered proofs replace unfolding by `condensedPushforwardHom_def`. The scalar-square uses
also rewrite this defining equation before applying the existing adjunction identity. No statement
or visibility changes. All four adapted modules compile together.

## New nodes

`lem-weil-pbc-finite-discrete-coefficient-terminal` is the strict terminal-object part of the original
plan; general sections follow by the proved naturality argument. It has the same coefficient and
scheme hypotheses, but fixes the test object and does not assert the arbitrary-section result.

Change records: `coord/changes/D3-coefficient-pushforward-api.md` and
`coord/changes/D3-finite-discrete-comparison-api.md`.

## Second reading by D3

1. **Declarations and signatures.** Compared every delivered module with the shared repository. The existing target and consumer signatures are unchanged byte for byte; the definition/API changes are covered by `coord/changes/D3-coefficient-pushforward-api.md` and `coord/changes/D3-finite-discrete-comparison-api.md`. Verdict: pass.

2. **Proof and axioms.** Compiled all sandbox modules individually and with `lcompile.py --all`. The only remaining `sorry` is the named public theorem `finiteDiscreteCoefficient_coefficientUnit_pushforward_terminal`, recorded by node `lem-weil-pbc-finite-discrete-coefficient-terminal`; no definition contains `sorry`, and no forbidden declaration is present. Verdict: pass subject to this explicitly documented split theorem.

3. **New statements and searches.** Checked the terminal theorem against the displayed Lean statement, its docstring, source references, and the node metadata; it is the strict terminal specialization and is strictly simpler than the item theorem. The equality APIs specify their chosen data exactly, so they do not introduce arbitrary witnesses. Existing library and Mathlib searches in the node records found no duplicate. Verdict: pass.

4. **Pruning and imports.** The item retains its required public import and uses the terminal module privately. The proof dependency of the item is exactly the terminal node; no planned unit dependency is pruned. The four consumer adaptations use only the new defining equation and compile. Verdict: pass.

5. **DAG and route.** The item node proof and `proof_deps` match the naturality proof, and the terminal node records the decomposition and its unit route. The unit's realized route is unchanged. Verdict: pass.

Changed in this second reading: no Lean proof or statement changes; added this review section to satisfy the stage-3 delivery contract.
