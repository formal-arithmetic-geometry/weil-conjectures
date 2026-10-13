## What changed

Proved `AlgebraicGeometry.exists_mixedAffineSections_chart_model_factorization` in the
item module. The proof introduces three strictly lower intermediate statements in
separate modules: the affine sections complex unit, extension unit normalization,
and pullback unit normalization. The main proof lifts `hc` to complexes, applies the
normalization statements, and cancels the invertible sections comparison.

## Proved and sorry left

Closed the hole in `AlgebraicGeometry.exists_mixedAffineSections_chart_model_factorization`.
This is a decomposition: one hole closed and three holes added (net -2), not a complete axiom-free proof. The following new intermediate declarations remain
`sorry`, each with a docstring describing its source and proof: 
`mixedAffineChart_sectionsComplexUnit_isIso`,
`exists_mixedAffineSections_extension_unit_normalization`, and
`exists_mixedAffineSections_pullback_unit_normalization`.

## No longer needed

The direct imports of `AffineTildeDerivedSectionsUnitIsIso`, `TensorPullbackTilde`,
and `AffineKFlatPullbackChartComparison` were replaced by the intermediate modules;
their declarations are used through those modules' stated reductions.

The old direct `proof_deps` replaced by the three normalization nodes are
`lem-pc-affine-kflat-pullback-chart-comparison`, `lem-pc-affine-tilde-kflat`,
`lem-pc-global-hom-adjunction`, `lem-sc-mixed-global-extension-adjunction`,
`lem-sc-mixed-global-sections-direct-image-iso`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-weil-pbc-tilde-pullback-base-change`, and
`new-affine-tilde-derived-sections-unit-isIso`. These remain needed below the
normalization nodes or by the public statement imports. No module is claimed
pruned from the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The original repository DAG plan already described the localization and naturality
glue. The first worker's sandbox node records replaced that with generic
“proof remains to be supplied” descriptions, including for the now-proved parent.
The second reading repaired these records to describe the actual cancellation
proof and the sourced plans for the three strictly smaller open statements.

## Earlier second reading (a previous round; superseded)

The item and all three new modules compile; the main statement is unchanged. Each new theorem is a strict intermediate unit or normalization statement, with the target assembled by a real Hom-equivalence cancellation proof.

## Second reading by J4

1. **Statement preservation:** Compared the delivered item module with the repository version. The target theorem signature is byte-for-byte unchanged; only its proof and proof-only imports changed. Verdict: pass.
2. **Proof and axioms:** Compiled all four delivered modules with `lcompile.py --all`. The target has no `sorry`, and the only remaining `sorry`s are the three named intermediate theorems listed above, each with a docstring and DAG node. No forbidden declarations occur. Explicit `#print axioms` in a scratch copy showed exactly `propext`, `Classical.choice`, `Quot.sound`, plus `sorryAx` in the four theorems. The constructed `mixedSectionsComplexUnit` definition has no `sorryAx`. Verdict: pass with the reported open dependencies.
3. **New statements:** Read each intermediate theorem and checked its hypotheses and conclusion against the construction used in the parent proof. LeanSearch was attempted and returned Internal Server Error (recorded unavailable). Independent LeanFinder, Loogle and grep searches found generic factors/naturality tools but no duplicate. Read the spectrum affine extension/unit modules and chart pullback comparison: they supply components but not these arbitrary-chart formulas. The new statements are strictly smaller unit/normalization claims and do not restate the parent target. Edge cases (zero complexes and zero maps) are covered by their universal formulations. Verdict: pass.
4. **Pruning and imports:** The parent proof uses the three normalization modules and no longer directly imports the affine derived-sections, tensor-tilde, or affine K-flat comparison modules. The removed imports are recorded in “No longer needed”; proof-only imports remain plain `import`. Removed the unused public KFlat import from the new sections-complex-unit module; its signature has no K-flatness assumption. Verdict: pass.
5. **DAG and route:** Updated node proof descriptions and dependencies to match the cancellation proof and the three intermediate applications. Inspected `dag/units/sk-thm-picard-duality.json`: its `realized` statement and step lists are empty, so this item is not a designated unit realization; the existing chart-factorization route and parent blueprint provenance remain intact. Verdict: pass.

Second-reading repairs: corrected generic DAG plans and their dependency unions, restored exact signature whitespace, removed the unnecessary public KFlat import in the new comparison module, recorded independent searches and explicit axiom output, and made the hole accounting explicit. No existing declaration signature or definition changed.

## New nodes

`lem-sc-mixed-affine-chart-sections-complex-unit-isIso` matches
`AlgebraicGeometry.mixedAffineChart_sectionsComplexUnit_isIso`, still open in
`MixedAffineSectionsComplexUnit`. Its data-bearing comparison is explicitly constructed.

`lem-sc-mixed-affine-extension-unit-normalization` matches
`AlgebraicGeometry.exists_mixedAffineSections_extension_unit_normalization`,
still open in `MixedAffineSectionsExtensionUnitNormalization`.

`lem-sc-mixed-affine-pullback-unit-normalization` matches
`AlgebraicGeometry.exists_mixedAffineSections_pullback_unit_normalization`,
still open in `MixedAffineSectionsPullbackUnitNormalization`.

No change records are needed: no existing interface changed.
