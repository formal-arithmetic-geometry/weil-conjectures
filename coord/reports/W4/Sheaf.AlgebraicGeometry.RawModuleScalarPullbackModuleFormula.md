## What changed

Repair of reviewer X-3d4a1's landing conflict: took `RawModuleScalarCoefficientSquare.lean` from the current `sheaf-dag` source, reapplied only the relocation/public re-export of `moduleCoefficientFactor` and `abelianCoefficientFactor`, and retained both current coefficient-square theorem proofs and `import all Sheaf.AlgebraicGeometry.HigherDirectImageOverMapCoefficient` byte-for-byte. The obsolete private shift-compatibility helpers from the returned sandbox are removed. `RawModuleScalarSourceFactors` explicitly publicly imports `HigherDirectImageRawTrianglePullback`, whose new shared source occurs in its public definition body; this makes the direct dependency visible to both delivery compilers. The old delivery's retained shift-transport `sorry` is not restored. The delivery tool fetches `origin/sheaf-dag` and reconstructs the commit on the fetched base. Fresh `lcompile.py --all` verification passed for all nine delivery modules without errors or warnings. The retained coefficient-square proof compiled in 46.6 seconds; the formula compiled in 51.4 seconds; the slowest file took 51.4 seconds, below the unchanged 60-second limit.

Proved `AlgebraicGeometry.Etale.rawModuleScalar_pullback_module_formula` with `rfl`, with its original signature. The source pair is shared by `rawTriangleMap` and `moduleSourceFactor` through the concrete `rawTriangleSource` construction. `moduleCoefficientFactor` now reuses `higherDirectImageRawOverComplex` and `higherDirectImageRawOverCoefficient`, including their instance parameters.

Moved the two module and abelian coefficient factor definitions to `Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientFactors`, re-exported publicly from `RawModuleScalarCoefficientSquare`. The formula imports the canonical definitions module. The canonical definitions import only `HigherDirectImageRawOverCoefficient` and `CohomologyPresheaf`; the scalar comparison, unshifted coefficient theorem, exact-functor proof import, and local attributes are unnecessary there. `scalarCoefficientFactor` stays byte-for-byte unchanged in `RawModuleScalarCoefficientSquare`.

Adapted the existing raw-triangle naturality, composition, adjunct and identity proofs by unfolding the shared source and normalizing associativity. Grouped the first two factors in RawDiagram's private additive lemmas. Every existing public declaration signature and visibility stays unchanged. The change record is `coord/changes/W4-raw-module-pullback-shared-factors.md`.

Fresh repair verification also compiled all thirteen unchanged current client sources in `scratch/repair-verify`, with no errors or warnings and every file below 60 seconds. The parent conjunction compiled in 38.6 seconds and needs no source change. The existing validation module compiled in 55.1 seconds; its equalities identify the old and new generic raw composites by `Category.assoc` and the old and new module source/coefficient expressions by `rfl`. Fresh `#print axioms` for `rawModuleScalar_pullback_module_formula`, `rawModuleScalar_pullback_formulas`, `rawModuleScalar_pullback_abelian_formula`, `rawModuleScalar_coefficient_square_of_unshifted`, and `rawModuleScalar_coefficient_square` all show exactly `propext`, `Classical.choice`, and `Quot.sound`. The current source snapshot used for the repair matches the live server's checked source hashes. The retained coefficient proofs and structural-exact import are unchanged. The prior second reading is archived in scratch; the repaired delivery awaits its independent second reading.

## Proved and sorry left

Closed one original hole:

- `AlgebraicGeometry.Etale.rawModuleScalar_pullback_module_formula` (`lem-sbc-raw-scalar-pullback-module-formula`). The proof is `rfl` after sharing the actual factors; it uses no scalar comparison theorem.

Added zero holes and split off zero statements. The item's module has no remaining `sorry`. The current coefficient-square module has already closed `AlgebraicGeometry.Etale.rawModuleScalar_coefficient_square_of_unshifted` (`lem-sbc-raw-scalar-coefficient-square-shift-transport`). This repair preserves that proof and its existing structural-exact import unchanged. No delivered module contains a remaining `sorry`.

All nine delivered modules contain no `sorry`. The new node records existing concrete definitions in their canonical home, with no proof obligation. The old coefficient-square node now lists the unchanged scalar factor and square theorem; the relocated module and abelian factors belong to the new node.

## No longer needed

Removed `Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare` from the formula's public imports, replacing it with the canonical coefficient definitions. Removed its redundant proof import of `Sheaf.AlgebraicGeometry.HigherDirectImageRawDiagram`, already public through the source/factor definitions.

The new canonical definitions do not import `Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison`, `Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted` or `WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor`. The formula needs no `rawModuleScalar_source_square`, no `rawModuleScalar_coefficient_square` or `rawModuleScalar_coefficient_square_of_unshifted`, and no relation between a module class and an abelian class. Thus the source-square, coefficient-square, and coefficient-shift-transport statements are unnecessary for this leaf. Other clients may still need them; none of their modules is withdrawn.

The leaf's old `proof_deps` contained only `def-sbc-higher-image-raw-diagram`, which remains used; no old leaf proof-dependency node was removed. The current coefficient-square node already records its direct application of `lem-sbc-raw-scalar-coefficient-square-shift-transport`; this repair retains that proof route and updates only its Lean record for the relocated factors. Their definitions and source APIs remain available through the statement imports; no module is withdrawn. No new associativity or evaluation statement is needed. The existing abelian formula, parent conjunction, shared raw-complex continuity APIs, and unit route are preserved. The parent conjunction already imports the two component formula theorems and has no direct hole to close.

## Where the brief, the DAG or earlier work was wrong

The first worker unnecessarily moved the scalar coefficient factor alongside the two pullback factors. It is not used by this leaf and already exists in RawModuleScalarMapFormula. The second reader retains it in its original coefficient-square module and creates no new copy. The route note is correct: independently expanding the same derived-category instances causes the expensive concrete associativity comparison; sharing the factors makes the original formula definitionally true. The node's proof now records this route. No mathematical statement was corrected or weakened.

The current Hom-composite module already uses its generic `map_three_factors` lemma, so the older concrete Hom-expansion failure described in the route evidence requires no additional change here. A rebuilt parent conjunction is axiom-clean; the cached parent artifact still used the previous holed leaf until that rebuild. The delivery compilers inspect explicit sibling imports. The identity module needs its direct proof import of the shared source module. The first server-enabled repair dry run rejected standalone `RawModuleScalarSourceFactors` with `Unknown identifier rawTriangleSource`, because its original import path reached the sibling only indirectly. The repair adds the direct public import required by its definition body, so the delivery compiler treats it as a dependent member of the set. No theorem or definition signature changes.

Claims were rechecked read-only on the live project at 22:30 +08 on 2026-10-14: W4 holds this item; the coefficient-square module and all other changed prerequisites and adapters are unclaimed. This delivery changes no module held by another group. Target statements are untouched; review of the extensionally equal definition refactor and the global build remain the maintainer's checks.

## New nodes

`def-sbc-raw-scalar-coefficient-factors` records the two existing module and abelian coefficient morphisms moved to the canonical `RawModuleScalarCoefficientFactors` module. The module factor uses the existing named raw coefficient and complex; the abelian factor retains its old expression and public type; the scalar factor remains in its original module. The node has no theorem and no `sorry`. Change record: `coord/changes/W4-raw-module-pullback-shared-factors.md`.


## Forced adaptations

Before this repair, the second reader compiled each original adapter against the freshly compiled changed definitions.
`HigherDirectImageRawTrianglePullbackComposition` fails at its rewrite because the source factors
remain folded in `rawTriangleSource`; adding that definition to its existing unfold is necessary.
`HigherDirectImageRawPullbackIdentity` fails with a type mismatch between the old expanded composite
and the regrouped raw pullback; unfold the three definitions and normalize associativity first.
`HigherDirectImageRawTriangleAdjunct` hits the default heartbeat limit in its convert without the
normalization; prove the normalized raw-map equality locally, then apply the existing generic adjunct theorem directly.
`HigherDirectImageRawDiagram` hits the default heartbeat limit when applying its private five-factor
lemmas; regroup their source pair by associativity. The exact old and new private signatures are
recorded in `coord/changes/W4-raw-module-pullback-shared-factors.md`. Existing public signatures and
visibility are unchanged in every adapter. No module claimed by another group is adapted.

## Second reading by W4

1. I compared every delivered module with the repository version. Existing public
   declaration signatures and visibilities are unchanged; the declared changes are
   the shared `rawTriangleSource`, relocation of the two coefficient-factor definitions,
   the direct public import, and proof-only adaptations. Verdict: pass.

2. I compiled all nine delivered Lean modules with `lcompile.py --all`. They compile
   without errors or warnings, contain no `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, `extern`, or `debug.skipKernelTC`, and the formula closes by
   `rfl`. Verdict: pass.

3. I checked the split-off definition node and the formula node against the delivered
   declarations, their docstrings, and local searches of `lean/`; the definitions are
   concrete existing constructions, the formula is unchanged and strictly uses the
   shared factors, and no duplicate library theorem replaces them. Verdict: pass.

4. I checked the proof from the target downward. The formula uses only the raw diagram,
   source factors, and canonical coefficient factors; the removed coefficient-square
   theorem and scalar-comparison imports are unused. The forced adapter proofs preserve
   the unit route and the change record identifies every regrouping. Verdict: pass.

5. I checked that the formula node's `proof`, `proof_deps`, and `proof_origin` match
   the `rfl` proof, that the new definition node has no proof obligation, and that the
   realized unit route remains unchanged. Verdict: pass.

I changed nothing during this second reading because the delivered proofs, interfaces,
node metadata, and pruning are consistent. The required delivery dry run is the final
mechanical check.
