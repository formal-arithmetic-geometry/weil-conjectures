## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_finite_generatingSections_tensorPow_of_affine_section_cover` in `Sheaf.AlgebraicGeometry.AffineSectionCoverTwistGeneration`, with its signature and visibility unchanged. The proof chooses finite spanning families of affine sections, clears their denominators, takes their finite maximum exponent, multiplies each lift into every higher degree, and proves the free evaluation map is surjective on the affine cover.

Added two fully proved private helpers: `finite_sections_of_finiteType` and `eqToHom_app_tmul_tensorPow`. The former adapts the already proved private finite-section helper in `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`; its localization descent avoids needing a finite-type restriction instance or the stronger bundled affine-generation theorem. Added proof-only imports of `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` and `WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`. Kept the original public imports and the proof-only ClearDenominators import. Updated the item's DAG proof and proof dependencies.

The local compile passes without warnings (about 13 seconds). A separate `#print axioms` check reports exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The construction includes empty finite index types and tensor degree zero: the maximum of the empty exponent family is zero and empty sums are used without a positivity hypothesis. No definitions or existing signatures were changed. Source arguments were checked against Stacks [01PB](https://stacks.math.columbia.edu/tag/01PB), [01PW](https://stacks.math.columbia.edu/tag/01PW), and the local-extension paragraph of [01Q3](https://stacks.math.columbia.edu/tag/01Q3).

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.exists_finite_generatingSections_tensorPow_of_affine_section_cover`
(node `lem-weil-pbc-affine-section-cover-twist-generation`).

No sorry remains in the delivered module. No holes were added or split off. The two private helpers are completely proved. The public theorem has only the three permitted axioms, so this is a proof, not a decomposition through unproved lower statements.

## No longer needed

Removed the proof-only import `Sheaf.AlgebraicGeometry.AffineFiniteTypeGeneratingSections` and the corresponding proof dependency `lem-weil-pbc-affine-finite-type-generating-sections`: the proof needs finite spanning sections on affine opens, which the proved private helper supplies directly, rather than its bundled finite global-generation conclusion. Consequently this item no longer needs the import branch through `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine` or `Sheaf.AlgebraicGeometry.Coherent` that this removed import supplied. Other target paths may still need these modules; this report makes no claim that they are globally unreachable.

Replaced `lem-weil-pbc-locally-surjective-iff-stalks` as a direct proof dependency with the already proved `lem-weil-pbc-quasicoherent-epi-affine-cover` (`epi_of_surjective_app`, QuasicoherentKernel). The proof does not use a separate stalkwise-surjectivity comparison. Restriction, basic-open localization, and localization finiteness descent are retained and recorded explicitly in the revised DAG. The unit's realized statement and steps are unchanged; this item is not among the unit's realized nodes.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was wrong. The plan omitted that the convenient forward finite-section result in `QuasicoherentFiniteTypeAffine` is private, and Mathlib does not automatically supply finite-type restriction instances here. Reusing its fully proved local argument avoids adding a new unproved restriction lemma. The source library's twisting and affine-cover epimorphism results suffice for all remaining steps. All existential choices occur inside the theorem proof; no definition chooses arbitrary data from an unproved existence statement.

## Second reading by A4

1. Compared the delivered module with the repository version. The existing public theorem signature, visibility, and statement are byte-for-byte unchanged; only the author line, imports, private helpers, and proof body differ. Verdict: pass.

2. Compiled the module with the launcher lcompile tool. It compiles without errors or warnings, contains no sorry, axiom, unsafe, opaque, extern, implemented_by, or sorryAx, and the proof uses only the permitted standard axioms. Verdict: pass.

3. Checked the new private helpers and searched the local library and recorded Mathlib searches for an existing equivalent. The helpers are strictly intermediate facts: finite section modules on affine opens and transport across equal tensor-power indices. Both are fully proved and are needed by the main reduction; no statement was split off. Verdict: pass.

4. Read the proof from the target downward. It uses the finite affine-section construction, denominator clearing, tensor-power multiplication, and affine-cover epimorphism, including empty index and degree-zero cases. The removed affine finite-type generating-sections import and the stalkwise-surjectivity dependency are genuinely unused; the revised proof dependencies match the code. Verdict: pass.

5. Compared the revised node proof and proof_deps with the Lean proof and checked the unit record. The DAG records the direct localization argument, denominator clearing, and affine-cover epi route, and the unit's realized route remains unchanged. Verdict: pass.

Changed during second reading: no Lean statements or proofs; this report section only.
