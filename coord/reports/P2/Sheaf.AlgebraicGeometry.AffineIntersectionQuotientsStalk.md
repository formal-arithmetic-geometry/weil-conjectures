## What changed

Proved `AlgebraicGeometry.affine_intersection_quotients_stalk` in
`Sheaf.AlgebraicGeometry.AffineIntersectionQuotientsStalk`, with its signature unchanged.
The proof constructs the source as `LocalizedModule` of the scalar-restricted L.
The maps are Mathlib localized maps, and the order homomorphism is submodule localization.
Surjectivity, compatibility, the kernel formula, and the ideal-power formula are proved directly.
Proof-only imports added: `Sheaf.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization`,
`Mathlib.Algebra.Module.LocalizedModule.Submodule`,
`Sheaf.AlgebraicGeometry.QuasicoherentPushforwardQcqs`, and
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`.
Updated the item's DAG proof, proof dependencies, and proof origin to this route.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.affine_intersection_quotients_stalk`
(node `lem-weil-pbc-affine-intersection-quotients-stalk`). No holes added or left.
No existence theorem with an arbitrary unproved witness supplies the module:
`LocalizedModule` and the localized maps are actual constructions. The auxiliary
localized germ is determined pointwise by the actual germ map.
The argument includes r=0 and requires neither finite generation nor Noetherianity.
An empty affine open has no x; zero L and zero/unit ideals require no separate assumption.
The single-file compile is clean, and the delivery dry run checks permitted axioms
and stage-3 metadata; independent second reading remains the next worker's step.

## No longer needed

No existing import was removed: the three public imports supply the existing signature.
Removed the exploratory proof import `Mathlib.RingTheory.Localization.Ideal`: the proof
uses submodule localization and the already available ideal-map formulas.
The proof does not need these former planned dependencies:

- `lem-weil-pbc-affine-tilde-gamma-adjunction` (`Mathlib.AlgebraicGeometry.Modules.Tilde`):
  affine stalk germ localization supplies the comparison directly.
- `lem-weil-pbc-spec-module-tilde-sections` (`Mathlib.AlgebraicGeometry.Modules.Tilde`):
  no associated-sheaf object is constructed.
- `lem-weil-pbc-module-restriction-open-immersion-colimits`
  (`Mathlib.AlgebraicGeometry.Modules.Sheaf`): no restriction/colimit comparison is needed.
- `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`
  (`Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`): the existing
  `IdealSheafData.range_toModulesι_app` calculates the affine ideal inclusion instead.
- `lem-weil-pbc-ideal-module-product-stalk`
  (`Sheaf.AlgebraicGeometry.IdealModuleProductStalk`): localization of ideal smul and
  ideal extension powers give the required formula without sheaf products.

These nodes are removed only from this item's proof dependencies; other users may still need them.
None realizes a required statement or step of the item's unit `sk-thm-p1`.

## Where the brief, the DAG or earlier work was wrong

The DAG's mathematical plan is valid but uses more sheaf machinery than needed.
The proof can use the already proved affine germ-localization interface and Mathlib's
localized kernel, range, and ideal smul formulas. No statement or definition was corrected.
The local checkout does not contain the cited Stacks .tex bodies. Read the Stacks tag pages
01IB, 01IC, 00CS, 01HV, 01LC, and 01I8 directly; they support the affine module/stalk
comparison, localization exactness, quasi-coherent kernels and pushforward, and products.

## Second reading by P2

1. **Interface unchanged.** I compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof-only imports and the theorem proof differ.

2. **Proof validity.** The module compiles cleanly with `lcompile.py`. The proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition. It constructs `LocalizedModule` and localized maps explicitly. The proof handles the transition maps, kernel formula, and ideal-power formula, including `r = 0`; no arbitrary witness is selected from an unproved existence theorem.

3. **Statements and nodes.** The sole target statement remains exactly the DAG statement. No new split-off statements were introduced. The existing node's proof route and dependencies agree with the implementation: affine germ localization, localized kernel/range formulas, and quasi-coherent pushforward/kernel facts are the declarations actually used. The node metadata records the proof-only route and the imports removed from the former plan.

4. **Pruning and imports.** The added imports are proof-only (`AffineModuleGermLocalization`, `LocalizedModule.Submodule`, `QuasicoherentPushforwardQcqs`, and `QuasicoherentKernel`), while the three public imports remain required by the theorem interface. The exploratory ideal-localization import and the former tilde, restriction-colimit, ideal-product, and ideal-stalk proof dependencies are not used. The unit route is preserved through the affine germ-localization step.

5. **Source and edge cases.** The report's Stacks sources support the localization and quasi-coherent kernel/pushforward steps. I checked the edge cases represented in the proof (zero/unit ideals, zero modules, and `r = 0`); no extra hypotheses are introduced and no conclusion is weakened.

No code changes were needed during this second reading.
