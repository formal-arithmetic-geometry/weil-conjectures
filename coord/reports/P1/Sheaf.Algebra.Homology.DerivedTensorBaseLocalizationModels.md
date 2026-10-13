## What changed

The target module now constructs its canonical base-localization map from the
restricted derived functor. The target combines two named obligations for
invertibility and comparison compatibility with the proved naturality theorem.
The canonical map is real data constructed by a universal lift, and its generator
formula determines the chosen isomorphism uniquely. The unfinished obligations
have source citations and complete proof descriptions.

## Proved and sorry left

The target declaration `RingTensorCohomology.derivedTensor_base_localization_models`
has a complete reduction proof from the three intermediate declarations (the
invertibility and comparison declarations remain sorry obligations).
`RingTensorCohomology.baseLocalizationTensorIso`,
`baseLocalizationCounit`, `baseLocalizationDerivedMap`,
`baseLocalizationInputIso`, `baseLocalizationCohomologyMap`,
`IsBaseLocalizationMap.ext`, `baseLocalizationInputNatIso`, and
`baseLocalization_naturality` are proved. Sorry remains in
`exists_baseLocalization_iso` and `baseLocalization_comparison`; each is a separately
named theorem with a blueprint node and a complete proof plan in its docstring.
Holes closed: one original target hole. Holes added: two strictly smaller holes.
This is a decomposition, not a net reduction of holes.

## No longer needed

The original public imports remain needed for the statement. The route now resolves
Q over Rp and restricts its resolution to R, instead of using a balanced resolution
of the second factor. The original proof dependencies
`lem-pc-balanced-derived-tensor-model` (module
`Sheaf.Algebra.Homology.BalancedDerivedTensorModel`),
`lem-pc-derived-tensor-action-naturality` (module
`Sheaf.Algebra.Homology.DerivedTensorActionNaturality`), and
`lem-pc-kflat-extension-of-scalars` (module
`Sheaf.Algebra.Homology.KFlatModuleBaseChange`) are no longer required by this route.
No existing import line was removed: these were planned DAG dependencies, not imports.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan omitted the universal derived-functor lift and the ordinary
restriction/extension factorization needed to define a canonical map. An
arbitrary chosen isomorphism cannot establish the comparison or naturality
clauses. The delivery adds strictly smaller named statements for these steps.

## New nodes

`lem-pc-base-localization-map` records the canonical universal-lift map and its
generator characterization. `lem-pc-base-localization-iso` records its
invertibility. `lem-pc-base-localization-comparison` records compatibility with
localized comparison. `lem-pc-base-localization-naturality` records naturality.

## Second reading by P1

1. Compared the delivered target module with the repository version: all existing
   declaration signatures are unchanged; only proof imports and the target proof
   differ, with the auxiliary declarations split into new modules.
2. Compiled all five delivered modules with `lcompile.py --all`; compilation
   succeeds. The only remaining `sorry`s are the named split-off theorems
   `exists_baseLocalization_iso` and `baseLocalization_comparison`; no sorry is
   inside a definition and no forbidden declaration was introduced.
3. Checked that the split-off statements are strictly smaller obligations, have
   source citations, proof plans, and matching DAG nodes, and do not restate the
   target.
4. The target proof follows the characterized-map route through the three
   split-off declarations. The report records planned dependencies no longer
   needed by this route.
5. The target node and unit route remain intact: it still realizes
   `sk-thm-picard-semicon`, and DAG proof metadata matches the Lean reduction.

I changed only this report section; no Lean statements or proofs needed repair.
