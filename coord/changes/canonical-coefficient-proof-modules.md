# WeilConjectures.canonicalCoefficientPullbackReduction

## Reason

The complete monolithic proof took 100.4 seconds after profiling and replacing the
slow colimit-instance search with direct single-complex cancellation. Its new
coefficient-map definitions were already locally irreducible. Split the models and
three groups of proved private helpers as permitted by the current worker brief,
step 3a. No mathematical statement, signature, construction, or global attribute changes.

## Old

`Sheaf.Paper.CanonicalCoefficientPullbackReduction` contained all coefficient
constructions, `canonicalCoefficientModelMaps_isIso`, and the final theorem.
Its five original public imports and all public declaration names are preserved.

## New

The entire declaration block from `canonicalCoefficientIntegralUnit` through
`canonicalCoefficientInverseTransition`, including the already proved model-map
lemmas and local attributes, moves verbatim to
`Sheaf.Paper.CanonicalCoefficientPullbackModels`. A byte-for-byte comparison of
that block with the original item succeeds. The item publicly imports this model
module, preserving all existing public names, signatures and data. The final
statement remains verbatim in the item, with its proof completed.

`CanonicalCoefficientUnitNormalization`, `CanonicalCoefficientChainNormalization`, and
`CanonicalCoefficientFiniteCompatibility` contain new proved comparison results and private helpers. Each now has its own
new DAG node with an exact `lean.file`; the parent proof dependency
records the unchanged definitions' new attachment. The parent statement and its
statement dependencies remain unchanged. Public entry declarations are
`coefficientIntegralInverseIso`, `coefficientUnit_roos`, `coefficientKappa_factor`,
and `coefficientStrictTransition`; their modules are private proof imports of the
item, so the item's existing exported interface remains unchanged.
The item imports them privately with `import all`; no private helper appears in a
public statement or public definition. Each supporting module has its own node; the item retains its original theorem attachment.

## Users

The source-only `tools/downstream.py --uses` check of all relocated public names
finds only the item and `FiniteRegularCoefficientComparisons`. There are 306
transitive importers; the two direct importers are listed below and compiled unchanged against the delivery successfully. No consumer needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | D7 | Same public API through model reexport; complete final proof. |
| Sheaf.Paper.FiniteRegularCoefficientComparisons | unclaimed in current records | Four aliases retain the same declarations and types. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed in current records | Imports the same coefficient theorem and constructions. |

## Status

landed 20261026T222616-L-673941 2026-10-26 (merge of deliver/D7/Sheaf.Paper.CanonicalCoefficientPullbackReduction)
