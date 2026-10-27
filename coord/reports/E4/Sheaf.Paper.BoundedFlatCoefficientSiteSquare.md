## What changed

Proved `AlgebraicGeometry.ProEtale.BoundedFlatCoefficientSiteSquare.boundedFlatCoefficientSiteSquare` from the existing fixed-ring source APIs. All public definitions, declaration signatures and public imports are preserved. The five complexes retain termwise flatness and interval support; source bounded-flat lemmas give their K-flatness and Tor bounds. The adjunction-transpose K-flat computation gives the two specified representative isomorphisms.

Added private proof imports for `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`, `WeilConjectures.SixFunctors.ProEtale.Comparison.Flat`, `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsFlat`, `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars`, `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel`, `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate` and `Sheaf.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative`. Private `import all` access reuses the already proved scalar K-flatness and mate-normalization helpers in the two publicly retained paper modules. Added proved private helpers for the bounded-flat bundles, cochain representative transformations, and normalized mate calculation. Performing the categorical calculation over abstract categories before specializing it avoids expensive kernel conversion of the site functors.

The final equality uses the actual published scalar/site comparisons. The proof identifies the ordinary comparison as the scalar mate of the restriction square, proves the corresponding cochain identity degreewise, and applies the existing mate-normalization calculation to the exact localization factors and the named scalar representatives. Cancelling the two specified isomorphisms gives precisely the required equality, including its direction and target coefficient action. No coefficient-flatness assumption or new object choice is introduced.

## Proved and sorry left

Closed the sole original hole, in `AlgebraicGeometry.ProEtale.BoundedFlatCoefficientSiteSquare.boundedFlatCoefficientSiteSquare`. No holes added; no `sorry` remains in this module. All added helpers are private and proved. This is a proof, not a decomposition.

Validation: the complete final module compiles without warnings in 58.0 seconds (the profiled version took 50.9 seconds). A separate temporary module checked `#print axioms` for the theorem and reported exactly `propext`, `Classical.choice` and `Quot.sound`; it was removed before delivery. There is no `sorryAx` dependency. The theorem signature, four public definitions and public-import list were also compared verbatim with the assigned source. Delivery runs the required independent preflight checks.

## No longer needed

Removed these proof-only imports and the corresponding planned dependencies from this item's route:

- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`: `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback`: `lem-weil-pbc-ringed-topos-flat-module-pullback`.
- `Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`: `lem-weil-pbc-independent-bounded-flat-kflat`.
- `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`: `lem-weil-pbc-ringed-topoi-derived-pullback`.
- `Sheaf.Paper.KFlatScalarComparisonNormalization`: `lem-sfb-kflat-scalar-comparison-normalization`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`: `lem-pc-kflat-resolution`.
- `Sheaf.Algebra.Homology.SiteOneSidedTensorNormalization`: `lem-trf-site-one-sided-tensor-normalization`.

The source fixed-ring flatness theorems, `CochainComplex.kFlat_of_bounded_of_flat`, `DerivedCategory.torAmplitudeIn_Q_obj_of_flat`, and the generic K-flat adjunction-transpose theorem replace those specialized ringed-topos constructions. The final normalization is a direct localization/mates calculation, so it does not resolve `B[0]`, compare two tensor resolutions, or use `def-pc-tensor-complex-sheaves` as a separate proof dependency. Removed the obsolete `tool_uses` entries for the seven nodes above; retained the comparison-exactness approval. The old proof-only dependency entries for `def-pur-sheaf-tensor-product`, `def-kun-tor-amplitude` and `def-weil-proetale-tor-amplitude` are also removed: these definitions remain statement dependencies. Public imports remain unchanged. These nodes/modules are unnecessary for this proof; no assertion is made that other targets no longer use them.

## Where the brief, the DAG or earlier work was wrong

The initial shared snapshot had the item in quarantine. After reading the current queue and rework records, I copied its archived source into the sandbox. The live source subsequently reappeared and matched that archive. The current queue assigned the original one-hole proof, rather than an import-collision or zero-hole definition repair.

The DAG plan's generic ringed-topos and coefficient-resolution route is longer than necessary for the published fixed-ring statement. In particular, the conclusion specifies the scalar-adjunction mate itself, so a direct calculation with the published restriction square proves its normalization. The existing generic source bounded-flat Tor theorem already supplies the universal Tor test. Updated the item's proof steps, proof dependencies and proof origin accordingly; no statement or definition was repaired or weakened.

## Related modules compiled before delivery

3 related module(s) compiled against this delivery by deliver3.py: 3 OK.

```json
{"capped": false, "direct": 3, "left_out": 0, "own": {"Sheaf.Paper.BoundedFlatCoefficientSiteSquare": "039a900d8409da52e0786e7ce5b95bb8c48ba428"}, "results": {"Sheaf.Paper.EtaleOpenCounitFlatModels": {"hash": "e8f0943d48eba783a925eba4082ebf3bad7c30fa", "status": "OK"}, "Sheaf.Paper.FiniteCoefficientInputModels": {"hash": "3262ba866480f102fb81cbe41016699559d58d6d", "status": "OK"}, "Sheaf.Paper.ProjectionReductionWitnessedFlatDomains": {"hash": "1cb9f25ccf08a643991904f6eded0827ab291e36", "status": "OK"}}, "seconds": 131, "time": "2026-10-28T01:09:08+0800", "transitive": 0, "version": 1}
```

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
