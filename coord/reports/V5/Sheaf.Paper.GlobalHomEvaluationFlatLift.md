## What changed

Proved `AlgebraicGeometry.Etale.ExternalRHom.globalHom_evaluation_flat_lift` from six source lemmas, preserving its complete statement and all three definitions in the item. The proof uses the native flat-resolution API for coefficient resolutions, tensor flatness and the cone lift, and the native exact inverse-image API for all four pullback cases. Added explicit scalar-coordinate comparisons and an unsigned evaluation construction. No adopted-source file or target was changed.

## Proved and sorry left

Closed the original body hole of `AlgebraicGeometry.Etale.ExternalRHom.globalHom_evaluation_flat_lift` (1 original hole). Added one genuine source subresult with a hole: `AlgebraicGeometry.Etale.ExternalRHom.globalHom_evaluation_model`, node `lem-pur-global-hom-evaluation-model`. This isolates steps 2, 4, 7 and 8 (the A-linear global Hom model and its universal normalization). It omits coefficient resolutions, evaluation existence, tensor flatness, cone lifts, localization equality and all pullback claims. This is a decomposition, not a net hole closure.

The other five new public theorems have complete proofs: `CochainComplex.exists_flat_term_kFlat_map_factorization`, `CochainComplex.flat_term_kFlat_tensor`, `AlgebraicGeometry.Etale.ExternalRHom.ringedComplex_flat_kFlat`, `AlgebraicGeometry.Etale.ExternalRHom.native_flat_kFlat_of_point`, and `AlgebraicGeometry.Etale.ExternalRHom.globalHom_chain_evaluation`. Every private helper is proved. There are no holes in definitions.

## No longer needed

Removed the item's direct private imports of `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`, `Sheaf.Paper.EtaleKFlatCriteria`, `Sheaf.Algebra.Homology.KInjectiveHomComplex`, `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, `Sheaf.AlgebraicGeometry.RGammaUnboundedWellDefined`, `WeilConjectures.Algebra.Homology.HomComplexGlobalCochains`, `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`, `Sheaf.CategoryTheory.ConstantModuleKFlat`, `Sheaf.CategoryTheory.ConstantModuleFlat`, `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`, `Sheaf.Algebra.Homology.KFlatTotalTensorModel`, `Sheaf.SixFunctors.ResolvingDerivedAdjunction`, `Sheaf.Paper.KFlatMapFactorization`, `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`, `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`, `Sheaf.Paper.KFlatRingedToposPullback`. Original public imports are preserved. Some removed direct imports remain needed transitively; none of those library files is withdrawn.

The item proof no longer applies `lem-pur-kflat-total-tensor-model`, `lem-weil-pbc-ringed-topos-kflat-pullback`, `lem-weil-pbc-etale-inverse-image-algebraic-structures`, or `lem-kun-rgamma-unbounded-well-defined`. Their top-level tool approvals are removed. The A-linear model retains its stated Hom and derived-adjunction dependencies. `lem-pur-kflat-map-factorization` is not applied as a public theorem: its module is still needed for its fully proved private cone-square completion. `lem-weil-pbc-ringed-topos-kflat-pullback` is not applied either, but its module supplies proved private coordinate/flatness helpers. Thus no entire module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The ringed-site global-sections model returns additive complexes and does not immediately supply the required A-linear, universally evaluation-normalized model in the ordinary étale module category. The new model node states that precise missing source result; no scalar action or normalization is silently forgotten. The native internal-Hom complex uses a different product differential, requiring a factor (-1)^(p*n) in any native product comparison. This prevents a naive degreewise identity comparison.

The supplied `IsResolvedGlobalEvaluation` clause already follows directly from the property of the chosen `HomModel`; the proof uses that equality. The bounded-below hypothesis on K is unnecessary for unbounded K-injective existence, but is preserved verbatim. The existing public import of `ExternalRHomConePairing` is preserved; its stage-2 review already records the eventual parent/interface import-direction issue. This delivery never uses its downstream theorem or the sibling lifted-evaluation theorem.

## New nodes

`lem-pur-flat-term-kflat-map-factorization-native` records the actual cone-square lift and flat degreewise biproduct, in `Sheaf.Algebra.Homology.FlatTermKFlatMapFactorization`.

`lem-pur-flat-term-kflat-tensor-native` records closure of native K-flat flat-term complexes under total tensor, in `Sheaf.Algebra.Homology.FlatTermKFlatTensor`.

`lem-pur-etale-scalar-flat-kflat-comparison` records transfer to the exact constant-ring realization, in `Sheaf.Paper.EtaleScalarFlatKFlatComparison`. Its private flatness comparison specializes the existing `lem-pur-etale-constant-module-flat` rather than duplicating that public node.

`lem-pur-coefficient-point-flat-kflat-comparison` records reflection from sheafified point coordinates to the ordinary module complex, in `Sheaf.Paper.CoefficientPointFlatKFlatComparison`. Its private forward helper applies the existing constant flat/K-flat theorems.

`lem-pur-global-hom-chain-evaluation` records the unsigned sheafified bilinear evaluation and total differential calculation, in `Sheaf.Paper.GlobalHomChainEvaluation`.

`lem-pur-global-hom-evaluation-model` records the separate A-linear model/normalization result of Stacks 0A96, 08J9 and 08JA, in `Sheaf.Paper.GlobalHomEvaluationModel`.

All new nodes inherit the item chapter/unit, identify the same supported-Künneth blueprint ancestor and exact proof location, and contain source proofs and three kinds of recorded Mathlib search. No existing statement or definition was changed, so there is no change record or forced consumer adaptation.

## Second reading by V5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
