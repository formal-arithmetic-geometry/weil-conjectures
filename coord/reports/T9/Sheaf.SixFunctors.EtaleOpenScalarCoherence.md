## What changed

Proved the restriction normalization by transporting the published reverse scalar mate through the exact inverse-image comparison. Proved uniqueness of both normalized comparisons using flat-term K-flat representatives, and proved the successive-scalar coherence by deriving the restriction coefficient cocycle and conjugating it under the scalar/open adjunctions. The original theorem assembles these arguments with two separate source obligations.

## Proved and sorry left

Closed the original body hole of `AlgebraicGeometry.Etale.etaleOpenScalarComparisons` by a complete assembly proof. This is a partial decomposition, not a complete proof: two holes are added, named `AlgebraicGeometry.Etale.etaleOpenExtensionNormalization` and `AlgebraicGeometry.Etale.etaleOpenMixedTensorScalar`. The former is only the q-normalization assertion; the latter is only the mixed tensor assertion. Both are strictly parts of the original six-field theorem. No definition contains a hole. Net holes: one original hole removed and two added (net minus one). Restriction normalization, the two uniqueness implications, and successive scalar coherence have complete Lean proofs from existing declarations.

Verification: the repaired three-module packet compiled, and the item compiled with profiling in 54.9 seconds. The profiling option is removed for delivery. Local cached instances and folded derived-category constructions keep elaboration within the file limit. The initial packet also passed the axiom probes; delivery reruns them on the repaired files.

## No longer needed

The retained uniqueness proof uses native flat-term K-flat resolutions and the existing constant-module comparison. It does not use `Sheaf.SixFunctors.EtaleOpenKFlat`, `lem-pc-kflat-resolution`, or the independent site-derived tensor descent in its own proof. Those dependencies remain relevant to the full mathematical proof plans of the two retained source obligations and are not withdrawn. No library module or declaration is deleted. The draft's tensor-model, monoidal, normalized-adjunction-composition, projection-mate and ancillary Mathlib proof imports are removed from the item because its retained proof does not use them. `Sheaf.Paper.FiniteCoefficientDirectImage` is removed: its node depends on this item. The exact localization composition identity and ordinary coefficient cocycle are proved as private local helpers instead, using the existing ordinary mate identity from `WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities`. `Sheaf.Paper.ScalarPullbackIsoExistence` is also removed because the retained proof does not use it. The redundant proof import of `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek` is removed; its public API is already exported by the statement dependency.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is disputed or weakened. The first delivery check caught a DAG cycle through `lem-coef-finite-direct-image`; the repaired proof removes that import and proves the two elementary helper identities locally. The draft also disabled transparency checking; both settings have been removed, and local unfolding is used explicitly where needed. The original combined hole hides six distinct assertions. Two remain unfinished after extensive work. The extension normalization draft constructs the equation by a four-adjunction localization argument, but its final conversion between hidden instances does not yet compile. The mixed tensor draft reduces the problem to monoidality of the restriction mate on flat-term K-flat representatives; the full proof still has unresolved elaboration cost. These are proof-engineering limitations of this attempt, not tool failures. The complete draft and compiler experiments are preserved only in the sandbox scratchpad, outside the delivered Lean tree.

## New nodes

`lem-coef-etale-open-extension-normalization` records the canonical q normalization, with its ordinary-to-derived adjunction-unit proof plan, in `Sheaf.SixFunctors.EtaleOpenExtensionNormalization`.

`lem-coef-etale-open-mixed-tensor-scalar` records only the mixed scalar/tensor projection equation, with the monoidality and projection-mate proof plan, in `Sheaf.SixFunctors.EtaleOpenMixedTensorScalar`.

Both nodes cite the current blueprint proof at `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/thm-coef-finite-hom.proof.md` and retain the parent chapter and unit. The parent node follows the actual assembly, normalization transport, cancellation and cocycle argument. No interface, definition or consumer is changed.

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
