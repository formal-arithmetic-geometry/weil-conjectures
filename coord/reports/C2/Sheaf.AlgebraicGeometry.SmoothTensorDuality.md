## What changed

Proved `AlgebraicGeometry.Etale.smooth_tensor_duality` from the existing source-library
`AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor`. Added three proof-only
imports: `WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality`,
`WeilConjectures.ConstructibleSheaf.Pullback`, and
`WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf`.

The proof converts stalkwise invertibility of N to `HasInvertibleExponent`, shifts the
source theorem's complex isomorphism, and constructs a cover of rank-one module
trivializations from local constancy and the geometric-stalk isomorphisms. Reindexing the
cover by points removes empty members without assuming X is nonempty. The private proved
helpers `braided_tensor_mate` and `smoothTensorDualityMap_eq` identify the specified canonical
mate with the source map precomposed by the Koszul braiding. The latter helper works at a
general coefficient category to keep kernel comparisons of derived monoidal structures
within the single-file limit. Existing definitions, theorem signatures, visibility, and
all public imports are unchanged. Updated the node's proof route and dependencies.

Validation: the full delivered module compiled cleanly through `lcompile.py` in 35.6 seconds.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.Etale.smooth_tensor_duality`
(node `thm-asd-smooth-tensor`). Added 0 holes; no `sorry` remains in the delivered module.
Both private helpers are proved. There are no split-offs or new modules.

This is reuse of an already stated theorem, not an independent proof of geometric smooth
duality. The imported source theorem
`AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor` itself still has its existing
`sorry`; this delivery does not claim to close that source-library hole. The interface
conversions and equality of canonical maps are complete Lean proofs.

## No longer needed

Removed these proof-only imports (existing public imports are retained as part of the
module's exported interface):

- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`
- `Mathlib.CategoryTheory.Sites.Point.Basic`
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`
- `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison`
- `Sheaf.AlgebraicGeometry.OpenSectionClopen`
- `Sheaf.Paper.RingedExchangeTensorCoherence`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullback`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Sheaf.AlgebraicGeometry.CompactificationCategory`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`
- `Sheaf.AlgebraicGeometry.EtaleLocalNormalForm`
- `WeilConjectures.Compactification.NagataCompactification`
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`
- `Sheaf.AlgebraicGeometry.ProperProjectionFormula`
- `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`

The following former proof dependencies are not needed directly by this interface proof;
the source theorem supplies the geometric result, so its geometric argument is not duplicated:

- `def-amb-etale-compact-support`
- `def-kun-truncations`
- `def-pur-sheaf-tensor-product`
- `def-weil-derived-cohomology-sheaves`
- `def-weil-pbc-etale-sum-extension`
- `def-weil-pbc-geometric-stalks`
- `lem-amb-etale-adjoint-locality`
- `lem-amb-proper-coproducts-projection`
- `lem-amb-shriek-tensor-composition`
- `lem-amb-unbounded-compact-support-comparisons`
- `lem-asd-etale-sum-extension-tensor`
- `lem-asd-finite-etale-twist-line`
- `lem-asd-ordinary-finite-p1-adjunction`
- `lem-asd-tensor-mate-etale-precomp`
- `lem-kun-proper-base-change-torsion-ring`
- `lem-pur-etale-support-map-compatibility`
- `lem-sbc-smooth-relative-dimension-permanence`
- `lem-weil-pbc-extension-by-zero-exact`
- `lem-weil-pbc-extension-by-zero-stalks`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `prop-nagata-compactification-category`
- `prop-weil-pbc-geometric-stalks-exact`
- `prop-weil-pbc-inverse-image-modules-exact`
- `sbc-lem-affine-space-smooth`
- `sbc-thm-etale-local-normal-form`
- `thm-nagata-compactification`

No module is withdrawn in this delivery. These dependency removals are from this node's
proof route; they do not assert that other targets or the source theorem no longer need them.
The unit record `sk-prop-sf-cbc` has empty `realized.statement` and `realized.steps`, so no
mandatory realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned geometric proof duplicates a source-library theorem for the same smooth-duality
result. Its interfaces differ: the source records stalkwise rank one, uses omega_f ≅ L[2d],
and orders the tensor factors oppositely. These differences require actual conversions;
existence of an unspecified isomorphism would not establish the specified canonical map.

Several current DAG attachments point to modules absent from this shared checkout:
`Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction`,
`Sheaf.AlgebraicGeometry.ShriekTensorComposition`,
`Sheaf.AlgebraicGeometry.EtaleSumExtensionTensor`, and
`Sheaf.SmoothPurity.TensorMateEtalePrecomp`. They were not restated or imported: the shorter
source-library route avoids them. This is not a blocker to the delivered proof.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
