## What changed

Proved `WeilConjectures.IntegralSupportNormalization.identityModuleImage_existsUnique`
in `Sheaf.Paper.IntegralSupportFunctorNormalization`, without changing its statement.
Three private proved helpers identify the constant coefficient structure map, then its
completed inverse-limit structure map, and finally the adjoint coefficient map.
Mathlib's `SheafOfModules.pushforwardCongr₂` applied to the canonical site identity
constructs the required module isomorphism, with `pushforwardId` as the final identity
identification. Keeping the coefficient sheaf abstract in a private irreducible construction prevents
repeated unfolding of its inverse limit. The specialized witness and its proved section
lemma preserve this boundary during uniqueness. Its inverse is restriction along
the canonical identity base-change projection. Equality on every section proves
uniqueness, so the existing choice defining `identityModuleImage` stays uniquely fixed.
All existing definitions, public imports, public signatures and existing docstrings are retained.

Searches used the required `msearch.py` LeanFinder, Loogle and grep modes. They found
Mathlib's module pushforward identity and its natural-isomorphism comparison; the
latter handles the actual site functor rather than a definitionally identical one.

## Proved and sorry left

Closed one existing hole:
`WeilConjectures.IntegralSupportNormalization.identityModuleImage_existsUnique`
(node `lem-sf-integral-support-functor-normalization`, also owned by definition node
`def-zl-ordinary-open-support-normalization`). All five private helper theorems are proved; both private constructions contain no holes.

One existing hole remains unchanged:
`WeilConjectures.IntegralSupportNormalization.integralSupportFunctorNormalization`
(node `lem-sf-integral-support-functor-normalization`). Its existing seven-step
natural-language proof is retained. No holes are added and no statements are split off.
This is a partial delivery: one of the module's original two holes is closed.

## No longer needed

Removed unused private proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.SixFunctors.IntegralOpenReductionComparison`
- `Sheaf.Paper.CompletedDirectImageLimits`
- `Sheaf.Paper.KoszulReconstruction`
- `Sheaf.Paper.OpenFiniteConstructibilityInterval`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`
- `WeilConjectures.ConstructibleSheaf.OpenClosed`
- `Sheaf.CategoryTheory.StrictRoosComparison`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Sheaf.Paper.SfIntegralConstructibleTriangulated`
- `Sheaf.Paper.SfIntegralConstructibleLinear`

The last three are already available through retained public imports. The remaining
imports were present for the unfinished main theorem and are unused by its current
proof or any other declaration of this module. Its planned DAG dependencies remain
recorded: this delivery does not claim that the still-unproved normalization can
omit those arguments. No node, library declaration or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The item source is currently present and the initial
unchanged source compiled, despite its historical quarantine entry in `coord/rework.tsv`.
The identity isomorphism cannot be obtained just by `pushforwardId`: the actual
base-change site functor is only naturally isomorphic to identity, and its completed
coefficient structure map must first be identified using the prescribed finite
projections. The larger normalization theorem still requires assembly across several
coefficient/module presentations and remains open in this partial delivery.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
