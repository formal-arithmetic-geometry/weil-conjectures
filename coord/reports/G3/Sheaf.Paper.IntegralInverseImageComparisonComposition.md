## What changed

Proved `AlgebraicGeometry.ProEtale.integralInverseImageComparison_composition` with its original signature. The existing section-normalized inverse-image compositor and all public definitions are unchanged. Added proved private helpers for restricted sections, the composite adjunction generator, whole-tower tensor-unit composition, abstract exact-derived pasting specialized to the concrete coefficient functors, and transport of the existing K-flat counit identity through the resolution actually chosen by kappa.

The proof compares the full tower adjuncts after the specified realization eta, then uses injectivity of the constant-tower/derived-limit adjunction and cancels eta. It uses the existing `integralPullbackKFlatReductionCounit` and proved `integralPullbackResolutionMatching`; it does not introduce a substitute for the original theorem.

Proof imports added: `Sheaf.Paper.IntegralPullbackResolutionMatching`, `Sheaf.Paper.IntegralPullbackReductionCounit`, and `Sheaf.CategoryTheory.ExactDerivedTransformationPasting`. Updated the item's DAG proof and proof dependencies to describe this route. No statement, public import, target, or other module was changed. The scoped abstract-category variables, extra private universes, and private exact-functor additive-instance helper are documented in `coord/changes/G3-integral-composition-private-pasting.md` for independent review.

Validation: the complete module passed the delivery compiler and declaration probe without warnings. The pullback projection calculation uses explicit component equations, with no suppressed warnings.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.ProEtale.integralInverseImageComparison_composition` (node `lem-trf-integral-inverse-image-comparison-composition`). Added zero holes; zero holes remain in the delivered module. The previously proved `integralInverseImageComposition_existsUnique` remains proved. No split-off statements were added. Existing imported theorems that retain their own holes remain their existing work items.

## No longer needed

Removed direct imports:

- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition`
- `Sheaf.TraceFormula.IntegralConeCounitRealization`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.CategoryTheory.StrictRoosComparison`
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`

The route does not use node `lem-trf-integral-composition-counit-images` / module `Sheaf.Paper.IntegralCompositionCounitImages`: the single-pullback counit equation, resolution matching, and the tower-unit composition calculation compute the needed images directly. It does not use node `lem-trf-integral-comparison-counit-characterization` / module `Sheaf.TraceFormula.IntegralComparisonCounitCharacterization`: the required injectivity is the actual adjunction hom-equivalence's injectivity. These are dependency removals for this item, not withdrawal of either module.

The old explicit dependencies `lem-trf-constant-coefficient-composition` and `lem-weil-pbc-proetale-derived-pullback-composition` are unnecessary here: the already proved completed compositor uses constant-section uniqueness and limit projections, while the sequence compositor's mate normalization supplies the required composition on generators. Other removed imports may remain transitive dependencies of the existing interfaces; no claim is made that they disappear from the whole target closure.

## Where the brief, the DAG or earlier work was wrong

No false statement or signature defect was found. The DAG's planned strict-tower route is valid, but the existing normalized tower-unit interface and exact-derived pasting theorem allow assembly without the two planned composite-image/characterization dependencies. The unit route is preserved; the unit record has no realized statement or step bypassed by this change. The proof handles identities, zero inputs, and empty schemes through the same naturality and adjunction equations, without extra hypotheses.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
