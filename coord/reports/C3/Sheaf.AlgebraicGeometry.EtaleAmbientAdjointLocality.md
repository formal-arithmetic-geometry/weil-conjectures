## What changed

Proved `AlgebraicGeometry.Etale.existsUnique_etaleAmbientAdjointLocalityIso` with its
existing signature and definition `etaleAmbientLeftComparison` unchanged. The proof
uses the existing unbounded sum-extension adjunction, the existing left comparison,
and Mathlib's composite-adjunction, transport and right-adjoint uniqueness APIs.

The simultaneous quantifier over normalization families requires comparison uniqueness.
Private proved helpers establish monicity of open extension into direct image, using
the empty-or-terminal Kan-extension calculation; sheafification and direct image
preserve these monomorphisms. Graph normalization then determines the sheaf comparison,
and derived normalization plus faithful precomposition by Qh determines its descent.
This also covers empty indexing categories and zero sheaves. No new public data definitions,
statements, hypotheses or public imports are introduced. Existing public imports remain
as the exported interface; obsolete proof-only imports are removed.

Updated the existing node's proof, proof dependencies, proof origin and Lean statement
record to match this route. Removed obsolete tool approvals, preserving the remaining order.
The unit `sk-prop-sf-cbc` has no realized statement or steps to bypass.

Validation: the final module compiles through lcompile.py without warnings in 9.5 seconds;
there are zero sorry tokens. The proof uses existing named dependencies, whose remaining
holes are not claimed closed by this delivery.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Etale.existsUnique_etaleAmbientAdjointLocalityIso`
(node `lem-amb-etale-adjoint-locality`).

Added 0 holes; split off 0 statements. No sorry remains in the delivered module.
All added helpers are private and fully proved.

## No longer needed

Removed the following proof-only imports from this module (this is local pruning;
other users may still need these modules):

- `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `Mathlib.AlgebraicGeometry.Sites.Etale`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Sheaf.AlgebraicGeometry.EtaleSumStalks`
- `WeilConjectures.Compactification.CategoryBaseChange`
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`
- `Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`
- `Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit`
- `Sheaf.CategoryTheory.FunctorPreservesSequentialHomotopyColimit`
- `Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`
- `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Sheaf.RingTheory.Etale.QuasiFiniteAtPrime`
- `Sheaf.AlgebraicGeometry.EtaleSheafClopenProduct`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison`
- `Sheaf.AlgebraicGeometry.OpenSectionClopen`
- `WeilConjectures.SixFunctors.Finite.Exact`
- `WeilConjectures.SixFunctors.Finite.Stalk`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.Compactification.NagataCompactification`
- `WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization`
- `Sheaf.AlgebraicGeometry.FiniteCohomologicalDimensionDirectImageCoproducts`
- `Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.CategoryTheory.Triangulated.HomologicalFunctor`
- `Mathlib.CategoryTheory.MorphismProperty.OverAdjunction`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Mathlib.AlgebraicGeometry.Morphisms.FlatMono`
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Mathlib.AlgebraicGeometry.OpenImmersion`
- `Mathlib.CategoryTheory.Sites.Point.Basic`
- `Mathlib.CategoryTheory.Sites.Point.Skyscraper`
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`
- `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`

The proof no longer needs these former direct proof dependencies:

- `lem-cbc-compactifiable-compatible-tower`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`
- `lem-weil-pbc-termwise-adjunction-homotopy`
- `prop-weil-pbc-inverse-image-modules-exact`

The compatible-tower existence lemma is not needed: the existing definition already uses
`d.ofComp c`. Finite-type/Noetherian propagation is supplied by the existing candidate
interfaces. The sheaf-to-module inverse-image bridge is already in the existing derived
adjunction. Reconstructing these arguments here would duplicate their library proofs.

The following obsolete `tool_uses` entries were removed:

- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-weil-pbc-etale-inverse-image-restriction`
- `lem-weil-pbc-etale-localization-functor-adjoint`
- `lem-weil-pbc-etale-section-clopen-immersion`
- `lem-weil-pbc-separated-base-change`
- `lem-weil-pbc-etale-ring-map-quasi-finite`
- `thm-pqf-zmt-factorization`
- `lemma-weil-pbc-finite-stalk-formula`
- `lem-weil-pbc-extension-by-zero-stalks`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `lem-weil-pbc-section-separated-closed-immersion`
- `lem-weil-pbc-finite-proper`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-open-immersion-base-change`
- `lem-weil-pbc-locally-noetherian-quasi-separated`
- `lemma-weil-pbc-finite-direct-image-exact`
- `lem-weil-pbc-exact-functor-derived-functor`
- `prop-weil-pbc-inverse-image-modules-exact`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-open-section-clopen`
- `lem-weil-pbc-proper-base-change`
- `lem-weil-pbc-etale-sheaf-clopen-product`
- `thm-nagata-compactification`
- `lem-sf-exact-functor-derived-triangulated`
- `lem-pc-right-derived-functor-triangulated`
- `lem-kun-complex-colimit-hocolim`
- `lem-kun-functor-preserves-hocolim`
- `lem-weil-pbc-commshift-nattrans-triangle-morphism`
- `lem-weil-pbc-derived-cohomology-ladder`
- `lem-fin-finite-type-fibre-dimension-bound`
- `lem-kun-proper-torsion-cd-bound`
- `lem-kun-unbounded-abelian-exchange-comparison`
- `def-weil-proper-morphism`
- `lem-exc-direct-image-coproducts`
- `prop-weil-pbc-geometric-stalks-exact`
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`
- `lem-weil-pbc-termwise-adjunction-homotopy`

Stalk calculations, finite Zariski-main factorization, finite-cohomological-dimension
bounds, coproduct preservation and telescope comparison are unnecessary here because
the existing unbounded comparison constructors already provide the required isomorphism.
Their underlying theory is still used transitively where those constructors need it.
The retained dependency nodes record that constructor-level route.

## Where the brief, the DAG or earlier work was wrong

The module docstring's long plan reconstructs exactness, compactification comparisons
and unboundedness that the current library already implements. The Lean proof can start
from those declarations, as required by the brief. The old plan did not explicitly
justify independence from every normalization family in the quantified counit equation;
the new proof supplies it, without choosing an arbitrary isomorphism from Nonempty.
The old Lean statement record also passed A instead of ModuleCat A to the existing
derived adjunction; its record now quotes the actual unchanged declaration verbatim.

The monomorphism argument follows the same empty-or-terminal Kan-extension proof as
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono`, adapted
and checked on the ordinary etale site, rather than importing a theorem on another site.
No mathematical statement was changed and no source claim was weakened.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
