## What changed

Replaced the proof of `WeilConjectures.PurityFiniteSetting.Dnc.existsUnique_dncInvariance`.
The proof constructs the deformation datum from the actual Rees scheme and canonical maps,
uses the existing etale DNC comparison theorem, and transports its all-base-change equation
through the natural etale-to-pro-etale comparison. Uniqueness follows by evaluating the
normalization at the identity base change using global family constancy. All declaration
signatures, definitions, docstrings, public imports, and the target statements are unchanged.
Added the private import `WeilConjectures.EtaleCohomology.TateTwist.Normalized` for the
normalized Kummer orientation. Updated the node proof and dependencies to match.

## Proved and sorry left

The proof of `WeilConjectures.PurityFiniteSetting.Dnc.existsUnique_dncInvariance`
closes its one original hole. Zero holes remain in the item, zero holes are added,
and zero statements are split off. No new modules are introduced. The existing declarations
used from the geometry and family-constancy APIs retain their separate proof obligations;
none is copied or restated in this delivery.

Validation: `deliver3.py H2 Sheaf.Paper.PurityDncInvariance --no-push` passed
compilation, the axiom probe, and preflight on 2026-10-19 (dry-run commit 71f38e06ba).
The delivery is CODEX because its node file records the shorter proof route.
The proof keeps the ordinary-etale comparison explicitly typed between `sourceEtale`
and `normalEtale`, and proves uniqueness directly through identity-pullback naturality.

## No longer needed

The following private imports are removed. Many remain available through unchanged public
imports, so this list describes this module's dependencies rather than claiming that every
listed module leaves the targets' entire import closure:

- `WeilConjectures.Blowup.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Sheaf.Paper.FiniteTypeExceptionalInverseImage`
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom`
- `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`
- `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`
- `WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex`
- `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Mathlib.CategoryTheory.Adjunction.Additive`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Sheaf.Paper.CohomologicalSmoothComposition`
- `Sheaf.Paper.CohomologicalSmoothEtaleLocality`
- `Sheaf.Paper.CohomologicalSmoothnessTheorem`
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`
- `Sheaf.Paper.DerivedPullbackTensorHom`
- `Sheaf.Paper.PurityDncFamilyIntrinsic`
- `Sheaf.Paper.TwistPreservesFiniteness`

The previous node proof expanded the underlying geometry, smooth-duality comparisons,
and sheaf descent again. The existing family-constancy/DNC API already supplies them.
The following previous direct proof dependencies are removed from the node; their facts
can remain needed within the existing API and are not asserted globally unnecessary:

- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-pod-separated-finite-type-base-change`
- `lemma-nagata-blowup-proper`
- `def-weil-proper-morphism`
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`
- `lem-weil-pbc-qc-open-immersion-finite-type`
- `lem-weil-pbc-proper-fp-permanence`
- `def-weil-exceptional-inverse-image`
- `def-sbc-closed-immersion-ideal-sheaf`
- `def-pur-dnc-section-family`
- `def-weil-derived-pullback-tensor-hom`
- `def-weil-closed-immersion`
- `pqf-def-locnoeth`
- `lem-pur-co-smooth-etale-locality`
- `lem-pur-co-smooth-composition`
- `thm-pur-cohomological-smoothness`
- `lem-weil-pbc-qcqs-morphism-permanence`
- `prop-weil-twist-preserves`
- `lem-weil-pbc-derived-single-fully-faithful`
- `def-weil-pbc-proetale-site`
- `lem-pur-sheaf-hom-cover-gluing`
- `def-pur-localized-ringed-site`
- `lem-weil-proetale-weakly-etale-localization`
- `lem-sbc-smooth-relative-dimension-permanence`

The obsolete `tool_uses` entries for these removed direct dependencies are withdrawn.
No Lean module or DAG node is deleted. The unit's construction via normalized family
constancy and zero-fibre restriction is preserved by the theorem used in the proof.

## Where the brief, the DAG or earlier work was wrong

The earlier DAG proof was a much longer route than the current library requires.
`Etale.exists_iso_sectionInvariant_normalCone` already supplies the etale comparison with
its equation for every base change and pulled-back presentation. The original statement's
universal normalization also permits a shorter uniqueness proof: a global presentation
exists by family constancy, so specialize to the identity base change and cancel the
canonical identity-pullback isomorphism. No change to a mathematical statement or definition
was necessary, and no arbitrary derived-pullback faithfulness assertion is used.

The earlier attempt classified requests with no server answer as a compilation
blocker. The resumed proof now passes compilation and preflight. No actual 60-second
Lean timeout or definition performance defect was reported by the successful dry run;
there is no basis for changing a shared definition. The proof keeps the normal-cone
presentation explicit and avoids unnecessary unfolding.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
