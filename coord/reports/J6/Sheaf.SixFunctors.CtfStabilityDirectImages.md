## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.CondensedRing.constructibleFiniteTor_stability_direct_images`
with a complete Lean assembly of its six clauses. Pullback uses the already proved helpers
of `UnboundedLocalizingPullback`; locally closed extension and the specified compactly
supported image use `compactification_localizing`. Exceptional preservation follows from
`exceptionalInverseImage_exists`, uniqueness of right adjoints, and invariance under isomorphism.
Tensor Tor intervals are added by the generic derived-category tensor theorem.

The tensor constructibility and ordinary direct-image arguments are separate new modules.
No existing statement, definition, public import, or target type changed. Local irreducibility
of `upperStarFromPoint` and `derivedTensor`, explicit unfolding of `curriedTensor` at the
amplitude calculation, and an explicit six-clause conjunction constructor avoid costly elaboration.
The original signature is retained verbatim.

## Proved and sorry left

Closed the one original direct hole:
`AlgebraicGeometry.ProEtale.CondensedRing.constructibleFiniteTor_stability_direct_images`
(node `det-thm-sf-ctf-stability-direct-images`). The item module now contains zero `sorry`.

Added two strictly smaller public theorem holes, one per module:

- `AlgebraicGeometry.ProEtale.CondensedRing.constantModelBoundedConstructible_tensor_of_admissible`
  (`lem-sfb-admissible-tensor-constructibility`): only bounded constructibility of tensor;
  the Tor conclusion is proved in the parent.
- `AlgebraicGeometry.ProEtale.CondensedRing.constructibleFiniteTor_rightDerivedLowerStar_of_admissible`
  (`lem-sfb-admissible-direct-image`): only ordinary direct image, with none of the other
  five clauses of the parent.

This is a decomposition: one original hole closed, two holes added, net minus one hole.
The parent proof is complete from these declarations and existing interfaces; neither
new theorem is reported as proved. The resumed all-module compile passed for both new
modules and the assembled parent against the current green library; after replacing
repeated conjunction search with the explicit six-clause constructor, the parent compiled
in 28.2 seconds. No definition contains a hole.

## No longer needed

The following direct proof imports were removed from the item module. Their arguments
are either inside the two isolated nodes or supplied by the existing compactification
and exceptional-adjoint interfaces; this does not claim their transitive modules are pruned.

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Mathlib.AlgebraicGeometry.Sites.Etale`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`
- `Sheaf.AlgebraicGeometry.ComparisonTorInterval`
- `Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel`
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`
- `Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula`
- `Sheaf.AlgebraicGeometry.OpenDirectImageClassicalAmplitude`
- `Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.Paper.CartesianCoefficients`
- `Sheaf.Paper.CoefficientHeartTriangulated`
- `Sheaf.Paper.CompletedCondensedCoefficients`
- `Sheaf.Paper.FiniteLocalizingExceptionalPreservation`
- `Sheaf.Paper.FiniteProperLocalizing`
- `Sheaf.Paper.IntegralModelsOperations`
- `Sheaf.Paper.IntegralProperBaseChange`
- `Sheaf.Paper.LocalizingClosureCtfEqualsBc`
- `Sheaf.Paper.LocallyConstantTensor`
- `Sheaf.Paper.OpenTorBoundArbitraryField`
- `Sheaf.Paper.PadicIntegersInvertEll`
- `Sheaf.Paper.ProperBaseChangeRational`
- `Sheaf.Paper.RationalExceptionalRestriction`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.SixFunctors.FieldTensor`
- `Sheaf.SixFunctors.IntegralExceptionalRestriction`
- `Sheaf.SixFunctors.IntegralModelsGenerators`
- `Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage`
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`
- `WeilConjectures.ConstructibleSheaf.KernelCokernel`
- `WeilConjectures.ConstructibleSheaf.Refinement`
- `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`

The complete old proof-dependency list is partitioned below. “Delegated” means still
needed by the two new nodes or an imported interface, rather than deleted mathematics.
The updated parent node lists only dependencies its Lean assembly uses directly.

- `sk-def-localizing-closure`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `sk-def-sfb-dc-setting`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `lem-weil-pbc-finite-type-over-noetherian`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `det-proper-base-change-unbounded-pullback`: retained directly.
- `det-def-localizing-closure-ctf-equals-bc`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `det-pe-finite-tor-comparison-noetherian`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `lem-sf-etale-flat-constructible`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `lem-weil-pbc-constructible-stratification-intersection`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `lem-weil-pbc-locally-constant-tensor`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `thm-constructible-serre`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `lem-pc-bounded-above-flat-kflat-site`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `det-lem-integral-models-operations`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `det-thm-sf-pf-field-tensor`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `lem-pqf-qc-immersion-open-closed-factor`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `sk-prop-sfb-cartesian-coefficients`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `lem-weil-pbc-proetale-ringed-open-closed`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `lem-weil-pbc-exact-functor-derived-functor`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `sk-def-sfb-constructible`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `lem-weil-pbc-proper-fp-permanence`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `det-lem-int-tensor-projection`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `cor-fin-deligne-open-finite-coefficients`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `lem-kun-0f10`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `det-geo-open-finiteness-ii-amplitude`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `lem-sf-projection-finite-constant`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `lem-sf-open-tor-bound-arbitrary-field`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `prop-weil-pbc-comparison-direct-image`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `lem-exc-comparison-tor-interval`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `det-thm-sf-pf-adic-open`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `det-lem-integral-models-generators`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `det-cor-coefficient-heart-ii-triangulated`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `sk-prop-sfb-qlbar-colimit-x`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `det-pe-bounded-continuity-direct-image`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `lem-pur-ringed-site-grothendieck-abelian`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `det-prop-sfb-qlbar-colimit-x-invert-ell`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `lem-weil-pbc-ring-sheaf-change-adjunction`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `sk-def-sfb-coefficient-change`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `det-ctf-finite-proper-localizing`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `det-thm-sfb-proper-base-change-integral`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `det-thm-sfb-proper-base-change-rational`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `sk-def-sfb-module-derived-lower-shriek`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `sk-prop-sf-rf-shriek-preservation`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `sk-thm-int-restriction`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.
- `sk-thm-restriction`: delegated to the tensor/direct-image nodes or the imported pullback, compactification, and exceptional interfaces; not a direct parent dependency.

## Where the brief, the DAG or earlier work was wrong

The saved exploratory tensor placeholder omitted admissibility and geometric hypotheses;
it was removed and never delivered. The new tensor statement restores those hypotheses.
The ordinary finite-coefficient comparison interfaces use coefficient-sized module-sheaf
presentations, so they cannot simply be applied to internal condensed module objects
without the comparison and scalar-transport glue. This glue remains explicit in the two
separate proof obligations.

The admissibility predicate also retains all continuous maps into the algebraic closure,
separately from the finite-subextension-valued coefficient. Several rational interfaces
cover only the latter. The retained proof obligations explicitly keep the two coefficients
distinct and do not claim that all continuous-coefficient local systems descend to one
finite extension. Their continuous-coefficient finiteness argument still needs formalization.

The previous attempt's two dry runs were killed with exit code 137 before preflight;
that historical tool failure is not the current outcome. The initial dry run on this resume
returned the split-off work gate normally. The resumed all-module compile then passed.
Further interface review confirmed that `tensorClosureRational` covers finite extensions
and the finite-subextension-valued closure, not the separate all-continuous closure.
`integralModelsOperations` uses canonical integral coefficients, and the finite-coefficient
comparison interfaces require the internal-module comparison. No identification or missing
coefficient transport is silently assumed in the parent proof: these remain in the two
explicit sourced mathematical lemmas. An independent source-DAG traversal found no path
back to the parent from exceptional existence, compactification, or unbounded pullback.

## New nodes

`lem-sfb-admissible-tensor-constructibility` isolates steps 2--3 of the original node,
with no amplitude-addition conclusion. Its source, proof steps, searches and exact Lean
signature are recorded in the new node and module.

`lem-sfb-admissible-direct-image` isolates steps 5--9 of the original node. It retains
the original ordinary derived direct image and every admissibility/geometric hypothesis;
it makes no assertion about pullback, tensor, extension by zero, compact support or f-shriek.
Change record: `coord/changes/J6-ctf-stability-local-proof-context.md`. The static
check flags the module-local irreducibility command; the record explains its scope and
lists all transitive consumers. Existing signatures and public imports are unchanged.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
