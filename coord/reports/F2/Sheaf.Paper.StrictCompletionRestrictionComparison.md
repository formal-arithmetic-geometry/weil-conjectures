## What changed

Replaced the original theorem hole by an assembly from six proved comparison/construction lemmas and one separate normalized quotient-model statement. The integral presentation, section scalar presentation, finite constant local-model equivalence, geometric limit preservation, scalar pullback square and complete scalar-cone/Roos comparison are proved. The actual quotient tower and its algebra map are constructed in the item module. The tensor structure comes from the existing module-object/ringed-site derived comparison. All nine packet modules compiled together in import order with no warnings (scratchpad/all9.log); the first delivery invocation also passed compilation and axiom probes, then reported only a mismatch between the interface node’s lean.statement and the parser’s structure-header signature. The node now records that exact header.

Moved the nine accompanying interface declarations into `Sheaf.Paper.StrictCompletionRestrictionData`, publicly imported by the original module. This prevents a cycle between the original theorem and reusable lemmas whose statements use its structures. The theorem signature and every existing mathematical predicate clause, universe and declaration name are unchanged. SectionReductionModels.unit now writes the identity-complex comparison explicitly before the mapped tensor unit, avoiding expensive endpoint inference; this has identity components. SectionReductionModels is an abbreviation specializing the same fields of the generic section-ring structure SectionReductionModelsFor; this avoids expanding the concrete integral-ring monoid instance during dependent field checking. No source-library file is changed.

## Proved and sorry left

The original hole in `AlgebraicGeometry.ProEtale.StrictCompletionRestriction.strict_completion_restriction_comparison` is closed by a complete proof from the named lemmas. The packet adds one hole in `AlgebraicGeometry.ProEtale.StrictCompletionRestriction.strictSectionPrincipalQuotientModels`, node `lem-sfb-strict-section-principal-quotient-models`. Consequently this is a decomposition: one original hole closed, one separate hole added, net zero holes closed. There are no holes in definitions or in the item module.

The following new theorems have complete Lean proofs, in the same namespace: `strictScalarCompletionFunctorComparison`, `strictIntegralCompletionPresentation`, `strictCompletionRestrictionLimits`, `strictCompletionFiniteConstantModels`, `strictSectionScalarPresentation`, and `strictIntegralScalarPullback`. Their proofs use existing declared dependencies, including dependencies with their own outstanding proofs. This does not assert that the target import closure is axiom-free.

The remaining statement is strictly the quotient-tensor part of the argument: for a fixed scheme, fixed scalar presentation, canonical coefficient datum, explicitly given actual section quotient tower, and existing normalized tensor structure, it supplies SectionReductionModels and the augmented completion isomorphism. It contains none of the finite-local-model, geometric restriction, product comparison, cone-coordinate or general functor-comparison conclusions of the item. Its docstring gives the full source argument, including positive exponents, zero quotient and empty site.

## No longer needed

The original seven proof-only imports are removed from the item module: `Sheaf.CategoryTheory.InternalModuleInverseImageComparison`, `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`, `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`, `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`, `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`, `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`, and `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`. Necessary geometric limit facts are used in StrictCompletionRestrictionLimits. InternalModuleInverseImageComparison and ProEtaleObjectInverseImageRestriction are absent from this theorem’s new Lean import closure: the proof reuses the already constructed upperComparison and upperStarIsoLocalizationRestriction APIs instead. Their named DAG nodes are not withdrawn, and other general tools remain in the import closure where existing dependencies use them.

The geometric Comparison is obtained directly from scalar compatibility, exactness and product preservation. It does not need a separate geometric derived-tensor/pullback comparison. The finite-model argument uses a biproduct matrix/cokernel calculation, with the same pro-etale cover, rather than a new local-model transport statement. The general comparison uses one scalar-cone map and the canonical product comparison, so no separate quotient-by-quotient comparison theorem is needed for that clause.

No existing module or declaration is withdrawn. Of the fourteen original direct proof dependencies, lem-sfb-proetale-object-inverse-image-restriction is no longer reachable in this item’s updated DAG proof closure. The other thirteen remain transitive through the interface and existing source lemmas. No claim is made that the project’s other targets cease to use the omitted node or its module. The parent proof dependencies are replaced by the actual assembly lemmas; all original tool approvals are retained in their original order.

## Where the brief, the DAG or earlier work was wrong

No false original statement was found. In particular IsSectionIntegral requires actual section quotient tensors and their augmented completion, not merely a presentation transported across an equivalence. The proof retains that distinction and leaves only the corresponding tensor-normalization subargument separate.

Keeping Presentation and Comparison in the theorem module would create an import cycle with comparison lemmas. The interface extraction and explicit identity-complex transport are documented in the change record, and preserve the same constructions. The reduction-model structure is generalized over its section ring and then specialized by an abbreviation; its fields and normalization are retained. The unit route is unchanged. Profiling the extracted interface exposed repeated unfolding of KFlatRoos.tensorUnit in its unit equation; local irreducibility annotations keep the tensor constructions folded while the explicit identity-complex comparison fixes the source of the mapped unit. The explicit scalar/unit aliases in the geometric scalar proof avoid repeatedly unfolding the large monoidal instance; generic extension-unit extensionality supplies the map equality.

## New nodes

`def-sfb-strict-completion-restriction-data` attaches the nine relocated interface declarations to their new module.

`lem-sfb-strict-scalar-completion-functor-comparison` proves all strict cone, product, Roos, localization and unit fields for an exact additive scalar-compatible functor preserving countable products.

`lem-sfb-strict-integral-completion-presentation` constructs the canonical integral presentation from CompletionTriangleComparison.

`lem-sfb-strict-completion-restriction-limits` proves preservation of all small limits by the permitted multiplicative closure of immersions and weakly etale arrows.

`lem-sfb-strict-completion-finite-constant-models` proves the finite scalar-matrix local-model equivalence.

`lem-sfb-strict-section-scalar-presentation` constructs the section scalar presentation and proves its local section formula.

`lem-sfb-strict-integral-scalar-pullback` proves geometric pullback of the canonical scalar.

`lem-sfb-strict-section-principal-quotient-models` states the remaining normalized quotient-tensor and augmented section-completion subargument.

Change record: `coord/changes/strict-completion-restriction-interface.md`.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
