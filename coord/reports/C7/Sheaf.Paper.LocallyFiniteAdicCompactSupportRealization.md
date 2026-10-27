## What changed

The assigned theorem is reduced to native section geometry and a finite-stage scalar-mate
comparison. Its statement, geometric assumptions and six-arrow integral normalization are
unchanged. The common-stage naturality argument and the final constructibility argument
are written in Lean. The stage action is assembled from the existing normalized rational
left laws, retaining the prescribed finite functors and scalar comparisons. Its private
assembly lemma works first over an arbitrary algebraic closure and specializes only at
the end; this avoids repeated unfolding of the concrete native closure algebra. Equality
transport in the scalar associator is handled by substitution of the coefficient-map
equality. Associator replacement and transport between equal stage systems are proved
abstractly before specialization. No shared reduction behavior is changed.

The original thirteen supporting declarations move verbatim to the new public data module
`Sheaf.Paper.LocallyFiniteAdicCompactSupportData`. The original module publicly reexports
that module and retains every original public import. This avoids a cycle between the
statements of the split lemmas and the theorem that combines them. The extraction changes
no definition, signature, instance or global attribute. No adopted source-library file is
changed. The change record is
`coord/changes/C7-native-compact-support-finite-stage-descent.md`.

The direct-importer check exposed a timeout in the unclaimed module
`Sheaf.Paper.NativeGeometricBrownConstructibleComparison`. Two local opacity declarations
keep its generic private adjunction constructors and the standard derived-category
construction from unfolding during the native proof. The existing conversion then needs
explicit reflexive type equalities before its pointwise transpose equation. Public
signatures, imports, attributes and definition bodies are unchanged; its mathematical
proof route is unchanged. The additional change record is
`coord/changes/C7-native-brown-proof-conversion.md`. (Reviewer, 2026-10-27: the timeout is
pre-existing, not caused by this delivery: the published module takes about 75 s both against
the published build and against this delivery; the adapted module takes 8.9 s. The change is
kept as a proof-speed repair of an unclaimed module, and the change record says so.)

All six implementation modules compiled. All five original direct importers were
checked: four compiled unchanged, and the Brown comparison compiled with the local
performance repair above. Its sole direct importer,
`Sheaf.WeilSheaf.CompactSupportBrownConstructibility`, also compiled unchanged.
The compiler accepted every checked file within the enforced limit. Unchanged check
copies and profiling settings have been removed from the delivery.

## Proved and sorry left

The original hole is
`WeilConjectures.LocallyFiniteAdicCompactSupport.locally_finite_adic_compact_support_realization`
(node `lem-sf-locally-finite-adic-compact-support-realization`). Its proof constructs the
comparison natural isomorphism from finite-stage components, checks integral normalization
componentwise and proves preservation using the two realization image characterizations.
This is a decomposition, not an axiom-free proof of the mathematical theorem.

The delivery closes one original hole and adds two holes (net -1), a decomposition.

Two new named holes remain:

- `WeilConjectures.LocallyFiniteAdicCompactSupport.native_compact_support_geometry`,
  node `lem-sf-native-compact-support-geometry`. This supplies only normalized section
  geometry, independently of the finite-field datum, compactification and operation.
- `WeilConjectures.LocallyFiniteAdicCompactSupport.native_compact_support_finite_comparison`,
  node `lem-sf-native-compact-support-finite-comparison`. Given that geometry and the
  stage action, this gives coefficient realizations and rational finite-stage comparison
  isomorphisms, their transition equation and an integral normalization certificate.
  This certificate uses the unchanged `IntegralNormalization` predicate for a comparison
  whose components are identified with those finite-stage components. It asserts neither
  naturality on arbitrary common-stage arrows nor preservation of native constructibility.

`CategoryTheory.StageSystem.stageComparison_naturality` and
`WeilConjectures.LocallyFiniteAdicCompactSupport.locally_finite_compact_support_stage_action`
are fully proved from their stated dependencies. The data module contains no holes. The existing
`WeilConjectures.NativeGeometricBrown.native_geometric_brown_constructible_comparison`
remains fully proved; its performance repair adds no holes. No hole is hidden in a
definition, instance or private declaration.

## No longer needed

The final preservation argument needs no independent application of
`lem-sf-integral-compact-support-constructible`
(`Sheaf.Paper.SfIntegralCompactSupportConstructible`). A stage morphism already takes a
stage object to a target-stage object. The realization image clause and the comparison
isomorphism then give native constructibility for every object in the source image.
The node is removed from this route. (Reviewer: the node's `tool_uses` list is restored to
its published value; an existing node changes only in `proof`, `proof_deps`, `proof_origin`
and the fields the relocation requires.)
This is local pruning; no existing module is withdrawn, since other routes may need it.

All original direct proof imports are removed from the assigned module:

- `WeilConjectures.WeilSheaf.LowerShriek`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`
- `Sheaf.Paper.SfIntegralConstructible`
- `Sheaf.Paper.FiniteTorAmplitudeSites`
- `Sheaf.Paper.SfRationalizationKaroubi`
- `Sheaf.Paper.IntegralResidueTor`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Paper.SectionDerivedPushpullNormalization`
- `Sheaf.Paper.ContinuousRationalDerivedRealization`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence`
- `Sheaf.Paper.SfIntegralCompactSupportConstructible`
- `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`
- `Sheaf.Paper.SfIntegralDirectImageConstructible`
- `Sheaf.SixFunctors.IntegralOpenReductionComparison`
- `Sheaf.Paper.OpenFiniteConstructibilityInterval`
- `Sheaf.Algebra.Homology.RingedOpenTotalTensorKFlat`
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`
- `Sheaf.CategoryTheory.InternalSectionScalarAdjunction`
- `Sheaf.Paper.LocalizedDirectImageComparison`
- `Sheaf.CategoryTheory.PastedMatesCounitNormalization`
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
- `Sheaf.Paper.CondensedFlatCoefficientCalculus`
- `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.CompletedDirectImageLimits`
- `Sheaf.Paper.CompletedCondensedCoefficients`

These are not all mathematically discarded. Apart from the integral compact-support
constructibility lemma just named, the existing planned dependencies remain in the two
split lemmas' proof plans or the data module's statement dependencies. Thus they remain
available work below those lemmas. The new proof imports are the two split-lemma modules,
the proved stage-action module and the generic stage-comparison naturality module.
The data module retains only the private derived-mate API import its definitions use.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The downstream check exposed a conversion bottleneck in
the Brown comparison; it is repaired with file-local proof opacity and explicit reflexive
conversion subgoals, with no statement or mathematical-route change. The original last proof step requested a separate integral
constructibility result where the already-constructed stage action and realization image
clauses suffice. The rest of the original argument is preserved as finite-stage and
native-geometry work. The unit's route is retained; no unit realization is bypassed. Searches across the
blueprint for locally finite coefficients, stagewise comparisons and realizations found
no blueprint node identical to any of the new supporting statements.

The old node attached thirteen definitions as well as the theorem to one module. Their
attachment is now recorded in a definition node; the old theorem node's mathematical
statement is unchanged. The relocation change record audits the downstream Lean users. Neither X nor Y acquires an
absolute separatedness hypothesis. Identity extensions and equal-stage representatives
are included in both the transition equation and the generic naturality proof.

## New nodes

`def-sf-locally-finite-adic-compact-support-data` records the unchanged original definitions
in their cycle-free public module. The existing theorem node now attaches only its own
theorem, with its new proof route.

`lem-sf-native-compact-support-geometry` isolates the internal/section equivalence and
normalized native ring and operation comparisons, with the original source dependencies.

`lem-sf-locally-finite-compact-support-stage-action` records the assembly of the prescribed
rational operations and scalar comparisons into a stage morphism using the existing
normalized rational composition law.

`lem-sf-native-compact-support-finite-comparison` records the integral proper/open scalar
mate construction at finite coefficient stages and its rational/transition compatibility.
Its docstring and node give the complete remaining argument. Its normalization
certificate reuses the unchanged six-arrow predicate, avoiding a duplicate definition.

`lem-sf-stage-comparison-naturality` records the general three-factor naturality argument:
source stage transition, a same-stage representative, and inverse target transition.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Reviewer corrections (2026-10-27)

- `lem-sf-locally-finite-adic-compact-support-realization`: `tool_uses` restored to the published list.
- `lem-sf-native-compact-support-finite-comparison`: `stmt_deps` += the owners of the declarations
  its statement uses directly (`def-weil-algebraically-closed-coefficients`,
  `def-sf-locally-finite-adic-realization-data`, `def-pur-integral-compact-support-coefficient-data`,
  `def-sf-constructible-exceptional-coefficient-construction-data`,
  `def-weil-compactifications-refinements`).
- `lem-sf-locally-finite-compact-support-stage-action`: `stmt_deps` +=
  `def-sf-constructible-exceptional-coefficient-construction-data`,
  `def-weil-compactifications-refinements`.
- Brown change record: reason corrected (pre-existing slowness, not forced).
