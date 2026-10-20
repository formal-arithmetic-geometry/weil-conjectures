## What changed

Replaced the original theorem's hole by a complete reduction to the normalized
module-sheaf extension system. The original theorem's statement is unchanged.

The original module now proves `coherent_of_normalized`: factor an arbitrary coefficient
immersion as closed then open, obtain full faithfulness from the separate adjunctions,
and transport through `gamma`. Naturality identifies the stated restriction-conjugation
Hom map with the inverse of the extension map, proving the module Hom bijection.

It also constructs every field of `DerivedCoherence` in `derivedCoherence`. Exact
adjunctions descend termwise through localization. The invertible restriction comparisons
give full faithfulness for the open left adjoint and closed right adjoint; the same
factorization gives it for every immersion. The derived Hom map is proved bijective,
with its precise formula. The comparison isomorphisms use the published exact-functor
APIs. Their three termwise formulas, both unit equations and associativity are proved,
including equality transports for composite coefficient immersions. The associativity
proof uses the adopted source library's `mapDerivedCategoryCompNatIso_cocycle`.

Three geometric components are now proved as well:
`proEtaleIdentifiedOpenClosed` constructs an exact additive open extension for actual
tensor pullback, with invertible unit, closed cross-vanishing, and invertible counit on
sheaves of zero closed restriction. It proves exactness of actual identified-coefficient
closed direct image and invertibility of the counit of its specified adjunction.
`proEtaleIdentifiedSupportedReconstruction` proves the normalized isomorphism, uniqueness
and naturality in the actual sheaf-of-modules presentation, using two support conditions.
`proEtaleLocallyClosedExtension` factors any immersion and constructs an exact pointwise
fully faithful extension with an invertible restriction comparison, transporting the composite
coefficient identification back to the given one. These three modules have no holes.

The unchanged module-sheaf definitions moved to
`LocallyClosedModuleExtensionCoherence`, publicly reexported from the original module,
to make the geometric result an acyclic dependency. `DerivedCoherence` remains in the
original module. A byte comparison confirms the moved declaration block is unchanged.
The new `NormalizedComposition` predicate contains only the four module composition
laws; module and derived full faithfulness and both Hom bijections are proved separately.
No source-library file or target was changed.

Validation: all five modules compile together cleanly through `lcompile.py` (the geometric
statement retains its one explicitly reported hole). The original downstream consumer
`FiniteDualityLocallyClosedComparison` also compiles unchanged. The final combined run
took 23.7 seconds for the original module and 15.4 seconds for the consumer.
The first delivery's combined compile-and-axiom probe exceeded its per-file limit;
preflight explicitly says that the merge runs it again. A separate cached-import axiom
probe compiled in 5.5 seconds. It checked all four changed/new public theorems.
Compiler diagnostics exposed
costly unfolding in concrete derived arguments. The final proof uses generic categorical
helpers for derived full faithfulness and associativity, and transports the closed
adjunction before deriving it. The complete original module compiles in 20.4 seconds
with the ordinary compiler time limit; no file or proof was split to change that limit.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.locallyClosedExtensionCoherence` by the complete Lean reduction
above. The original module has zero `sorry` declarations.

Added one hole:
`AlgebraicGeometry.Scheme.locallyClosedModuleExtensionCoherence`, node
`lem-sfb-locally-closed-module-extension-coherence`, in the new module of the same name.
Its proof is exactly `by sorry`, and its docstring and node retain the complete sourced
module-sheaf construction and normalization argument. It asserts the normalized exact
extension system only: it assumes no full faithfulness or Hom bijection on either
category and no derived comparison, termwise equation, or derived coherence law.

This is one decomposition (one upper hole closed, one smaller geometric hole added),
with net hole change zero. It is not a claim that the geometric construction is proved.
The axiom probe reports only `propext`, `Classical.choice` and `Quot.sound` for
`proEtaleIdentifiedOpenClosed` and `proEtaleIdentifiedSupportedReconstruction`.
The original theorem still reports `sorryAx` because of the geometric hole. The pointwise
`proEtaleLocallyClosedExtension` has no new hole but inherits `sorryAx` through the
existing `proEtaleRingDerivedPullbackComposition` used by the canonical pullback
composition comparison. That existing theorem and its node are unchanged.

The module and derived categorical consequences described above have no new holes.
The three named geometric interface theorems are fully proved; their components include
the pointwise exact extension, the open support criterion and normalized reconstruction.
The remaining hole still includes simultaneous factorization independence, mixed
composition comparisons and their normalized module unit/associativity laws.

## No longer needed

No DAG node or module is globally pruned: the remaining geometric theorem still needs
the open/closed localization, open-slice, support-reconstruction and normalization route.
The unit's route is preserved.

The original proof imports of `ProEtaleRingedOpenClosed`,
`ProEtaleImmersionLimitPreservation`, `ProEtaleRingedOpenComparison`,
`ProEtaleInverseImage`, `ProEtaleOpenRestrictionCounit`, `SiteMorphismComposition`,
and `Mathlib.CategoryTheory.Sites.CoverLifting` moved to the geometric dependency.
Direct imports of `ProEtaleRingedClosedCounit`, `ProEtaleSupportedReconstruction`,
and `ModulePullbackPushforwardAdjunction` are replaced by the proved actual-coefficient
factor and reconstruction interfaces. These older modules remain transitive dependencies
of the proved lower interfaces and are not globally pruned. The duplicate
`SiteMorphismComposition` import was removed. They are not withdrawn dependencies.

Removed `Sheaf.Paper.PbcCompletedPullbackActual`: the construction uses ordinary,
uncompleted module and derived categories. The geometric module also does not need
`WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction` or
`Mathlib.CategoryTheory.Localization.Predicate`; the original module imports the
termwise-adjunction and localization APIs for its now-complete derived proof.
No public import of the original module was removed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The existing supported-reconstruction interface uses
module objects in additive sheaves. Its generic adjunction algebra is reused, while the
new interface establishes the needed assertion for actual `SheafOfModules` tensor
pullbacks and direct images, including arbitrary inverse-image coefficient presentations.

The previous proof correctly distinguished open and closed
adjunctions. There is no adjunction for an arbitrary locally closed extension in the
argument. Exactness and module full faithfulness alone were not used to infer derived
full faithfulness: the proof explicitly descends the two separate factor adjunctions.

The new geometric statement was checked conceptually for identity and empty immersions,
open and closed special cases, and the zero coefficient ring. The normalizations reduce
to their specified adjunction maps in those cases. No extra coefficient or boundedness
hypothesis is imposed.

## New nodes

`lem-sfb-locally-closed-module-extension-coherence` extracts the genuine module-sheaf
construction and normalized composition assertion, strictly below the original combined
module/derived assertion. It retains the original geometric sources and nine proof
steps, with their declared dependencies. Its recorded Mathlib searches were run;
the source library and the complete blueprint were also searched for a shorter route.
The derived descent and both full-faithfulness/Hom arguments remain complete Lean in
the original module. The original node's proof and proof dependencies now follow this
reduction.

`lem-sfb-proetale-identified-open-closed` is the proved transport of the ringed
open/closed localization interface to arbitrary identified coefficient presentations.
The scalar transport, sectionwise direct-image comparison and localization argument
are complete Lean proofs. It supplies the special factor adjunctions and support criterion.

`lem-sfb-proetale-identified-supported-reconstruction` proves the needed normalized,
unique and natural reconstruction directly with the actual module functors. The
closed-unit assertion uses the existing closed-essential-image theorem; the rest reuses
the existing generic adjunction algebra, with the actual support hypotheses made explicit.

`lem-sfb-proetale-locally-closed-extension` proves the pointwise exact construction from
closed/open factors, Noetherian quasi-compactness, vanishing-ideal complements and actual
coefficient composition. The required LeanSearch, Loogle/LeanFinder and grep searches for each new node were run
and recorded. The change record lists all transitive textual users found by `--uses`,
including incidental short-name matches; their declarations remain unchanged. The geometric
node now uses these proved interfaces in Steps 1, 5 and 7; the unit route is unchanged.

Change record: `coord/changes/P1-locally-closed-extension-data-relocation.md`.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
