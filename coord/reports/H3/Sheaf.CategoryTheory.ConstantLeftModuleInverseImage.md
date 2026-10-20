## What changed

Completed `CategoryTheory.constant_left_module_inverse_image` with its original signature:
normalized exact transport, composition and presentation uniqueness, localization,
preservation of quasi-isomorphisms, and the bounded-below derived comparison.

The unchanged supporting abbreviations, operation predicates, and
`ConstantLeftModuleInverseImageLift` are extracted to the publicly imported
`Sheaf.CategoryTheory.ConstantLeftModuleTransport`. Its theorem constructs the normalized
coefficient comparison, both abelian and module adjunctions, and exactness. It uses
`AddCommGrpCat.leftExactFunctorForgetEquivalence` sectionwise and extends transported
constant scalars along ring sheafification using `PresheafOfModules.sheafify`.

`Sheaf.CategoryTheory.ConstantLeftModuleInverseImageCoherence` proves the composition,
presentation, and over-site localization comparisons using constant-scalar linearity
and faithful forgetting. Its public import of module-sheaf pushforward supplies
`SheafOfModules.overFunctor` in its statement. All three delivery modules compile
without warnings, within the single-file limit (46.3, 13.9, and 7.9 seconds).

The extracted declaration block, original data structure, and original theorem signature
match current sources exactly: all 12 existing declarations retain their signatures,
and all non-theorem bodies are unchanged. No consumer needs adaptation.

The earlier return on head `1afa1abf98` added five missing users. The current
return on head `b1473c27a` identifies one further user:
`Sheaf.Paper.ConstantTowerDirectImageNormalization`. Added it to the sorted change-record
table with its current unclaimed status. It uses the unchanged, publicly re-exported
`Modules`, `V`, and `U` declarations; no consumer source adaptation is needed.

The official `tools/downstream.py` scan agrees with the refreshed source graph:
all 47 current transitive consumers are listed. The table preserves all earlier
consumer rows and refreshes their current holders.
All three retained proof modules compile on the server against the current published
build, without warnings (46.4, 14.3, and 7.4 seconds respectively). The unchanged
consumers `Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget`,
`Sheaf.CategoryTheory.Sites.ToposComplementModuleStalks`, and
`Sheaf.SixFunctors.GeometricInverseImageConstantModule` were previously compiled
against the delivery.

The explicit `#print axioms` check of the main theorem and both supporting theorems
reports exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
The rebased dry run passes. Its additional all-declarations transport probe timed out
at 60 seconds; the transport module itself compiled in 46.4 seconds, and the landing
performs its own axiom check.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.constant_left_module_inverse_image`
(`lem-pe-constant-left-module-inverse-image`).

Both new supporting theorems are completely proved:

- `CategoryTheory.constantLeftModuleTransport`
  (`lem-pe-constant-left-module-transport`).
- `CategoryTheory.constantLeftModuleInverseImageCoherence`
  (`lem-pe-constant-left-module-inverse-image-coherence`).

Holes closed: 1. Holes added: 0. Remaining holes: 0 across all three delivered modules.
No definition obtains arbitrary data from an unproved existence theorem, and no private
helper or definition contains a hole. Arbitrary unital rings, including noncommutative
and zero rings, and empty sites remain allowed.

## No longer needed

Removed proof imports from the item:

- `WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings`.
- `Sheaf.CategoryTheory.ContinuousCocontinuousToposAdjunctionForCoverings`.
- `Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects`.
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
- `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`.
- `Mathlib.CategoryTheory.Adjunction.Mates`.

The general abelian-group-object transport route
(`lem-weil-pbc-adjunction-lifts-abelian-group-objects` and
`lem-weil-pbc-sheaf-algebraic-structures-objects`) is replaced by the sectionwise
left-exact-functor equivalence. Scalar extension and linearity use Mathlib's module
sheafification and locally-surjective restriction APIs, so
`lem-weil-pbc-site-sheafification-sections-local` and
`lem-weil-pbc-module-sheaves-colimits-forgetful` are unnecessary. Coherence is proved
from normalized set comparisons and faithful forgetting, without
`lem-weil-pbc-conjugate-iso-unit-equation`. The actual over-site adjunction APIs replace
`lem-weil-pbc-continuous-cocontinuous-topos-adjunction` and
`def-weil-pbc-special-cocontinuous-functor` in localization.

Removed the parent's obsolete top-level tool approvals for
`lem-weil-pbc-site-sheafification-sections-local`,
`lem-weil-pbc-sheaf-algebraic-structures-objects`,
`lem-weil-pbc-module-sheaves-colimits-forgetful`, and
`lem-weil-pbc-continuous-cocontinuous-topos-adjunction`.
No entire library module is claimed globally pruned: other consumers may still need them.
The new nodes record the dependencies actually used; the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The reviewer passed the proof, but landing head `b1473c27a` found
`Sheaf.Paper.ConstantTowerDirectImageNormalization` missing from the change record's
`## Users` table. This repair adds that user and retains the earlier inventory. The
unchanged interface is publicly re-exported, so no source adaptation is needed.
All three modules compile against the current server build, and the rebased dry run
passes compilation and preflight. No mathematical statement or target interpretation changes.

## New nodes

`lem-pe-constant-left-module-transport` records the fully proved transport result
(original steps 1–6), with coefficient normalization, sectionwise abelian transport,
scalar extension, adjunctions, and exactness.

`lem-pe-constant-left-module-inverse-image-coherence` records the fully proved existence
of normalized comparison isomorphisms (original steps 7–9); uniqueness is proved in
the parent. Neither new node leaves an obligation for another worker.

Change record: `coord/changes/H3-constant-left-module-transport-extraction.md`.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
