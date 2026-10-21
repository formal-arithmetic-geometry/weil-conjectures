## What changed

The original theorem `CategoryTheory.ringedSheafSliceDerivedComparison` now has a
complete Lean proof from the ordinary ringed localization square. Its signature
and `HasRingedSheafSliceDerivedComparison` are unchanged.

The parent proves `sliceNormalizedDerived`: use uniqueness of left adjoints to
transfer quasi-isomorphism preservation to each supplied pullback, construct the
left derived functor by a resolving class, and normalize its adjunction on all
complexes. `derivedComparisonOfOrdinary` constructs beta by right-derived
uniqueness, constructs theta as its inverse mate, proves its representative
formula, proves its invertibility using flat K-flat resolutions, and proves the
mate and counit equations. The generic calculations are reused from the private
helpers of `RingedSliceDerivedComparisons` and `RingedSliceDerivedMate`.

`SheafSliceOrdinaryComparison` is also proved: it adds exact additive restriction,
K-injective preservation and K-flat preservation to the ordinary square. Its
`restrictKFlat` proof compares the actual canonical restriction with tensor
pullback through uniqueness of left adjoints, then transports K-flatness and
flatness across the resulting isomorphisms.

The three existing ordinary interfaces move unchanged into
`SheafSliceOrdinaryData`, publicly re-exported by the parent, to avoid an import
cycle. The square-only data record is new. `SheafSliceOrdinarySquare` isolates the
ordinary geometric/module Stacks 04IF lemma, with no derived hypotheses or
resolution-preservation conclusions.

## Proved and sorry left

Original holes closed: `CategoryTheory.ringedSheafSliceDerivedComparison` (one).
Holes added: `CategoryTheory.ringedSheafSliceOrdinarySquare` (one), node
`lem-sbc-ringed-sheaf-slice-ordinary-square`.

This is a decomposition, with net zero holes closed. The retained lemma is strictly
the ordinary geometric/module construction, with no derived-category assumptions
and none of the derived comparisons, representative equations, invertibility
arguments, or resolution-preservation claims. Its source is the separate Stacks
04IF lemma. Its docstring and node give its full natural-language argument.

`CategoryTheory.ringedSheafSliceOrdinaryComparison`, the normalized derived
adjunction helper, the derived comparison helper, and restriction K-flat
preservation are proved without additional local holes. The only delivered
`sorry` is the ordinary-square theorem above. No definition contains `sorry`.
No arbitrary data is defined by choosing a witness of that theorem: the parent
eliminates its existence proof only inside a theorem proof.

Edge cases checked mathematically: no section of the slicing sheaf is chosen, so
initial/empty slices are included; terminal slices give the original square.
The K-flat comparison uses arbitrary structural maps and includes the zero ring.
The derived universes and the four supplied HasDerivedCategory assumptions are
preserved exactly.

## No longer needed

Direct proof imports removed from the parent:

- `Sheaf.Paper.ProjectionMateExact`
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.CategoryTheory.GeometricModuleTransport`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.Paper.RingedTopoiDerivedPullback`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`

The generic resolving-class construction supplies the adjunction and all its
normalizations directly; the old projection-mate theorem and the separate
site-derived-tensor descent step are not used by this derived proof. The parent statement-dependency list remains unchanged; the projection-mate
reference in that list is retained as existing metadata, although this proof
does not apply that theorem. The old
right-adjoint/K-injective argument is replaced by the existing presentation
restriction API. The K-injective chain-representative construction is replaced by
right-derived uniqueness, so the parent no longer directly uses
`lem-weil-pbc-kinjective-hom-derived`. The parent no longer directly uses
`lem-weil-pbc-ringed-topoi-derived-pullback` or
`lem-weil-pbc-site-derived-tensor-descent`.

The tensor, module-adjunction and geometric-transport dependencies remain in the
ordinary-square node for its future proof. They are moved below that separate
result, not claimed globally unnecessary. The tensor pullback preservation API is
still needed (via `RingedToposKFlatPullback`); its internal dependencies remain.
No module is withdrawn, no upstream declaration is removed, and no global pruning
of a still-needed source-library dependency is claimed.

## Where the brief, the DAG or earlier work was wrong

The plan's ordinary Stacks 04IF construction is a separate substantial argument;
its listed dependencies supply tensor/adjunction tools but do not themselves
state the normalized arbitrary-sheaf slice square. That result is now the one
remaining named item. The derived construction needs no new homotopy-category
glue theorem: the existing generic right-derived comparison and mate calculation
suffice, including a beta equation on all complexes.

The `RingedSheafSliceAdjunctionData.pullback` field has a default value but is
still a freely supplied structure field. An arbitrary witness's module adjunction
therefore does not definitionally give the adjunction for canonical restriction.
The K-flat proof instead uses `continuous_cocontinuous_ringed_restriction`, whose
adjunction is explicitly for canonical module restriction. No definition repair
or weakening was necessary.

The ordinary-square node now consistently writes `A × F → A` and `B × E → B`,
using the first projection, as `Over.star` and the existing section-normalization
field require. The earlier prose used the opposite product ordering in places.

The unit `sk-rem-rest` has empty `realized.statement` and `realized.steps`; no unit
route is bypassed. All source-library files remain unchanged.

## New nodes

`def-sbc-ringed-sheaf-slice-ordinary-data` attaches the three unchanged moved
interfaces and the square-only record. Their explicit fields carry all ordinary
normalizations. Change record: `coord/changes/Q2-sheaf-slice-ordinary-data.md`.

`lem-sbc-ringed-sheaf-slice-ordinary-square` is the sole remaining hole: Stacks
04IF's geometric and module square, without any derived or resolution claims.

`lem-sbc-ringed-sheaf-slice-ordinary-comparison` is proved from that square and
existing restriction APIs, including the new proof of restriction K-flat
preservation. The parent node's proof, dependencies, origin and Lean attachment
now describe the actual reduction. No second reader was started.

Validation: first preflight rejected only the three missing LeanSearch search
records. An explicit LeanSearch query has now run and its exact logged result
is recorded for each new node. The unsupported parent stmt_deps edit was removed.
The canonical restriction and ordinary comparison module compile cleanly in 6.0 s.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
