## What changed

Prove `transitionExact` for the prescribed integral-image-normalized shift, rather
than choosing an arbitrary exact-functor shift. The ordinary comparison and the
integral normalization give a shift-compatible natural isomorphism through the
fully faithful intrinsic inclusion, proving integral exactness. The rational
comparison square is shift-compatible at one by the two localization identity
normalizations and the recorded transition normalization. Integer-shift coherence
extends this square to all integers. Finally, every rational distinguished triangle
is isomorphic to an integral image, so its transition image is distinguished.
The rational integral-image descent is factored into the new proved module
`Sheaf.Paper.SfRationalScalarExactOfIntegral`, privately imported by the item.
Its sole public theorem `WeilConjectures.sfRationalScalarExactOfIntegral` proves
this genuine substep for arbitrary finite coefficient extensions. The other
comparison helpers are private and proved. This extraction follows profiling
and the category-cache simplification below; it adds no proof obligations.

Prove `associator_cocycle` directly from `sfRationalScalar_coherence` and the actual
coefficient-inclusion laws. Compare whole natural transformations before taking
components. The stage-system uniqueness and the two pair-shift obligations
remain unchanged.

Cache `stageCategory` by returning its existing `ScalarLocalization.category`
instance directly. The old `inferInstanceAs` elaborated into an expanded record
of the same instance. The data and public signatures are unchanged. This avoids
expensive repeated record conversions in the kernel. The change record describes
the cache and its direct-consumer checks. Move only proof-local opacity settings;
keep respectTransparency enabled. No other existing Lean module is changed.

Update the two owning nodes' proof descriptions/origins to match these arguments.
The final clean `lcompile.py` request passed for the helper, item, and both unchanged
direct importers `GeneralAlgebraicallyClosedCoefficientStages` and
`GeneralAlgebraicallyClosedCoefficients`, with no warnings. Their temporary sandbox
copies were removed, so neither importer is delivered.
No target, public import, coefficient model, shift comparison, constructibility
predicate, or distinguished-triangle predicate is changed.

## Proved and sorry left

Closed two of the five original holes, without adding any holes:

- `WeilConjectures.SfAlgebraicallyClosedCoefficients.transitionExact`
  (`lem-route-transition-exact`).
- `WeilConjectures.SfAlgebraicallyClosedCoefficients.associator_cocycle`
  (`lem-pur-general-intrinsic-finite-field-transport`).

The remaining original holes are:

- `WeilConjectures.SfAlgebraicallyClosedCoefficients.stageSystem_existsUnique`
  (`lem-pur-general-intrinsic-finite-field-transport`).
- `WeilConjectures.SfAlgebraicallyClosedCoefficients.shift_existsUnique`
  (`lem-pur-general-intrinsic-finite-field-transport`).
- `WeilConjectures.SfAlgebraicallyClosedCoefficients.transitionIso_commShift`
  (`lem-pur-general-intrinsic-finite-field-transport`).

No split-off `sorry` statements are added. The new exactness module is fully
proved. These are proofs from the existing scalar and localization declarations, not a claim that all their
transitive dependencies have no remaining holes.

## No longer needed

No imports or modules are removed, and no node is claimed globally pruned.
The completed scalar-stage proofs use the intrinsic scalar pentagon, the actual
coefficient-inclusion laws, and normalization directly.
They do not import `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficientStages` or
`Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`. The completed scalar-stage
step replaces its planned use of `lem-general-algebraically-closed-coefficient-stages`
by the direct pentagon argument and `lem-route-transition-exact`.
The remaining pair-shift obligations retain their statements and planned
dependencies, so those modules are not declared globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The suggested route through `GeneralAlgebraicallyClosedCoefficients` cannot be
imported here: the import-direction checker finds that the general module already
reaches this item. Its scalar-stage proof pattern can instead be used directly
in proved private helpers. The remaining pair-shift proof must address that
dependency direction without changing its normalization.

The existing stage-category cache expands the raw category instance into a record.
The profiler and compiler diagnostics identified repeated conversions through
that record as a source of timeouts. Returning the same instance directly keeps
its data fixed and avoids the expansion. The generic rational exactness argument
also avoids repeatedly elaborating the small-model instance conversions.

The attempted stage-system uniqueness proof is not included: the generic
field-extensionality argument checks quickly, but the concrete cocycle-to-record
conversion times out in the kernel. Profiling isolated that conversion after
separating transition, associator, and coherence caches. The original named
`stageSystem_existsUnique` hole remains; it is not counted as closed.

Search: LeanFinder on uniqueness of directed stage systems returned eight unrelated
generic category/extensionality results; Loogle does not know the project-specific
`CategoryTheory.StageSystem`; the grep search found Mathlib's localization shift
construction and `Functor.isTriangulated_iff_comp_right`. Local searches located
the intrinsic scalar pentagon, the exactness argument, and the existing private
stage-system uniqueness arguments. These justified reusing the APIs without new
public mathematics.

## New nodes

`lem-route-rational-transition-exact-of-integral` records the proved rational
integral-image descent substep used by `transitionExact`. Its module is
`Sheaf.Paper.SfRationalScalarExactOfIntegral`; it constructs the localization
comparison, verifies its prescribed shift compatibility, and transports
distinguished integral image triangles. It is strictly the rational part of the
original exactness proof and adds no holes. Its source is the intrinsic scalar
exactness argument in the current blueprint.

Change record: `coord/changes/S2-sf-normalized-scalar-proofs.md`.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
