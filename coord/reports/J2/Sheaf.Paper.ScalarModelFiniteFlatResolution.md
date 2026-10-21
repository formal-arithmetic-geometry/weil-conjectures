## What changed

Completed `CategoryTheory.independentConstantRingUnit_locallyBijective` in
`Sheaf.Paper.ScalarModelFiniteFlatResolution`. After forgetting rings to types, the
map is the original commutative-ring sheafification unit. Mathlib's local
injectivity and local surjectivity instances for that unit give the two conjuncts.
The proof uses `Presheaf.isLocallyInjective_forget_iff` and
`Presheaf.isLocallySurjective_iff_whisker_forget`. This is the same existing proof
pattern as the coefficient-map instances in
`Sheaf.AlgebraicGeometry.ResidueQuotientDerivedUnit`.

All existing declaration signatures, definitions, imports and docstrings are
preserved. A declaration-local `linter.unusedSectionVars` setting preserves the
existing public instance parameters without a warning now that the proof uses
fewer of them. No source-library files are changed.

Validation history: an earlier attempt compiled the modified module in 4.2 seconds
and checked the completed declaration's axioms. Subsequent attempts could not reach
Lean because of compile-service failures. In this fifth resumption on 2026-10-21,
the required initial `deliver3.py` invocation returned
`COMPILE FAILED (local), nothing pushed` after 196 seconds without Lean diagnostics.
The corresponding launcher process logged repeated `busy` responses. After waiting
two minutes, the worker retried the unchanged module through `lcompile.py`. That
retry also ended after 196 seconds with exit 124 and `NOT compiled`; its process
logged three remote exit-75 `busy` responses of about 60 seconds each. Nothing was
pushed. This failure concerns the service before Lean runs, not a Lean compile
exceeding the file limit.

The launcher records `busy` specifically for remote exit 75. A read-only SSH check
succeeded; the live compatibility entry point forwards to the versioned compile
service, whose source confirms exit 75 occurs only when the publication guard
remains active for 60 seconds, before the request is read or Lean starts. A separate
read-only process check found zero active `rsync` publishers. This reproduces the
previous attempts' publication-service failure; an ordinary busy-message exit 124
alone is not the evidence for this diagnosis. No launcher or service script,
publication marker, lock, or compiled artifact was changed.

Three scratch files outside the delivered `lean/` tree hold the ordinary scalar
resolution, the short-exact double-complex augmentation, and the regular constant
module / finite-power comparison. The first two adapt existing private arguments
in `Sheaf.Paper.FiniteConstantModelResolution`; the third adapts the local
bijectivity argument in `Sheaf.CategoryTheory.ConstantFiniteFreeSectionBasis`.
Their compiler validation is pending. `scratch/NEXT.md` records the additional
current-source interface checks from this resumption. They introduce no delivery declarations,
nodes, imports, or holes. The item's two main proofs remain unchanged.

## Proved and sorry left

Closed one of the module's three original holes:
`CategoryTheory.independentConstantRingUnit_locallyBijective`.
The compile-server axiom check reports only `propext`, `Classical.choice`, and
`Quot.sound` for this declaration. No holes were added or split off.

The following two original holes remain unchanged, both attached to
`lem-sfb-scalar-model-finite-flat-resolution`:

- `SheafOfModules.scalarModel_finite_flat_resolution_dvr`.
- `SheafOfModules.scalarModel_finite_free_field`.

This is a partial delivery of the existing multi-hole module, rather than a
claimed proof or decomposition of either main resolution theorem.

## No longer needed

None. No imports, nodes, modules or planned proof dependencies are withdrawn.
The two remaining main statements still require the scalar-resolution and tensor
arguments in the node.

## Where the brief, the DAG or earlier work was wrong

The recorded bounded-flat dependency
`CochainComplex.isKFlat_of_boundedAbove_flat` has equal site-object, site-morphism
and coefficient universes, whereas this item's statements allow all three to be
independent. The existing
`SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite` in
`Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients` supplies the general
bounded-flat interface. Neither main proof is changed in this delivery, so their
DAG route is retained. The finite-free power isomorphism in
`Sheaf.CategoryTheory.ConstantFiniteFreePowerIso` concerns extension between two
constant ring sheaves, not extension of an arbitrary finite module to the
arbitrary algebra sheaf B here; it does not directly prove the field clause.

Searches used the launcher's Lean Finder, Loogle and grep services, together with
local searches of Mathlib, `lean/Sheaf` and `lean/WeilConjectures`. No existing
complete theorem for this item's arbitrary ringed-site assertions was found.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
