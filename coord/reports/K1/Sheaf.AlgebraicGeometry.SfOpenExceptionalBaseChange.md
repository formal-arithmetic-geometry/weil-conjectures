## What changed

Proved both original theorems of `Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange`.
All existing declaration signatures, definitions, visibility and public imports are unchanged.

The ambient proof restricts the supplied FullCD bound by extension by zero, including
its second clause at every weakly-etale base object. Projection-preserving pullback
isomorphisms identify iterated direct images. The published FullCD theorem supplies the
new ambient datum. A local categorical calculation using fully faithful open adjunctions
and `iterated_mateEquiv_conjugateEquiv` proves invertibility of the specified comparison;
the support condition comes from the proper/open comparison and composition of open
extensions. No arbitrary map or unproved existence witness is used to define data.

The finite proof reuses the existing etale open-base-change theorem and unfolds the
specified five-arrow transported comparison. Each factor is invertible. Its stronger
applicability to all inputs of that transported composite does not assert an unrestricted
ambient pro-etale adjunction.

Updated the item's DAG proof, proof dependencies and proof origin to this argument.
Added one DAG attachment for the existing proved etale theorem; no new Lean module.
Retained `ProEtaleComparisonPullbackSections` as required by the comparison unit route.
Single-file validation and profiling pass against the current compiled library.
The resumed dry run identified two metadata defects in the existing-theorem attachment:
the missing LeanSearch category and a forbidden `lean.file` on an existing declaration.
Both have been corrected; the independent delivery reviewer checks the final packet.

## Proved and sorry left

Closed 2 of 2 original holes:

- `AlgebraicGeometry.ProEtale.sfAmbientExceptionalOpenBaseChange`.
- `AlgebraicGeometry.ProEtale.sfFiniteExceptionalOpenBaseChange`.

Both belong to `cor-exc-base-change-open-immersion-general`. Zero literal `sorry`s remain
in the item. Zero holes added; zero split statements. Every private helper is proved.
Existing imported declarations can still depend on their own recorded holes; this is a
proof from those declarations, not a claim that the complete axiom closure is finished.

## No longer needed

Removed direct proof imports (public imports remain unchanged):

- `Sheaf.AlgebraicGeometry.ExceptionalBaseChangeReducesToProper`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`.
- `WeilConjectures.Compactification.NagataCompactification`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived`.
- `Sheaf.Paper.EtaleOriginDerivedCategory`.
- `Sheaf.Paper.ComparisonPullbackExact`.
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`.
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact`.
- `Sheaf.AlgebraicGeometry.SfFullCohomologicalDimension`.
- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`.
- `Sheaf.Paper.EtaleCoefficientSystemAdjoint`.
- `Sheaf.Paper.FullCDClassRestriction`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`.
- `Sheaf.Paper.ProEtaleConstructibleOrigin`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.

These are pruned from this module's direct proof plan; no claim is made that other
parents or transitive imports no longer need them. The Noetherian/dimension/Nagata and
relative etale-origin adjunction construction is unnecessary here because the finite
comparison is already explicitly transported from the existing etale map. The ambient
proof implements the proper/open support argument directly for the specified mate,
without the differently presented reduction theorem. The compactification is supplied,
so no new Nagata compactification is needed. Unit-level statements and steps are kept;
`ProEtaleComparisonPullbackSections` remains imported for the comparison unit.

Old proof dependencies no longer directly used:

- `def-weil-proper-morphism`.
- `def-weil-finite-type-morphism`.
- `def-weil-extension-by-zero`.
- `lem-cbc-sieve-slice-sheafification`.
- `lem-weil-proetale-weakly-etale-localization`.
- `cor-exc-base-change-reduces-to-proper`.
- `lem-weil-pbc-finite-type-over-noetherian`.
- `lem-weil-pbc-locally-noetherian-quasi-separated`.
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`.
- `lem-weil-pbc-qc-open-immersion-finite-type`.
- `thm-nagata-compactification`.
- `lem-kun-dimension-finite-type`.
- `thm-sf-ambient-adjoint-class`.
- `thm-weil-pbc-site-comparison`.
- `lem-pur-etale-coefficient-system-adjoint`.
- `def-sf-etale-origin-subcategory`.
- `lem-sf-fullcd-class-restriction`.
- `lem-sf-comparison-pullback-exact`.
- `lem-cbc-proetale-extension-zero-comparison`.
- `lem-weil-extension-by-zero-exact`.
- `lem-weil-pbc-extension-by-zero-exact`.
- `prop-weil-pbc-inverse-image-modules-exact`.
- `lem-sf-class-compact-support-comparison`.
- `lem-cat-right-adjoint-composition`.
- `lem-weil-pbc-proetale-derived-pullback-composition`.
- `def-sf-fullcd-used-class`.
- `lem-sf-proetale-constructible-origin`.

The exact remaining dependencies and the generic open full-faithfulness and coefficient
pullback tools are recorded in the revised node. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The previous report was stale: the sandbox now contains a complete ambient proof,
not an ambient `sorry`. Earlier dependency availability and service failures are resolved
for the successful required dry run. Historical scratch probes and their logs are not
part of the delivery. The initial dry run flagged removal of the comparison unit's
`ProEtaleComparisonPullbackSections` import; it has been restored.

The planned independent finite clause was much longer than needed: its actual comparison
definition is a composite whose middle arrow is exactly the existing etale theorem.
The ambient proper-reduction theorem has a different presentation; the proved local
mate calculation handles the actual supplied adjunctions and comparison directly.
Neither target statements nor definitions have changed. No forced adaptations.

## New nodes

`lem-sf-etale-exceptional-open-base-change` records the unchanged existing proved theorem
`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion`
in `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange`. This is a source-library
reuse attachment, with its source proof and Mathlib searches, not a new statement or hole.
No change record is needed: no existing statement, definition or public interface changed.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
