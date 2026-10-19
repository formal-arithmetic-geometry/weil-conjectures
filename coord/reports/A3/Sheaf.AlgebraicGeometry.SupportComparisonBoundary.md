## What changed

Proved `AlgebraicGeometry.exists_support_comparison_boundary` with its original
signature and all its normalization, exactness, comparison-square and naturality
clauses. The proof constructs the two normalized boundaries, realizes the three
specified comparison maps on injective cochain models, and transports the three
homology squares, including the snake boundary with its specified sign.

Moved the eight existing public definitions verbatim into
`Sheaf.AlgebraicGeometry.SupportComparisonBoundaryMaps`; the item publicly
reexports that module. This breaks the import cycle between the definitions and
the helpers used to prove their theorem. The declarations retain their types,
visibility, mathematical meaning and bodies. Replaced the retired pro-etale
lower-shriek import with the current source-library path. No other group's
module is edited.

The new fully proved modules are `SiteNormalizedSupportSequence`,
`SupportComparisonSnakeModel` and `SupportComparisonInjectiveLadder` under
`Sheaf.AlgebraicGeometry`. The site theorem uses the shared, proved
`CategoryTheory.Functor.exists_injectiveBoundary` API. Its additional input,
surjectivity of restriction on injective module sheaves, is proved explicitly
by extending a map from a sheafified free representable. The ladder uses
independent injective representatives and a chain map lifted into the
K-injective target. A direct base-change-unit calculation identifies all three
induced homology maps with the prescribed comparisons.

Validation: all five delivered Lean modules compile without errors or warnings
through lcompile.py, within the per-file limit. The original main signature and
each relocated definition were compared with the current source. No target
signature is changed. The three original direct consumer modules also compile unchanged against the
delivery overlay: `Sheaf.AlgebraicGeometry.SupportedBottomGluing` (21.3 s),
`Sheaf.Paper.PurityAffineLineOrientation` (15.6 s), and
`Sheaf.Paper.PurityRankOneLocalCalculation` (21.3 s). SupportedBottomGluing first
hit the time limit, then compiled against both the baseline and the overlay;
no consumer edits were required. The first full dry run passed compilation and
axiom checks and found only a node-signature metadata mismatch: the checker
omits the `noncomputable` modifier. That record is corrected. The repeated full dry run passed compilation,
axiom checks and preflight (`657f3cfaf2`, CODEX review class); nothing was
pushed by the dry run.

## Proved and sorry left

Closed the original single hole:
`AlgebraicGeometry.exists_support_comparison_boundary`
(`lem-pur-support-comparison-boundary`). Thus 1 of 1 original sorries is proved.

Added zero holes. There are no `sorry`s in any of the five delivered modules,
including their definitions. In particular these new results are fully proved:

- `AlgebraicGeometry.exists_site_normalized_support_sequence`;
- `AlgebraicGeometry.exists_supportComparison_injective_ladder`;
- `AlgebraicGeometry.SupportComparisonSnakeModel.f_naturality`;
- `AlgebraicGeometry.SupportComparisonSnakeModel.g_naturality`;
- `AlgebraicGeometry.SupportComparisonSnakeModel.δ_naturality`.

No unfinished statements are split off. The proof continues to use the existing
site-comparison and support interfaces supplied by the library, as authorized
by this stage.

## No longer needed

Removed these eight direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`;
- `Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives`;
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`;
- `Sheaf.Paper.ComparisonPullbackExact`;
- `Sheaf.Paper.PurityComparisonUnitInjectiveModel`;
- `WeilConjectures.CategoryTheory.InjectiveModulePresheaf`;
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves`;
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`.

The original public imports are now supplied through the public Maps import;
this relocation preserves the public interface. The old
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`
import is replaced by
`WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Defs`.

The main node now directly depends on the proved site-normalization, cochain
ladder and transported-naturality nodes, on the existing
`lem-pur-comparison-pullback-open-unit`, and on the relocated map definitions.
Its former direct dependencies removed from that node are:

- `def-pur-support-cohomology`;
- `def-sp-injective-resolutions`;
- `def-weil-pbc-site-comparison-morphism`;
- `lem-pur-comparison-unit-injective-model`;
- `lem-pur-support-site-comparison`;
- `lem-sc-bounded-below-injective-resolution-existence`;
- `lem-sf-comparison-pullback-exact`;
- `lem-sp-grothendieck-enough-injectives`;
- `lem-sp-right-adjoint-preserves-injectives`;
- `lem-weil-pbc-comparison-global-cohomology`;
- `lem-weil-pbc-comparison-pullback`;
- `lem-weil-pbc-complex-ses-long-exact-naturality`;
- `lem-weil-pbc-etale-restriction-injectives`;
- `lem-weil-pbc-free-yoneda-presheaf-module`;
- `lem-weil-pbc-proetale-restriction-injectives`;
- `lem-weil-pbc-right-derived-plus-injective`;
- `lem-weil-pbc-ringed-site-injective-module-injective-presheaf`;
- `prop-pur-kinjective-resolutions-exist`;
- `thm-pur-with-support-exactness`;
- `thm-weil-pbc-site-comparison`.

The fourteen old top-level `tool_uses` entries are withdrawn, in their original
order: `prop-pur-kinjective-resolutions-exist`,
`lem-sp-grothendieck-enough-injectives`,
`lem-sc-bounded-below-injective-resolution-existence`,
`lem-sf-comparison-pullback-exact`, `lem-sp-right-adjoint-preserves-injectives`,
`lem-weil-pbc-right-derived-plus-injective`,
`lem-weil-pbc-ringed-site-injective-module-injective-presheaf`,
`lem-weil-pbc-free-yoneda-presheaf-module`,
`lem-weil-pbc-etale-restriction-injectives`,
`lem-weil-pbc-proetale-restriction-injectives`,
`lem-weil-pbc-complex-ses-long-exact-naturality`,
`thm-weil-pbc-site-comparison`,
`lem-weil-pbc-comparison-global-cohomology`,
`lem-weil-pbc-comparison-pullback`.

Several of these remain necessary below the new helper nodes or in the
unchanged statement interfaces, as their dependency lists record. The genuinely
unneeded part of the old argument is the construction using direct-image
preservation of injectives, invertibility of the derived comparison unit, and
separate preservation-of-injectives lemmas for open restriction. The proof only
needs a lifted comparison chain map and a short exact restriction row. No claim
is made that every removed direct import is unreachable from all other targets.
No blueprint unit statement or realized step is removed.

## Where the brief, the DAG or earlier work was wrong

The old six-step proof route was valid but supplied much more than this
naturality theorem needs. Its derived-unit injective model and unit-isomorphism
steps can be avoided by lifting the canonical identification from the exact
inverse image of an etale injective representative into a pro-etale injective
representative. Inverse image is never assumed to preserve injectives.

The earlier attempt's compile-server failure has cleared. The retained sandbox
was resumed and its unfinished site-normalization and cochain-realization
proofs completed. No clock metadata or launcher files were changed.

Edge cases: the construction works for identity restriction and empty opens,
zero coefficients and the zero sheaf, and closed supports equal to the whole
scheme or empty. It uses only monicity to prove restriction surjectivity on
injectives. Both rows use the same `ShortExact.δ`; the comparison proof never
chooses a sign or an arbitrary comparison isomorphism.

## New nodes

`def-pur-support-comparison-boundary-maps` records the eight existing canonical
maps and normalization definitions in their new module, with unchanged bodies.

`lem-pur-site-normalized-support-sequence` proves normalized exact support
localization for a monomorphism on an arbitrary site. It supplies both boundary
existence and all three exactness assertions from the generic proved derived
boundary API and the explicit injective restriction argument.

`lem-pur-support-snake-model-naturality` packages the three graded objects and
cochain models and proves transport of all three naturality squares by cancelling
the model isomorphisms.

`lem-pur-support-comparison-injective-ladder` proves that the prescribed three
site-comparison maps admit a common cochain realization compatible with the two
normalized boundaries. Its proof includes the needed derived-base-change-unit
calculation.

Change record: `coord/changes/support-comparison-boundary-maps.md`, including the
verbatim old and new declarations and all 188 modules listed by the downstream
consumer check with their current holders. No forced adaptations are needed.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
