## What changed

Completed the two remaining proofs in `Sheaf.Paper.PbcVerdierAxioms`, retaining the
sandbox proof terms and checking them against the current sources. No public signature,
public import, instance declaration or definition was changed.

`qbarStageTriangulated` compares the raw tensor-Hom category with the existing
rationalization by `Rationalization.tensorHomEquiv`. The private comparison is fully
faithful and essentially surjective, so the raw localization has the required universal
property. Mathlib's localization triangulation uses the published shift directly.
Uniqueness in `qbarStagePretriangulated_exists` identifies its integral-image triangle
set with the published one and transports TR4. These private helpers repeat the
localization comparison used privately in `PbcCommonStageCones`; that private theorem
is unavailable to importers.

`qbarScalarExtensionExact` obtains exact ambient tensor from its adjunction to exact
scalar restriction, restricts it through the fully faithful integral inclusions, and
transfers distinguishedness through the normalized integral/rational comparison. This
uses the actual shift comparisons, including identity coefficient extensions.

Retained the three already landed common-stage proofs and the existing unique-witness
pretriangulation. Updated the node's proof and proof dependencies to describe this route.
Single-file validation via `lcompile.py` passed cleanly in 8.7 seconds after the
private helpers' universe binder was localized; the file-level commands match the original.

Added proof-only imports of `Mathlib.CategoryTheory.Triangulated.Adjunction`,
`Mathlib.CategoryTheory.Localization.Triangulated`, and
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom`.

## Proved and sorry left

Closed both holes present in the current repository module:

- `AlgebraicGeometry.Scheme.qbarStageTriangulated`;
- `AlgebraicGeometry.Scheme.qbarScalarExtensionExact`.

Added zero holes and split off zero statements. The delivered module has zero `sorry`.
The three other original holes were already closed by the earlier R3 landing:
`CategoryTheory.StageSystem.qbarStageInclusionAdditive`,
`CategoryTheory.StageSystem.qbarTransIsoCommShift`, and
`AlgebraicGeometry.Scheme.pbcVerdierAxioms`; this delivery does not count them again.

The proof still uses previously stated dependencies with their own holes, including
`CategoryTheory.StageSystem.commonStage_verdier_existsUnique` and the coefficient
shift/preservation interfaces. This is a completed proof of this module from those
interfaces, not a claim that the entire target closure is axiom-free.

## No longer needed

Removed these ten explicit proof-only imports:

- `Sheaf.CategoryTheory.RingedSiteModules`;
- `Sheaf.CategoryTheory.ScalarLocalizationTriangulated`;
- `Sheaf.Paper.AdicCoefficientDatum`;
- `Sheaf.Paper.CommonStageCalculus`;
- `Sheaf.Paper.FiniteStagePairCategory`;
- `Sheaf.Paper.PbcConeIndependence`;
- `Sheaf.Paper.PbcDistinguishedDiagramLifting`;
- `Sheaf.Paper.PbcRationalCategory`;
- `Sheaf.Paper.PbcScalarExtension`;
- `Sheaf.Paper.PbcUniformCompleteTriangulated`.

The coefficient, pair-category, calculus, rationalization and integral triangulation
interfaces remain available through the existing public imports. Their repeated explicit
imports are unnecessary. This does not withdraw those modules or their needed results.

The concrete theorem does not need `prop-weil-pbc-cone-independence` or
`lem-weil-pbc-distinguished-diagram-lifting`: the generic Verdier theorem attached to the
same node already supplies the common-stage axiom argument. No unit statement or unit
proof step is bypassed. It also does not use
`lem-weil-linear-scalar-localization-triangulated`'s existential package of new shifts:
Mathlib localization is applied directly to the already published shift. Removed these
three direct proof dependencies and the obsolete scalar-localization `tool_uses` entry.
The direct dependencies `def-weil-pbc-adic-coefficient-datum`,
`def-weil-sheaf-of-modules-category`, and `lem-weil-linear-abelian-derived-category` are
also unnecessary here: the integral category already inherits their scalar actions and
linear shifts through the rational-category and calculus interfaces. They remain needed
by those constructions. A source-graph check removes `Sheaf.Paper.PbcConeIndependence` and
`Sheaf.Paper.PbcDistinguishedDiagramLifting` from this item's transitive import closure.
Both also leave the `TargetsCheck` import closure in the current source graph.

## Where the brief, the DAG or earlier work was wrong

The retained report incorrectly counted all five historical holes as newly closed and
said that no imports were removed. The current source already contained three of those
proofs. The counts and pruning list above use the current source as baseline.

The earlier R3 report left finite-stage triangulation and transition exactness unresolved.
The published interfaces now suffice: localization can use the recorded shift directly,
and the normalized tensor comparison transfers exactness. No mathematical statement or
definition repair was required. Search results confirmed Mathlib's localization theorem
and `Adjunction.isTriangulated_leftAdjoint`; the existing generic Verdier theorem supplies
the common-stage assembly.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
