## What changed

Repair of returned head `5b85642a3aa` (reviewer C-5b856): mathematical review passed;
landing failed because the reviewer correction named the change record by basename.
The retained change record is included at the full delivery path
`coord/changes/C4-orientation-support-data-relocation.md`, which must also be used for
reviewer corrections. Refreshed its consumer table and recorded claim holders against
current sheaf-dag. All five original public signatures still match current source.
The five reviewed Lean files and five node records are retained. Delivery rebuilds this
packet on current sheaf-dag; no source-library declarations are changed.

Replaced the sorry in `WeilConjectures.PurityFiniteSetting.affineLine_orientation` by
an explicit proof assembling the existing `affine_line_boundary_realization`, a proved
coordinate-pullback assembly lemma, and a separate local-residue step. The realization
provides both finite-Tor assertions, concentration, the complement bound, and the global
Gysin chart. The comparison's own exact snake-normalized boundary supplies the chart's
boundary. Its unique realization gives m. At each geometric point, the proof rewrites the
realized class as the coordinate boundary, applies actual supported pullback, and then the
local residue. No finite-type assumption on the geometric field is introduced.

Moved the four existing chart/map declarations into
`Sheaf.Paper.PurityAffineLineOrientationData`, publicly re-exported by the original
module. The chart, coordinate boundary and restriction map are verbatim. The coefficient
pullback wrapper orientationInputPullback now uses the existing shared
coordinateProCoefficientPullback implementation, with identical factors and an unchanged
signature. This fixes repeated expansion during kernel conversion. (Reviewer correction:
the delivered rewrite of orientationSupportRestriction as coefficientGroupMap broke the
`unfold … Transport.derivedMap` in PurityAffineLineOrientationInjectivity; its old body is
restored verbatim, and every direct importer compiles.)
Original public imports remain. Change record:
`coord/changes/C4-orientation-support-data-relocation.md`.

The new `orientation_coordinate_boundary_pullback` proof uses choice projections to extract
only the needed models, transport, and pro-etale
coefficient-compatible equality of `coordinate_boundary_geometric_pullback`, identifies
both class presentations, and rewrites the geometric structure map. The restriction
map unfolds in one step to coefficientGroupMap, so the existing equality is used directly.

## Proved and sorry left

Closed the original syntactic hole:
`WeilConjectures.PurityFiniteSetting.affineLine_orientation` (node
`thm-pur-affine-line-orientation`). Its combination proof is complete.
Also proved `WeilConjectures.PurityFiniteSetting.orientation_coordinate_boundary_pullback`
(node `lem-pur-orientation-coordinate-boundary-pullback`).

Two new named public theorem holes remain, each in its own module, with source and full
proof in words:

- `WeilConjectures.PurityFiniteSetting.orientation_coordinate_model_boundary`
  (`lem-pur-orientation-coordinate-model-boundary`): compare the Gysin and coordinate-model
  open-class presentations and their injective snake boundaries.
- `WeilConjectures.PurityFiniteSetting.orientation_local_residue`
  (`lem-pur-orientation-local-residue`): construct the geometric Gysin chart and transport
  the already stated rank-one residue to its total-derived support presentation.

Original holes: 1. Original holes closed syntactically: 1. New holes: 2. This is a
**decomposition**, with net hole count -1, not a completed purity proof. There is no sorry
inside a definition, private lemma, or combination proof. Existing dependency theorem
holes, including boundary realization and coordinate geometric pullback, are untouched.
The pullback assembly uses local irreducibility attributes on the large derived maps and
unrelated predicate fields to keep their implementation terms out of elaboration. These
attributes are local and change no public definition or instance.

## No longer needed

Removed these unused proof-only imports from the orientation module; they are supplied
inside the existing realization/pullback interfaces when those interfaces need them:

- `Sheaf.AlgebraicGeometry.OpenComplementKnown`
- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`
- `Sheaf.AlgebraicGeometry.EtaleClosedSupportAmplitude`
- `Sheaf.AlgebraicGeometry.EtaleClosedSupportTorAmplitude`
- `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`
- `Sheaf.Paper.PurTwistSheafLocallyFree`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `WeilConjectures.SixFunctors.Finite.BaseChange`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.SupportLongExact`
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`
- `Sheaf.Paper.FiniteTorAmplitudeSites`
- `Sheaf.Paper.PurityAffineLineDatum`
- `Sheaf.Paper.PurityRelativeKummer`
- `Sheaf.Paper.SupportedCohomologyHom`

The parent no longer directly needs `lem-pur-closed-support-exceptional-mate`: its exact
Lean conclusion is about the actual support-kernel pullback and has no separate assertion
identifying it with an exceptional adjunct. The local chart construction may still need
that result. The rank-one local calculation is needed by the local-residue item. The
coordinate geometric-pullback theorem is needed by the proved pullback assembly. No
whole module is claimed globally unreachable or withdrawn. The unit's relative Kummer
route stays in use through the existing interfaces. No source declaration is pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG's assembly identifies mathematical classes, but the Lean dependencies present them
in different forms: gysinKummerSection uses derived global sections, CoordinateBoundaryModel
uses evaluation of an Ext class and comparison, and rankOne_local_calculation uses
nonnegative right-derived functors on sheaves. None of the existing signatures directly
states the equality between the first two presentations or the local chart needed by the
parent. The two split-off statements isolate precisely these steps. In particular applying
`gysin_structure` over Omega would incorrectly require finite type over the original k;
the local item instead works over Omega itself. Empty bases are covered by boundary
realization and have no geometric points; arbitrary geometric extensions remain allowed.

The sandbox contained two stale modules from an earlier attempt:
`PurityOrientationSupportData` and `OrientationCoordinateResidue`. They were unimported
by this packet and were removed from the sandbox before delivery, without withdrawing
any repository module. No old delivery or quarantined source is deleted.

## New nodes

`def-pur-orientation-support-data` attaches the unchanged relocated chart and three maps.
`lem-pur-orientation-coordinate-model-boundary` is the chart/model boundary comparison.
`lem-pur-orientation-coordinate-boundary-pullback` records the proved assembly from the
existing geometric coordinate-pullback theorem and that comparison.
`lem-pur-orientation-local-residue` is the local chart/residue step, without global
orientation construction or geometric pullback. Mathlib LeanSearch, LeanFinder/Loogle,
source grep and all-blueprint searches found no exact replacement for these comparisons.

Verification note: every new node's direct dependencies exist, and a traversal found no
cycle through any new node. The inherited closure itself contains a pre-existing cycle
between `lem-pc-ring-hom-extension-differential` and its adjacent node, and eleven existing
missing references; this packet neither creates nor repairs those unrelated records.

Compilation: the data module, both split-off theorem modules and the proved geometric
pullback assembly compiled through lcompile.py. The pullback assembly completed in 46.7 s
after sharing its coefficient-map implementation and using projections of the existing
large existential theorem result. The original nested existential eliminations forced
repeated kernel conversion of the derived-functor terms and exceeded the fixed limit.
No compile limit was raised and no file was split for the time limit.

The previous ordered follow-up compilation of `OrientationCoordinateBoundaryPullback`
and `PurityAffineLineOrientation` exited successfully. The repair compiled all five modules
in dependency order through lcompile.py against the current server build, exit code 0.
The complete delivery checks are run by deliver3.py before the repaired push.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Forced adaptations

None. The six direct importers of `Sheaf.Paper.PurityAffineLineOrientation`
(AffineSpaceZeroSectionPurity, PurityAffineLineOrientationInjectivity,
TwistedCoordinateSectionCore, FiniteDiagonalOrientationReduction,
PurityAffineLineOrientationUniqueness, PurityAffineLineSupportStalk) compile unchanged against
the reviewer-corrected delivery.
