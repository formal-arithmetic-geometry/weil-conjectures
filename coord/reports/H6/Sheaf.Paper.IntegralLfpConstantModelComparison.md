## What changed

Implemented the integral comparison without changing its statement or coefficient definitions.
The proof retains the original stratification, descends full scalar cokernel classes through
flat presentation covers, applies the local Smith-to-model bridge, composes the covers, and
transports coefficient rings explicitly. The converse explicitly pulls finite presentations from the point and transports
them across the canonical coefficient isomorphism. Added the canonical continuous-ring realization in universe u,
explicit matrix and fibre-class constructions, and a complete geometric compatibility proof.
Named wrappers keep the coefficient morphism and pullback
composition folded during kernel checking. The model-cover composition uses the standard
bind construction and explicit local model witnesses. Generic coefficient-ring lemmas
keep descent, stratification and coefficient change independent of the large integral
coefficient instance. Public naturality of the test projection keeps the canonical adjoint
construction independent of private proof helpers.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.integralLfpConstantModelComparison`. The assigned module and
all four new supporting modules contain zero sorry occurrences. One original hole closed; zero holes added; zero holes remain in the five delivered modules.

`AlgebraicGeometry.ProEtale.ContinuousRingUniverse.integral_cokernel_hasFiniteConstantLocalModel`
is implemented using the canonical integer-ring equivalence, equality of adic and valuation
topologies, continuous local Smith form, and explicit scalar-matrix point models. All five modules compile without warnings. The full packet check compiled the four
supporting modules in 10.4, 14.9, 28.4 and 37.9 seconds; after deriving the point-pullback
additivity and colimit instances locally, the assigned comparison compiled in 21.2 seconds with the original public commands retained.
No timeout limit was changed. Delivery checks noted 60-second axiom-probe timeouts in the realization, fibre-compatibility
and local-model modules across the dry runs; ordinary compilation of all three succeeded.
The tool schedules those probes again at merge. The required delivery tool also runs project preflight and classifies the independent review.

Proved `ContinuousRingUniverse.comparison_isIso` and its ring compatibility,
`ContinuousRingUniverse.presentationFiberType_specializes`, and
`ContinuousRingUniverse.presentationFiberType_eq`. The latter constructs geometric evaluation
for arbitrary totally disconnected commutative topological rings, its regular-module scalar
normalization and finite-biproduct coordinates, then compares both cokernels at one common
geometric point. All isomorphism, local-presentation, cover-composition and stratification glue
in the assigned module is written without sorry. The delivery closes one existing hole and adds no holes; its proof uses existing stated
dependencies, including the continuous local Smith theorem.

## No longer needed

Removed these original proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`: the existing stratification
  interface is available through the statement imports.
- `Sheaf.CategoryTheory.RingedSiteModules`: no separate ringed-site module construction is used.
- `WeilConjectures.FieldTheory.CommonExtensionFields`: a point of the fibre product, followed by the
  algebraic closure of its residue field, supplies the common geometric representative.
- `Sheaf.LinearAlgebra.ContinuousIntegralMatrixLocalSmith`: the single-presentation
  bridge owns the Smith step; the main comparison no longer applies it directly.
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`: available through the coefficient definitions;
  the main comparison itself only uses nonarchimedeanness and total disconnectedness.
- `Sheaf.Paper.ContinuousIntegralCoefficients`: replaced by canonical continuous realization
  in the coefficient universe required by the assigned statement.
- `Sheaf.Paper.GeometricFieldProEtaleEvaluation`: used inside the geometric compatibility
  module, rather than directly by the main comparison.
- `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`: no separate relative-tensor API
  is used by the comparison proof.

The old Type 0 APIs `Sheaf.Paper.ContinuousCoefficientRealizations` and
`Sheaf.Paper.IntegralRegularCoefficientPullback` are not used: the new canonical realization
and geometric scalar calculation work for T : Type u. The separate node
`lem-weil-common-extension-fields` is unnecessary. The minimal-closed-subsets Noetherian
argument is replaced by Mathlib's Noetherian-space instances and the immersion's inducing-map
inheritance. Continuous integral Smith form remains necessary inside the local Smith-to-model bridge;
no pruning of it is claimed. The generic implication from finite constant models to local
finite presentation is proved directly, so `det-def-sfb-constructible-local-model` is not used. Scalar-tensor bookkeeping is expressed through point pullback
and preservation of cokernels, rather than a separate scalar relative-tensor construction.

Removed direct DAG dependencies are accounted for as follows (this does not claim that
facts retained inside the new supporting modules were pruned):

- `pqf-def-locnoeth`, `def-weil-pbc-quasi-compact-scheme`, and
  `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`: Mathlib supplies the
  Noetherian-space, compactness and immersion-inheritance instances directly.
- `def-weil-sheaf-of-modules-category` and `def-sc-finitely-presented-module`:
  the proof uses the existing internal `Mod` category and its presentation predicate.
- `lem-weil-pbc-continuous-coefficient-realizations`,
  `def-weil-pbc-continuous-integral-coefficients`,
  `lem-weil-pbc-integral-regular-coefficient-pullback`, and
  `det-pe-condensed-point-coefficients`: the universe-polymorphic canonical comparison
  and the explicit geometric scalar calculation replace these direct interfaces.
- `lem-pc-algebraic-closure-exists-unique`, `lem-weil-pbc-morphism-from-spec-field`,
  and `lem-weil-pbc-fibre-product-points`: the compatibility proof uses Mathlib's
  algebraic closure, residue-field point and pullback-carrier interfaces directly.
- `lem-weil-common-extension-fields`: the common geometric representative is constructed
  from a point of the fibre product, so no common-extension-fields module is imported.
- `def-sfb-modobj-relative-tensor`: preservation of presentations by point pullback
  replaces the separate relative-tensor argument.
- `lem-weil-pbc-geometric-field-proetale-evaluation` remains used by the compatibility
  module; `lem-weil-l-adic-extension-integers-dvr` and
  `lem-sfb-continuous-integral-matrix-local-smith` remain used by the local-model bridge.
  Their direct dependencies and imports were removed only from the parent comparison.

The removed parent `tool_uses` entries are the continuous coefficient realization,
geometric-field evaluation, extension-integers DVR, integral regular coefficient pullback,
condensed point coefficients, and common extension fields entries named above.

## Where the brief, the DAG or earlier work was wrong

The assigned statement is unchanged and is not disputed. Several planned coefficient APIs
accept E : Type 0, while this statement has E : Type u. The canonical adjoint construction
was therefore generalized. The local Smith declaration uses the original integer ring with
explicit adic topology; the assigned coefficients use the WithAbs integer subring with its
valuation topology. Their identification is necessary, not definitional. Empty schemes,
zero-sized matrices and torsion are retained. The inherited report listed geometric compatibility and the Smith-to-model bridge as
remaining holes; both now have complete proof terms. A local alias for the coefficient
subring caused repeated unfolding of the valuation and point inverse-image constructions.
Using the explicit coefficient expression avoids that reduction without changing any definition.

## New nodes

`lem-sfb-continuous-ring-universe-realization` records the proved canonical continuous-ring
comparison and its ring compatibility, constructed by the point inverse-image adjunction.

`lem-sfb-integral-continuous-presentation-matrix` records the explicit matrix, scalar cokernel
class, coefficient wrappers and proved specialization invariance.

`lem-sfb-continuous-presentation-fiber-compatibility` records the proved comparison of two
presentations at equal base points, by common geometric evaluation and finite coordinates.

`lem-sfb-integral-continuous-cokernel-local-model` records the proved Smith-to-sheaf
bridge. Each node inherits the parent's chapter and restricted-functor unit. No unit route
or statement changed. No existing public signature or definition is changed by this packet. The earlier
import-cycle repair is present in the current shared sources, so the delivery contains
only the assigned module, four new supporting modules, their DAG records, and this report.
No forced consumer adaptations are included.
The conservative command-interface check also requires the record
`coord/changes/H6-integral-comparison-proof-local-elaboration.md`, which documents
the file-local transparency option, notation scope and local instance attributes,
and lists every current transitive consumer. These commands change no exported
statement or coefficient construction.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
