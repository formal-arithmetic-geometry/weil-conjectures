## What changed

Proved the assigned theorem from field-curve completion, a proved normalization/open-locus
lemma, a marked-diagram spreading theorem, and a proved fibre-density lemma. The original
statement and all public imports remain unchanged.

The normalization lemma handles a nonreduced target by factoring the component normalization
through its reduction. It constructs a finite surjection, a dense thickening locus, and dense
inverse images on every normalized component. The density lemma derives both required
fibrewise density conclusions from surjectivity of the marked opens onto the constant-field
models, using regular connected smooth fibres and continuity.

The remaining spreading theorem takes an explicitly supplied field diagram, preserves its
fixed number of components, and retains its curves and constant fields by compatible cartesian
squares. It is a separate descent problem: it does not construct that field diagram, and does
not assert the final density conclusions. The main theorem performs those two parts in Lean.

Continued on the descent problem after the initial split-policy refusal. Proved common-stage
descent for finite families of objects, arrows and equations. Also proved descent of universal
injectivity through surjectivity of the diagonal; finite radicial model descent; the affine
neighbourhood limit of a local stalk; extension of a specified finite radicial local model;
and realization of a prescribed purely inseparable generic field extension on a finite radicial
cover. Also proved simultaneous affine shrinking below finitely many finite maps,
which supplies the closed-image shrinking step. This replaces the degree-p tower in the remaining spreading node's proof plan.

All thirteen modules compile through lcompile.py. A separate temporary axiom audit
confirmed that each of the eleven fully proved new declarations uses only propext,
Classical.choice and Quot.sound; that audit file was removed. The assigned theorem and
the spreading declaration still report sorryAx, as this decomposition requires. No existing definition, target statement,
source-library declaration, or public interface was modified. No arbitrary existence witness
was used to define data.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.exists_good_curves_generic_diagram` (1 of 1).

Added eleven fully proved declarations, each with zero sorry:

- `AlgebraicGeometry.exists_affine_neighbourhood_stalk_limit`.
- `AlgebraicGeometry.exists_universallyInjective_pullback_stage`.
- `AlgebraicGeometry.field_curve_normalization_good_open`.
- `AlgebraicGeometry.exists_finitePresentation_arrows_stage`.
- `AlgebraicGeometry.exists_finitePresentation_equalities_stage`.
- `AlgebraicGeometry.exists_finitePresentation_family_stage`.
- `AlgebraicGeometry.exists_finite_radicial_model_stage`.
- `AlgebraicGeometry.exists_finite_radicial_neighbourhood_model`.
- `AlgebraicGeometry.good_curves_fibre_density`.
- `AlgebraicGeometry.exists_affine_neighbourhood_below_finite_maps`.
- `AlgebraicGeometry.exists_purely_inseparable_generic_cover`.

Added exactly one hole:
`AlgebraicGeometry.exists_spread_marked_curve_diagram`, in
`lean/Sheaf/AlgebraicGeometry/SpreadMarkedCurveDiagram.lean`, node
`lem-weil-pbc-spread-marked-curve-diagram`. Its body is exactly `by sorry`.
The remaining work is to apply the descent APIs to the supplied finite diagram, descend its
morphism properties and marked open, and perform the simultaneous shrinkings. Its docstring
and node give that proof, including empty index families. The radicial extension construction
and common-stage refinement results are now supplied by the proved declarations listed above.

This is a decomposition: one original hole closed and one new hole added, net zero holes.
It is not a sorry-free proof of the original theorem's entire dependency closure. Existing
imported declarations, including field-curve completion, retain their repository hole status.

## No longer needed

Removed the following direct proof imports from the assigned module:

- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`.
- `WeilConjectures.FieldTheory.PurelyInseparableDegreePIntermediate`.
- `Mathlib.FieldTheory.PurelyInseparable.Basic`.
- `WeilConjectures.RingTheory.LocalizationColimitPrincipalLocalizations`.
- `WeilConjectures.AlgebraicGeometry.LimitAffineTransition`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`.
- `WeilConjectures.AlgebraicGeometry.DescendFinite`.
- `WeilConjectures.AlgebraicGeometry.DescendSurjective`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent`.
- `WeilConjectures.AlgebraicGeometry.EventuallyProper`.
- `WeilConjectures.AlgebraicGeometry.DescendClosedImmersion`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore`.
- `Mathlib.AlgebraicGeometry.Properties`.
- `Sheaf.AlgebraicGeometry.DescendSmoothQcqs`.
- `Sheaf.AlgebraicGeometry.OpenImmersionInverseLimitDescent`.
- `Sheaf.AlgebraicGeometry.ProperFibreDimensionUpperSemicontinuous`.
- `Sheaf.AlgebraicGeometry.ProperSmoothGeometricComponentsLocallyConstant`.
- `Sheaf.AlgebraicGeometry.ReducedAlgebraicNormalizationFieldChange`.

These are direct-import removals, not withdrawals of their modules. The revised main proof
imports only FieldCurveCompletionInsep, FieldCurveNormalizationGoodOpen,
SpreadMarkedCurveDiagram and GoodCurvesFibreDensity. The corresponding descent results remain
in the spreading node's proof dependencies, while normalization results remain below the
proved normalization lemma or the existing field-completion lemma.

The original direct dependency and approved tool entry
`lem-sbc-smooth-connected-generic-geometry-core` are removed: the proved density argument uses
regular connected fibres over fields instead. The new density node records that geometry
input explicitly. The degree-p tower is no longer the radicial-extension route of the new
spreading node; its replacement is the proved prescribed-generic-cover theorem. This does not
claim that the degree-p lemma is unused elsewhere. No module or upstream declaration is
withdrawn, and no `deleted.txt` is supplied.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original DAG combined field construction, simultaneous
spreading, and fibrewise density in one proof. Their separation exposes a smaller descent
problem and permits complete proofs of the normalization and density parts. The original
unit route is preserved, including the parent that still needs this item. The edge-case review
covered n=0 in normalization, density and shrinking; empty finite object/arrow/equality families;
and nonreduced targets. The stalk model uses an actual point and therefore never assumes an
affine neighbourhood exists in an empty scheme without such a point.

The node's inseparable-extension tower can be replaced by finite-presentation model descent
and surjectivity of the diagonal. The new generic-cover theorem proves this replacement on
an arbitrary reduced base, without a Noetherian or irreducibility assumption on the whole base.
Its intermediate local-stalk theorem applies at any point.

The initial delivery attempt was refused by the split-off timing policy. It pushed nothing.
Work continued with the nine additional fully proved descent and local-model results; the
spreading statement was strengthened with cartesian realization data and its DAG updated.
A later preflight required LeanSearch as a separate search category. All twelve new nodes now
include individual successful LeanSearch queries and exact query records from searches.jsonl,
alongside the recorded LeanFinder/Loogle and Mathlib grep searches. Neither refused attempt
pushed a branch.

## New nodes

`lem-weil-pbc-affine-neighbourhood-stalk-limit`: proved the local stalk limit with canonical projection equations.

`lem-weil-pbc-descend-universally-injective-qcqs`: proved universal-injectivity descent using surjectivity of the diagonal.

`lem-weil-pbc-field-curve-normalization-good-open`: proved finite component normalization and dense thickening locus.

`lem-weil-pbc-finite-presentation-arrows-descent`: proved simultaneous arrow descent retaining the specified limit arrows.

`lem-weil-pbc-finite-presentation-equalities-descent`: proved simultaneous eventual equality at a common stage.

`lem-weil-pbc-finite-presentation-family-descent`: proved simultaneous object descent with cartesian squares.

`lem-weil-pbc-finite-radicial-model-descent`: proved finite radicial model descent at a common stage.

`lem-weil-pbc-finite-radicial-neighbourhood-model`: proved extension of a specified radicial local model to an affine neighbourhood.

`lem-weil-pbc-good-curves-fibre-density`: proved both fibrewise density conclusions from marked-open surjectivity.

`lem-weil-pbc-purely-inseparable-generic-cover`: proved realization of a specified purely inseparable generic field extension.

`lem-weil-pbc-spread-marked-curve-diagram`: one remaining sorry for descent and shrinking of a specified marked field diagram.

`lem-weil-pbc-finite-images-neighbourhood-shrinking`: proved simultaneous affine shrinking
below finitely many finite maps, including the empty family.

No change record is needed: all new statements have new modules and nodes; existing signatures
and definitions are unchanged.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
