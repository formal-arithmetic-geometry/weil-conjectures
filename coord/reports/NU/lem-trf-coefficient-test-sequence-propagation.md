## Worker report

The module `Sheaf.AlgebraicGeometry.CoefficientTestSequencePropagation` states
`AlgebraicGeometry.HilbertCoefficient.coefficient_test_sequence_propagation` with
`sorry`, and supplies six declarations in total. All definitions have real data;
there is exactly one postponed theorem, corresponding to this DAG node. Its docstring
carries the fifteen-step proof, including the boundary-history repair accepted from NY.
The inherited BLOCKED ending concerned stage 1. The current queue assigns this item to
stage 2, the live node has no Lean record, and the stage-2 handoff in brief-stage2 §0
explicitly authorizes proceeding. No stage-1 proof or statement was reopened.

Hypotheses, one by one:

- The rational ground field is `ULift.{u} ℚ`, allowing every scheme universe u.
  `p : Z ⟶ Spec (.of (ULift.{u} ℚ))` is its structure morphism.
- The smooth ambient and reduced closed embedded finite-type scheme are `[Smooth p]`,
  `[IsClosedImmersion i]`, `[IsReduced X]`, `[LocallyOfFiniteType (i ≫ p)]` and
  `[QuasiCompact (i ≫ p)]`.
- The point is `a : X`. The level is literally `HilbertSamuel.function (i ≫ p) a`.
  `hbound` gives the specified neighbourhood's lexicographic upper bound: X and Z
  are understood after restricting to that neighbourhood. The conclusion additionally
  chooses one `V : D.U.Opens` with `D.center ∈ V`, as in the common-power lemma.
- `D : RegularHilbertCoefficientDatum p i a m n s α Q` is the recorded datum,
  including its one affine étale neighbourhood, smooth coefficient scheme, Taylor
  homomorphisms, regular coefficients and the five division/Jacobian conditions.
  `hα : orderedVertices α` expresses the node's ordered minimal vertices (the
  datum record itself leaves this separate). `hQ` is exactly the newly explicit
  bound `(α l).degree - 1 ≤ Q`, pointwise in l; it is vacuous for s=0.
- `b`, `hb`, `hempty`, `hcommon` give positive common marking, the empty-list
  convention b=1, and divisibility by every positive weight d_i-|γ|.

Conclusions, clause by clause:

- `Nonempty (InitialCoefficientTestModel D V b)` asserts actual existence. Its three
  isomorphisms identify the ambient with `V.toScheme`, X with the actual cartesian
  pullback `pullback i (V.ι ≫ D.e)`, and the support with `(D.j ⁻¹ᵁ V).toScheme`,
  all over the prescribed maps. Its `ideal` field is the existing
  `commonPowerIdeal α D.coeff b` pulled along
  `supportIso.hom ≫ (D.j ⁻¹ᵁ V).ι`, so the ideal and every principal coefficient
  ideal are restricted to exactly this same support.
  Its marking, retained level and boundary are b, H_X(a) and the empty list.
- `InitialCoefficientTestModel.coefficients` is the principal ideal of each actual
  supplied coefficient, restricted along `A.supportIso.hom ≫ (D.j ⁻¹ᵁ V).ι`.
  Individual coefficient functions after blowup are only
  local (exceptional local equations differ by units). Their principal ideals
  therefore express the global coefficient transforms without choosing equations.
- `∀ d, CoefficientTestsThrough ... d ...` is quantification through every finite
  sequence and every prefix, including length zero. Its recursive step uses the
  existing `HilbertSamuel.Step`, hence precisely the three operations, actual
  blowups, scheme-theoretic strict transforms, cartesian pullbacks and labelled
  boundary rule from the dependency, rather than private versions of those notions.
- The predicate's first clause is the ambient equality `M.cosupport = S.locus`.
  `Embedded.locus` is the image of the exact retaining-level equality, so both sides
  are subsets of the current ambient. The explicit next-center equivalence uses
  `t.Admissible S.locus ↔ t.Admissible M.cosupport` on the very same labelled Step.
- The following clause gives the upper bound at every current X-point. The level
  in `Step.levelTransform` is summed exactly for line products, so induction gives
  Λ to the number of line products at each prefix, unchanged at either blowup.
- The `M.ideal = ⨆ ...` clause preserves the coefficient-power identity at every
  stage, not merely the order locus. For an empty vertex list the supremum is zero.
- `HasEtaleCoordinateFlag S.p M.j.ker M.j.ker S.boundary` gives boundary
  transversality everywhere, including points below the retained level, by distinct
  coordinate hyperplanes disjoint from the normal-coordinate indices of N.
  The center is N itself in this use of the existing flag, so its inclusion
  condition adds no extra geometric restriction.
- `HasRetainedCoefficientCharts` gives the five conditions at *every* retaining
  point using the recorded RegularHilbertCoefficientDatum. Its support square is
  cartesian, its coefficient principal ideals match the current ones, and each
  labelled boundary equation is a distinct W coordinate in that same datum's
  coordinates. Empty labels use the unit ideal on the chart.
- Recursive successor existence is `∃ M' C', CoefficientsTransform ...`. The
  universal clause then continues through *every* such transform. It does not
  assume any transform's existence as a hypothesis.
- `CoefficientsTransform` uses the dependency's controlled marked transform, and
  the exceptional-power identities for each coefficient: positive weights divide,
  negative weights multiply. For a line or boundary-intersection blowup its last
  branch is ordinary pullback. The commuting support map is determined by the
  closed immersion and is not an arbitrary map.
- `HilbertSamuel.Presents A.marked` states the named finite-test presentation
  notion explicitly, in addition to the stronger coefficient bookkeeping.
- Smooth pullback quantifies over arbitrary T, f into the chosen restricted
  ambient, r and the dependency's
  `Pullback f r`. Its prescribed cartesian square and level/boundary transport
  specify exactly X_1, Λ^r H_0 and the pulled boundary. For every cartesian source
  map g and every point y, the numerical formula is written explicitly.
- The next existential asserts existence of the actual marked pullback. Every
  marked pullback and its support square then satisfies `Presents` and all finite
  coefficient tests, with coefficients literally `(A.coefficients l γ).comap q`.
- The last universal clause gives preservation AND reflection of equality, strict
  lexicographic inequality, and non-strict inequality for all sequences F,G and
  every r. It never equates a positive-dimensional pulled-back level with H_0.
- Restriction and arbitrary relative-dimension pieces are included: the assertion
  is universal over every r and every smooth map of that dimension, including open
  immersions and identity maps with r=0. All test and pullback identities are actual
  cartesian/ideal identities and therefore apply on every open restriction too.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.HilbertSamuelInvariant`:
  `AlgebraicGeometry.HilbertSamuel.function`, `summation`, `lt`, `le`.
- `Sheaf.AlgebraicGeometry.MarkedIdealOrder`: `HilbertSamuel.order` through cosupport.
- `Sheaf.AlgebraicGeometry.HilbertSamuelPresentation`: `Embedded`, `Embedded.locus`,
  `Marked`, `Marked.cosupport`, `Step`, `Step.Admissible`, `Step.Transforms`,
  `Presents`, `Pullback`, `MarkedPullback`. Full signatures/docstrings were read.
- `Sheaf.AlgebraicGeometry.RegularHilbertCoefficientDatum`:
  `HilbertCoefficient.RegularHilbertCoefficientDatum`, `orderedVertices`, and the
  recorded formal/Taylor conditions included in that structure. The current server
  source was also checked with `scompile.py --source`.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, through Step.
- `WeilConjectures.Compactification.StrictTransform`: `strictTransform`,
  `strictTransformMap`, through Step and its marked transforms.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `Scheme.Modules.IsQuasiCoherentFiniteType`, through Marked. Smooth N is locally
  Noetherian, so this recorded finite-type predicate is coherence here.
- Mathlib: `IsReduced`, `Smooth`, `SmoothOfRelativeDimension`, `IsClosedImmersion`,
  `LocallyOfFiniteType`, `QuasiCompact`, `Scheme.IdealSheafData.ofIdealTop`,
  `Ideal.span`, ideal multiplication/powers, `IsPullback`. Relevant declarations
  and their docstrings were read in the pinned sources.
- Added already-landed statement dependency `def-trf-etale-coordinate-flag`:
  `Sheaf.AlgebraicGeometry.EtaleCoordinateFlag`, `HasEtaleCoordinateFlag`. This is
  the existing global labelled coordinate transversality predicate, not a copy.

All currently stated proof-dependency modules are imported privately:
CommonPowerHilbertMarking (public, since its ideal appears in the signature),
FormalCoefficientTransformCriterion, ImplicitTaylorCoordinateCalculus,
JetDiagramHilbertControl, MarkedControlledBlowupCharts, PermissibleCoordinateChart,
EtaleLocalNormalForm. Homogeneous continuous division,
coordinate-blowup division generators, extended local upper bound and logarithmic
transform nodes have no Lean record, so their modules cannot yet be imported.
They are retained in the node's proof dependencies and the theorem's proof docstring.

Searches (2026-10-23):

- msearch leanfinder: “Hilbert Samuel coefficient ideal presentations are stable
  under finite admissible blowups, affine line products, boundary intersection
  blowups and smooth pullback”: eight hits, concerning ordinary power-series
  ideals, ramification indices and smooth algebra charts; none states this theorem.
- msearch loogle: `AlgebraicGeometry.HilbertSamuel.Presents,
  AlgebraicGeometry.HilbertCoefficient.RegularHilbertCoefficientDatum`: zero hits,
  unknown project identifier. These are project declarations, not Mathlib ones.
- msearch grep in Mathlib/AlgebraicGeometry:
  `HilbertSamuel|coefficient.*[Pp]resentation|[Pp]resentation.*coefficient`: zero hits.
- msearch leansearch: “A Hilbert Samuel coefficient ideal is the sum of powers of
  coefficients with a common positive marking”: eight hits (Rees algebra, leading
  coefficient ideals, powers and graded ideals), none the presentation construction.
- msearch grep: `CoefficientTestsThrough|InitialCoefficientTestModel|
  CoefficientsTransform|HasRetainedCoefficientCharts`: zero hits.
- rg in WeilConjectures and Sheaf for HilbertCoefficient, coefficient presentation,
  commonPower/common_power, finite tests and the proposed helper names found the
  existing datum, presentation, local presentations, formal transform criterion,
  and MinimalEnvelopeCoefficientComparison. None states the supplied-data
  propagation theorem with all coefficient/boundary clauses. The source-tree search
  for this node id found nothing.
- The downstream MinimalEnvelopeCoefficientComparison module already has
  `markedCoefficientIdeal` and `coefficientMarked`. It has this item as a proof
  dependency. This delivery does not redeclare either construction or depend on
  its downstream theorem: InitialCoefficientTestModel only specifies the initial
  data by its defining equality. Importing that downstream theorem would create
  the dependency cycle forbidden in the brief. The public helpers here specify
  exactly the conclusion data and recursion belonging to this node, not new
  independent mathematical notions.

Edge cases checked before drafting:

- s=0 forces n=0 via orderedVertices, all weights and jet bounds are vacuous,
  the initial ideal and its propagated power supremum are zero, and b=1.
- Depth zero asserts initial equality and all coefficient conditions. Positive
  depths include the next-transform existence assertion, preventing vacuous tests.
- Empty schemes after a center removes a component are allowed; neither the
  recursion nor Marked nor Step has a nonemptiness or proper-center restriction.
- Empty cosupport permits the empty next smooth center; a boundary-intersection
  test need not have its center in cosupport. Admissible treats only type (i)
  as constrained. The five conditions are required at retaining points, whereas
  transversality is required globally, including lower-level boundary germs.
- Absent strict boundary labels remain unit ideals, and distinct active labels
  are distinct W coordinates.
- r=0, arbitrary étale residue-field lifts, open immersions, identities and r>0
  are included. The numerical formula is stated at every scheme point and retains
  the extended Hilbert--Samuel convention.
- A possibly empty/degree-zero vertex contributes no positive weights; the datum
  has an actual X-point, so the unit Taylor-ideal inconsistency is not silently
  removed by an extra positivity assumption on degrees.
- No independent small universe for test schemes or coefficient algebras is
  imposed: all schemes use u and the rational field uses its u-lift.

Source checked: ILO printed pp.93--94 (PDF pages 99--100), including the reference
from 2.3.11 to the embedded algorithm and the correction of smooth synchronization
in 2.3.13. The current blueprint ancestor lem-trf-local-term-locality was read;
this is its historical resolution branch, not its own unit statement.
The returned H3 required the local-scope statement clarification recorded below.
No new definition node or dependency rebind was needed.
No STATEMENT-DISPUTED claim remains after this correction. The older split_report
records the already-applied jet-bound correction; hQ retains it exactly.

Validation: scompile.py compiled the module in sandbox and library mode, within the
60-second per-file limit and without errors or non-sorry warnings. Delivery preflight
is run below through the prescribed wrapper; no live files or launcher tools are edited.


## Repair of returned delivery 898bf2a82bd2

H3 is repaired by one existential open `V` with `D.center ∈ V`. Every initial model
is now over `V.toScheme`; its source is `pullback i (V.ι ≫ D.e)` and its support
is `(D.j ⁻¹ᵁ V).toScheme`. The base, embedding and support equalities use these
restrictions. Both the common-power ideal and each principal coefficient ideal
pull back along the composite from the restricted support to the original D.N.
The finite-depth predicate, `Presents`, numerical smooth-pullback identity,
existence of marked pullbacks and their universal propagation all occur under
this same existential V. The purely numerical summation assertion stays global.

The advisory is also addressed: `InitialCoefficientTestModel.ideal` uses the landed
`AlgebraicGeometry.HilbertCoefficient.commonPowerIdeal` from
`Sheaf.AlgebraicGeometry.CommonPowerHilbertMarking`, imported publicly. No private
copy of that construction remains. Its theorem `commonPowerHilbertMarking` was
read in full: the final conjunct supplies exactly `∃ V, D.center ∈ V ∧ ...`.

Checks specific to the repair: depth zero is on V, not U; the distinguished point
and its supplied lift on N survive because `D.j D.b0 = D.center ∈ V`; V need not
be affine, since the original global sections restrict as ideal sheaves and the
five-condition charts are local. Empty coefficient lists still give the zero
ideal on the restricted smooth support with b=1. Empty transforms, identities,
open restrictions, arbitrary etale residue-field lifts and every relative dimension
remain allowed. No new condition on a, no chosen arbitrary map, and no extra
shrinking depending on a test sequence or smooth map is introduced.

## Statement corrected

The old statement, verbatim, is recorded in `statement_change.old_statement`.
It claimed the presentation for all of a supplied chart, although step 1 invokes
only the germ assertion of `lem-trf-common-power-hilbert-marking`. In the returned
example `X = V(xy(x+y-6))` in A² at the origin, with `N={z=0}`, coefficients
`(-w²,0,1)`, vertex 2, Q=1 and b=2, cosupport is only the origin whereas the
retaining Hilbert level includes all three nodes. This prevents whole-chart equality.
The correction copies the common-power lemma's allowance of a further open about
the distinguished point, and makes the initial objects and every subsequent
geometric assertion live over that one open. Smooth maps are explicitly into V.
Source: the local-restriction wording and landed `commonPowerHilbertMarking` of
`lem-trf-common-power-hilbert-marking`, extracting the local coefficient input in
BM 1997 Definition 6.2, (6.1), Theorems 7.20--7.21 and BMT 5.2, 6.2--6.3;
ILO VIII 2.3.11--2.3.13, printed pp.93--94, read again for its resolution context.
The current blueprint ancestor `lem-trf-local-term-locality` was also read in
`literature/blueprint/latest/`: this is a historical support node, not a unit statement.

All citers were found with `rg -l '"lem-trf-coefficient-test-sequence-propagation"'
under `dag/nodes`, then filtered by actual stmt_deps/proof_deps membership:

- `lem-trf-minimal-envelope-coefficient-comparison`: holds. Both the regular empty-list
  construction and the pointed etale comparison are local; shrink the former chart,
  or restrict the common comparison into the inverse images of both chosen opens.
  Relative dimension zero, retained level and ordered earlier-center ideals persist.
- `lem-trf-hilbert-samuel-local-presentations`: holds. Its conclusion explicitly allows
  restriction and a pointed etale neighbourhood at each a; choose V before its tests.
  Smooth pullbacks into that presentation chart are exactly what its proof needs.

Neither citer is edited. The node's proof and proof_deps remain verbatim; the
already-added landed coordinate-flag stmt_dep is retained, with old_stmt_deps
recorded in statement_change. This is a local-scope clarification, not a change to
the blueprint unit or its route.

## Second reading by NU

Self-check required by this dispatch (no other agents may be started): re-read the
returned H3, the corrected node and the full Lean signature. All original hypotheses
remain: rational base, smooth ambient, reduced closed finite-type X, point a,
ordered vertices, Q bound, the given lex upper bound, full regular datum, positive
marking, empty-list convention and all divisibilities. The one chosen V contains
the supplied center; initial ambient/source/support maps and every ideal restriction
use V consistently. Every finite test, boundary and coefficient identity is unchanged
in the depth predicate and is now applied to the restricted model. Every smooth map
has the restricted model as target, with the same cartesian source/support squares,
all r including zero, summed numerical formula and full propagated presentation.
The three numerical preservation/reflection equivalences stay outside the existential
and keep all sequences and all r. No whole-U presentation assertion remains.
The defect found in the saved packet was exactly the missing initial restriction;
this check confirms both it and the common-power advisory were repaired.

Validation of the repaired module: prescribed scompile.py passed both sandbox and
library compilation (19.1 s and 15.4 s), with no errors or non-sorry warnings.
Final dry-run and delivery are performed using deliver2.py only.
