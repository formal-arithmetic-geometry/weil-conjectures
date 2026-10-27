## Worker report

States `WeilConjectures.PurityFiniteSetting.vector_model_chart_descent` in
`Sheaf.Paper.VectorModelChartDescent`. Its proof is `sorry`; all five supporting
definitions have actual data. The natural-language statement and proof are unchanged.
The theorem docstring gives all four steps of the node's proof, including the
nonaffine-open issue repaired during stage 1.

### Hypotheses and clauses

- The fixed finite-field datum is `F : FiniteFieldDatum`; `C : F.CoefficientDatum`
  records the prime ell different from the characteristic and the chosen coefficient
  closure. `E : IntermediateField (Padic C.l) C.Qbar` with the existing
  `FiniteDimensional` instance is the finite extension. `projectionSetting F C E n`
  uses the existing uniformizer quotient at level `n + 1`. Thus `n : ℕ` enumerates
  every positive level, with no divisibility condition and no restriction `E = ⊥`.
  No field instance is required for the quotient coefficient ring.
- The separated finite-type k-scheme is `Z` with named structure morphism `aZ` and
  `[LocallyOfFiniteType aZ] [QuasiCompact aZ] [IsSeparated aZ]`. Noetherianity is
  installed internally using `isNoetherian_of_locallyOfFiniteType aZ`; it is not
  another hypothesis on the theorem.
- A vector bundle of constant rank `d : ℕ` is the recorded
  `VectorBundleZeroSection.scheme Z d M`, for `M : Z.Modules` with
  `[M.IsFiniteLocallyFreeOfRank d]`. Its projection is precisely the dependency's
  `VectorBundleZeroSection.π Z d M`. This is the relative Spec Sym(M) convention
  of the node, rather than an unrelated topological vector bundle. Its finite-type
  and smooth geometry is supplied by the existing `vectorIntegration_geometry`
  and `finite_type_frames` results, not assumed.
- `Q` is the dependency's `P.diagonalTwist (VectorBundleZeroSection.scheme Z d M) d`:
  the compared ordered tensor of shifted finite root lines, namely A_V(d)[2d].
  `vectorModelDualizing` is `P.diagonalDualizing π`, the actual standing
  exceptional functor on the compared ordinary coefficient unit. Compactifiability
  is supplied internally from the affine finite-type projection.
- The specified isomorphism is the universal binder `c : Q ≅ vectorModelDualizing`.
  There is no existential replacement of c and no arbitrary orientation parameter.
- The cover is `(I : Type w) (U : I → Z.Opens) (_hU : iSup U = ⊤)` for an independent
  explicit index universe `w`. The frames
  `e : ∀ i, VectorBundleZeroSection.Trivialization Z d M (U i)` are exactly the
  recorded linear trivializations. Their actual induced inverse-frame morphisms
  are `Etale.vectorIntegrationChart Z d M (U i) (e i)`.
- The local equality hypothesis is the `∀ i, HEq ...` clause in
  `VectorModelChartDescentConclusion`. `vectorModelChartRestriction` first uses
  canonical Tate pullback inversely, then site pullback comparison, then pullback
  of **c.hom**, followed by `diagonalDualizingComparison`, `Dnc.pullComparison`,
  and `chartOrdinaryBaseChange` in the recorded Cartesian inverse-frame square.
  The latter is the actual exceptional base-change mate, including the ordinary
  coefficient-unit comparison. The other side is the recorded `chartGamma F C E n`
  followed by `diagonalDualizingComparison`, in the same ordinary-target coordinates.
  `chartGamma` explicitly uses `projectionAffineInPresentation`, and hence the
  ordered `affineSpacePurityComparison` with its published associators and trace.
- `HEq` is needed only because `affineTraceTower` and `iteratedAffineLine` are separate
  recursive definitions of the same ordered polynomial tower. Read both definitions:
  both start at the base and apply `AffineSpace PUnit` at each successor, and their
  projections have the same identity/successor recursion. Induction identifies them
  and their projections. The heterogeneous equality therefore transports along
  those type equalities; it does not quantify over an extra comparison isomorphism,
  omit a scalar, or identify arbitrary isomorphic schemes.
- The conclusion is ordinary equality `P.vectorModelSmoothUnit Z aZ d M = c.hom`.
  This helper is the recorded `smoothPurityTensorMapInPresentation` at the canonical
  compared ordinary unit and its identity presentation. It is precomposed by
  `(smoothPurityReassociation ≪≫ vectorModelTensorUnit).inv`, and then by the same
  reassociation as in `smoothPurityMap`. `vectorModelTensorUnit` is only cached-tensor
  endpoint transport, `chartUnitPullback`, and the actual left unitor. Thus this is
  exactly gamma_(pi,A_Z) with its source identified with Q, not a replacement by
  `diagonalDualizingObject.inv` or by the integration arrow. Both gamma and c have
  the same specified exceptional target. Working in the established fixed-scalar
  pro-etale realization uses the dependency's existing coefficient equivalence;
  no site or coefficient-universe equality is imposed.

### Dependency declarations read and used

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, its `Ring`, `Coefficient`,
  finite-field and positive-level fields.
- The convention `def-weil-scheme-morphism-properties` collects existing properties;
  the actual binders use Mathlib `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`.
- `Sheaf.AlgebraicGeometry.VectorBundleZeroSection`: `scheme`, `π`, `Trivialization`,
  `trivializationMap`, `trivializationMap_spec`, including their affine geometry and
  coordinate docstrings.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the intrinsic finite operation interfaces;
  the existing `smoothPurityPullback`, `smoothPurityTensor`, and `Dnc.pullComparison`
  supply their fixed-scalar presentations used here.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: standing finite
  exceptional transport; `smoothPurityExceptionalOver` and `diagonalDualizing`
  instantiate that same functor at the specified compactification.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: recorded coefficient twists;
  `FixedFinitePositiveCoefficientTwist.diagonalTwistEtale` and `diagonalTwist`
  (in namespace `PurityFiniteSetting`) expose precisely their finite positive
  shifted-root-line presentation, with `diagonalExponent_annihilates` at every level.
- `Sheaf.Paper.AffineDiagonalTateCoordinates`: `projectionSetting`, owned by
  `def-pur-affine-diagonal-tate-coordinates`, is the positive-level coefficient setting.
- `Sheaf.Paper.ProjectionPurityAgreement`: `projectionAffineInPresentation` and
  `projection_purity_agreement`; their explicit source, unit and exceptional target
  normalizations were read.
- `Sheaf.Paper.AffineSpacePurityComparison`: `affineSpacePurityComparison`,
  `projection_geometry`, `orderedSource`, and its tensor/exceptional recursion.
- `Sheaf.Paper.SmoothPurityMap`: `smoothPurityTensorMapInPresentation`,
  `smoothPurityMap`, `smoothPurityReassociation`, `smoothPurityTensorPresentation`.
- `Sheaf.Paper.DiagonalDncChartNormalization`: `chartGamma`, `chartUnitPullback`,
  `chartProjectionUnitSourceGeneric`, `chartProjectionUnitSourceRaw`,
  `chartProjectionUnitSource_existsUnique`, `chartProjectionUnitSource`,
  `chartCoefficientUnit_finiteTor`, and `chartOrdinaryBaseChange` are owned by the
  new definition node `def-pur-chart-unit-affine-comparison`. The normalization
  theorem remains a proof dependency only; its conclusion is not a statement input.
- `Sheaf.Paper.PurityDncInvariance`: `Dnc.pullComparison`, owned by the explicitly
  cited `def-pur-section-pullback-site-comparisons`, is the canonical site comparison.
- `Sheaf.AlgebraicGeometry.VectorBundleFiniteTypeFrames`: `finite_type_frames`,
  added as an already landed statement dependency for the internally supplied
  smoothness witness. No finite cover restriction is imposed on the given cover.
- `Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts`:
  `Etale.vectorIntegration_geometry`, `vectorIntegrationChart`,
  `vectorIntegrationChart_isPullback`, `vectorIntegrationBaseCoefficientPullback`.
  Its owning recorded node `def-amb-vector-integration-charts` is cited in `stmt_deps`.
  These are geometry/coefficient helpers; the integration comparison theorem is
  not used as a hypothesis or as the definition of either purity map.
- `def-sbc-affine-space` is the Mathlib match `AlgebraicGeometry.AffineSpace`;
  `AffineTraceTower` and upstream `iteratedAffineLine` are the existing ordered
  affine-space presentations, with no new notion defined here.

Proof-only imports retain `DualizingUnitComposite`, `StandingExceptionalComposition`,
`CanonicalOriginCompactSupportComposition`, `DegreeZeroDerivedMapGluing`, the upstream
smooth polynomial projection result, and the relevant Mathlib finite-type, affine,
Noetherian, separated, proper and triangulated modules. The Mathlib-only dependency
records were read: affine implies quasi-compact/separated, finite-type and separated
composition, Noetherian open restriction, and finite type for quasi-compact open
immersions. No dependency record is repaired or duplicated in this delivery.

### Edge cases

`d = 0` is permitted by the natural-number binder: both ordered affine towers are
literally the base in degree zero, twists are the coefficient unit, and inverse
shift/unitor comparisons use zero shift. Empty Z and the empty cover are permitted:
there is no nonempty index or nonempty-scheme assumption. The sole cover hypothesis
is still `iSup U = ⊤`. Disconnected and nonreduced Z are permitted without another
assumption. Opens U_i need not be affine or nonempty. All positive coefficient levels
are retained, including ramified extensions and levels not divisible by ramification
index; the exponent is the recorded ell^level annihilator. Rescaling c by a nontrivial
unit changes its actual pulled-back hom in the local hypothesis, so the normalization
does not become vacuous or forget the specified scalar.

### Searches

- `msearch.py`, LeanFinder: "A specified shifted Tate line isomorphism with the
  exceptional dualizing object of a vector bundle equals diagonal smooth purity if
  it agrees with ordered affine space purity on a trivializing Zariski cover".
  Eight hits: ordinary scheme-module isomorphism criteria and affine coordinate
  formulas, none stating the purity comparison.
- `msearch.py`, Loogle: `"DerivedCategory", "singleFunctor"`. Twelve hits on
  `DerivedCategory.singleFunctor`, its standard natural comparisons and full
  faithfulness. None states the normalized vector-model equality.
- `msearch.py`, grep: `purity|upperShriek|dualizingComplex|TateTwist` in
  Mathlib/CategoryTheory: zero hits.
- `msearch.py`, LeanSearch: "Two normalized purity maps from a shifted Tate line
  to a vector bundle dualizing object agree if they agree on a Zariski cover".
  Eight hits on normalization of schemes, local isomorphism properties, and
  linear base change; no matching statement.
- `rg` on upstream `WeilConjectures` and project `Sheaf` for
  `vector_model_chart_descent|vectorModelChart|lem-pur-vector-model-chart-descent`:
  no existing declaration. Concept searches for chart descent and normalized
  charts found `VectorIntegrationChartComparison` and
  `CompositionModelOrientationDescent`, both read. The former compares integration
  with ordered affine purity and the latter is the composition analogue; neither
  states this specified c equals the diagonal smooth map. Their canonical
  coefficient/chart constructions were reused where appropriate.
- Read the current blueprint `latest` smooth-purity unit and proof and its
  orientation-chart proof Steps 1--4, rather than relying on an older snapshot.
  The older source path in the node is retained, as required.

### Verification

Compiled with the prescribed `scompile.py`, once as a sandbox module and once at
its intended library path. No errors or non-sorry warnings. `autoImplicit` is
false, all universes are explicit, and the file has no line over 100 characters.
A probe replacing the local HEq by homogeneous equality diagnosed the separate
recursive polynomial towers; the final local HEq is intentional. The global
conclusion successfully compiles as homogeneous equality. No statement correction, dependency module, or `STATEMENT-DISPUTED` issue is needed.
The ownership node below is added for the returned H2 point.


## Repair of returned delivery 52033ad4eab2

The sole H2 return asked for definition ownership of the canonical chart maps and
three missing definition-owner citations. Re-read the retained delivery and the
current main node/source records. Current main still has the original item statement
and no Lean record; the sandbox item differs only in `stmt_deps` and `lean`. The
retained theorem and all five concrete helper bodies remain byte-for-byte unchanged;
only explicit public imports of the owning modules are adjusted. Delivery tooling
rebases this repaired packet on the current live branch.

1. Added existing-definition node `def-pur-chart-unit-affine-comparison`, on
   `Sheaf.Paper.DiagonalDncChartNormalization`, owning every requested declaration:
   `chartUnitPullback`, `chartProjectionUnitSourceGeneric`,
   `chartProjectionUnitSourceRaw`, `chartProjectionUnitSource_existsUnique`,
   `chartProjectionUnitSource`, `chartCoefficientUnit_finiteTor`, `chartGamma`,
   and `chartOrdinaryBaseChange`. Replaced
   `lem-pur-diagonal-dnc-chart-normalization` in `stmt_deps` by this definition node.
   The theorem remains in the unchanged `proof_deps`; no data or proof was copied.
2. Cited `def-amb-vector-integration-charts` for inverse-frame chart maps, the
   Cartesian-square fact, coefficient pullback and geometry, and imported its exact
   module publicly. Removed the broader integration theorem's statement dependency.
3. Cited and publicly imported `def-pur-section-pullback-site-comparisons` for
   `Dnc.pullComparison`, and `def-pur-affine-diagonal-tate-coordinates` for
   `projectionSetting`.
4. Retained `lem-pur-vector-bundle-finite-type-frames`: its `.choose_spec` really
   supplies the smoothness instance, as the independent return confirmed.

The accepted hypotheses, local HEq premise, global ordinary equality, and theorem
signature are unchanged. Rechecked rank zero, empty/disconnected base, nonaffine
chart opens, independent index universe, all positive levels and ramified E: the
ownership repair introduces no binder, assumption or new comparison choice.

## New nodes

`def-pur-chart-unit-affine-comparison` records existing canonical coefficient-unit,
tensor/shift source-normalization, ordered affine comparison and actual smooth
ordinary-dualizing base-change constructions, including their two typing facts, in
`Sheaf.Paper.DiagonalDncChartNormalization`. Its source is the current blueprint
orientation-chart proof Steps 3–4 and the coefficient-unit normalization of
projection-purity-agreement. `chartUnitPullback` is the actual monoidal pullback
unit; Generic is shift cancellation followed by tensor of the specified unit
isomorphism and the left unitor; Raw specializes this to the computed polynomial
tower endpoints; `_existsUnique` pins Source by HEq to that exact raw composite.
`chartCoefficientUnit_finiteTor` is the constant degree-zero rank-one coefficient
complex. `chartGamma` precomposes the existing ordered affine comparison at that
unit by Source inverse. `chartOrdinaryBaseChange` is the actual smooth exceptional
base-change mate conjugated by the ordinary coefficient-unit isomorphisms. No
diagonal-orientation equality is used to define any map. Their full signatures,
bodies and docstrings were read; `lean.statement` is the verbatim `chartGamma`
signature, and all eight full names are in `lean.declarations`.

New-node searches are recorded with their actual results in `mathlib_searches`.
LeanSearch's unit/pullback/shift query gave eight general sheaf-unit or categorical
pullback hits; LeanFinder's canonical-unit/ordered-affine query gave eight scheme
affine-space hits, with no exact match. Mathlib grep of all eight helper-name
patterns returned zero. Upstream WeilConjectures has no exact match; Sheaf contains
these published definitions. DAG grep found their theorem record and the separate
base-change alias owner, but no definition owner for the requested unit/Gamma
suite. `blueprint_refs.py search 'chart unit'` returned zero and `'ordered affine'`
returned three related orientation nodes. Thus this new node reuses exact existing
declarations (`existing:true`) and adds ownership only; it creates no Lean module,
parallel notion, hollow data or additional sorry.

Repair verification: prescribed `scompile.py NL lem-pur-vector-model-chart-descent`
compiled the delivered module both as sandbox and intended library module against
the live server build, clean (11.4 s and 7.3 s). The new existing-definition owner
introduces no file to compile.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
