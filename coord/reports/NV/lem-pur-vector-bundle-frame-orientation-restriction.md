## Worker report

Item: lem-pur-vector-bundle-frame-orientation-restriction. Group: NV. Stage: 2.
Date: 2026-10-24.

The new module is `Sheaf.Paper.VectorBundleFrameOrientationRestriction`.
Its main declaration is
`WeilConjectures.PurityFiniteSetting.vectorBundle_frame_orientation_restriction`.
All supporting declarations are in the nested `FrameOrientation` namespace and
listed in `lean.declarations`. They specify the maps and the conclusion of this
same node, rather than introduce a second notion of purity or vector bundle.
The repaired item changes only `lean` and the added `stmt_deps`. Three new
existing-declaration definition nodes record previously missing ownership.
There are no dependency-module repairs, mathematical statement corrections,
or statement disputes. See the point-by-point repair section below.

The source read was the current blueprint under `literature/blueprint/latest/`,
`blueprint/sec-smooth-purity/sk-prop-sp-orientation/`:
`sk-prop-sp-orientation-vector-bundle.md` and its `.proof.md`, especially Step 3.
The DAG's seven-step proof provides the detailed frame-refinement bookkeeping.

### Hypotheses and objects

- The fixed algebraic closure of a finite field, coefficient prime distinct from
  its characteristic, finite coefficient level, and the coefficient realizations
  are the existing `P : PurityFiniteSetting.{u}`. Its `level_pos` excludes level
  zero. The hypothesis `_hE : P.extension = ⊥` specializes the finite extension
  inside the fixed algebraic closure of Q_l to Q_l itself. Thus the existing
  coefficient ring `P.Coefficient` is the convention's realization of
  Z/l^n Z, with its existing universe lift. We do not substitute an arbitrary
  coefficient category or add a ramification hypothesis.
- `S : Scheme.{u}`, `aS : S ⟶ Spec (.of P.field.k)`,
  `[LocallyOfFiniteType aS] [QuasiCompact aS]` mean finite type over k.
  There is no `[IsSeparated aS]` hypothesis. Noetherianity and the relative
  geometry of the bundle are obtained from the recorded dependencies.
- `d : ℕ`, `F : S.Modules`, and `[F.IsFiniteLocallyFreeOfRank d]` specify the
  rank-d vector bundle, using `VectorBundleZeroSection.scheme`, `.π`, and
  `.zero`. The `bundleSmooth` instance only repackages the smoothness supplied
  by `VectorBundleZeroSection.finite_type_frames`; it adds no premise.
- `U : S.affineOpens` is an arbitrary affine open. It is automatically finite
  type over k because S is Noetherian finite type. The universal quantifier over
  `e : VectorBundleZeroSection.Trivialization S d F U.1` is the chosen linear
  frame. It does not require the bundle to be trivial on every affine open:
  the assertion applies to every frame wherever a frame is supplied.
- The affine model is the existing `affineTraceTower U.1.toScheme d`, identified
  with Mathlib's `AffineSpace (ULift (Fin d)) U.1.toScheme` by the canonical
  `affineTraceAffineSpaceIso`. The ordered tower is needed to name the actual
  ordered affine integration map. This transports the specified affine space;
  it does not replace it by an arbitrary isomorphic object.
- `Etale.vectorIntegrationChart S d F U.1 e` is the inverse-frame map from
  this affine model into the global bundle. Pulling directly along this map
  combines Lj* and transport along phi; thus the written formulas live in the
  derived category on X, as in the node.

### Maps and clauses of the conclusion

- `orientation` is exactly `P.diagonalDualizingObject d π aS`, and its exceptional
  source is the published `P.diagonalDualizing π`. No integration adjunct occurs
  in this definition.
- `adjunctEtale` is the adjunction transpose of the actual
  `Etale.vectorBundleIntegration`, at the coefficient unit, preceded by the
  inverse canonical Tate-pullback identification. `adjunct` applies the fixed
  comparison pullback and the inverse `P.diagonalDualizingComparison`. This is
  the actual pro-etale P_pi; it is not defined to be inverse orientation.
- `rho` composes the canonical exceptional site comparison, the canonical
  pullback/site comparison, the ordinary exceptional base-change isomorphism,
  and the inverse site comparison on the new source. `frameRho` specializes it
  to the Cartesian inverse-frame chart over U. Its direction is the node's
  Lj* omega_pi -> omega_p, with the frame transport already included.
- `frameTate` uses `OrientationRefinement.tate` for the same chart. This is the
  specified Tate restriction including the frame identification, rather than
  a newly chosen isomorphism.
- `P.chartDiagonalAlpha` and `P.chartDiagonalDelta` are the existing diagonal
  base-change and normalized DNC factors. The former already contains the
  canonical inverse derived pullback compositor for p2 Delta = id. We retain
  that exact map rather than an independent identification of its endpoints.
- `normalBeta` constructs the third factor from actual integration. For the
  diagonal z, use the canonical conormal sheaf
  `ConormalGradedAlgebra.piece z 1`, the canonical normal-cone/bundle model from
  `chartNormal_model_exists`, and canonical section exchange. On this bundle
  `OrientationRefinement.vectorBetaInverse` is the actual integration adjunct
  pulled along zero with its Tate restriction. `zeroAdjunct_isIso` records its
  invertibility. `normalBeta` takes its inverse and transports back by section
  exchange and `Dnc.normalComparison`. Thus it is precisely the normal-bundle
  inverse-integration factor, independently of `chartDiagonalBeta` and of any
  diagonal/integration agreement theorem. Its data are specified constructions,
  not an arbitrary map chosen from an existence assertion.
- `affineAssembly` is alpha.inv followed by delta.hom followed by
  `normalBeta.hom`. Its local `[IsSeparated aB]` is discharged automatically
  on affine U; it imposes no separatedness condition on the global base S.
- `affineAdjunct` is the comparison image of `P.diagonalAffineMate` using the
  actual projective-line trace transport and trace datum. The fixed target
  comparison identifies it with the actual P_p on the affine coordinate model.
- The first conjunct of `Equations` reads
  `frameOrientation ... = affineAssembly ...`.
  `frameOrientation` is `frameRho.inv` followed by the pulled-back global
  orientation and then `frameTate.hom`. In ordinary right-to-left notation this
  is exactly tau o Lj* theta_pi o rho^{-1} = beta o delta o alpha^{-1}.
- The second conjunct reads `frameAdjunct ... = affineAdjunct ...`.
  `frameAdjunct` is `frameTate.inv` followed by the pulled-back actual adjunct
  and then `frameRho.hom`: exactly rho o Lj* P_pi o tau^{-1} = P_p.
- `frameMap` is the actual coordinate transition between two frames on nested
  opens U' <= U. It is formed from the affine-space/tower isomorphisms,
  inverse smaller frame, the actual inverse-image open inclusion, and the
  larger frame. With U'=U it is an arbitrary linear frame change; with a
  restricted frame it is the further target-open restriction.
- `PairGeometry` specifies the resulting self-product and normal maps. Both
  product projections and the diagonal are required to commute. Its normal
  map is constrained by equality with the coefficientwise
  `SectionReesBaseChange.pairMap` after the canonical normal closed-fibre
  immersion. Consequently its existential witness cannot be a free normal
  automorphism. The Cartesian and zero-section equations are recorded too.
- `sourceExchange` and `normalExchange` use the canonical pullback/site and
  section comparisons for those specified geometric maps.
- `Factors` states three separate morphism equalities: alpha commutes with
  source and exceptional exchange; delta commutes with source and normal
  exchange; beta commutes with normal exchange and the specified Tate
  transport. These are individual factor equations, not just an equality
  of the assembled composite. They apply also to linear changes of frame.
- `Compatible` quantifies over arbitrary frames e and e' on U and U'. It
  asserts the actual transition square is Cartesian and that its composite
  into V equals the smaller inverse-frame chart. It then requires `Factors`
  and the two actual transported-map equalities for `frameOrientation` and
  `frameAdjunct`, under the canonical rho and Tate arrows. Together with
  `Equations` these express commutation of both displayed formulas, including
  their right sides, under restrictions and changes of frame.
- `Conclusion` includes `Equations` on every affine open, `Compatible` for
  every nested pair, and the overlap assertion. For any U1,U2 the supremum
  of all affine W contained in their intersection is that intersection.
  For every such W, compatibility with each frame chart is asserted. There
  is no assumption that the intersection itself is affine. Further affine
  refinements are covered by the same universal compatibility assertion.
- No hypothesis or definition equates theta_pi and inverse P_pi. In particular
  the normal beta and the actual integration formulas are defined independently
  of the diagonal orientation and of the desired final purity agreement.

### Dependency declarations

These are the recorded statement dependencies, with the concrete declarations
used directly or through their canonical fixed-coefficient interfaces:

| Node | Module | Declarations |
| --- | --- | --- |
| def-pur-conventions | Sheaf.Paper.PurityFiniteSetting | WeilConjectures.PurityFiniteSetting, its field/extension/level/coefficient data and noetherian |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType | AlgebraicGeometry.LocallyOfFiniteType, QuasiCompact |
| def-asd-vector-bundle-zero-section | Sheaf.AlgebraicGeometry.VectorBundleZeroSection | AlgebraicGeometry.VectorBundleZeroSection.scheme, π, zero, Trivialization, trivializationMap |
| def-weil-derived-pullback-tensor-hom | Sheaf.Paper.DerivedPullbackTensorHom | commonStageDerivedInternalHom_existsUnique (recorded general interface); ProEtale.upperStar.leftDerivedFunctor and its fixed-ring comparison interfaces used here |
| def-weil-exceptional-inverse-image | Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | WeilConjectures.ConstructibleExceptionalCoefficients.System; finite exceptional inverse image via P.diagonalDualizing |
| def-coefficient-twists-detailed | Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | sfQbarTwistingFunctor (recorded general interface); P.diagonalTwist, diagonalTwistEtale, diagonalExponent at the existing finite presentation |
| thm-pur-diagonal-dualizing-object | Sheaf.Paper.PurityDiagonalDualizingObject | existsUnique_diagonalDualizingObject, diagonalDualizingObject, diagonalDualizingComparison, diagonalAffineMate |
| def-amb-vector-integration | Sheaf.AlgebraicGeometry.VectorBundleIntegration | AlgebraicGeometry.Etale.vectorBundleIntegration, vectorIntegrationChart, vectorIntegrationBaseCoefficientPullback |
| lem-pur-vector-integration-site-comparison | Sheaf.Paper.VectorIntegrationSiteComparison | AlgebraicGeometry.ProEtale.VectorIntegrationSite.finiteTypeSiteComparison |
| cor-pur-vector-bundle-purity | Sheaf.Paper.VectorBundlePurity | WeilConjectures.PurityFiniteSetting.vectorBundlePurity |
| def-sbc-affine-space | Mathlib.AlgebraicGeometry.AffineSpace | AlgebraicGeometry.AffineSpace, transported by affineTraceAffineSpaceIso |
| def-pur-normal-bundle | Sheaf.Paper.PurityNormalProjection | AlgebraicGeometry.Scheme.Hom.purityNormalProjection, normalConeProj, purityNormalProjection_eq |
| def-pur-section-invariant | Sheaf.Paper.PuritySectionInvariantIntrinsic | WeilConjectures.PurityFiniteSetting.sectionInvariantFinite; Dnc.sourceSection, normalSection and their comparison isomorphisms |
| lem-pur-diagonal-base-change | Sheaf.Paper.PurityDiagonalBaseChangeCompared | comparedDiagonalBaseChange, diagonalComparedRestriction |
| thm-pur-dnc-invariance | Sheaf.Paper.PurityDncInvariance | WeilConjectures.PurityFiniteSetting.Dnc.existsUnique_dncInvariance |
| lem-pur-projection-purity-agreement | Sheaf.Paper.ProjectionPurityAgreement | WeilConjectures.PurityFiniteSetting.projection_purity_agreement |

Additional recorded proof dependencies provide the concrete chart interfaces:

- `Sheaf.AlgebraicGeometry.VectorBundleFiniteTypeFrames`:
  `AlgebraicGeometry.VectorBundleZeroSection.finite_type_frames`.
- `Sheaf.Paper.AffineTargetDiagonalDnc`: `affineTargetDiagonalDnc`.
- `Sheaf.Paper.DiagonalDncChartNormalization`:
  `diagonal_dnc_chart_normalization`, `chartDiagonalAlpha`, `chartDiagonalDelta`,
  `chartOrdinaryBaseChange`, and the canonical normal model and affine tower.
- `Sheaf.Paper.DiagonalOrientationRefinement`:
  `diagonalOrientationRefinement`, `OrientationRefinement.vectorBetaInverse`,
  `pull`, `tate`, `sectionExchange`, and `inclusion`.
- `Mathlib.CategoryTheory.Adjunction.Mates`:
  `CategoryTheory.mateEquiv_vcomp`, `mateEquiv_hcomp`, and conjugate equations.
- `Sheaf.Paper.IntegralFinitePullbackComposition`:
  `integralTowerGeneralPullbackComposition`; its finite pullback compositor is
  the canonical one used by the chart alpha interface.
- `Sheaf.Paper.CartesianCoefficientTwists`: `ProEtale.spTwists_cartesian`.
- `Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance`:
  `Etale.affineSpaceLinearTraceInvariance`.
- `Sheaf.Paper.TraceTransposeBaseChange`:
  `ProEtale.purityTraceTranspose_baseChange` (used only on separated charts).
- `Sheaf.Paper.BoundedSiteExchangeTransposes`: `boundedSiteExchangeTransposes`.
- `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`:
  `ProEtale.IsCohomologicallySmoothFiniteCompared`.

All these sources and their recorded signatures/docstrings were read. Public
imports expose dependencies used in the statement; plain imports retain proof
interfaces not needed as public signature dependencies. No competing private
copy of a bundle, exceptional inverse image, twist, DNC map, or orientation is
introduced. The repaired dependency list additionally cites the published
integration-charts and diagonal-chart-data definition nodes, the bundle-frame
geometry theorem, the coefficientwise Rees map definition owner, and the other new
existing-declaration definition owners listed below.

### Edge cases

- Rank zero is included: d is an unrestricted natural number. The tower,
  normal-model, integration and frame constructions all have their published
  zero-rank cases. There is no positive-rank premise or division by rank.
- The empty affine open is included. No frame construction uses a point or
  assumes the base ring is nonzero. The corresponding derived zero-category
  equations are the unique morphism equations.
- The base S can be nonseparated: no global absolute separatedness is supplied
  or inferred. The bundle morphism is separated, and DNC statements occur over
  the affine charts where absolute separatedness is available.
- Frame changes include d=1 with multiplication by -1 and a rank-two shear.
  `frameMap` allows all linear trivializations, not just determinant-one or
  constant matrices. `PairGeometry.normal_eq` forces their induced normal
  map, and `Factors` retains the corresponding integration-normalized beta.
- The identity refinement and unrelated frames on the same open are both
  instances of `Compatible` with U'=U. Arbitrarily small affine refinements
  of nonaffine overlaps are included, without an affine-intersection premise.
- Level n=1 and coefficient prime 2 are allowed; only the conventions'
  prime/characteristic condition and positive level remain.

These are checks of the statement's domain and named constructions; they are
not new Lean proofs. The only postponed proofs are `zeroAdjunct_isIso` and
`vectorBundle_frame_orientation_restriction`, both listed in this node's Lean
record and both with source and complete natural-language proofs in docstrings.
Definitions contain no sorry data and choose no arbitrary map. The canonical
normal model is already uniquely specified by the normalized Rees comparison
in its owning dependency.

### Searches and validation

- `msearch.py` / LeanFinder: "Restriction of diagonal DNC orientation and actual
  vector bundle integration adjunct to a linear affine frame". Eight hits were
  topological/manifold frame results; none stated these algebraic derived maps.
- `msearch.py` / Loogle:
  "AlgebraicGeometry.Etale.vectorBundleIntegration, diagonalDualizingObject".
  No result; the project-specific identifier is not a Mathlib Loogle symbol.
- `msearch.py` / Mathlib grep:
  "diagonalDualizingObject|vectorBundleIntegration|DncInvariance" in
  `AlgebraicGeometry`. No matches.
- `msearch.py` / LeanSearch: "Vector bundle integration adjunct and diagonal
  deformation orientation commute with restriction to an affine linear frame".
  Eight unrelated manifold/vector-bundle hits; none gave this statement.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the item id, `frameOrientation`, and
  `frame_orientation`: no existing declaration of this item.
- Broader source searches for frame/orientation/restriction led to the existing
  diagonal chart normalization, orientation refinement and vector integration
  chart comparison modules, whose full interfaces were read. The chart
  comparison theorem requires a separated base and states comparison with the
  ordered affine Gamma map; it does not assert this node's simultaneous
  diagonal-factor and actual-adjunct restrictions on possibly nonseparated S.
  It cannot serve as an existing exact declaration for the item.
- Mathlib affine-space, pullback and adjunction declarations were inspected in
  their source. The project interfaces above supply the actual canonical maps;
  no new Lean construction was needed. The repair adds definition ownership
  nodes for existing canonical constructions as requested by the review.
- Server compilation through `scompile.py NV
  lem-pur-vector-bundle-frame-orientation-restriction` succeeded for the full
  module with no errors and no warnings beyond permitted sorry warnings.
  The prescribed delivery dry-run recompiles the final module, including its
  explicit Mathlib mate-pasting import, and checks the node record and report.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and
the maintainer's independent review is the only review. I reread the statement
against the node after compilation, specifically checking the independent
normal integration beta, the three separate factor equations, transported-map
compatibility rather than repeated formulas, and nonaffine overlaps.


## Repair of returned delivery cc21555125b2

The immutable-head review accepted the mathematics, including both equations,
the independent integration-normalized beta, all three pinned factor equations,
frame changes, nonaffine overlaps, empty charts, rank zero, and nonseparated S.
This repair addresses every ownership and statement-dependency finding. The
mathematical Lean declarations and their signatures and docstrings are unchanged;
the module additionally imports the integration-charts and Rees-map owner modules
publicly. The prescribed delivery wrapper refreshes the current server main and
builds this packet on that main, rather than stacking on the returned head.
The sandbox item was compared against the current read clone before applying the
repair; the updated copy retains all current node fields apart from the authorized
Lean record and added statement dependencies.

1. Added `def-pur-diagonal-dnc-chart-data` to the item's `stmt_deps`. It is the
   existing definition owner of `chartDiagonalAlpha`, `chartNormal_model_exists`,
   `chartNormalModel`, and `chartDiagonalNormalBundle`. Its record and full
   statement were read and are not changed.
2. Added `def-amb-vector-integration-charts` to the item's `stmt_deps`. It owns
   `vectorIntegrationChart`, `vectorIntegrationChart_isPullback`,
   `vectorIntegrationBaseCoefficientPullback`, and `vectorIntegration_geometry`.
   Its published module is now an explicit public import; no copy is introduced.
3. Added and cited `def-pur-diagonal-chart-transports`, an `existing: true`
   definition node owning `chartDiagonalDelta`, `chartOrdinaryBaseChange`, and
   the supporting typing fact `chartTraceProjection_smooth`. The existing
   chart-data node remains intact. The new node's statement gives the exact
   normalized DNC choice, ordinary inverse-compact-support mate with coefficient
   unit comparisons, and smoothness of the published ordered affine tower.
   It does not cite the chart-normalization theorem as a statement dependency.
4. Added and cited `def-pur-orientation-refinement-comparisons`, an
   `existing: true` definition node owning exactly `OrientationRefinement.pull`,
   `tate`, `vectorBetaInverse`, `sectionExchange`, and `inclusion`. Its statement
   spells out each existing construction and its hypotheses, including the
   actual integration transpose and the coefficient-unit comparison at zero.
   The compatibility theorem `diagonalOrientationRefinement` remains only a
   proof dependency, and its module is not duplicated or altered.
5. Added `lem-pur-vector-bundle-finite-type-frames` to `stmt_deps`. This now
   records the exact theorem used by the `bundleSmooth` instance term to type
   the global orientation. No extra smoothness assumption has been introduced.
6. In the first repair, added `lem-trf-section-rees-base-change-etale` to `stmt_deps`.
   This was superseded by the second return and the definition owner below. Its declaration
   list owns `AlgebraicGeometry.SectionReesBaseChange.pairMap`, which pins the
   normal map in `PairGeometry.normal_eq`. The module is an explicit public
   import. The new normal map is not arbitrary and the formula is unchanged.
7. `lem-pur-conormal-graded-algebra-basic` is already an immediate statement
   dependency of the now-cited `def-pur-diagonal-dnc-chart-data`. A recursive
   statement-dependency traversal verified its presence in the item's closure.
   Consequently no redundant separate item edge or owner repair is needed.

## New nodes

`def-pur-section-rees-pair-map`: added in the second repair, this `existing:true`
record owns only `AlgebraicGeometry.SectionReesBaseChange.pairMap` in its
unchanged published module. Its complete statement and source describe the
coefficientwise extended-Rees map for arbitrary commuting squares of closed
immersions. It cites the ideal-containment conclusion of
`lem-weil-pbc-closed-immersion-conormal-functorial` and uses no conormal-module
map or Rees base-change theorem. Its primary signature is copied verbatim.
Actual LeanSearch, LeanFinder, Mathlib grep, project/DAG grep and blueprint
searches are recorded in the node and in the second repair section below.
The empty and identity-square cases remain included. There is no new Lean file.

`def-pur-diagonal-chart-transports`: this definition node records the already
published `Sheaf.Paper.DiagonalDncChartNormalization` constructions
`chartDiagonalDelta`, `chartOrdinaryBaseChange`, and their affine-projection
smoothness typing fact. The source is current blueprint vector-bundle proof
Step 3, specifically the first two diagonal-orientation arrows and their frame
restriction. The DNC factor is the uniquely normalized one; the ordinary exchange
retains the actual mate and coefficient-unit maps. Its signature is copied
verbatim from `chartOrdinaryBaseChange`. Its statement separately includes the
absolute separatedness needed only for the DNC domain, and permits arbitrary
Cartesian base change in the smooth ordinary exchange. Empty bases and dimension
zero remain in scope. All declarations stay in the existing module, so the
record is `existing: true` and there is no new Lean module.

`def-pur-orientation-refinement-comparisons`: this definition node records the
five already published constructions in `Sheaf.Paper.DiagonalOrientationRefinement`
requested by point 4. The source is current blueprint vector-bundle proof Step 3,
with the actual zero-section integration normalization of Steps 1 and 2. Its
signature is copied verbatim from `OrientationRefinement.tate`. The statement
names the actual pro-etale pullback, canonical Tate transport, ordinary actual
integration adjunct pulled along zero with its coefficient-unit map, section
exchange for a smooth Cartesian square and compatible sections, and actual
inverse-image open inclusion. It assumes neither a diagonal-purity agreement
nor absolute separatedness of a global base. Again it is `existing: true` and
creates no Lean declaration.

Before creating these nodes, the full DAG was scanned for definition-node owners
of all requested names; only theorem-node declaration lists contained them.
`tools/blueprint_refs.py ancestor` gives `det-sp-orientation-vector-bundle` for
this item; both new records use that ancestor and `via` equal to this item.
Blueprint searches for "diagonal chart" and "orientation refinement" returned
zero matching blueprint nodes. Source searches in `lean/WeilConjectures` and
`lean/Sheaf` located the existing declarations only in the published modules.
Each new node records actual logged searches from LeanSearch, LeanFinder and
Mathlib grep, including the wrapper's hit counts and names. The chart queries
returned smooth/base-change or scheme-normalization results, while the
refinement queries returned generic module-pullback or topological bundle
results; none was an exact Mathlib match. Both exact-name Mathlib greps returned
zero hits. These searches establish that a new object is unnecessary while the
missing definition ownership does need the two records.

The previous second-reading section describes only the worker's own rereading.
No second agent was started for the repair. The maintainer's independent review
remains the independent reading. Compile and dry-run are rerun on this repaired
packet, including server checks of every `existing: true` declaration.

Repair validation: the final item module passed `scompile.py` with no errors or
unexpected warnings (sandbox 36.5 s including server setup, library 8.3 s).
The dry-run also checks all eight existing declarations in the two ownership
records through a separate server compilation probe.


## Repair of returned delivery 586c0a0389be

The second independent immutable-head review reconfirmed the Lean mathematics
and all previous repairs except one statement-dependency ownership distinction.
The final Lean module, its imports, signatures, docstrings and proof placeholders
are byte-identical to the returned delivery. This repair changes node metadata
and the report; it introduces no Lean construction.

1. Replaced the item's statement dependency
   `lem-trf-section-rees-base-change-etale` with the new existing-declaration
   definition node `def-pur-section-rees-pair-map`. The former theorem is not
   used to type or state the item and is no longer cited for its helper def.
   The new node owns exactly `AlgebraicGeometry.SectionReesBaseChange.pairMap`
   in the unchanged module `Sheaf.Paper.SectionReesBaseChangeEtale`.
   Its `stmt_deps` explicitly include
   `lem-weil-pbc-closed-immersion-conormal-functorial`: the actual definition
   uses the `.1` ideal-containment conclusion to construct the upstream
   `Scheme.IdealSheafData.deformationSpaceMap`. The `.2` module/conormal map
   conclusion and the helper `conormalMap` are not used. The new statement
   spells out the same affine coefficient map r -> h#r, t -> t,
   a/t -> h#a/t and its gluing, with exactly the general commuting-square
   hypotheses of the published signature. It adds no smoothness, Noetherian,
   Cartesian, section or dimension assumption.
2. Retained `lem-pur-vector-bundle-finite-type-frames` as a statement dependency:
   the review explicitly confirms its smoothness conclusion genuinely types
   the orientation. The other earlier owner and dependency repairs are retained.
3. Checked the current live server DAG by a read-only scan before changing the
   packet. `def-pur-diagonal-dnc-integration-comparisons` from Q138 is ABSENT;
   our `def-pur-diagonal-chart-transports` and
   `def-pur-orientation-refinement-comparisons` are also not yet landed. Thus
   the earlier reviewed records remain part of this packet. The live scan
   likewise found no definition-node owner of `SectionReesBaseChange.pairMap`.
   The delivery wrapper will refresh main and build a new commit on that base.

Additional new node: `def-pur-section-rees-pair-map` (listed in New nodes above).
This existing:true definition record owns the published coefficientwise map of
Rees spaces for arbitrary commuting closed centres. Its source is the current
vector-bundle proof Step 2, x=tu under linear frame changes, and Step 3's
restriction of the diagonal DNC assembly. Its role is the exact map used in
`PairGeometry.normal_eq`, fixing the induced normal map by its closed-fibre
composite. The new record's signature is verbatim from the published def;
its dependencies name schemes, closed immersions, their ideal sheaves, affine
spectrum and the specific ideal-containment theorem. It has no file field and
adds no copied or moved module. Its statement includes all arbitrary squares,
including empty schemes and identities, and asserts no base-change theorem.

Searches for this new owner were performed with `msearch.py`: LeanSearch for
"Canonical extended Rees deformation space map induced by a commuting square of
closed immersions" returned eight general image/closed-immersion/ideal-sheaf
results; LeanFinder for "Canonical coefficientwise map of extended Rees
deformation spaces for a commuting square of closed immersions" returned eight
general ideal-sheaf and closed-immersion results; Mathlib grep for
`deformationSpaceMap|SectionReesBaseChange|pairMap` returned zero hits. Full
logged results are copied into the new node. Source grep located the exact
existing def and upstream map, while a DAG scan found only a theorem owner;
`blueprint_refs.py search "Rees pair"` returned zero blueprint matches and the
ancestor remains `det-sp-orientation-vector-bundle`. This warrants a definition
ownership record for the existing map, rather than any duplicate construction.

All three existing-declaration ownership records are included in the delivery
check probe. The unchanged item module is recompiled through `scompile.py`, and
the prescribed dry-run/preflight and delivery are rerun on the repaired packet.
