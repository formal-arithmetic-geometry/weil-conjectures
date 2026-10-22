## Worker report

The delivery states equality of the two specified purity arrows for the affine-space
projection. The main declaration is
`WeilConjectures.PurityFiniteSetting.projection_purity_agreement` in
`Sheaf.Paper.ProjectionPurityAgreement`. The node statement is unchanged. All theorem
proofs are `sorry`; the definitions contain actual constructions or choices from named
existence-and-uniqueness theorems whose equations determine the data uniquely.

### Hypotheses and clauses

* The finite coefficient conventions are the existing `FiniteFieldDatum`, its
  `CoefficientDatum C`, and a finite-dimensional intermediate extension `E` of `C.Qbar`.
  `projectionSetting F C E n` is the existing `PurityFiniteSetting` at level `n + 1`.
  This covers every positive coefficient level. There is no ramification-divisibility
  assumption: the scalar ring is exactly the existing quotient by the `(n + 1)`st
  power of the uniformizer; `Coefficient` is its existing sheaf-universe `ULift`.
* The separated finite-type scheme is `Y : Scheme.{u}` with its structural morphism
  `aY : Y ⟶ Spec (.of F.k)` and `[LocallyOfFiniteType aY] [QuasiCompact aY]
  `[IsSeparated aY]`. Finite type is expressed by its two standard Mathlib properties.
  No Noetherian, dimension-bound, compactification, adjoint or orientation assumption
  is added to the main theorem.
* `d : ℕ` covers every nonnegative dimension. `iteratedAffineLine Y d` and
  `iteratedAffineLineProj Y d` are exactly the coordinate-tower presentation used by
  the recorded `def-pur-affine-space-comparison`. They present the ordered coordinates
  of A^d_Y; rank zero is Y with its identity projection. `projection_smooth` states
  the smooth pure-relative-dimension consequence of the polynomial charts.
* `K : Scheme.proEtaleDerivedCategory Y (projectionSetting F C E n).Ring` is the
  original intrinsic pro-etale object. Its only domain condition is the recorded
  `finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) Y K`. The theorem does not
  ask for a representative, an etale-origin witness, a lower bound, or an extra
  finite-Tor condition on an exceptional image.
* The smooth side is `projectionSmoothIntrinsic ...`: it installs the induced
  k-structures and the geometric instances of the projection, then applies the
  recorded `P.smoothPurityMap`. Its orientation is the existing normalized diagonal
  orientation; its middle map uses the inverse orientation. The underlying source is
  `projectionSmoothSource`, the existing tensor with the unshifted diagonal twist
  followed by `[2d]`; `smoothPurityReassociation` identifies this with tensoring by
  the already shifted diagonal coefficient power.
* The affine side is `projectionAffineIntrinsic ...`. It is uniquely determined by
  the equation in `projectionAffineIntrinsic_existsUnique`, for EVERY lower bound
  and EVERY etale finite-Tor representative of the original K. In each presentation
  its value is the intrinsic realization of `projectionAffineInPresentation`.
  This last definition is `projectionSourceIso.hom ≫ affineSpacePurityComparison ≫
  inv projectionTargetMap`. Thus the existing ordered affine-line comparison is
  actually used; it is not replaced by a new arbitrary isomorphism or by the smooth map.
* The rank-one construction is the recorded `AffineLinePurity.affineLinePurityComparison`:
  its `integration` is ordinary projective-line trace after the open counit,
  its `augmentation` first uses inverse canonical projection and then tensor trace,
  and its `comparisonFromOrigin` is the specified exceptional Hom transpose.
  The existing `affineSpacePurityComparison` starts with `comparisonZero`, the literal
  identity, and applies its ordered successor recursion with canonical source and
  exceptional compositors. The delivery does not change any of these definitions.
* The two existing finite Tate-line presentations use exponents ell^(n + 1) and
  ell^(n + 2). `projectionRootTransition_existsUnique` fixes their comparison on
  every etale test object and every pure tensor by the actual ell-th-power root map,
  using the published `Scheme.IsFiniteTateEtaleTransition`. Applying single, shift
  and exact site pullback to its inverse gives `projectionSingleShiftIso`.
  The coefficient unit and successor tensor constraints, followed by the generic
  ordered tensor recursion, determine `projectionTensorActionIso`. Every endpoint
  transport is uniquely fixed by HEq with a displayed actual construction;
  none refers to either purity arrow. General independence of every annihilating
  exponent and agreement with the named ramification-divisible-level maps are the
  recorded normalization of the dependency constructions and the proof import
  `VectorIntegrationSiteComparison.finiteTypeSiteComparison`.
* The source comparison is the actual shift/tensor reassociation, the root-normalized
  ordered tensor action, and the exact-versus-derived pullback comparison. In rank
  zero it additionally uses the exact identity pullback comparison. The target map
  at positive rank is identity on the common finite exceptional transport. At zero
  it is the ordinary exceptional identity comparison followed by the comparison
  adjunction counit. `projectionTarget_isIso` derives its invertibility on the given
  etale-origin class; invertibility is never an extra hypothesis.
* The conclusion is equality of morphisms, not existence of an isomorphism and not
  equality only up to an unspecified automorphism. Both sides inhabit the displayed
  Hom from Lp* K(d)[2d] to Rp! K in the original intrinsic category. The proof docstring
  follows the node's normalized diagonal, DNC, trace-transpose, projection-compositor
  and ordered-counit route, with the modules of all stated proof dependencies imported.

### Dependency declarations read and used

* `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting` — `WeilConjectures.PurityFiniteSetting`.
* `def-weil-scheme-morphism-properties`: convention collector; the named Mathlib morphism properties are used.
* `def-sbc-affine-space`: existing Mathlib match `{'declaration': 'AlgebraicGeometry.AffineSpace', 'file': 'Mathlib/AlgebraicGeometry/AffineSpace.lean', 'line': 44, 'how': 'specializes in one line: take coordinate type ULift (Fin n). AffineSpace (line 44) is exactly the alternative base-change definition in Stacks 01M0/01LZ; over (line 66) is the first projection. SpecIso (line 228) and SpecIso_inv_over (line 255) give the polynomial spectrum and constants inclusion on affine bases; isPullback_map (line 325) applies to each affine-open inclusion to identify its restriction. The instance at line 442 (AlgebraicGeometry.AffineSpace.instIsIsoSchemeOverInferInstanceOverClassOfIsEmpty) makes the projection an isomorphism for an empty coordinate type, including ULift (Fin 0). No affineness assumption on S is required.'}`.
* `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitudeSites` — `WeilConjectures.finiteTorConstructibleEtale`.
* `def-coefficient-twists-detailed`: `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` — `WeilConjectures.sfQbarTwistingFunctor`.
* `def-weil-exceptional-inverse-image`: `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` — `WeilConjectures.ConstructibleExceptionalCoefficients.System`.
* `def-amb-p1-trace`: `Sheaf.AlgebraicGeometry.ProjectiveLineTrace` — `AlgebraicGeometry.Etale.projectiveLineTrace`.
* `lem-amb-cartier-kummer-map`: `Sheaf.AlgebraicGeometry.CartierKummerMap` — `AlgebraicGeometry.Etale.cartier_kummer_map`.
* `lem-sf-class-compact-support-comparison`: `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison` — `AlgebraicGeometry.ProEtale.compactSupportSiteComparison`.
* `def-exchange-projection`: `Sheaf.Paper.ExchangeProjectionSuppliedDomains` — `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`.
* `def-pur-affine-space-comparison`: `Sheaf.Paper.AffineSpacePurityComparison` — `AlgebraicGeometry.ProEtale.AffineSpacePurity.affineSpacePurityComparison`.
* `def-pur-affine-line-datum`: `Sheaf.Paper.PurityAffineLineDatum` — `WeilConjectures.PurityFiniteSetting.coordinateKummer`.
* `def-pur-affine-line-purity-comparison`: `Sheaf.Paper.AffineLinePurityComparison` — `AlgebraicGeometry.ProEtale.AffineLinePurity.affineLinePurityComparison`.
* `thm-pur-affine-line-purity`: `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace` — `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineLine`.
* `cor-pur-affine-space-purity`: `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace` — `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineSpace`.
* `def-pur-smooth-purity-map`: `Sheaf.Paper.SmoothPurityMap` — `WeilConjectures.PurityFiniteSetting.smoothPurityMap`.
* `lem-pur-diagonal-base-change`: `Sheaf.Paper.PurityDiagonalBaseChangeCompared` — `WeilConjectures.PurityFiniteSetting.comparedDiagonalBaseChange`.
* `thm-pur-dnc-invariance`: `Sheaf.Paper.PurityDncInvariance` — `WeilConjectures.PurityFiniteSetting.Dnc.existsUnique_dncInvariance`.
* `def-pur-section-invariant`: `Sheaf.Paper.PuritySectionInvariantIntrinsic` — `WeilConjectures.PurityFiniteSetting.sectionInvariantFinite`.
* `thm-amb-vector-bundle-purity`: `Sheaf.Targets.VectorBundlePurity` — `AlgebraicGeometry.Etale.vectorBundlePurity`.
* `def-amb-vector-integration`: `Sheaf.AlgebraicGeometry.VectorBundleIntegration` — `AlgebraicGeometry.Etale.vectorBundleIntegration`.
* `thm-sf-ambient-adjoint-class`: `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom` — `AlgebraicGeometry.ProEtale.specifiedExceptionalHomEquiv`.
* `lem-amb-finite-tate-site-descent`: `Sheaf.Paper.FiniteTateSiteDescent` — `AlgebraicGeometry.Scheme.finite_tate_site_descent`.

The finite Tate site-descent node is a statement dependency of the new coefficient
coordinate node because its normalization equations explicitly use the published
transition predicate. The item gains the two coordinate nodes as statement dependencies.
Its statement, source, proof and proof-dependency list remain unchanged.

The added coordinate dependencies are
`Sheaf.Paper.AffineDiagonalTateCoordinates` —
`WeilConjectures.PurityFiniteSetting.projectionLineIso`, and
`Sheaf.Paper.AffineDiagonalTensorCoordinates` —
`WeilConjectures.PurityFiniteSetting.projectionTensorActionIso`.

### Edge cases

* Positive coefficient level one is `n = 0`; it is retained, including ramified
  extensions for which the ramification index does not divide the level. Both selected
  ell-powers annihilate the quotient. No division by the ramification index occurs.
* Rank zero is retained throughout: the tower projection is identity, `comparisonZero`
  is identity, the source comparison uses tensor-unit/zero-shift/identity-pullback
  normalizations, and the target comparison is the canonical exceptional identity map.
  The same normalized morphism is therefore the identity of K.
* Empty schemes and the zero object are allowed. No nonemptiness, nonzero coefficient
  class, or positive-dimension hypothesis occurs. Origin and boundedness arguments
  work in the trivial sheaf category as well, and the identity case remains the zero identity.
* In characteristic two the coefficient prime is still distinct from the base
  characteristic by `CoefficientDatum`. All tensor shifts here are even, preserving
  the prescribed ordered-coordinate sign convention.
* Scheme universe `u` is arbitrary. Coefficients and ModuleCat have exactly the
  existing `u + 1` sheaf convention. No extra universe equality is imposed.

### Searches

The launcher wrapper records the searches in `searches.jsonl`.

* LeanFinder: "Smooth purity for an affine space projection agrees with the ordered
  composite of affine line integration transposes" — eight irrelevant coordinate
  results in Mathlib; no equality of these purity maps.
* Loogle: "smoothPurityMap, affineSpacePurityComparison" — no result (the project
  declaration names are not in Mathlib's search database).
* Mathlib grep: "purity|upperShriek|dualizing", CategoryTheory — only unrelated
  dualizing-category comments, no scheme purity comparison.
* LeanSearch: "Equality of canonical smooth purity and the iterated affine line
  integration comparison" — eight unrelated analysis/affine-map results.
* Source rg in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `smoothPurityMap` and `affineSpacePurityComparison` — the two defining modules
  and downstream uses, no existing agreement statement.
* Additional targeted source reads found the published root transition predicate,
  tensor comparison, exact/derived pullback comparison, identity exceptional
  comparison, and intrinsic realization equivalence. Those interfaces are reused.

No STATEMENT-DISPUTED issue or source correction is asserted. The historical stage-1
repair note is resolved and explicitly requires retaining the current statement.

## Second reading by NI

The dispatcher expressly forbids starting other agents and supplies no lead. This
section records a separate self-review pass, not an independent worker's endorsement.
I reread the node, the dependency signatures and the three completed modules against the
hypothesis/clause table above. The review pays particular attention to coefficient
indexing, actual normalized arrows, the lack of representative hypotheses, the
ordered tower and dimension zero. Final compiler/preflight results are recorded below.

## New nodes

`def-pur-affine-diagonal-tate-coordinates` defines only the missing connection between the
two existing finite Tate presentations, and the normalized degree-zero unit constraint.
Its module is `Sheaf.Paper.AffineDiagonalTateCoordinates`. The inverse root-power map is
realized by single, shift and exact comparison; all endpoint transports are uniquely
fixed by the actual isomorphism. It reuses the existing coefficient and twist objects.

`def-pur-affine-diagonal-tensor-coordinates` defines the missing canonical connection
between the existing diagonal tensor powers and the ordered shifted-line action.
Its module is `Sheaf.Paper.AffineDiagonalTensorCoordinates`. Its actual recursion uses
only the preceding unit/line constraints, comparison monoidality, associator and tensor
functor. It supplies no new tensor structure and uses neither purity arrow.

Both notions come from the source model paragraph's canonical twist identifications.
They are isolated as definition nodes so their nontrivial coefficient specializations
can be checked separately within the unchanged compile limit. Their node records
contain the raw launcher search counts and names: LeanSearch returned ordinary tensor
power results; Loogle and Mathlib grep returned no finite Tate comparison; blueprint
search and source/DAG searches found no such connection already stated. The review
also checked these modules, their normalizations, and their positive-level indices.

The tensor specialization uses the literal fixed-scalar shifted line internally,
then uniquely transports its computed isomorphism to the recorded affine-line ring alias.
Both aliases denote the same positive quotient: `(n + 1) - 1 = n`. This avoids
repeated normalization of derived tensor instances while retaining the exact
recorded endpoint and the same root-power hom. The explicit successor annihilator
is derived from the existing annihilator by multiplication by ell.

The separate review pass checked three implementation pitfalls explicitly. The positive
coefficient level is a successor, so the recorded affine-ring index reduces to the
original quotient rather than imposing ramification divisibility. The rank-zero target
uses the actual comparison counit, whose invertibility is derived only on the stated
etale-origin class. Finally, presentation witnesses remain inside the unique defining
normalization of Gamma and do not become hypotheses of the main equality.

The concrete isomorphism selectors now have explicit cached return types. This is
an elaboration change only: their unique normalization equations and actual data
constructors remain the same. The root transition is shifted and site-realized
directly in its normalization proposition, avoiding a repeated concrete wrapper.

The final tensor bridge checks its composition first at a general coefficient category.
Its endpoint normalizations quantify over all identical presentations of the existing
coefficient ring, root sheaf map, unit and successor maps; HEq fixes both the ring
structure and the displayed maps. The canonical tuple always exists: take the recorded
ring and coefficientCommRing, diagonal powers, actual root transition, and the specified
unit/successor constraints. Thus these universal normalizations are not vacuous and
supply no arbitrary map or additional hypothesis to the agreement theorem. Packaging
the generic tensor composite with its computed endpoints avoids repeatedly comparing
large specialized derived-category instance terms in the kernel.

The source and target coordinate constructors use Q.Coefficient consistently internally;
the source endpoint theorem then transports to the existing orderedSource alias. Both
coefficient presentations are still the same prescribed quotient and lift. This avoids
normalizing the affine-ring alias during composition of actual morphisms; it does not
change either canonical source map or target comparison.

## Validation

The final three-file scompile.py run passed on 2026-10-22 with no errors or unexpected
warnings. Every delivered file was compiled separately against the published live build,
including its actual module name: AffineDiagonalTateCoordinates (10.9 s),
AffineDiagonalTensorCoordinates (8.8 s), and ProjectionPurityAgreement (23.1 s).
No timeout or heartbeat setting was raised in any delivered file. Diagnostic scratch
probes are outside lean/ and are not part of the delivery.

The first delivery dry run found only two blueprint provenance-path errors. Both new
nodes now use the empty via path required for derivation directly from this native
blueprint item; their ancestor remains lem-pur-projection-purity-agreement.

Final required dry run: OK on 2026-10-22. The server preflight and all per-file
compiles passed (dry-run commit 023970183e9); delivery repeats those checks.
