## Worker report

Delivered statement module: `Sheaf.Paper.AffineDiagonalIntegrationOrientation`.
The main theorem is `WeilConjectures.PurityFiniteSetting.affineDiagonalIntegrationOrientation`.
The same node's additional clauses are named `affineDiagonalIntegration_translation`,
`affineDiagonalIntegration_exponent`, and `affineDiagonalIntegration_zero`.
Every theorem has `sorry`; definitions contain actual constructions. The helper
statements and their complete mathematical proof plans belong to this node and
are listed in `lean.declarations`.

Source read: the current main-20261015 projection-purity-agreement proof, especially
its paragraph identifying the diagonal normal bundle and the normalized standard
DNC family, together with this node's expanded eight-step proof. The Q100 delivery
was a stage-1 split of this node, not a Lean statement; the earlier worker's claim
that this prevented a stage-2 delivery does not apply to the live node.

Hypotheses and objects, clause by clause:

* `P : PurityFiniteSetting.{u}` is the recorded finite coefficient setting, retaining
  the algebraic closure of the finite field, the prime different from the
  characteristic, the finite intermediate extension of Q_ell, and every positive
  quotient level. `P.Coefficient` is the standard size lift of the actual quotient,
  not a new coefficient ring. No ramification-divisibility hypothesis is imposed.
* `Y`, `aY`, `[IsSeparated aY]`, `[LocallyOfFiniteType aY]`, and `[QuasiCompact aY]`
  express precisely separated finite type over the fixed field. No smoothness,
  affineness, nonemptiness, connectedness, or reducedness of Y is assumed.
* `affineDiagonalSpace` and `affineDiagonalProjection` reuse the ordered affine
  trace tower. Its published `affineTraceAffineSpaceIso` is the canonical
  coordinate-preserving isomorphism to `AffineSpace (ULift (Fin d)) Y`. At d=0
  the tower and projection are literally Y and its identity.
* `p`, `W`, `p₁`, `p₂`, and `s` in `AffineDiagonalIntegrationConclusion` are the
  affine projection, its actual self-pullback, the two pullback projections, and
  `pullback.diagonal p`. `aX` is `p ≫ aY`. Smoothness and compactifiability used
  to type the functors are derived locally, not additional theorem hypotheses.
* The coefficient object `L T d` is the published ordered tensor of shifted
  finite root lines `affineLinearBaseCoefficient`. Its finite-etale presentation
  is taken to the actual small pro-etale derived category by `C`, the recorded
  comparison inverse image on derived categories. `affineDiagonalTateRestriction`
  uses `vectorIntegrationBaseCoefficientPullback`, normalized on pure root tensors.
* `affineDiagonalPresentedTranspose` is the actual ordered counit trace,
  preceded by the inverse compact-support comparison and transposed through the
  published exceptional adjunction. A coordinate isomorphism is transported by
  pullback composition and `dualizingComplexBaseChangeMap`. The unit-input inverse
  projection and unit identifications reduce the specified `(1 tensor t) Pi` to
  this very trace, by projection-formula coefficient coherence. Thus no arbitrary
  dualizing isomorphism is substituted for integration-transposed purity.
* `I`, `J`, and `Q` are existential isomorphisms whose hom maps are constrained
  by equality to this explicit transpose for p, p₁, and πN. Their invertibility
  is asserted, rather than assumed. The existential notation introduces no
  freedom in their maps or inverses.
* `affineDiagonalDifferences` is literally y_i-x_i. Its unique ideal-power lift
  is justified by the named ideal-membership theorem, and
  `affineDiagonalNormalFunction` uses its actual degree-one homogeneous class.
  `affineDiagonalNormalCoordinates` uses these functions on the actual
  extended-Rees normal cone through a homogeneous-normalized Rees comparison q.
  The conclusion is universal in q and its normalization, whose existence is
  already published; this is not a new normal bundle or an arbitrary orientation.
  The normal-coordinate theorem states isomorphy and the projection equation.
  The Rees homogeneous normalization sends these functions to u_i/t, giving
  u_i=t v_i in exactly the displayed order and sign.
* `πN` and `z` are `normalConeProj p₁ s` and `s.normalConeZeroSection`. This is
  the same normal bundle as the recorded normal-projection definition for a
  smooth section, in its extended-Rees presentation.
* `B` is exactly `dualizingComplexBaseChangeMap` for the flipped self-pullback
  square. Its pro-etale image is the canonical counit-transposed B in the
  recorded finite comparison interface for cohomological smoothness.
* `α` is `Dnc.sourceComparison` followed by the comparison image of
  `diagonalComparedRestriction p (asIso B)`. That recorded declaration first
  pulls back B inverse and then uses the diagonal/p₂ composition identity.
* `δ` is selected only from `Dnc.existsUnique_dncInvariance`, which uniquely
  specifies the normalized actual pro-etale DNC arrow. Its normalization and
  arbitrary-base-change equations are retained in that declaration; no bare
  existence of an isomorphism is used as data.
* `T` is the comparison image of the diagonal pullback of J, preceded by the
  inverse Tate restriction and followed by inverse `Dnc.sourceComparison`.
  It is precisely the node's `LΔ* J` with the specified identifications inserted.
* `β` is `Dnc.normalComparison` followed by the comparison image of the
  zero-section pullback of Q inverse and the canonical Tate restriction.
* The four displayed equalities are respectively
  `(C W).map J.hom = (C W).map (TateRestriction.inv ≫ F(p₂).map I.hom ≫ B)`,
  `T.hom ≫ α.hom = (C X).map I.hom`,
  `δ.hom ≫ β.hom = T.inv`, and
  `α.inv ≫ δ.hom ≫ β.hom = (C X).map I.inv`.
  Lean's composition order is left-to-right. All are equalities of morphisms,
  not merely assertions that endpoints are isomorphic.
* `affineDiagonalTranslatedCoordinates` is the y-coordinate chart followed by
  `ambientAffineTranslation` at the tautological x vector. Its specification
  includes the actual coordinate equation h* u_i=y_i-x_i, isomorphy over X,
  and the diagonal-to-zero equation. `affineDiagonalIntegration_translation`
  equates the actual integration maps in the two presentations and separately
  equates their exceptional transposes. The transpose's transport uses the
  canonical dualizing mate, and the integration is its inverse adjunction
  image, so the same compact-support identifications are used in both equations.
* `r` and `hA` allow every positive annihilating ell-power. This introduces no
  restriction on P: the recorded positive coefficient twist supplies a valid
  exponent at every positive quotient level. `affineDiagonalIntegration_exponent`
  explicitly compares any ordered pair of annihilators. Its root map is fixed
  by its monic inclusion in G_m, its line comparison is fixed on every pure
  tensor, and `affineDiagonalPowerComparison` tensors it in coordinate order.
  Both the integration and transpose commute with this comparison. Two arbitrary
  exponents are compared through their maximum. The same assertion applies to
  p, p₁, and πN with the coordinate presentations already displayed.
* `affineDiagonalIntegration_zero` identifies the rank-zero integration with
  `rightDerivedLowerShriekIdIso` and the transpose with the inverse of
  `dualizingComplexIdIso`. Together with the zero-coordinate identity charts,
  normalized DNC identity, and the four equations, this gives exactly the
  stated identity specialization. No nonempty-base hypothesis is present.

Dependency declarations used (all recorded modules are imported):

| Node | Module and declaration/interface |
| --- | --- |
| def-pur-conventions | `Sheaf.Paper.PurityFiniteSetting`, `WeilConjectures.PurityFiniteSetting` |
| def-weil-scheme-morphism-properties | convention node; standard scheme morphism classes |
| def-sbc-affine-space | `Mathlib.AlgebraicGeometry.AffineSpace`, `AlgebraicGeometry.AffineSpace`; tower comparison from `Sheaf.AlgebraicGeometry.AffineTraceTower` |
| def-weil-derived-pullback-tensor-hom | `Sheaf.Paper.DerivedPullbackTensorHom`; actual derived inverse-image and tensor interfaces reexported by the dependencies |
| def-coefficient-twists-detailed | `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`; same node's `Sheaf.Paper.FixedFinitePositiveCoefficientTwist` exposes `diagonalTwistEtale`/`diagonalTwist` and positive-level coefficient finiteness |
| def-compact-support-direct-image-detailed | `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`, `Scheme.sfIntrinsicCompactSupport`; canonical compactification comparison coordinates |
| def-weil-exceptional-inverse-image | `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`, `ConstructibleExceptionalCoefficients.System`; finite comparison adjunction normalization |
| def-amb-vector-integration | `Sheaf.AlgebraicGeometry.VectorBundleIntegration`, `Etale.vectorBundleIntegration`; its chart trace is the ordered counit used here |
| lem-pur-vector-integration-site-comparison | `Sheaf.Paper.VectorIntegrationSiteComparison`, `finiteTypeSiteComparison`, `vectorTensorComparison`, and `vectorExponentIndependence` |
| def-exchange-projection | `Sheaf.Paper.ExchangeProjectionSuppliedDomains`, `SuppliedExchangeProjection.ExchangeProjectionStage`; canonical projection convention, unit normalization in the recorded coherence lemma |
| def-pur-section-invariant | `Sheaf.Paper.PuritySectionInvariantIntrinsic`, `sectionInvariantFinite`; `Dnc.sourceComparison`/`normalComparison` supply the recorded exact finite-site presentations |
| def-pur-normal-bundle | `Sheaf.Paper.PurityNormalProjection`, `Scheme.Hom.purityNormalProjection`; actual graded-algebra/extended-Rees realization and canonical normal cone comparison |
| lem-pur-diagonal-base-change | `Sheaf.Paper.PurityDiagonalBaseChangeCompared`, `comparedDiagonalBaseChange` and `diagonalComparedRestriction` |
| thm-pur-dnc-invariance | `Sheaf.Paper.PurityDncInvariance`, `Dnc.existsUnique_dncInvariance`, `sourceComparison`, `normalComparison` |
| thm-amb-vector-bundle-purity | `Sheaf.Targets.VectorBundlePurity`, `Etale.vectorBundlePurity` |
| def-pur-co-smoothness | `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`, `IsCohomologicallySmoothFiniteCompared`, `finiteComparedBaseChangeClause` |

The eight-step theorem docstring follows all proof dependencies in the node,
including trace transpose/base change, coefficient coherence, finite compact
projection, finite-level compact-support exchange, DNC section geometry, and
translation trace. Those recorded proof modules are imported with plain `import`.
Additional construction modules supply coordinate charts, normalized roots,
the homogeneous conormal algebra, the normalized Rees comparison, and identity
adjunction isomorphisms. No dependency record required repair and no new general
notion required a definition node. Helpers are specialized canonical maps in the
owning node's module, as authorized in the dispatch brief.

Edge cases checked: d=0 (literal identity tower), d=1 (v=[y-x], positive trace
normalization), arbitrary d (the order of the root-line tensors is unchanged),
empty Y (no chosen point or nonemptiness), nonreduced and disconnected Y,
level n=1, arbitrary ramification and levels not divisible by the ramification
index, equal exponents, and two unrelated annihilators via their maximum.
Scheme universe u and coefficient universe u+1 are explicit; no small-site
universe equality or implicit unbound parameter is imposed.

Searches actually run:

* msearch LeanFinder: “For affine space the diagonal deformation to the normal
  cone orientation equals the inverse exceptional transpose of integration”.
  Eight results: affine morphism diagonal properties, affine-space reindexing,
  coordinate maps, and affine-space spectrum comparisons; no derived DNC result.
* msearch Loogle: `"dualizingComplexBaseChangeMap"`: zero Mathlib hits.
* msearch grep: `dualizingComplexBaseChangeMap|sectionInvariant`, restricted to
  Mathlib AlgebraicGeometry: zero hits.
* `rg` of project `lean/WeilConjectures` and `lean/Sheaf` for diagonal/orientation,
  trace-transpose, normal coordinates, section invariants, and the item id.
  The upstream item-id grep has no hit. Related chart-normalization and bundle
  orientation modules do not state these four specified-map equations and import
  the downstream projection-purity agreement, so using them would be circular.
  Reused the actual upstream affine trace/translation constructions and the
  recorded diagonal and DNC comparisons instead.

No statement correction and no STATEMENT-DISPUTED claim. The node copy changes
only `lean`. All compile checks use the prescribed server wrapper; no live source
was edited and no global build was run.

## Second reading by Q29

The dispatch explicitly assigns a solo worker and prohibits starting other agents;
the maintainer performs the independent reading after delivery. This section records
my second pass over the open node and final module, not a fabricated independent
review. I checked each of the four equations against the node's composition order,
checked that α pulls back B inverse, and that β pulls back Q inverse. I also checked
the actual y-x normal class rather than an arbitrary isomorphism of bundles.
The pass identified missing explicit translation, exponent-transition, and rank-zero
clauses in the initial draft. These are now separate named theorem declarations in
the same module and record, with concrete maps and complete proof docstrings.
I checked that no n-divisibility, affineness, or nonempty-base hypothesis entered
through the comparison APIs. The existential I/J/Q maps are all fixed to the
constructed transposes; q is universally quantified with the actual homogeneous
normalization, not arbitrary auxiliary orientation data.
