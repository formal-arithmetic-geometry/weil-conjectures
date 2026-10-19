## Worker report

The module `Sheaf.Paper.PurityAffineLineOrientation` states
`WeilConjectures.PurityFiniteSetting.affineLine_orientation`, with one postponed proof.
Its four auxiliary declarations package the existing canonical Gysin comparison,
form the actual coordinate boundary, and construct coefficient and supported
pullback by explicit composites. No data definition contains sorry.

The statement follows the unchanged node and the current blueprint
`main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/thm-pur-affine-line-orientation.md`.
The resolved stage-1 repair note was read: the natural statement stays unchanged.

Clause-by-clause reading:

- The chapter's finite-field and coefficient conventions are `P : PurityFiniteSetting.{u}`.
  This retains the finite-field algebraic closure, ell distinct from its characteristic,
  the specified finite subextension, the actual quotient ring and its positive level.
- The affine-line datum's divisibility is `h : P.ramificationIndex ∣ P.level`.
  Its exponent, twist and coordinate are the recorded constructions; no abstract
  Kummer-class or normalized-twist hypothesis is introduced.
- The separated finite-type base is `Y`, `a : Y ⟶ Spec (.of P.field.k)` and
  `[IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]`.
- The source of `m` is `P.derivedSheaf h Y false`, the coefficient unit in degree zero.
  The target is exactly `P.gysinValue h Y`: the recorded exceptional inverse image
  of the finite root-tensor twist, shifted by two. The shift is outside that inverse
  image, as in the recorded Gysin interface.
- The first two conjuncts assert `finiteTorConstructible` for both objects, using
  `finiteCoefficientIntrinsicRealization` to pass from fixed scalars to the intrinsic
  constant-ring-sheaf presentation used by that predicate. Since its category is full,
  the ambient morphism `m` is precisely a morphism of D^b_ctf; no different Hom is used.
- The third conjunct asserts vanishing in every integer degree other than zero.
- The fourth conjunct supplies quasi-compactness of the actual complement and the
  recorded `Scheme.HasOpenComplementCondition`. Its bound is existential: the item
  specifies no particular dimension bound. There is no extra open-complement hypothesis.
- The chart `D : OrientationSupportData P h Y` uses the same Comparison, open-coefficient
  isomorphism, normalized edge and support isomorphism as `GysinSupportIdentification`.
  Its three specification fields copy the published formulas exactly. It additionally
  records the exact boundary, constrained by `supportBoundaryNormalization` on all
  bounded-below injective models. Exactness alone would leave a sign ambiguity.
- `D.coordinateBoundary P h a` applies that boundary to the actual `coordinateKummer`,
  through the published `gysinKummerSection`. The equation
  `D.support.hom (P.gysinHomToSections h Y m) = D.coordinateBoundary P h a`
  says exactly that the degree-zero sheaf morphism sends 1 to the supported boundary.
- Every geometric point is quantified by an algebraically closed field `Ω`, its
  `P.field.k`-algebra structure and the compatible scheme arrow `y`. The equation `hy`
  retains that compatibility. No finite-type condition is imposed on Ω or y.
- The fibre chart uses the same finite coefficient ring, exponent and twist.
  `p : proEtaleSupportHomTransport ... (AffineSpace.map ... y)` has actual scheme
  inverse image and its adjunction, not an arbitrary functor. Its terminal/complement
  arrows are unique because their targets are base changes of terminal/open objects.
  `supportUnit_spec` fixes the kernel map by its monic inclusion.
- `orientationSupportRestriction` takes H^2 of that published derived kernel pullback
  and then applies `orientationInputPullback`. The latter is the canonical
  etale/pro-etale pullback comparison followed by the published root-line pullback.
  Thus it is pullback of the supported class represented by m. The supported-Hom
  pullback dependency identifies this with restriction of the exceptional adjunct;
  no invertibility of exceptional base change is assumed.
- The coefficient-linear residue `ρ` is normalized by
  `ρ.hom (D'.coordinateBoundary ...)=1`, independently of m. An A-linear isomorphism
  normalized on that generator is unique, so this is exactly the residue of the
  rank-one local calculation. The last equation says the restricted global
  orientation has residue 1 under that same normalization. In particular it does
  not merely choose a different residue for the restricted class.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, `constant`, `twistEtale`,
  `twist`, `derivedSheaf`, `Ring`, `Coefficient`, exponent and Kummer-level definitions.
- `Sheaf.Paper.PurityAffineLineDatum`: the actual line, coordinate, zero section,
  punctured open, `coordinateKummer`, and `twistEtalePullback`.
- `Sheaf.Paper.PurityGysinStructure`: `gysinInput`, `gysinEtaleInput`, `gysinClosed`,
  `gysinValue`, `gysinSupport`, `gysinHomToSections`, `gysinKummerSection`,
  `GysinSupportIdentification`, `gysin_structure` and their normalized formulas.
- `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`: `sfFiniteExceptionalAt`;
  the Gysin object's recorded proper compactification uses the same transported
  ordinary etale exceptional construction (through its existing fixed-ring wrapper).
- `Sheaf.AlgebraicGeometry.SupportCohomology`: `ProEtale.supportHypercohomology`,
  the actual right-derived kernel-of-restriction construction.
- `Sheaf.Paper.FiniteTorAmplitude`: `finiteTorConstructible` and its full category;
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison` supplies its
  canonical fixed-scalar realization.
- `Sheaf.Paper.SupportedHomPullback`: `proEtaleSupportHomTransport`,
  `SupportHomPair.Transport.derivedMap`, `supportHomDerivedComparison` and
  `supportedHom_pullback`, including their kernel/constant/cocycle normalizations.
- `Sheaf.AlgebraicGeometry.SupportComparisonBoundary`:
  `supportBoundaryNormalization`, fixing the snake-boundary sign.
- `Sheaf.AlgebraicGeometry.OpenComplementCondition`: `Scheme.HasOpenComplementCondition`.
- `Sheaf.Paper.PurityRankOneLocalCalculation`: `RankOne.rankOne_local_calculation`,
  whose A-linear residue is uniquely fixed by the coordinate boundary.
- The recorded closed ambient adjoint, closed cohomological amplitude, closed Tor
  amplitude and open-complement-known declarations are imported as the node's
  existing preservation inputs. Their full recorded signatures and source docstrings
  were read. Proof imports also include finite exchange, twist local freeness,
  finite-type dimension and the fixed-coefficient comparison unit.

Three already landed nodes were added to stmt_deps to name the interfaces actually
appearing in the signature/helpers: `lem-pur-supported-hom-pullback`,
`lem-pur-support-comparison-boundary`, and `def-exc-open-complement-bound`.
No new nodes, dependency module repairs, or statement corrections are delivered.

Edge cases checked before writing:

- Y empty: its sheaf category and the two displayed complexes are zero, the orientation
  exists, and there are no geometric points. No nonempty-base assumption occurs.
- Arbitrarily large algebraically closed extensions within the scheme universe are
  included. In particular Ω/k need not be finite type; the fibre comparison is over Ω.
- Nonreduced or disconnected bases are retained. The coordinate, root twist, exact
  support sequence and canonical evaluation make sense on all of them.
- Positive levels and ramified coefficient extensions retain e|n; no invalid replacement
  of this condition by n≥1 or a field-coefficient restriction is made.
- Degrees include all integers, including negative degrees. The only surviving degree
  after the shift is zero, and supported cohomology is evaluated in degree two.
- A change of primitive root cannot change the assertion: the twist is the actual
  tensor root line, the coefficient maps are canonical, and the A-linear residue is
  normalized by its coordinate boundary. Changing the sign of a boundary is excluded
  by the injective-model normalization.

Searches for existing declarations:

- msearch.py leanfinder, query "The boundary of the Kummer class of the affine line
  coordinate defines the global zero section orientation normalized to one at geometric
  points": eight Weierstrass-coordinate hits, no matching theorem.
- msearch.py loogle, query `"Kummer", "orientation"`: zero hits.
- msearch.py grep, query `orientation|kummerBoundary|gysin`, Mathlib/AlgebraicGeometry:
  zero hits.
- msearch.py leansearch, query "Kummer class boundary zero section affine line global
  orientation": eight unrelated vector-bundle, basis-orientation and Proj hits.
- rg in upstream WeilConjectures and side lean/Sheaf for
  `affine.line.orientation|gysinHomToSections|globalOrientation|purityOrientation`:
  located the Gysin API and upstream Smooth.Orientation/AffineLine. These source files
  were opened. The upstream statements require an abstract normalized HasKummerClass
  and use a different etale exceptional interface; they do not state this node's
  concrete finite-coefficient pro-etale orientation or its local residue normalization.
- grep for the exact node ID in upstream WeilConjectures: no declaration.

The first compile exposed the legacy/fixed-coefficient duplicate
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification`, imported by
`Sheaf.Paper.PurityRelativeKummer` through legacy derived LowerShriek and its
`ComparisonGlobalCohomology` proof import. That proof-only import is omitted here:
its finite coordinate-class definitions already come from the smaller
`PurityAffineLineDatum` module. The proof plan continues to cite relative Kummer;
its legacy proof module cannot be imported into this fixed-coefficient environment.
The mathlib adjunct-counit identity needs no additional module. No live source was edited.

## Second reading by Q35

This is the author's second reading; the dispatcher forbids spawning another agent.
The maintainer's separate review supplies the independent reading. Reopened the node,
current blueprint and final file, and checked each binder and conjunct against the
mapping above. The statement keeps the concrete class, actual coefficient quotient,
exceptional support object, full finite-Tor category and all geometric points. The
normalization is stated for restriction of the actual global class under a canonical
kernel pullback, with the residue fixed separately by the fibre coordinate class.
The initial risk was sign ambiguity in exact support boundaries; the final chart
explicitly requires the published injective-model snake normalization. No change
to the natural statement was needed. The additional chart and pullback declarations
are supporting data for this same construction, and contain no postponed data.
