## Worker report

Q20 states lem-pur-finite-diagonal-orientation-reduction in
Sheaf.Paper.FiniteDiagonalOrientationReduction. Nothing is proved: the five
statements have sorry proofs, and every new definition has explicit data.
The namespace of the delivery is
WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction.
The original mathematical statement and proof are unchanged. Only lean and the
additional statement dependencies change in the existing item.

Hypotheses and clauses, checked against the node and the latest blueprint
sec-smooth-purity/sk-lem-sp-reduction/thm-pur-finite-reduction-of-purity.proof.md,
Steps 3–4:

- The binder P : PurityFiniteSetting carries the algebraic closure of the finite
  field, the prime distinct from its characteristic, finite coefficient
  extension, actual valuation ring and uniformizer, and positive upper level.
  m, hm : 1 ≤ m, hmn : m ≤ P.level specify every finite quotient in the
  affine-adjunct and diagonal statements. quotient is exactly the universe-lifted
  finiteReductionRingHom. No flatness or ramification-divisibility assumption
  appears. The supported-product API instead uses predecessor indices a ≤ b,
  representing every pair of positive levels a+1 ≤ b+1 of the same extension.
- Scheme.{u}, LocallyOfFiniteType, QuasiCompact, and IsSeparated on the structural
  morphisms express separated finite type over the prescribed field. The affine
  statements use the supplied Over instance or the explicit aS required by the
  existing API. The diagonal section has aY, f, the same finiteness and separation
  instances, and SmoothOfRelativeDimension d f for arbitrary natural d. The
  composite f ≫ aY gives the structural morphism of X. There is no affine-base,
  connectedness, nonemptiness, reducedness, or positive-dimension assumption.
- supportedKummerReduction is the actual zero-divisor Cartier equation. Its
  supportedKummerReductionAt conclusion spells out both semilinear maps, their
  values on supported constant and integral-root generators, BOTH derived
  scalar-unit universal properties, and the supported Ext square. The unique
  cartier_kummer_map family supplies c; primeUnit supplies invertibility of ell
  from the field conventions. The full scalar-unit properties identify this
  equation with equality of the B-linear derived adjuncts Q(c_A) and c_B; it is
  not merely an equality after arbitrary restriction of scalars. The coordinate
  zero divisor uses finiteReductionZeroCartier, valid over nonreduced bases.
- affineOrientationReduction spells out the equality for finiteReductionOrientation
  with its exceptional comparison, shifted-line input comparison, and unit
  comparison. This is exactly the exceptional transpose of the supported Kummer
  class, at every positive uniformizer level, rather than a chosen purity map.
- supportedProductsReduction quantifies over every r : Nat. The first equation
  uses the actual ordered supportedClass and the specified closed-source and
  tensor-power target comparisons. The second equation uses the actual thom,
  the reduced exceptional counit proCoefficientMap, the same target comparison,
  and the canonical productUnitMap. The existential CoefficientLineComparison
  is a fully normalized record: its hom is fixed on root powers and every
  scalar/root generator and obeys the derived scalar counit condition. Thus it
  supplies required coefficient data rather than adding a hypothesis or choosing
  comparisons by the orientation equation. Every tensorator in the product
  target is the published site tensorator and ordered root tensor comparison.
- supportedProductsUnit explicitly states the r=0 clause: supportedClass is the
  coefficient unit under lowerStarCongr zero_zero and lowerStarId, and thom
  followed by the specified normalization at zero is the identity. The empty
  product is consequently included with its actual identity-adjunction unit.
- diagonalOrientationReduction uses W = pullback f f and pullback.diagonal f
  through the published chartDiagonalAlpha and chartDiagonalDelta interfaces.
  normalSectionMap uses normalConeProj and normalConeZeroSection of this actual
  diagonal, not an arbitrary rank-d bundle. The factor a is chartDiagonalAlpha.inv;
  delta is chartDiagonalDelta.hom; v is vectorFactor.hom, namely
  chartDiagonalBeta with projectiveLineTraceTransport. The latter is the
  integration-normalized normal-bundle comparison restricted to its zero section.
  The four equations, in order, are precisely the q_C/a square, q_N/delta square,
  q_L/v square, and the composite square for diagonalDualizingObject.hom.
  q_omega, q_C, q_N use the published ordinary reduced-counit and pullback mates,
  transported through the published site comparisons; q_L is proTwistMap of the
  normalized root comparison. None is selected by conjugating an orientation.

Category convention: proScalar and the objects above use the published fixed-scalar
pro-etale presentation. pbcComparisonReduction, comparisonB, and the ordinary
comparison isomorphisms canonically identify it with the intrinsic ordinary
small pro-etale presentation used by the statement. Comparisons are actual
morphisms, with the section formulas and unit/counit normalizations retained.
This adds no extra universe equality and no arbitrary category equivalence.

Recorded dependency declarations read and used (module names have their full
Sheaf prefix; declaration names below are full names):

- Sheaf.Paper.PurityFiniteSetting:
  WeilConjectures.PurityFiniteSetting.
- Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted:
  WeilConjectures.sfQbarTwistingFunctor.
- Sheaf.Paper.FiniteReductionComparisons:
  WeilConjectures.PurityFiniteSetting.finiteReductionSourceComparison and its
  finiteReductionRingHom, setting, unit, and scalar APIs.
- Sheaf.Paper.FiniteReductionAffineOrientation:
  WeilConjectures.PurityFiniteSetting.finiteReductionOrientation and its three
  independently normalized comparisons.
- Sheaf.AlgebraicGeometry.CartierKummerMap:
  AlgebraicGeometry.Etale.cartier_kummer_map, CartierKummerFamily, and the
  generator-normalized coefficient-compatibility clause.
- Sheaf.Paper.PurityAffineLineOrientation:
  WeilConjectures.PurityFiniteSetting.affineLine_orientation (orientation source;
  the unrestricted finiteReductionOrientation interface supplies the actual map).
- Sheaf.Paper.AffineSpaceZeroSectionPurity:
  AlgebraicGeometry.ProEtale.AffineZeroPurity.zeroSection_purity, supportedClass,
  thom, zero, target, unit, normalization, and closedSingleIso.
- Sheaf.AlgebraicGeometry.DiagonalRegularPureCodimension:
  AlgebraicGeometry.diagonal_isRegularImmersionOfPureCodimension.
- Sheaf.Paper.PurityNormalProjection:
  AlgebraicGeometry.Scheme.Hom.purityNormalProjection.
- Sheaf.Paper.PuritySectionInvariantIntrinsic:
  WeilConjectures.PurityFiniteSetting.sectionInvariantFinite.
- Sheaf.Paper.PurityDiagonalBaseChangeCompared:
  WeilConjectures.PurityFiniteSetting.comparedDiagonalBaseChange.
- Sheaf.Paper.PurityDncInvariance:
  WeilConjectures.PurityFiniteSetting.Dnc.existsUnique_dncInvariance.
- Sheaf.Paper.VectorBundlePurity:
  WeilConjectures.PurityFiniteSetting.vectorBundlePurity.
- Sheaf.Paper.PurityDiagonalDualizingObject:
  WeilConjectures.PurityFiniteSetting.existsUnique_diagonalDualizingObject and
  diagonalDualizingObject.
- Sheaf.Paper.DiagonalDncChartNormalization:
  WeilConjectures.PurityFiniteSetting.diagonal_dnc_chart_normalization,
  chartDiagonalAlpha, chartDiagonalDelta, chartDiagonalBeta, and the Dnc source
  and normal presentation comparisons.
- Sheaf.Paper.FiniteSmoothCoefficientArrows:
  AlgebraicGeometry.Etale.FiniteSmoothPurity.proCoefficientMap, proScalar,
  proCompactCoefficientMap, proTwistMap, CoefficientLineComparison, and their
  ordinary scalar, site, and ordered tensor-power comparisons.
- Sheaf.SecSmoothPurity.PurityDncCoefficientTransport:
  WeilConjectures.DncCoefficientTransport.dualizingMap and sectionMap. The new
  definition node def-pur-dnc-coefficient-section-maps owns these existing plain
  maps. The theorem dncCoefficientTransport is not a statement dependency.

All original recorded statement modules are public imports of the main module;
recorded proof modules are plain imports. Proof docstrings give the nine-step
argument: Cartier scalar units, exceptional transposition, balanced supported cup,
ordered induction, actual diagonal exchange, coefficient-free etale frames,
uniqueness of normalized DNC, vector integration counits, and composition.
The additional already-landed finite-smooth coefficient-arrow dependency and the
new existing-definition owner for the ordinary DNC coefficient maps are included
in stmt_deps. Neither has a dependency path back to this item. A downstream finite-reduction
purity theorem with an overlapping affine clause is deliberately not imported.

Edge cases checked: m=n uses scalar unitors; arbitrary ramification imposes no
extra condition on levels; r=0 is explicit above; d=0 uses the normalized
rank-zero chart and bundle data; empty schemes remain allowed; the coordinate
of the zero divisor is regular even over nonreduced S; general finite-type S
is not required affine. Positive predecessor indexing does not omit level one.
All variables and the universe are bound explicitly, with autoImplicit false
and relaxedAutoImplicit false. No file-local notation, local instance, or private
copy of a published definition is used.

Searches for the original statement, through msearch.py Q20:

- leanfinder: “Scalar extension of coefficients preserves supported Kummer
  classes and normalized diagonal purity orientation”: eight unrelated results,
  including Weierstrass results; no match.
- loogle: “Etale.scalarExtension, finiteReductionOrientation, chartDiagonalAlpha”:
  no result (unknown query identifiers).
- leansearch: “Finite coefficient scalar extension supported Kummer product
  diagonal orientation”: eight unrelated Hahn-series/finite-field results.
- Mathlib grep: “finiteReduction.*(Orientation|Diagonal)|diagonal.*reduction”:
  no result. Read-only rg searches in lean/WeilConjectures and lean/Sheaf found
  the recorded component interfaces and partial affine conclusions, but no
  statement comprising the supported, ordered-product, and three-factor clauses.
  The exact node id was also searched in upstream sources.

Searches for the new canonical notions:

- leansearch and leanfinder: “Canonical site scalar presentation of supported
  Cartier reduction equations ordered Tate product comparisons and diagonal
  section coefficient maps”: eight irrelevant results each (cotangent spaces,
  PiTensorProduct, PreTilt/BDeRham); none supplies these comparisons.
- Mathlib grep: “productTargetPresentation|productSourceMap|supportedKummerReductionAt|diagonalSectionMap”:
  no result. The same read-only search of lean/Sheaf, lean/WeilConjectures and
  dag/nodes found no declaration or node for the missing composites.
- tools/blueprint_refs.py search finite-diagonal-reduction: zero blueprint nodes.
  Its ancestor query gives thm-pur-finite-reduction-of-purity, through this item.
  Exact search outputs are recorded in the new nodes' mathlib_searches.

There is no STATEMENT-DISPUTED flag and no mathematical node correction.
Six modules were compiled individually, in dependency order, using the prescribed
scompile.py on the published server build. Both sandbox and library presentations
passed, with no unexpected warnings. Final import cleanup is checked again by
the delivery dry run. No global build or direct edits to the shared clone were used.

## Second reading by Q20

Q20 separately reread the node and all six modules, including the five new
notions, against the source. The dispatcher explicitly prohibits starting other
agents; this section records a self-review, not a claim of an independent agent's
review. The maintainer's independent review remains the delivery review.

The second pass checked each hypothesis and clause mapped above. It caught the
need to state the empty-product unit explicitly rather than only quantify over
r=0; supportedProductsUnit was added and compiled. It also checked that the
ordinary ordered action and root-power target require their actual zero/successor
comparison isomorphisms, rather than a definitional identification. Those maps
are explicit in productTargetPresentation. The supported source specialization
passes the exact zero-section direct-image instances to closedSourceMap; no
extra exactness assumption is left on S. The Ext square retains both scalar-unit
universal properties. Finally all four diagonal equations use the independently
specified coefficient maps and the actual normalized DNC and integration factors.
No statement-level mathematical mismatch remains in this reading.

## New nodes

**def-pur-finite-orientation-scalar-presentation** defines quotient, realize,
presented, and the cached published Cartier family. Source: the latest blueprint
reduction proof Steps 3–4, realized by the recorded scalar/site APIs. The missing
notion is the explicit transport of ordinary arrows between the fixed presentations
needed by these orientation squares, not a new scalar functor. The collective
LeanSearch, LeanFinder, Mathlib/project/DAG grep and blueprint search above found
no such presentation node. The maps are literal compositions, with no new choice.

**def-pur-finite-supported-reduction-equation** defines the single affine-zero
Cartier scalar-unit equation, retaining the two generator formulas and derived
universal properties. Source: the same reduction proof Step 3 and the Cartier
compatibility clause (Stacks 07A6). The existing general supported coefficient
and Cartier APIs supply all ingredients but not this zero-divisor statement
predicate. The searches above found no such specialization. This definition
contains the actual Ext square, not an abstract assertion that a comparison exists.

**def-pur-finite-product-scalar-presentation** defines the unit presentation,
recursive ordered tensor-power presentation, product target presentation, and
product unit map. Source: reduction proof Steps 3–4 and the existing ordered
zero-section supported-product construction. The searches above found the
component tensorators but no assembled presentation of those actual targets.
Its recursion starts at the coefficient unit and uses the published successor
isomorphism, so it covers the empty product without choosing a root frame.

**def-pur-finite-product-reduction-comparisons** defines closedSourceMap,
productSourceMap, and productTargetMap. Source: reduction proof Steps 3–4,
the existing compact-support coefficient mate and closed/single identifications.
The searches above found no canonical closed-supported source or ordered-target
comparison assembled for these objects. The target uses the fully normalized
root coefficient record; the source uses the actual compact-support mate.

**def-pur-finite-diagonal-reduction-comparisons** defines omegaMap,
diagonalSectionMap, normalSectionMap, and vectorFactor. Source: reduction proof
Step 3 and the recorded chart-normalization and DNC coefficient-transport modules.
The searches above found their ordinary component maps but no maps on these actual
fixed-scalar diagonal and associated-graded-normal presentations. The definitions
transport the existing reduced counit and pullback mates, with geometric finiteness
instances derived from the hypotheses; they never derive a coefficient map from
purity. Every module belongs to exactly its corresponding new definition node.


## Returned-delivery repair: 074e72914534, point L (H2)

The immutable returned head used lem-pur-dnc-coefficient-transport as a statement
dependency solely for its two plain helper definitions. The return correctly
identified that no theorem conclusion was used and no definition node owned them.
Added def-pur-dnc-coefficient-section-maps with existing: true, owning exactly
WeilConjectures.DncCoefficientTransport.dualizingMap and sectionMap in the already
published Sheaf.SecSmoothPurity.PurityDncCoefficientTransport module. The record
contains the verbatim dualizingMap signature and both declaration names. Replaced
the theorem dependency by this definition node in both the item and
def-pur-finite-diagonal-reduction-comparisons, and changed the latter's textual
citation to agree. This is the requested ownership repair; all six accepted Lean
files, all five theorem signatures, and the original item statement are unchanged.
The same public import provides the now definition-owned maps.

Compared the retained records with current shared main: the five original new
definition nodes have not landed; the existing item differs only in lean and
stmt_deps. The prescribed delivery wrapper refreshes and rebases on current main.
No direct Git command or shared-source mutation was used.

Second reading of the repair: verified both map bodies and full signatures, their
exceptional counit and scalar/pullback ingredients, the two consumer dependency
lists, and the textual citation. The new node's dependencies own the actual
compact-support mate, scalar unit, and scalar/pullback constructions; the ambient
exceptional-adjoint theorem supplies genuinely required right-adjoint data. It
does not claim coefficient transport or invertibility. The existing maps allow
arbitrary compactifiable g and arbitrary s, all finite rings including the zero
ring, and identity scalar changes; no smoothness, section identity, quotient
flatness, positivity, or universe equality is introduced. The accepted four
diagonal equations and their r=0, d=0, equal-level, and level-one coverage remain
unchanged.

**def-pur-dnc-coefficient-section-maps** is the sixth new definition node. Source:
the latest general-ring smooth-purity proof (2), coefficient transport for the
deformation family. It registers the two existing canonical ordinary maps, with
no new Lean module and no copy of any construction. The fresh LeanSearch and
LeanFinder query was “Canonical coefficient map on relative dualizing complex
and section invariant via scalar pullback and exceptional counit”; each returned
eight component or unrelated results. Mathlib grep dualizingMap|sectionMap|
scalarPullbackIso returned only an unrelated free-sheaf section lemma. Project
and DAG searches found the exact definitions in the theorem's module and no
definition owner; the blueprint search dnc-coefficient returned zero nodes.
These search results are recorded in the new node.
