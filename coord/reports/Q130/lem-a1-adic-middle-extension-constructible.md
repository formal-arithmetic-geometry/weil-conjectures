## Worker report

The module `Sheaf.Paper.AdicMiddleExtensionConstructible` states
`WeilConjectures.adicMiddleExtension_constructible`, with `sorry` as its proof.
It renders the two conclusions as membership in the inverse images of the
recorded constructible hearts under the recorded fixed-pair forgetful functors.
Thus the objects in the theorem really include the induced Weil structures.
All supporting theorems also have `sorry` proofs and source/proof docstrings.
All definition data is explicit or selected from a uniqueness characterization.

Hypotheses and clauses are rendered as follows.

- The global finite field, its characteristic, its chosen algebraic closure, and
  its actual geometric Frobenius are `D : FiniteFieldDatum.{u}` and the published
  `D.geometricFiber` and `D.geometricFrobenius`. The prime is `(l : ℕ)` with
  `[Fact l.Prime]`; distinctness from the characteristic is `hl : l ≠ D.p`.
  The chosen coefficient closure is `(Ω : Type (u + 1)) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]`, exactly the universe convention
  of the recorded lisse/middle-extension construction. No identification of the
  site object and morphism universes is imposed.
- `c : MiddleExtensionCurve D` is the recorded bundle of C0, U0, j0, smoothness,
  separatedness, finite type, pure dimension one and density. Its fields are used
  directly. `adicMiddleExtensionOpen c` is the actual base change of `c.j`.
  `adicMiddleExtension_geometric_properties` derives the category-domain
  hypotheses on the geometric open; these are not extra assumptions.
- `adicMiddleExtensionBoundary0 c` is the subscheme of the vanishing ideal of
  the complement of `c.j.left.opensRange`, with its composite structure map to
  the finite field. `adicMiddleExtensionClosed0 c` is its actual closed inclusion.
  Their geometric base change is `adicMiddleExtensionClosed c`.
  `adicMiddleExtensionClosed_properties` states closedness, reducedness and the
  exact complement equality. This fixes one actual representative of the reduced
  closed complement; the recorded uniqueness theorem for reduced induced closed
  subschemes identifies any other presentation uniquely over C0. It neither
  requires nor assumes a nonempty boundary.
- The underlying lisse sheaf is `F : adicMiddleExtensionLisse l Ω c hl`, using
  the recorded `LisseAlgebraicSheaf`. `adicMiddleExtensionLissePair` retains
  its literal finite coefficient pair, and `adicMiddleExtensionLisseModel`
  retains the integral lattice already contained in that pair. The completed
  realization `adicMiddleExtensionInput` is placed in degree zero. The `theta`
  binder is an isomorphism from the recorded geometric Frobenius pullback of
  this input to itself, exactly the data of the recorded `IsoAlgebra` Weil
  complex. In particular theta is an arbitrary common-stage Weil isomorphism;
  no integral lattice preserved by theta or its inverse is assumed.
- The ordinary image A is `adicMiddleExtensionObject`. Its integral model is
  `DerivedCategory.singleFunctor _ 0` of the actual ordinary completed-module
  pushforward of the input module. `adicMiddleExtensionImageIntegral_comparison`
  states that this explicit object is isomorphic to the recorded finite-level
  ordinary-image construction, transported through the published completed-ring
  isomorphism. This comparison is not used to choose any definition data.
  No full `Rj_*` is used to define A.
- `adicMiddleExtensionBoundaryObject` is literally
  `(adicMiddleExtensionClosedPull ...).obj (adicMiddleExtensionObject ...)`.
  That functor is the published `commonStageDerivedPullback`, with the residue
  prime units derived from D and hl. The normalized immersion comparison
  identifies it with ordinary exact inverse image on the single-sheaf model.
- `adicGeometricFrobenius_naturality` supplies the actual commuting scheme
  squares for j and i. The canonical square is retained all the way from
  sections to common stages: `adicSquareSites` uses fibre-product pasting;
  `adicSquarePush` has its value on every module section specified;
  `adicSquareModule` is its mate under the published normalized adjunctions;
  `adicSquareComplex` is fixed degreewise; `adicSquareDerived` retains its
  representative equation. The Roos augmentation `adicPullAugmentation` is
  uniquely fixed on module-unit generators and both cone coordinates, and
  `adicPullComparison` is uniquely normalized on all flat K-flat representatives.
  `adicSquareIntegral` and `adicSquareCommonStage` compose exactly these maps
  with the actual coefficient-stage inclusions.
- `adicMiddleExtensionOpenRestriction` uses the actual ordinary open counit,
  with the normalized immersion comparison. The displayed equation in
  `adicMiddleExtensionWeilIso_existsUnique` fixes theta_A uniquely by its open
  restriction: the canonical square, Frobenius of that counit, and theta_F.
  By the ordinary j^*–j_* adjunction this is precisely j_*theta_F after
  automorphism base change, without assuming a comparison or theta_A as input.
  `adicMiddleExtensionWeil` is the fixed pair with this unique isomorphism.
- `adicMiddleExtensionBoundaryWeil` uses the inverse canonical closed square
  followed by the actual closed pullback of theta_A. Its carrier is precisely B.
- The first conjunct of `adicMiddleExtension_constructible` is the recorded
  common-stage heart property pulled back along `sfCommonStageWeilForget`
  on C and evaluated on `adicMiddleExtensionWeil`. The second is the same
  property on Z evaluated on `adicMiddleExtensionBoundaryWeil`. These are
  exactly the full-subcategory predicates defining `sfCommonStageWeilSheaf`.
  The supporting `adicMiddleExtension_heart` spells out the ordinary degree-zero
  carrier assertions separately.

Dependency declarations used:

- `Sheaf.Paper.CurveMiddleExtension`: `MiddleExtensionCurve`,
  `middleExtensionIntegralComplex`, and its recorded lisse coefficient
  construction. Its `LisseAdicSheaves` import supplies `LisseAlgebraicSheaf`,
  `lisseAlgebraicPair` and `lisseCoefficientPairModel`.
- `Sheaf.Paper.SfConstructibleHeart`: `sfCommonStageHeartProperty` and the
  integral/rational/common-stage standard classes it uses.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilPrimeInvertible`,
  `sfCommonStageWeilFrobeniusPullback`, `sfCommonStageWeilComplex`,
  `sfCommonStageWeilForget`, and the fixed-pair heart convention.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralPullback`,
  `rationalDerivedPullback_existsUnique`, `commonStageDerivedPullback`, and
  their actual object and representative-map clauses.
- `Sheaf.Paper.SfImmersionCompletedPullbackComparison`:
  `ImmersionCompletedPullback.transport`, whose coefficient ring isomorphism
  is fixed by every finite projection, and the normalized immersion interface.
- `Sheaf.Paper.SfOpenClosedTriangleAllStages`:
  `sfRecollementCoefficientMap`, its invertibility, and
  `sfRecollementModuleAdjunction`; the latter retains the ordinary tensor-unit
  normalization. No recollement triangle or Weil structure is assumed.
- `Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition`, reexporting
  the source of `proEtaleRingModuleUnitSection`, and the actual ringed pro-etale
  operations and normalized module adjunctions.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  the recorded `IdealSheafData.reduced_induced_closed_subscheme`. Its current
  source was read with `scompile.py --source` because the recorded module is
  absent from the older local checkout.
- The stated geometric proof leaves are Mathlib base-change stability of
  separatedness, local finite type and quasi-compactness, smooth relative
  dimension permanence in `Mathlib.AlgebraicGeometry.Morphisms.Etale`, and
  universal openness over a field in `Morphisms.UniversallyOpen`.

The four additional statement dependencies are already recorded nodes used for
these actual canonical constructions. No dependency node is changed. The needed
specialized comparison declarations belong to the item's induced-structure
construction and are listed in `lean.declarations`; no independent notion or
unrecorded prerequisite is assumed. The unstated broad
`lem-a1-qbar-open-closed-cohomology` interface is not assumed as a Lean hypothesis:
the item's specialized carrier and normalized-comparison clauses are stated here.

Edge cases checked: empty curve/open, empty boundary (j an isomorphism), a
nonproper or disconnected smooth curve, zero lisse sheaf, l=2 with p different
from 2, coefficient stages enlarged to represent theta and its inverse, and
nonunit Frobenius scalars such as multiplication by l. The last case is why the
Weil isomorphism is not required to preserve the original integral lattice.
The boundary construction is valid for every number of components, and only
perfectness of the finite field is used for its reduced geometric base change.

Searches performed, with no exact existing statement found:

- `msearch.py leanfinder`, ordinary direct image of a lisse adic sheaf on an open
  smooth curve and boundary constructibility: eight unrelated scheme/sheaf hits.
- `msearch.py leansearch`, "Ordinary pushforward of lisse adic sheaves along dense
  open immersions of curves is constructible with induced Frobenius structure":
  eight general sheaf-pushforward or module-adjunction hits, no exact match.
- `msearch.py loogle`, `DerivedCategory.singleFunctor, Functor.mapIso`: no hits;
  the latter name was not recognized as a standalone identifier by the service.
- `msearch.py grep`, `middleExtension|[Cc]onstructible.*[Dd]irect`, restricted
  to Mathlib AlgebraicGeometry/Sites: no hits.
- `rg` in Mathlib, upstream WeilConjectures and the project's `lean/Sheaf`,
  including the node id and the proposed declaration prefixes: no existing
  declaration of this statement or name collision. Upstream `WeilSheaf.lowerStar`
  and its constructibility theorem concern the canonical adic coefficient
  presentation and do not directly state the chosen-closure common-stage
  fixed-pair statement of the recorded dependencies. The existing ordinary
  finite-stage construction is therefore reused and explicitly transported.

No `STATEMENT-DISPUTED` issue or source correction is needed. The statement,
proof, proof dependencies and all other original node fields are unchanged.

Validation uses only the prescribed single-file `scompile.py` and `deliver2.py`
wrappers. The final dry run must pass compilation and the server preflight before
this packet is pushed.

## Second reading by Q130

Independent maintainer second reading, 2026-10-18, of immutable delivery
30985869caac0287c237ac8ec011be48856a0ca4. The reviewer did not author this delivery.
The original placeholder in this section is replaced by this actual reading.

Hypothesis and conclusion correspondence:

- Global datum: `D : FiniteFieldDatum.{u}` retains the prime characteristic,
  finite field of cardinality p^a, and its chosen algebraic closure. `l`,
  `[Fact l.Prime]`, and `hl : l ≠ D.p` give precisely the coefficient-prime
  assumptions. `Ω`, its field/algebra instances and `IsAlgClosure` retain the
  chosen coefficient closure. Its universe u+1 is the recorded lisse-category
  convention, not an identification of site object and morphism universes.
- Model geometry: `c : MiddleExtensionCurve D` contains U0, C0, their actual
  map j0, finite type, separatedness, smoothness, pure dimension one and
  `DenseRange`. Finite type and separatedness of U0 follow automatically for
  an open in this Noetherian separated curve, so bundling them adds no
  mathematical assumption. No properness, connectedness or nonemptiness is
  imposed. The geometric maps use the recorded `D.geometricFiber` pullback.
- Boundary: `adicMiddleExtensionBoundary0` uses the vanishing ideal of the
  actual complement of the open range, and `adicMiddleExtensionClosed0` is
  its inclusion. Closedness, reducedness and complementary range after base
  change are stated in `adicMiddleExtensionClosed_properties`. Over the
  perfect finite field this finite reduced boundary is geometrically reduced.
  The recorded reduced-induced-closed-subscheme theorem identifies any other
  presentation uniquely over C0; fixing this representative loses no case.
- Input: `F` uses the recorded `LisseAlgebraicSheaf`, literal coefficient
  pair and integral model. Its completed module is put in degree zero by
  `adicMiddleExtensionInputIntegral`. `theta` is any common-stage isomorphism
  from geometric Frobenius pullback of that input to itself. It need not
  preserve an integral lattice, and may be represented after coefficient
  enlargement. This is the stated lisse Weil-sheaf datum.
- A: `adicMiddleExtensionImageIntegral` applies the actual ordinary
  `proEtaleRingModuleDirectImage` to that module, then `singleFunctor _ 0`.
  `adicMiddleExtensionImageIntegral_comparison` compares it with the recorded
  finite-level ordinary image after the projection-normalized coefficient
  transport. Both objects are explicitly constructed; its Nonempty assertion
  supplies no chosen data. `adicMiddleExtensionObject` rationalizes and
  includes this model at its literal original coefficient stage. It is not
  the full derived image Rj_*F.
- B: `adicMiddleExtensionBoundaryObject` is literally the recorded
  common-stage closed pullback applied to A. The normalized immersion
  comparison and `adicMiddleExtension_heart` retain its ordinary degree-zero
  sheaf meaning. Both heart assertions are present.
- Weil structures: `adicSquarePush` is fixed sectionwise by fibre-product
  pasting, `adicSquareModule` is its normalized adjunction mate, and the
  complex/derived comparisons retain their representative equations. The
  Roos augmentation is fixed on unit generators and both cone coordinates;
  `adicPullComparison` is fixed on every flat K-flat representative.
  `adicMiddleExtensionWeilIso_existsUnique` fixes theta_A by the actual open
  counit and commuting Frobenius square. Ordinary adjunction into j_*F makes
  this exactly j_*theta composed with automorphism base change, and proves
  uniqueness. The boundary structure is the inverse closed square followed
  by i^*theta_A. No arbitrary isomorphism or Weil structure is an input.
- Conclusions: the two conjuncts of `adicMiddleExtension_constructible`
  apply the recorded common-stage heart predicate, pulled back through the
  recorded fixed-pair forgetful functor, to these exact Weil objects.
  They are precisely membership in the two constructible Weil-sheaf hearts.

Dependency and source checks:

Read all eight statement-dependency JSON statements and records, and the
signatures/docstrings actually used from CurveMiddleExtension,
SfConstructibleHeart, SfWeilSheafComplex, DerivedPullbackTensorHom,
SfOpenClosedTriangleAllStages, ProEtaleCanonicalPullbackComposition, and
SfImmersionCompletedPullbackComparison in the read-only group clone. Read
ReducedInducedClosedSubscheme through the prescribed `scompile.py --source`
wrapper because its recorded module is absent locally. Its vanishing-ideal
construction and uniqueness agree with Stacks schemes.tex, Tags 01J3/01J4.
Read the blueprint boundary-sequence statement and proof (first sentence
and finite-boundary sentence), and Bhatt--Scholze 6.8.6, 6.8.8,
6.8.11, 6.8.14 and 6.8.15. These support the ordinary heart convention and
immersion inverse image; finite inertia invariants provide boundary finiteness.
The specialized comparisons belong to this item's ordinary-image and induced
Weil-structure construction. No unrecorded independent prerequisite is assumed.
The broader unstated open-closed cohomology interface is not a Lean hypothesis.

Independently searched the group side tree and the older upstream tree for
middleExtension, lowerStar and constructibility. Opened the finite-coefficient
curve Boundary declarations and upstream WeilSheaf/LowerStar. They concern
finite-ring etale sheaves or another adic/coefficient presentation, rather than
this chosen-closure common-stage fixed-pair statement. Existing ordinary image,
lisse systems, hearts, pullback and fixed-pair notions are reused. The worker's
LeanSearch, LeanFinder/Loogle and grep search records were also checked. No
exact duplicate of the delivered statement was found.

Edge cases: empty curve/open, empty boundary, identity open, disconnected or
nonproper curve, zero and torsion-only integral input, coefficient prime 2
with different residue characteristic, and Frobenius multiplication by l.
The last case is allowed because theta is common-stage and rational, with no
lattice-stability assumption. Finite levels use n+1; no n=0 quotient is mistaken
for a positive exponent. Scheme/site universes remain the published ones;
there are no unbound parameters or silent universe equalities.

Mechanical checks and compiler evidence:

The item's mathematical statement and proof are unchanged from its parent;
the four added dependencies expose the canonical constructions actually used.
There are no new nodes or dependency repairs. All 61 declared names are
recorded, and `lean.statement` equals the main signature verbatim, including
newlines. All 16 postponed theorem proofs are `sorry`. Definitions contain
explicit data or choices from characterizations that determine the data; none
chooses an arbitrary map from mere existence. Module/declaration docstrings
carry source places and blueprint identifiers; theorem docstrings explain
construction and proof steps. No line exceeds 100 characters.

Reproduced the immutable file with:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q130 lem-a1-adic-middle-extension-constructible snapshot/lean/Sheaf/Paper/AdicMiddleExtensionConstructible.lean`.
Exit code 0, no diagnostics: sandbox path 28.4 s, library path 35.8 s, each
under the wrapper's 60-second per-file limit. The installed wrapper currently
uses the server's private side overlay, not a local-machine lcompile entry
point; this is the actual reproduction path, without invoking ssh directly.
No lake build, global build, live Lean write, or project-clone edit was made.

Checked the available origin/newtargets-dag route-pivot dropped list: none of
the item's statement/proof dependencies is on it. There is no item-specific
repair note at that ref. The delivery introduces no enhanced, infinity,
dg/model-category, Quillen, coherent-section, straightening or operadic
machinery. Its pro-etale ringed-site module constructions are the recorded
coefficient conventions, not a substitute for the intended statement.

Finding and repair: H1/H11, the delivered Second reading section was only a
placeholder. This complete report replaces it with the independent reading
and explicit compiler evidence. No mathematical or Lean change is needed.
