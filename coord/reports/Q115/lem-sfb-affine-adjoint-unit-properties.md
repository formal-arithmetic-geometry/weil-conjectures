## Worker report

The item is stated as
`AlgebraicGeometry.AlgebraicSpace.affineAdjointUnit_properties` in
`lean/Sheaf/AlgebraicGeometry/AffineAdjointUnitProperties.lean`. Its sole proof is `sorry`.
The accepted Q76 stage-1 split, statement, proof and proof dependencies are preserved.
The stage-2 handoff paragraph of coord/brief-stage2.md explicitly resolves the inherited
stage-1 refusal: a reviewed split does not prohibit stating its Lean interface.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A scheme base and algebraic spaces over it are `{S : Scheme.{u}}`,
  `X : AlgebraicSpace S`. The target scheme is `Y : Over S`; `schemeSpace Y` is its
  existing representable algebraic space, with `[IsAffine Y.left]`. Taking an arbitrary
  base and an arbitrary scheme over it imposes no restriction on the source's data.
- The actual morphism is `f : X ⟶ schemeSpace Y`, so its underlying natural
  transformation is the map of the same algebraic spaces, not an unrelated site map.
- Properness is `hproper : MapIsProper f`: exactly separated, finite type and universally
  closed. Flatness is `hflat : MapIsFlat f` and local finite presentation is
  `hfp : MapIsLocallyOfFinitePresentation f`, the existing all-compatible-etale-chart
  tests. Since properness already implies quasi-compactness and quasi-separatedness,
  local finite presentation here is equivalent to finite presentation. No dimension,
  Noetherian, smoothness, connectedness, reducedness or nonemptiness restriction appears.
- `[HasDerivedCategory.{w} X.SmallModules]` and its target analogue retain the arbitrary
  localization morphism universe. The small model has objects and arrows in `u`, with
  the original coefficient and module universe `u`: no equality between the original
  etale site's object universe `u+1` and morphism universe `u` is imposed. Actual affine
  chart restriction is an equivalence with the original module category.
- `F : QCohDirectImagePresentation f` is a presentation of the fixed `derivedDirectImage f`
  on the full D_QCoh categories: `F.comparison` identifies its entire functor naturally
  with the canonical ambient K-injective derived direct image. Thus it supplies precisely
  the statement's Rf_* on D_QCoh, never an arbitrary unconstrained functor. The hypothesis
  `adj : F.functor ⊣ a` supplies the right adjoint in the node, for the arbitrary right
  adjoint `a`; it is not the ordinary tensor-pullback adjunction.
- W is `(a.obj (schemeSpace Y).derivedQCohStructure).obj`. The structure object is the
  actual structure sheaf in degree zero, whose quasi-coherence is separately stated.
- Clause (1) is `IsPerfectRelativeToScheme Y f W`. Its definition first asserts
  quasi-coherent cohomology (already true for W), and on every affine etale chart uses
  `Scheme.IsPseudoCoherent` and `Scheme.HasFiniteTorDimensionOver` for the actual
  chart map `chartToScheme Y f T` and canonical derived Zariski restriction. The former
  is locally a bounded-above complex with finite-free terms. The latter restricts
  scalars to the inverse-image structure sheaf and tests a K-flat representative against
  every module sheaf over that ring. Its finite interval may depend on the chart.
  Stacks spaces-more-morphisms.tex, lemma-affine-locally-rel-perfect immediately after
  Tag 0DKN, explicitly identifies these tests with the small-etale definition. Affine
  chart quasi-compactness changes locally finite bounds to one bound on that chart.
- Clause (2) is `∀ i : ℤ, 0 < i → IsZero ((homologyFunctor _ i).obj (Rf_*.obj W))`.
  This is vanishing of the cohomology SHEAF, not merely its global sections, and imposes
  no condition at zero or in negative degrees.
- Clause (3) is `IsIso (derivedScalarEndomorphism X W)`. That definition is the transpose
  of the normalized left unitor after the actual ordinary-unit comparison. Its target
  is the existing K-injective derived internal Hom. The closed model retains the
  K-flat representative comparison, pure-tensor transposition and ordinary unit
  normalization from RingedSiteDualityModel. Thus this is the scalar map itself;
  an unspecified isomorphism of the two objects would not suffice.

Dependencies read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicSpace`, `EtaleSite`, `etaleForget`,
  `etaleTopology`, `structureSheaf`, `Modules`.
- Sheaf.CategoryTheory.RingedSiteModules: `CategoryTheory.ringedSiteModules`.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory`, `HasDerivedCategory`;
  its homology functor is from HomologySequence.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: `QCoh` and the slice
  sheafification interfaces, with Mathlib `SheafOfModules.IsQuasicoherent` unchanged.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties: `MapIsProper`, `MapIsFlat`,
  `MapIsLocallyOfFinitePresentation`.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations: `moduleDirectImage`, its
  complete compatible-chart limit universal property and its adjunction normalization.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction: `schemeRestriction`.
- Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite: `schemeSpace`.
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs:
  `Functor.rightDerivedFunctor`, the unbounded K-injective derived functor.
- WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex: `Scheme.IsPseudoCoherent`.
- WeilConjectures.AlgebraicGeometry.FiniteTorDimensionOver:
  `Scheme.HasFiniteTorDimensionOver` (actual inverse-image ring and K-flat test).
- Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses:
  `derivedInternalHomOfUniverses`, from the recorded internal-Hom interface, specialized
  on the equivalent genuinely small affine site rather than forcing original universes.
- Sheaf.CategoryTheory.RingedSiteDualityMaps: `RingedSiteDualityModel`,
  `ringedSiteDualityMaps_exists`; its normalized closed transpose and unit comparison.
- The already stated proof inputs are imported: Sheaf.CategoryTheory.RingedSitePerfectDuality,
  WeilConjectures.AlgebraicGeometry.PerfectAffineModulePreimage,
  Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition, and
  Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal.
  The remaining twelve proof inputs have no lean record on the read base and are not
  imported. They are not prerequisites for stating the theorem and their mathematical
  statements remain in the unchanged seven-step proof docstring and DAG proof plan.

Edge cases checked: empty X or Y (zero module categories and zero structure object);
zero coefficients; identity morphism (W is the structure sheaf, the scalar map is its
canonical unit map); finite flat maps; arbitrary singular/nonreduced proper flat fibres;
positive degree 1 versus degree 0 and negative degrees; all integral shifts; arbitrary
site size u and localization size w. Local Tor bounds are never made uniform on a
non-quasi-compact X, and bounded-above free complexes need not be bounded below.
A chart has finite ranks degree by degree, with no uniform rank assumption.

Searches actually run through msearch.py Q115 for this item:

- LeanFinder: “Proper flat finitely presented algebraic space affine base right adjoint
  of structure sheaf is relatively perfect and scalar derived endomorphism map is an
  isomorphism”: eight scheme flatness/open-map/ring-map-property hits, no match.
- Loogle: `AlgebraicGeometry.AlgebraicSpace, DerivedCategory`: zero hits, unknown identifier
  AlgebraicGeometry.AlgebraicSpace. `HasKInjectiveResolutions, DerivedCategory` likewise
  gives zero hits, unknown identifier HasKInjectiveResolutions.
- Mathlib grep: `affineAdjoint|relativeDualizing|relativelyPerfect|semidualizing`: zero hits.
- LeanSearch: “Small affine etale site of an algebraic space equivalence module sheaves
  derived tensor internal Hom”: eight hits on scheme sites, sheafHom, sheafCongr,
  Grothendieck sheaves and module category instances. Those general APIs are reused.
- LeanFinder: “small affine etale site algebraic space module sheaves equivalence”:
  eight hits on AffineScheme.ΓIsEquiv, AffineZariskiSite.sheafEquiv, scheme Etale forgetful
  functors and smallEtaleTopology; no algebraic-space small ringed-model construction.
- LeanSearch: “relative perfect complex algebraic space pseudo coherent finite Tor
  dimension”: eight unrelated PerfectSpace/formal-smoothness/perfect-pairing hits.
- rg in the named Mathlib, WeilConjectures and Sheaf trees for `IsPerfectRelative`,
  `SmallEtaleModel`, `smallModuleRestriction`, `QCohDirectImagePresentation`, relative
  perfectness and the item id: no existing notion or theorem with the required signature.
  Existing scheme/algebra relative dualizing-pair results have different objects.
- DAG definition title/statement inspection found no relative-perfectness or small-model
  calculus node. blueprint_refs.py search returned zero for “relative perfect”,
  “derived module calculus” and “small affine etale derived module calculus”.
  blueprint_refs.py ancestor returns None, matching the inherited blueprint ancestry.

Validation: scompile.py compiles every module separately in dependency order. Initial
unused local-instance lambda variables were renamed; a guessed proof import was corrected
from the recorded node. All four modules subsequently compiled cleanly; final checks are
repeated through the delivery dry run after the last relative-perfectness edit.
No STATEMENT-DISPUTED finding, statement correction or dependency-record replacement.
No existing declaration is rewritten. All added definitions have real data; every
postponed theorem is named, has its source and full proof docstring, and belongs to the
construction stated in its matching new definition node.

## New nodes

`def-sfb-space-small-ringed-model`: the full affine-chart subcategory of the EXISTING
small etale site, its essentially-small proof obligation, Mathlib small model and induced
regular-functions ringed site, with the actual module restriction equivalence. Source:
Stacks 03ED, 03G7 and the comparison lemma 039Z. It retains sections and rings in u;
no coefficient lift and no second algebraic-space or module-sheaf definition occurs.
Searches above found only scheme sites and generic small-model/sheaf-equivalence APIs.
The named construction obligations assert essential smallness, the sheaf condition and
that the specified restriction functor is an equivalence, as the new node states.

`def-sfb-space-derived-module-calculus`: actual derived category on that equivalent
ringed model; the cohomology-based D_QCoh full subcategory; degree-zero structure object;
the conjugated ordinary compatible-chart direct image and its unbounded derived functor;
a presentation explicitly identified with that functor; canonical derived scheme-chart
restriction; Yoneda scheme-chart structure maps; existing internal derived Hom; normalized
closed model and scalar endomorphism map. Sources: Stacks 079V, 08J7, 0A98, 03G7, 03M0,
0E58 and 0E5V. General-site and scheme APIs exist and are used, but their specialization
to the original algebraic-space module universe was absent. Construction obligations
assert only quasi-coherence of O[0], additivity, and K-injective resolutions, exactly as
stated in this definition node. Selection of the closed model uses its complete existing
representative-normalized universal property; it is not a bare choice of an arbitrary map.

`def-sfb-space-relative-perfect`: source-based affine-chart characterization of Tag
0DKN, explicitly restricted to quasi-coherent cohomology. Every chart restriction uses
existing scheme pseudo-coherence and relative finite Tor dimension definitions, with
all inverse-image ring-sheaf test modules. Sources: 0DKN and the immediately following
lemma-affine-locally-rel-perfect, whose proof explicitly cites the unbounded derived
small-etale/Zariski comparison and relative Tor comparison. Searches found the scheme
notions but no algebraic-space relative-perfectness definition. This node defines the
missing specialization using those notions, without copying their definitions.

## Second reading by Q115

I reread the node, Stacks 0E5V and 0DKN with their complete proofs, and all four final
modules. This is a self-review, not an independent-agent review: the dispatched brief
explicitly prohibits starting other agents and assigns the independent read to the
maintainer. The section is included for the delivery format without claiming another
worker has reviewed it.

The second reading found two substantive issues before delivery. First, ordinary
etale-to-Zariski restriction is not exact on arbitrary module sheaves. The draft's
exactness assertion was removed entirely and the canonical unbounded RIGHT derived
functor is now used. On D_QCoh this is exactly the comparison in the source's
lemma-affine-locally-rel-perfect. Second, such chart tests alone should not silently
replace the ambient quasi-coherent hypothesis: the relative-perfectness definition now
includes `X.derivedQCohProperty K`, which pseudo-coherence implies in the source.
For W it follows already from its type in D_QCoh, so this adds no theorem hypothesis.

I matched affine Y, proper/flat/finite-presentation f, the arbitrary right adjoint and
O_Y again to the theorem binders. Proper plus local finite presentation gives the
same finite-presentation condition. The three conclusions are respectively the exact
relative-perfectness test, sheaf-valued positive cohomology vanishing, and IsIso of the
specified scalar map, not existence of a Hom-object isomorphism. F.comparison identifies
its whole direct-image functor with canonical K-injective Rf_* and so prevents the
adjunction hypothesis from being an arbitrary-map substitute. The closed model's unit
normalization prevents any unrelated choice of a map O_X to RHom(W,W).

The small-model construction was checked against the one-definition rule: the original
module category remains `X.Modules`, and the new one is explicitly equivalent via
restriction to the original affine chart basis. No equality of original site universes
is assumed. All scheme and ringed-site notions are the recorded declarations. The
local Tor condition, empty-space case, identity case and zero/positive-degree boundary
were reread without a further mismatch. The accepted stage-1 split is unchanged.
