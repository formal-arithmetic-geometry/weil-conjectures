## Worker report

The item is stated as `AlgebraicGeometry.Etale.exists_etaleHypercohomology_pullback_functorial`
in `lean/Sheaf/Paper/EtaleHypercohomologyPullbackFunctorial.lean`. Its only proof is `sorry`.
All accompanying definitions have complete data and no `sorry`.

The theorem chooses Cartan--Eilenberg presentations `D X K` for all schemes and bounded-below
complexes, maps `M f K L v` between their intrinsic spectral sequences, eventual-stage bounds
`R`, and stable-page identifications `eInf`. This uniform choice expresses the identity and
composition assertions without taking unrelated witnesses for each individual pair. Page-zero
resolution data remain in each presentation; maps start at E₁. The node indexes by
(cohomology degree p, complex/filtration degree q); Mathlib indexes by (q,p), with differential
of bidegree (r,1-r). This is the same index exchange used by the recorded first-page theorem.

Clause-by-clause correspondence:

* A morphism of schemes f:Y→X is `{X Y : Scheme.{uNatural}} (f : Y ⟶ X)`.
  No finiteness, separation, properness, torsion or field assumption is imposed.
* Bounded-below abelian étale complexes are
  `CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})` and the
  corresponding type for Y. `Plus` allows any integer lower bound, not only degree zero.
* The complex morphism u:f⁻¹K→L is `v` with source the object of
  `(upperStar AddCommGrpCat f).mapHomologicalComplex (ComplexShape.up ℤ)` on `K.obj`.
  Its degree-q component is `v.f q`.
* These are the hypercohomology spectral sequences of Γ: the new presentation type retains
  the CE augmentation and all its injectivity/quasi-isomorphism conditions, the mapped and
  extended total complex of Γ(I), its second-degree filtration `L`, its E₀ graded differential
  and cycle/boundary subquotients, the signed E₁ derived-functor identification, its d₁,
  vanishing in negative resolution degree, and the canonical derived abutment comparison.
  These are witnesses of `Functor.exists_hypercohomology_firstPage`, not arbitrary
  spectral sequences given only an E₁ page.
* E₁^{p,q}=H^p(X,K^q) is `(D X K).firstPageIso p q`, for p:ℕ and q:ℤ.
  Negative cohomology degrees vanish by the presentation's `negative` field.
* The induced morphism of spectral sequences is `M f K L v`, an actual Mathlib
  `SpectralSequence.Hom`; its defining `comm` field enforces compatibility with
  `E_{r+1}=H(E_r)` on every page r≥1.
* The E₁ formula is the first conjunct. It states the conjugated component of `(M ...).hom 1`
  equals `AddCommGrpCat.ofHom ((Sheaf.H.map (v.f q) p).comp
  (cohomologyMap f (K.obj.X q) p))`: first pull back, then apply H^p(u^q).
* The abutment is `(cohomology AddCommGrpCat X n).obj (DerivedCategory.Q.obj K.obj)`.
  Its canonical map is `hypercohomologyPairMap f K.obj L.obj v n`, the homology of derived
  pullback on RΓ followed by RΓ(u), using `mapDerivedCategoryFactors` to identify termwise
  inverse image with the derived exact functor.
* The finite decreasing filtration is `(D X K).H n`. Its `finite` field is `IsFinite`;
  its `H_formula` is the image of the cohomology of the second-degree filtered total,
  transported by the canonical resolution comparison `c n`. Thus the abutment filtration
  is tied to Γ(I), not independently postulated.
* Preservation is the factorization `ht q` through every target filtration step, with
  underlying map explicitly `hypercohomologyPairMap ... n`. The coherence `hc q` makes
  these lifts into a map of successive inclusions. The next displayed equation identifies
  each sufficiently late page component, via `eInf`, with `cokernel.map` on these successive
  inclusions: precisely the map on gr^q H^n, with n=p+q. The common stable range requires
  both `hX : R X K q n ≤ r` and `hY : R Y L q n ≤ r`.
* The identity conjunct uses `upperStarId`, mapped to complexes and followed by
  `Functor.mapHomologicalComplexIdIso`; it states M=identity and the canonical abutment
  map=identity for every n.
* The composition conjunct uses `upperStarComp ... g f`, mapped to complexes by
  `mapHomologicalComplexCompIso`. Its inverse component identifies (g≫f)⁻¹K with
  g⁻¹f⁻¹K, followed by g⁻¹(v) and w. It states equality with `M f ... ≫ M g ...` and
  equality with the composite canonical abutment maps, for every n.

Dependencies read and used (recorded modules and full names):

* `def-weil-pbc-scheme-conventions`: a convention record; schemes are Mathlib
  `AlgebraicGeometry.Scheme` and arrows are its category morphisms.
* `def-weil-pbc-etale-sheaves`: read `Sheaf.AlgebraicGeometry.EtaleSheaves` and its mixed
  record. The relevant existing declaration is `CategoryTheory.Sheaf`, with abelian values
  `AddCommGrpCat`; none of its unrelated locally-constant/torsion predicates are assumed.
* `def-weil-pbc-inverse-image`:
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.upperStar` and `upperStarLowerStarAdjunction`.
* `def-weil-pbc-cohomology-pullback`: the ordinary map remains
  `AlgebraicGeometry.Etale.cohomologyMap` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`, with
  `CategoryTheory.Sheaf.H.mapFunctor`. The missing derived clause is supplied below.
* `def-weil-pbc-etale-cohomology`:
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `AlgebraicGeometry.Etale.rightDerivedGlobalSections` and `cohomology`.
* `lem-weil-pbc-inverse-image-composition`: read `lowerStarComp`/`upperStarComp` and
  `upperStarId` (Defs and UpperLowerStar.Coherence). The theorem uses `upperStarComp`
  and `upperStarId`, whose definitions derive the identifications from the adjunctions.
* `thm-sp-if-e1`: `Sheaf.CategoryTheory.HypercohomologyFirstPage`,
  `CategoryTheory.Functor.exists_hypercohomology_firstPage`; the presentation retains
  its CE, filtered-total, first-page and canonical resolution-comparison witnesses.
* `def-sp-spectral-sequence`: Mathlib.Algebra.Homology.SpectralSequence.Basic,
  `CategoryTheory.SpectralSequence` and `SpectralSequence.Hom`.
* The new presentation additionally uses `CartanEilenbergPresentation.mappedFunctor`
  (Sheaf.CategoryTheory.CartanEilenbergPresentation), `HomologicalComplex₂.secondFiltration`
  (Sheaf.CategoryTheory.DoubleComplexTotal), `CochainComplex.KInjectiveResolutionChoice`
  (Sheaf.CategoryTheory.KInjectiveBridge), and `DecreasingFiltration`, `IsFinite`,
  `gradedPiece` (Sheaf.CategoryTheory.Filtration). Their declarations and signatures were read.

The derived dependency uses existing `Adjunction.mapDerivedCategoryRightDerivedAdjunction`
(WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction),
`rightDerivedLowerStarCompRightDerivedGlobalSectionsIso`
(WeilConjectures.SixFunctors.Etale.Derived.GlobalSections),
`Functor.rightDerivedFunctorObjQIso`
(WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective), and
`DerivedCategory.homologyFunctorFactors`. The resolution comparison is written as the
inverse of the canonical comparison from RΓ(K) to Γ of the K-injective resolution.
The ordinary Ext/right-derived-Γ bridge is represented by the presentation's
`ordinaryComparison` and `ordinary_naturality`, as the existing cohomology records require.

Edge cases checked: the zero complex; the empty scheme; a complex concentrated in any single
integer degree (including a negative degree); p=0 and negative cohomology degrees; identity
pairs; two successive pairs; unrelated lower bounds for K and L (a common bound can always
be their minimum); unrestricted scheme and sheaf sizes under the project's Scheme.{u} /
AddCommGrpCat.{u+1} convention. There is no empty index-set hypothesis and no nonempty-scheme
assumption. For a one-degree complex, the filtration has only that complex-degree piece,
the E₁ formula is the usual cohomology pullback and H^p(u), and the stable graded map is the
same map. No statement correction or STATEMENT-DISPUTED flag is needed.

Sources inspected online because the read-only clone has no Stacks TeX checkout:
[015J](https://stacks.math.columbia.edu/tag/015J),
[015K](https://stacks.math.columbia.edu/tag/015K), and
[0EZM](https://stacks.math.columbia.edu/tag/0EZM).
015J provides the first-page identification and finite induced filtration, 015K its
functoriality in complexes, and 0EZM the maps along scheme morphisms implicit in its two
termwise spectral sequences. The docstring records all three proof steps of the DAG node,
including CE lifts, the row-resolution computation, and derived/filtered functoriality.

Searches performed:

* `msearch.py ... leanfinder` query "naturality of hypercohomology spectral sequence under
  pullback of complexes of etale sheaves": eight unrelated sheaf-pullback and hypercover
  declarations; none states this theorem.
* `msearch.py ... loogle` query "SpectralSequence.Hom, Functor.rightDerivedFunctorNatTrans":
  no hits, unknown identifier SpectralSequence.Hom in the search service. Its actual local
  Mathlib source was opened and used.
* `msearch.py ... grep` query "hypercohomology|spectral.*pullback|pullback.*spectral" in
  Algebra/Homology: no hits.
* `rg` on WeilConjectures and lean/Sheaf for hypercohomology and spectral pullback:
  existing HypercohomologyFirstPage and truncation/weight applications, but no theorem
  asserting this naturality. Searching the exact item id in WeilConjectures found no match;
  tools/lean_names_upstream.py show supplies no attachment for it.
* For the new presentation, `msearch.py ... leansearch` query "Cartan Eilenberg termwise
  hypercohomology spectral sequence presentation": unavailable (Internal Server Error),
  recorded as unavailable, not as a no-match result.
* `msearch.py ... leanfinder` with that query: eight hits on HomComplex and K-injective
  factorization, none a presentation type.
* `msearch.py ... grep` query "Hypercohomology|hypercohomology|CartanEilenberg" in
  Algebra/Homology: no hits.
* `rg` on DAG, Mathlib, WeilConjectures and lean/Sheaf for FirstPagePresentation,
  FirstPageData, TermwiseHypercohomology and all new declaration names: no existing
  definition or name collision. `tools/blueprint_refs.py search 'termwise hypercohomology
  presentation'`: zero blueprint nodes. `ancestor` gives
  prop-weil-pbc-strict-henselization-stalk-formula.
* Source inspection found the explicit TODO in Derived/GlobalSections.lean: deriving
  the pullback map on RΓ for an arbitrary scheme morphism. The old dependency's record
  also explicitly identifies this missing derived clause. Existing iso-only comparisons
  do not provide that map for arbitrary f.

Validation: the final combined server compile passed cleanly in 52.5 seconds with no errors
or warnings, using the default 120-second file limit and explicit universes /
`autoImplicit=false`; combined compilation checks imports between the three delivery modules.
Scoped heartbeat allowances handle the many dependent resolution witness fields without
raising the wall-clock timeout. The first delivery dry run identified a dependency-node
chapter-path error, the unavailable-search status field and an incomplete inherited blueprint
via chain; all were repaired before rerunning it. The next preflight required the recorded signature
to begin at the keyword `def`, omitting its `noncomputable` modifier; that record was fixed.
The second-reading section is left for the
independent second reader, as required by the worker brief.

## New nodes

`def-weil-pbc-termwise-hypercohomology-presentation` defines
`AlgebraicGeometry.Etale.EtaleTermwiseHypercohomology`, a type of the CE, filtered-total,
first-page and canonical filtered-abutment witnesses of the already landed first-page
theorem. Its source is Stacks 015H/015J/015K. Its data are written fully as fields;
`sequence` restricts the page-zero construction to the intrinsic pages from E₁, and
`firstPageIso` composes its signed derived-functor identification with the ordinary
cohomology comparison. The searches above found no presentation type for an arbitrary
bounded-below complex. `CartanEilenbergPresentation` instead presents the image of an
object's injective resolution under another functor, and cannot carry these data for an
arbitrary K. The new type reuses its `mappedFunctor`, not a duplicate of that operation.
The definition introduces no theorem and no opaque construction. The item gains only
this node in its statement dependencies.

## Dependency modules

`def-weil-pbc-cohomology-pullback`: its existing `cohomologyMap` is usable for ordinary
sheaves, but its own record explicitly lacks the map RΓ(X,K)→RΓ(Y,f⁻¹K) required by the
item. `Sheaf.Paper.DerivedEtaleCohomologyPullback` supplies `derivedGlobalSectionsPullback`
from the canonical derived unit and the existing Leray isomorphism, consistent with the
node's derived-unit characterization (the resolution-recipe agreement is the existing
lem-weil-pbc-cohomology-pullback-derived-unit bridge). It also writes the canonical
`resolutionEtaleCohomologyIso` and the degree-n map of a pair `hypercohomologyPairMap` by
composing that pullback with RΓ(u). All data are compositions of existing constructions;
ordinary `cohomologyMap` and `Sheaf.H.mapFunctor` are retained in the mixed node record and
are not redefined. Only this dependency node's `lean` field changes.

## Second reading by S1

I independently read the node statement, its source references (Stacks Tags 015H, 015J,
015K and 0EZM), the dependency records, and all three delivered modules.

The node's objects and hypotheses match the Lean as follows. The scheme morphism
$f:Y\to X$ is `{X Y : Scheme.{uNatural}} (f : Y ⟶ X)`, with no properness,
separation, finiteness, characteristic, field, or torsion assumptions. The bounded-below
complexes are `CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})`
and the corresponding type over `Y`; the complex map
$u:f^{-1}K\to L$ is the displayed `v` between the `upperStar`-mapped homological
complex and `L`. The presentation object `D` is
`EtaleTermwiseHypercohomology`, whose fields retain the CE resolution, filtered total,
page-zero and page-one data, ordinary cohomology comparison, negative-degree vanishing,
canonical derived-resolution comparison, and finite abutment filtration. `M` is an
actual `SpectralSequence.Hom` between the intrinsic page-one-and-later sequences;
`R` and `eInf` express the eventual $E_\infty$ identifications required by the node.
All these binders are existential witnesses, so no extra structure is assumed of the
input pair.

The first conclusion clause is rendered by the displayed conjunction whose left side is
`((M f K L v).hom 1).f (q, (p : ℤ))` and whose right side conjugates the map by
`firstPageIso`; it is exactly pullback `cohomologyMap f ...` followed by
`Sheaf.H.map (v.f q) p`, with Mathlib's `(q,p)` bidegree order. The second clause is
rendered by `t`, `ht`, and `hc`: `ht` factors the canonical
`hypercohomologyPairMap ... n` through every target filtration step, `hc` makes the
successive lifts compatible, and the final equation identifies every sufficiently late
page with the cokernel map on the successive filtration inclusions. The identity clause
uses `upperStarId`, `mapHomologicalComplexIdIso`, and states both spectral-sequence and
abutment identities. The composition clause uses `upperStarComp` and
`mapHomologicalComplexCompIso` and states both composition equalities for `M` and for
`hypercohomologyPairMap`. Quantifier order and the common stable range hypotheses are
preserved.

The dependency definition `EtaleTermwiseHypercohomology` was checked against its node:
its fields are precisely the CE/filtered-total witnesses from `thm-sp-if-e1`, including
row and horizontal quasi-isomorphisms, page-zero differential, cycle/boundary
subquotients, signed derived identifications and differential naturality, negative
vanishing, and the canonical derived abutment comparison and finite filtration. The
modified dependency module `DerivedEtaleCohomologyPullback` retains the existing ordinary
`cohomologyMap` and adds the missing derived global-sections pullback and the induced
hypercohomology pair map; these use existing derived adjunction and resolution comparison
constructions and do not redefine a notion.

Edge cases checked were the zero complex, an empty scheme, a complex concentrated in any
integer (including a negative integer) degree, `p = 0`, negative resolution degrees,
identity pairs, successive pairs, unrelated lower bounds, and unrestricted allowed
universes. No empty-index or nonempty-scheme hypothesis is introduced; zero and identity
maps elaborate in the displayed categories. The structure's lower-bound witness covers
all bounded-below cases, and the finite filtration/stable-page witnesses cover the
one-degree and zero-complex cases.

I repeated the existing-declaration searches with the item name and with
`hypercohomology`, `spectral sequence pullback`, and `termwise hypercohomology
presentation` over Mathlib, `WeilConjectures`, `lean/Sheaf`, and the DAG; the only
matches were the intended generic first-page, spectral-sequence, filtration, and
resolution infrastructure. LeanSearch/LeanFinder/Loogle and grep yielded no existing
statement of this pullback naturality or its presentation type (LeanSearch was
unavailable for the presentation query, recorded as unavailable in the node). The
source modules and declarations were opened and agree with the dependency records.

No mismatch was found. I changed no statement, hypothesis, quantifier, dependency, or
Lean declaration; I only added this independent second-reading record to the report.
