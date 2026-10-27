## Worker report

The module `Sheaf.CategoryTheory.PostnikovAdditiveExactCouple` states
`DerivedCategory.exists_postnikov_additive_exact_couple`. Its sole postponed proof is
that theorem. All definitions have real data; the structures bundle its existential
witnesses and impose their canonical normalization equations. No object is defined
by choosing from the theorem. No change to the natural-language node is required.

Hypothesis and clause correspondence (the node and the delivered file were read together):

- Arbitrary abelian A and B: independent object and morphism universes `u,v,uB,vB`,
  `[Category.{v} A] [Abelian A] [Category.{vB} B] [Abelian B]`. The derived category
  uses `[HasDerivedCategory.{w} A]` with an independent morphism universe w.
- The standard cohomology, truncations, embedding and shifts are Mathlib's
  `DerivedCategory.homologyFunctor`, `DerivedCategory.TStructure.t.truncLE`,
  `DerivedCategory.singleFunctor`, and `shiftFunctor`. No boundedness, enough
  injectives, Grothendieck or derived-category hypothesis on B has been added.
- The additive homological functor is `(T : DerivedCategory A ⥤ B)
  [T.Additive] [T.IsHomological]`. Its degree-n value is the existing `postnikovValue T n`, the composite of
  `[n]` with T, used by the imported `postnikovD` and `postnikovE`. No arbitrary shift sequence is assumed.
- `postnikovLayer q` is `homologyFunctor A q ⋙ singleFunctor A q`, the usual
  H^q(L)[-q]. Its functor maps are the canonical cohomology maps followed by the
  single-term embedding.
- `PostnikovTriangleData.layerIso` identifies the imported canonical single-degree
  truncation layer `truncGELT q (q+1)` with `postnikovLayer q`. Its
  `layer_normalized` field specifies its H^q map after the canonical quotient
  `triangleLTLTGELT` by the canonical `singleFunctorCompHomologyFunctorIso`.
  This is a conclusion witness, not an added input assumption. The quotient
  induces an isomorphism on H^q, so the normalization determines the comparison.
- `PostnikovCoupleData.couple ρ L` uses the dependency's actual
  `BigradedExactCouple B 0`; hence all three zero composites and exactness
  conditions are present. `dIso/eIso` identify its terms with
  T^{p-ρ+q}(τ≤q L) and T^{p+q-ρ}(H^q(L)[-q]), using the existing canonical truncation
  representative for the latter and `tower.layerIso` for its cohomology comparison. `ρ=0` recovers the node's
  unreindexed objects. Isomorphisms retain the exact objects up to canonical
  categorical comparison, rather than demanding equality of different chosen
  truncations or kernels.
- `alpha_eq`, `g_eq` and `f_eq` use the imported `postnikovAlpha`,
  `postnikovG` and `postnikovF`. These are respectively the canonical next
  truncation inclusion, the quotient of `triangleLTLTGELT`, and its boundary
  followed by the coherent shift comparison. Their bidegrees remain (-1,+1),
  (0,0) and (+2,-1); no independently chosen triangle arrows remain.
- `PostnikovPageData` uses the existing `pageCouple r`, with actual page r+2.
  Its D/E functors are additive. Its `map` is the dependency's `CoupleMorphism`,
  and `mapD/mapE` identify its components with those functor maps.
  `initialD/initialE` specify precisely the truncation/cohomology maps obtained
  by applying T. `image_square/homology_square` characterize each successor
  on the alpha image and the cycles quotient; they rule out independently
  chosen maps on later pages.
- `PostnikovSpectralData.sequence` is a Mathlib `SpectralSequence` starting at
  2 with shape `ComplexShape.up' (r,1-r)`. Its `iso/differential` fields identify
  every term and differential with the exact-couple iteration. `homology`
  identifies cycles via their kernel inclusion and identifies the homology
  projection with `derivedEProjection`; thus its page transition is exactly
  kernel(out)/image(in). Its `naturality` identifies its morphisms with P.map.
  The sequence functor laws give identities and composition; P.E.additive gives
  componentwise addition, which determines addition of page morphisms.
- The initial page identification is `initialPageIso`; `initialPageIso_eq`
  specifies its canonical single-functor coherent shift comparison. The equation
  uses two `singleFunctors.shiftIso`s through degree ρ-p. At ρ=0 this identifies
  T^{p+q}(H^q(L)[-q]) with T^p(H^q(L)[0]), naturally in L.
- `postnikovStable` means the finite cycles and boundaries at the entry are
  eventually constant. `PostnikovStableData` supplies the additive stable-entry
  functor, late-page isomorphisms, their naturality, and their successor
  compatibility with the kernel inclusion and page projection. For any finite
  family of morphisms, a common late page exists by taking a maximum. This
  states the stable-page claim without supposing arbitrary infinite lattice
  operations exist in B.
- `postnikovHalfPlane C ρ` states exactly the two vanishing hypotheses of
  `halfPlaneConvergence`, with an existential integer cutoff for each object.
  Morphisms in its full subcategory are ALL morphisms of the ambient derived
  category, so source and target need not have a common chosen lower bound.
- `PostnikovAbutmentData.limits/colimit` use the recorded `LimitSubobjects` and
  `AlphaColimit`, not a private replacement. `converges` is the recorded
  `ConvergesTo`. `abutmentIso/normalized` identify the canonical abutment with
  D^{0,n} and normalize the degree-zero cocone arrow.
- `abutmentMap_eq` specifies the actual T/truncation map on that abutment.
  `cocone_square` asserts compatibility with EVERY canonical abutment arrow,
  including negative filtration indices. `step/graded` are additive functors,
  with `stepIso/gradedIso` identifying exactly the image filtration subobjects
  and successive cokernels of `imageFiltration`.
- `inclusion/inclusion_eq` give the filtration squares as a natural
  transformation into the canonical additive abutment functor. `quotient` and
  `quotient_eq` specify the canonical quotient map; its naturality therefore
  gives the induced maps on associated graded pieces. Additive functors imply
  preservation of zero, sums, identities and composition on both types of maps.
- `infinity/infinityIso/infinity_natural` specify the stable map on the actual
  limiting cycles modulo boundaries induced by the initial E-map.
  `comparison/comparison_eq` state the canonical stable-page/graded isomorphism
  and its compatibility with `toPageInfinity` and `toGradedPiece`.
  `stableIso/stable_natural/stable_projection` identify sufficiently late pages
  with that same infinite-page map using the canonical cycle-tower projection.
- `H.Transport` quantifies over every integer ρ and total degree n, every
  additive functor F, and every natural isomorphism η from the canonical
  abutment functor to F. It gives the transported inclusions, their image
  filtration, the canonical quotient comparison e, the filtration square, and
  explicit addition equations. The original step and graded functors remain
  the same, hence keep identities and composition. Composing e with
  H.comparison gives the transported stable/graded comparison and its natural
  square. No alternative arbitrary abutment map is substituted.

Dependency declarations inspected and used:

- `Mathlib.CategoryTheory.Abelian.Basic`: `CategoryTheory.Abelian`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `singleFunctor`, `singleFunctors`, shift instances.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`:
  `DerivedCategory.TStructure.t` and its cohomology descriptions.
- `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT`: `truncLE`,
  `truncLEι`, their additivity and universal property.
- `Mathlib.CategoryTheory.Triangulated.HomologicalFunctor`:
  `Functor.IsHomological`, `homologySequenceδ`, its naturality and exactness.
- `WeilConjectures.CategoryTheory.ExactCouple`: `BigradedExactCouple`,
  `derived`, `pageCouple`, `derivedDInclusion`, `derivedEProjection`.
- `WeilConjectures.CategoryTheory.DerivedCoupleFunctoriality`: `CoupleMorphism`
  and `derivedCoupleFunctoriality`; `DerivedCoupleExact`: `derived_couple_exact`
  and `pageCouple_image` (proof imports).
- `WeilConjectures.CategoryTheory.ExactCoupleConvergence`: `CycleBoundaryTower`,
  `LimitSubobjects`, `AlphaColimit`, `imageFiltration`, `toPageInfinity`,
  `toGradedPiece`, `ConvergesTo`; `HalfPlaneConvergence`: `halfPlaneConvergence`.
- `WeilConjectures.CategoryTheory.Abelian.Filtration` and
  `WeilConjectures.CategoryTheory.CanonicalFiltration`: `DecreasingFiltration`,
  `gr` and image filtration operations. The existing convergence API itself
  returns `PBCDecreasingFiltration`, which is used directly for its steps and
  graded pieces; no duplicate filtration structure is introduced.
- `Mathlib.Algebra.Homology.SpectralSequence.Basic`: `SpectralSequence`, its
  morphisms and page cohomology isomorphisms.
- `Sheaf.CategoryTheory.PostnikovFiniteCutoffAbutment`: `DerivedCategory.postnikovValue`,
  `postnikovD`, `postnikovE`, `postnikovAlpha`, `postnikovG`, `postnikovF`.
  The source was read both locally and live with `scompile.py --source`.
  The new definition node `def-per-postnikov-truncation-couple-terms` owns
  these existing declarations and is cited in `stmt_deps`; the finite-cutoff
  theorem is not a statement dependency.
- Proof-only imports also include the recorded `TruncationTriangle` and
  `Sheaf.CategoryTheory.ExactCoupleMorphism`. The live source of the latter was
  read with `scompile.py --source` because its recorded theorem is commented out
  locally; its module imports successfully. The delivered statement needs none
  of that absent theorem's data, and makes no new declaration for it.
- The additive standard-functor dependency is a Mathlib leaf: the truncation,
  homology, single-functor and shift additive instances are already imported.

Edge cases checked mathematically: L=0 and T=0 give zero exact couples and
spectral sequences. L concentrated in degree q0 has a single nonzero initial
row, including negative q0. Every integer p,q is allowed. Zero, identity, and
sums of parallel morphisms are covered by the additive functors. Iteration starts
at r=0 (E2), with differential (+2,-1). The translations allow ρ of either sign
and zero. Source/target half-plane cutoffs are independent. No stable-entry
existence is asserted outside the explicit stabilization subcategory. The zero
abelian category and empty half-plane subcategories cause no extra assumptions.

Searches (2026-10-23):

- `msearch.py ... leanfinder`: “An additive homological functor applied to the
  Postnikov truncation tower defines an additive exact couple and spectral
  sequence natural on filtered abutments”. Eight hits, including the three
  `Functor.homologySequence_exact` lemmas, `shortComplexTruncLE_shortExact`, and
  truncation natural transformations. Ingredients only, no matching theorem.
- `msearch.py ... loogle`: `"BigradedExactCouple", "Additive"`: zero hits.
- `msearch.py ... grep`: `Postnikov|postnikov|[Ee]xact[Cc]ouple` in
  `Algebra/Homology`: zero hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for Postnikov/postnikov and
  exact couples: the existing NaturalTruncationCouple theorem requires
  Grothendieck categories, a bounded-below object, and a left-exact functor
  whose right-derived functor is used. It cannot state this arbitrary
  homological-functor result. Other Postnikov hits concern towers, convergence,
  and finite extension generation, not the full statement here.
- `grep -rn lem-per-postnikov-additive-exact-couple lean/WeilConjectures`:
  no matching declaration. The upstream name index was also searched for
  exact-couple/Postnikov entries. The later immutable-head return identified D/E overlaps with
  `PostnikovFiniteCutoffAbutment`; the repair below supersedes that name-search conclusion.

There is no statement correction, disputed statement, or dependency-record repair.
The new definition ownership node is documented below. The structures are witness bundles belonging
to this theorem's own construction and are all recorded in `lean.declarations`.

## Second reading by Q144

Single-agent rereading, as the launcher's brief explicitly forbids starting
another agent. This is not claimed to be an independent reviewer; the maintainer
will independently review the packet. I reopened the node, the entire module,
and the recorded dependency interfaces. The clause correspondence is above.
The rereading strengthened the spectral-sequence witness from merely comparing
kernels to comparing both the cycles inclusion and the page-homology quotient,
so that the Mathlib page identifications cannot be arbitrary. It also checked
that the initial quotient is normalized on H^q, the boundary uses the coherent
shift comparison, the full half-plane subcategory allows distinct cutoffs, and
transport uses images of η-composed inclusions. `autoImplicit false` forbids
accidental new parameters, and all universe variables are explicitly declared.


## Repair of immutable-head return 929a602c8206

The initial retained-packet dry run passed as commit `cc3248306a1`, but did not
remove the independent review finding. I compared the retained module with the
current main source and read the server's current
`Sheaf.CategoryTheory.PostnikovFiniteCutoffAbutment` using `scompile.py --source`.
The repair retains the packet's theorem and its page, stable, abutment and
transport witness bundles. It removes both duplicate declarations
`DerivedCategory.postnikovD` and `DerivedCategory.postnikovE` and their entries
in `lean.declarations`, and publicly imports their existing owning module.

The existing D-term uses the equal degree expression `p+q-ρ`. The existing
E-term represents H^q(L)[-q] by the canonical single-degree truncation
`truncGELT q (q+1)`, whereas the returned packet used `homologyFunctor A q ⋙
singleFunctor A q`. Reusing it requires an explicit comparison rather than a
rename: `PostnikovTriangleData.layerIso` supplies exactly that natural
isomorphism, and `layer_normalized` fixes it by the canonical quotient's H^q map.
The initial-page normalization first applies this isomorphism and then the same
coherent single-functor shift comparison as before. The canonical inclusion,
quotient and boundary are now reused as `postnikovAlpha`, `postnikovG`, and
`postnikovF`; the previous independently bundled `i/j/k` fields are removed.

The repair adds the already landed owning node to `stmt_deps`, as authorized
by brief-stage2 §5 for reuse requested by a return. No source statement,
hypothesis, page indexing, universe or conclusion changes. In the second reading
I checked the canonical quotient has source `truncLT (q+1) = truncLE q`, the
layer is the same cohomology object up to the normalized natural isomorphism,
and all three exact-couple equations use the existing canonical arrows. The
zero object, negative q and arbitrary integer ρ cases are preserved.

Validation of the repaired module uses only `scompile.py` and `deliver2.py`.
The final dry run checks the rebased packet against the live server. No live
source or launcher file was edited, and no direct Git operation was run.


## New nodes

`def-per-postnikov-truncation-couple-terms` records the six existing declarations
`DerivedCategory.postnikovValue`, `postnikovD`, `postnikovE`, `postnikovAlpha`,
`postnikovG`, and `postnikovF` from
`Sheaf.CategoryTheory.PostnikovFiniteCutoffAbutment`. It has `existing: true`:
no module is added and none of the six declarations is moved or copied.
Its source is Stacks derived.tex Tag 08J5,
`remark-truncation-distinguished-triangle`, with the shifted-value convention
following Tag 0147, `definition-homological`. Those source passages were opened.
The node cites exactly `def-sbc-standard-tstructure-derived-category`,
`def-weil-abstract-derived-category`, and `def-sp-abelian`, as requested by the
immutable-head return. The recorded signatures are extracted verbatim from the
existing file, stopping before `:=`, and the live file was also read with
`scompile.py --source`.

Hypotheses and clauses: A and B are independently sized abelian categories,
with the chosen derived-category localization universe exactly as in the
existing module's section variables. T is any functor: none of the six existing
signatures requires additivity or homologicalness. `postnikovValue T n` is
`shiftFunctor (DerivedCategory A) n ⋙ T`. `postnikovD T r P Q` is the composite
of `truncLE Q` with that value in degree `P+Q-r`. `postnikovE T r P Q` uses
`truncGELT Q (Q+1)`, the single-degree truncation representative.
`postnikovAlpha` applies the shifted value to `natTransTruncLEOfLE Q (Q+1)`
and inserts equality of degrees. `postnikovG` applies it to `mor₂` of
`triangleLTLTGELT Q (Q+1)`. `postnikovF` applies T to the shifted `mor₃`,
composes the canonical `shiftFunctorAdd'` comparison, and identifies `truncLT Q`
with `truncLE (Q-1)`. Thus the bidegrees are precisely (-1,+1), (0,0), (+2,-1).
There is no assertion of exactness in the new definition node. All integers,
including negative r,P,Q,n, are allowed. At r=0 the original indices are
recovered; the arithmetic equalities remain valid when any index is zero.
Zero objects or a zero additive functor give the expected zero terms. Arbitrary
nonadditive T is also allowed by these constructions.

Searches run for this ownership node on 2026-10-23:

- `msearch.py leansearch`, query “Postnikov truncation exact couple shifted
  functor canonical inclusion quotient boundary”: eight hits, the truncate and
  truncation functors and `TStructure.truncGE`; ingredients, no matching node.
- `msearch.py leanfinder`, query “Postnikov truncation exact couple terms
  canonical inclusion quotient boundary”: eight hits on `πTruncGE`,
  `shortComplexTruncLEX₃ToTruncGE`, `truncGE'Map`, and related complex maps;
  ingredients, no exact shifted Postnikov interface.
- `msearch.py grep`, query
  `postnikovValue|postnikovD|postnikovE|postnikovAlpha|postnikovG|postnikovF`:
  zero Mathlib hits. Direct `rg` with the same expression in
  `lean/WeilConjectures` and `lean/Sheaf` found precisely the existing
  `PostnikovFiniteCutoffAbutment` definitions (which this node reuses).
- The DAG search for those names and the proposed node id found only the
  finite-cutoff theorem's record, not a definition node. The whole-blueprint
  search `tools/blueprint_refs.py search Postnikov truncation` found only
  `lem-module-object-postnikov-roos`, a different theorem about condensed
  module objects. The ancestor query returned
  `lem-per-artin-gabber-affine-curve`; the new node's via chain prepends this
  item to its existing via chain.

## Repair of immutable-head return 13478f6f2d3c

H2 is repaired by replacing `lem-per-postnikov-finite-cutoff-abutment` in the
item's `stmt_deps` with `def-per-postnikov-truncation-couple-terms`, whose
`existing: true` attachment owns the exact six already imported definitions.
The theorem is not used or chosen from. No node statement, proof, proof
dependency, or accepted Lean declaration is changed. The Lean module's SHA256
before and after this repair is
`59e011522fdfb9a1144e3a093c0d7fe01306fd812de24656de47f6949d23f91a`.
The historical repair section above describes the prior return; this ownership
repair supersedes its theorem-node dependency assignment.

For the required second reading, I reopened the saved item, the accepted Lean
module, the six existing definitions with their docstrings, and the new node.
I checked the six signatures against the source, the exact dependency set,
the canonical inclusion/quotient/boundary bodies, and the shift arithmetic
`(P-1)+(Q+1)-r=P+Q-r`, `(P+2)+(Q-1)-r=1+(P+Q-r)`.
The new node records the definitions without adding the finite-cutoff theorem's
amplitude or boundedness hypotheses. The item's `lean` record is unchanged,
and its natural-language statement, page indices, layer normalization and
stable/filtration compatibility clauses retain the accepted implementation.
This is a single-agent second reading, as the dispatch brief forbids delegation.

Validation: the initial retained-packet dry run passed at `1d283775611` but did
not resolve H2; it was not pushed. The unchanged Lean module subsequently passed
`scompile.py` in both sandbox and library mode (15.8 s and 8.1 s), with no
unexpected warnings. The repaired-packet dry run passed at `66f6ffecb3e`: both existing-source
checks and the delivered module compile, and preflight reports OK. Final
self-check confirms the item changes only in `lean` and the newly added
definition dependency relative to current main; the six signatures are verbatim,
JSON layout is preserved, and the module hash above is unchanged.
