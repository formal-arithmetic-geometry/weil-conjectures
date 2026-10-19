## Worker report

The delivery states `AlgebraicGeometry.Scheme.qcqsOrientedTriplePresentation` in
`Sheaf.Paper.QcqsOrientedTriplePresentation`. It uses the published full étale triple site;
it constructs its separated finite-presentation full subcategory, actual skeleton, generated
finite-cover topology, componentwise base-change functors and canonical generator map. There
are two postponed theorems, `finiteOrientedTripleBaseChange_mem` and the main statement. All
other declarations have complete data. The helper theorem is the coordinate-membership part
of the item's base-change clause, with its proof documented; its proof is used only to attach
membership certificates to explicitly constructed pullbacks. No object is chosen from an
undetermined existence theorem.

Source read: ILO arXiv:1207.3648, Exposé XI 1.1, 1.3–1.7 and 1.9, and proof of Lemma 2.5,
PDF pages 177–185 (printed pages 171–179). In particular the actual three generators are those
of 1.1, the inverse-image formula is 1.6 (1.a), functoriality is 1.9, and the finite-composite
pretopology argument is on printed page 179. The imported universal-product node and its
large-site interface, all statement-dependency records, and their declarations/docstrings
were read. The ordinary finitary étale-site lemma is a future proof dependency, not an
unstated object needed to type this statement: the restricted triple category is defined
directly inside the published full triples, so no dependency repair is necessary.

Hypotheses and clauses, in order:

- `X S Y : Scheme.{u}` and `[CompactSpace X] [QuasiSeparatedSpace X]`, with the corresponding
  instances for `S,Y`, express precisely the three qcqs schemes. `f : X ⟶ S`, `g : Y ⟶ S`
  have both `[QuasiCompact ...]` and `[QuasiSeparated ...]`, as in the node.
- The full oriented product `P` is `Sheaf (orientedEtaleTopology f g) (Type (u + 1))`. Its
  underlying `OrientedEtaleTriples f g` is the existing comma category
  `OrientedProduct.largeTriples f.Etale g.Etale`. Thus its structural arrows are over the
  named maps `f,g`; no abstract unrelated sites or geometric morphisms are assumed.
- `finiteOrientedTripleProperty` checks all three coordinate structure maps, in order
  `U → X`, `V → S`, `W → Y`. For each it requires `IsSeparated`,
  `LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated`. The coordinates already
  belong to the respective `Scheme.Etale` categories, hence are étale. The four predicates
  use exactly the finite-presentation convention of Stacks 01TP; no absolute separatedness
  is imposed on the schemes.
- `FiniteOrientedTriples` is the full subcategory for that property.
  `FiniteOrientedTripleSite` is its Mathlib `Skeleton`. The explicit functor
  `finiteOrientedTripleInclusion` is `fromSkeleton` followed by the full-subcategory inclusion.
  Objects remain in `Type (u+1)` and morphisms in `Type u`; sets of values are in the containing
  universe `Type (u+1)`. No equality of site-object and site-arrow universes is imposed.
- `IsFiniteOrientedTriplePresentation` first asserts `HasFiniteLimits` of this actual
  skeleton. Its terminal clause supplies a terminal skeleton object whose three coordinates
  are isomorphic in their respective étale categories to `Etale.mk (𝟙 X)`,
  `Etale.mk (𝟙 S)`, `Etale.mk (𝟙 Y)`. The structural arrows are necessarily `f,g` under
  these identifications, since arrows to a terminal étale object are unique. This states
  the specified terminal triple up to its skeleton representative.
- `finiteOrientedTripleGenerators` is a real `Precoverage`: it consists of presieves
  represented by a `Finite I` family whose image is a generating full-site family. The
  reused `largeGenerators` tests the full étale covering condition on the left coordinate
  for (a), on the right for (b), and the singleton/cartesian-square condition for (c).
  With a finite indexing family the first two are precisely finite jointly-surjective
  families. The unchanged coordinates may be isomorphic, as in the published universal
  interface; this is the isomorphism closure and generates the same topology.
  `finiteOrientedTripleTopology` is exactly this precoverage's `toGrothendieck`.
- The finite-refinement clause quantifies over every presieve `R` with covering generated
  sieve. It supplies a finite indexed family `r` whose generated sieve still covers and
  whose arrows lie in `Sieve.generate R`. Membership in that generated sieve says that
  each new arrow factors through an arrow of the original family. Thus it is a finite
  covering refinement, not a claim that every cover is already one elementary generator.
- The existential equivalence `e` goes from full-site sheaves to finite-site sheaves.
  The presheaf-level natural isomorphism in `IsFiniteOrientedTriplePresentation` identifies
  `e.functor` with restriction along the explicit inclusion, after forgetting to presheaves.
  This specifies restriction, not an unconstrained equivalence. Its next natural
  isomorphism identifies every full associated representable restricted by `e` with
  `finiteOrientedTripleAssociated`. Both use the dependency's `largeAssociated`, i.e.
  `uliftYoneda` followed by `presheafToSheaf`; subcanonicity is never assumed.
- The second paragraph is the universal primed-diagram part of the theorem. `X',S',Y'`
  have the same six qcqs instances; `f',g'` have both required morphism properties.
  The maps `a,b,d` have no additional hypotheses. `ha : a ≫ f = f' ≫ b` and
  `hd : d ≫ g = g' ≫ b` express the two specified commuting squares.
- `orientedSquareBaseChangeIso` is the actual comparison of the iterated pullbacks,
  using `MorphismProperty.Over.pullbackComp` and the supplied square equality.
  `orientedTripleBaseChange` is `Comma.map` with these comparisons. Its three coordinates
  are exactly `a.Etale`, `b.Etale`, `d.Etale`, hence the three displayed scheme fibre
  products, with their structural maps retained. `finiteOrientedTripleBaseChange_mem`
  asserts that these objects still satisfy the same coordinate predicate. Its derived
  functor on skeletons, `finiteOrientedTripleBaseChange`, uses the actual full-subcategory
  lift and the specified skeleton equivalences; it makes no arbitrary choice of schemes.
- The geometric morphism named `u` in the conclusion is constrained by a natural
  isomorphism `θ` between its direct image and literal precomposition along that full
  componentwise base-change functor. This is the induced morphism of the two oriented
  topoi. Adjunction uniquely identifies its inverse image with the usual one.
- The canonical generator map is constructed in `orientedGeneratorBaseChangeMap`.
  Start with the identity section of `h_(B Z)`, apply the primed sheafification unit, and
  use `θ.inv` to regard it as a section of the direct image. Transpose it through
  `uliftYonedaEquiv`, the sheafification adjunction and `u.adj`. The main theorem asserts
  `IsIso` for this actual map for every finite-site triple. Thus the claimed canonical
  comparison is specified by its unit, rather than replaced by an arbitrary isomorphism.
  The last two natural isomorphisms state the same generator formula on the full sites
  and after transport through the two restriction equivalences on the finite sites.
  The primed equivalence `e'` satisfies all the same presentation clauses.

Dependency declarations reused:

- `Sheaf.CategoryTheory.Sites.OrientedProductLargeSites`:
  `CategoryTheory.OrientedProduct.largeTriples`, `largeGenerators`, `largeTopology`,
  `largeAssociated`, and the proof interface `universalWithLargeSites`. The last green
  interface has independent object/arrow universes, so it applies to `Scheme.Etale`.
- `Sheaf.Paper.OrientedAffineNeighbourhoodLimit`:
  `AlgebraicGeometry.Scheme.OrientedEtaleTriples`, `orientedEtaleTopology`,
  `orientedEtaleAssociated`; their actual definitions were read and are used unchanged.
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`:
  `CategoryTheory.GeometricMorphism`, with its actual inverse/direct adjunction and
  left-exactness field. It is publicly supplied by the oriented-product dependency.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`, `smallEtalePretopology`,
  `smallEtaleTopology`; `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale`:
  `Scheme.Hom.Etale`, whose object data are the actual pullbacks.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`,
  `toSheafify`, `sheafificationAdjunction`; `Mathlib.CategoryTheory.Yoneda`:
  `uliftYoneda`, `uliftYonedaEquiv`. These realize the sheafification dependency and
  specify the canonical generator map.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  projections and universal maps; `Mathlib.CategoryTheory.MorphismProperty.OverAdjunction`:
  `Over.pullbackComp`. `Mathlib.CategoryTheory.Skeletal`: `Skeleton`, `fromSkeleton`,
  `toSkeletonFunctor`. These supply fibre products and the metatheoretic size convention.
- The recorded scheme-conventions node has no independent definiendum; its Mathlib
  predicates are used directly. The size-convention node likewise has no Lean object.
- The formalized proof dependencies are imported as ordinary imports:
  `Sheaf.CategoryTheory.SiteInverseImageTensor`,
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, and
  `WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`.
  The current composition-unit source was read using `scompile.py --source`.
  Unformalized proof dependencies remain named in the complete seven-step proof docstring.

Edge cases checked against the source and the definitions: empty schemes and empty covering
families (`Finite I` has no `Nonempty I` requirement); non-affine and non-separated qcqs
schemes (the site is not restricted to affine schemes, and each relative identity is
separated); identity diagram maps (the iterated pullback comparisons give the usual identity
identification up to skeleton isomorphism); arbitrary non-étale and non-finite-type `a,b,d`
(their base-change functors and the membership theorem require neither); type-(c) coverings
(the last coordinate is changed by its required cartesian square); sites that are not
subcanonical (all generators are sheafified). No statement correction or dispute is needed.

Searches actually run with `msearch.py` for this item:

- LeanFinder, “The oriented product of etale topoi of quasi compact quasi separated schemes
  has a finite cover triple site and base change pulls back associated representable
  generators”: 8 results, ordinary étale topologies, pullbacks and refinement APIs; no exact
  theorem for this presentation.
- Loogle, `AlgebraicGeometry.Scheme.smallEtaleTopology, CategoryTheory.Skeleton`: 0 results.
- Mathlib grep, `oriented.{0,20}(product|topos|site)|triple.{0,15}site`: 13 results about
  orientations in analysis/geometry, no site theorem.
- LeanSearch, “A separated finite presentation etale triple site presents the oriented
  product topos and associated representables pull back under componentwise scheme base
  change”: 8 results, including étale/separated/quasi-separated base-change instances and
  ordinary small étale topologies; no exact combined statement.
- Direct `rg` in upstream `WeilConjectures`, the side `lean/Sheaf`, and
  `dag/lean_names_upstream.json`, first by the item id and oriented-triple/site phrases,
  then by every new declaration's distinctive names. The existing large triple construction,
  full étale triple aliases and special slice base-change construction were found and read.
  They are reused; none supplies the finite-presentation skeleton and finite-cover theorem.
  No new declaration name collides with the upstream or side library.

Validation: the one delivered module compiled through `scompile.py` with no errors and no
warnings (sandbox and library module checks). Every universe and variable is explicit;
`autoImplicit` is disabled. Both theorem bodies are exactly `by sorry`; the definitions
contain no `sorry`, no arbitrary chosen map and no file-local notation or instance.
The item's JSON is copied from the repository with only `lean` added; all original fields
are unchanged. No new node or dependency-node changes are delivered.

## Second reading by N0

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
