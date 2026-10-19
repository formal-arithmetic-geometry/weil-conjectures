## Worker report

This delivery states `AlgebraicGeometry.Scheme.orientedTripleLimitDescent` in
`lean/Sheaf/Paper/OrientedTripleLimitDescent.lean`. Its proof is `sorry`; every helper has real
data. The statement, proof, dependencies and source of the DAG node are unchanged. Q15's
already merged work is the stage-1 split, not a stage-2 declaration; this delivery uses that
split and does not split the item again. No repair note for this item was present.

The source read is ILO, Exposé XI, proof of Lemma 2.5 and §2.7(2.c), printed pp. 179–180
(PDF pp. 185–186), with the triple-site presentation of §§1.1, 1.6, 1.9 already formalized in
the dependencies. As the reviewed stage-1 report explains, the affine-limit scheme statement
is a concrete elaboration of that localization argument, supported by Stacks 01ZM, 07RP,
09YL and 0A35. The local Stacks statements and their site-colimit proof were read too.

Hypotheses, one by one:

* A small cofiltered category is `(I : Type u) [SmallCategory I] [IsCofiltered I]`.
  In particular the index is nonempty. The index lives in the scheme universe; it is not an
  unrelated universe that could invalidate finite-presentation descent.
* The three inverse systems are `X S Y : I ⥤ Scheme.{u}`. The two compatible structural
  arrows are the natural transformations `f : X ⟶ S` and `g : Y ⟶ S`.
* Qcqs stage schemes are the six families of `CompactSpace` and `QuasiSeparatedSpace`
  instances. Affine transitions are the three families `IsAffineHom (X.map a)`, and similarly
  for S and Y, for every index arrow. There is no finite-presentation assumption on f or g,
  and no cartesian-square or surjectivity assumption on the transition diagrams.
* `[HasLimit X] [HasLimit S] [HasLimit Y]` selects the componentwise limits already named in
  the node. Their structural arrows are the real `limMap f`, `limMap g`; projections are
  `limit.π`. This is an encoding of “let X,S,Y be their componentwise limits”, not an added
  geometric restriction. Existence for the stated systems is supplied by the cited limit
  theorem and initial directed reindexing.
* The size convention is realized by explicit `u` on schemes, `u+1` on small site models
  and their hom types, and `Type (u+1)` for set sheaves. The actual triple categories retain
  their original hom universe u. Equivalences may change hom universe; no equality of those
  universes or extra smallness hypothesis is imposed.

Clause (1):

* The five first conjuncts give qcqs of each limit scheme and of both limit arrows, using
  `CompactSpace`, `QuasiSeparatedSpace`, `QuasiCompact` and `QuasiSeparated` respectively.
* `HasFiniteTripleLimitDescent` states finite-table descent on the dependency's actual
  `FiniteOrientedTripleSite` skeletons. Its `n m : ℕ`, `Z : Fin n → …`, and
  `A : Fin m → Arrow …` describe any finite diagram. It lifts objects, arrows, incidence,
  identity relations and composition relations together. To encode a finite list of longer
  path equations, include each intermediate composite in the finite arrow list. This is
  equivalent to descent of finite diagrams with finitely many specified relations and
  avoids imposing all relations of an infinite presented category. Skeleton equalities
  represent the node's “up to isomorphism”; isomorphic objects of this skeleton are equal.
* Its second conjunct starts with two arrows at a fixed stage whose images under the actual
  projection base change are equal, and supplies `j` and `c : j ⟶ i` where their transition
  images are equal. It does not replace the given cofiltered category by a poset.
* Its third conjunct starts with an arbitrary finite stage family whose limit image belongs
  to the exact finite-composition precoverage, and gives an actual further stage where it
  belongs to that precoverage. Together with finite-table descent this also gives descent
  of any finite limit covering family, including its domain/target identifications.
* `finiteTripleSystemTransition` and `finiteTripleSystemProjection` call the recorded
  `finiteOrientedTripleBaseChange`, with naturality or `limMap_π` providing the squares.
  They introduce no alternative scheme pullback or arbitrary functor.
* `finiteTripleCompositePrecoverage` is the infimum of precoverages containing the recorded
  finite three-type generators and closed under finite indexed composition. This is exactly
  the finite-tree closure of ILO XI 2.5. It is intentionally kept before Grothendieck
  saturation: a finite family generating a covering sieve is not silently substituted for
  membership in the specified pretopology. The helper belongs to this node's site data.

Clause (2), in the conclusion's `Nonempty (OrientedTripleLimitPresentation X S Y f g)`:

* `F : Iᵒᵖ ⥤ Cat.{u+1,u+1}` is the strict diagram of small models. `F.map a.op` is v_a.
  `V : Cocone F` gives C and v_i as its vertex and legs. Functor and cocone laws are the
  requested literal identity/composition/cocone equalities, not just isomorphisms.
* `E i` and `L` identify these categories with the stage and limit finite triple skeletons.
  `P i` and `Q` are their finite precoverages. `stageCovers` and `limitCovers` identify them
  with the precise finite-composition precoverages under these equivalences. The explicit
  `Finite R.uncurry` excludes infinite presieves whose images might collapse under an
  equivalence. Consequently these are site equivalences, not just category equivalences.
* `stageFiniteLimits`, `limitFiniteLimits`, `transitionFiniteLimits`, and
  `projectionFiniteLimits` give the finite limits and their preservation.
  `transitionContinuous` and `projectionContinuous` give continuity;
  `transitionCovers` and `projectionCovers` preserve the specified finite covers.
* `objects : IsColimit (Cat.objects.mapCocone V)` and
  `arrows : IsColimit (Cat.arrows.mapCocone V)` are the actual filtered set-colimit witnesses.
  `transportedCovers` says that a limit presieve covers exactly when it is the transported
  image of a stage covering presieve, with the target equality included. Thus this has the
  defining colimit-site data of `CategoryTheory.exists_colimit_site`.

Clause (3):

* `κ` identifies transitions, and `π` identifies cocone legs, with the actual componentwise
  `orientedTripleBaseChange`, after the specified category realizations. These are natural
  isomorphisms of full triple-valued functors, hence also respect the cross arrows.
* The `identity`, `composition` and `cocone` fields compare their three underlying scheme
  projections simultaneously, in `Scheme × (Scheme × Scheme)`. The displayed maps are
  literally the comparison inverse followed by the three `pullback.fst` maps. These
  equations uniquely characterize the canonical pullback comparison; they do not allow
  an arbitrary noncoherent collection of equivalences. Equality in `Arrow` includes the
  strict source/target transports required by the functor and cocone laws.
* `e`, `l`, `ρ` and `σ` supply the oriented-topos equivalences and identify them with
  restriction on every sheaf and section, along the displayed category realizations.
  The oriented products are the dependency's `Sheaf (orientedEtaleTopology …) (Type (u+1))`.
* `transitionLeftExact` and `projectionLeftExact` assert left exactness of the actual
  `sheafPullback` functors. With their canonical continuous-site adjunctions, these are
  the geometric morphisms defined by v_a and v_i.
* `transitionGeometric` and `projectionGeometric` use
  `HasOrientedTripleGeometricComparison`. They compare these morphisms with any representative
  t of the componentwise scheme-base-change geometric morphism, presented by its direct-image
  restriction formula θ. Existence of t and θ is already in the recorded triple-presentation
  theorem. Quantifying over representatives avoids making a noncanonical choice of adjoints.
* The helper specifies the direct-image comparison δ on EVERY sheaf and section: restrict by
  ρ, apply θ, transport along κ inverse by the contravariant presheaf map, undo ρ', and apply
  the equivalence counit. Thus δ is the induced canonical comparison, not merely an
  existential natural isomorphism with no normalization.
* The inverse-image comparison is the specified `conjugateIsoEquiv` mate of δ, and the final
  equation explicitly identifies the two adjunction units. The coherence fields for κ/π
  make the section formula respect the canonical identity, composition and cocone comparisons
  on direct images. The mate bijection preserves these equations (with its standard
  reversal of direction), giving exactly the node's inverse-image identity/composition
  compatibility. This also includes identity arrows and arbitrary adjunction representatives.

Dependency declarations reused:

* `Sheaf.Paper.QcqsOrientedTriplePresentation`:
  `AlgebraicGeometry.Scheme.FiniteOrientedTripleSite`, `finiteOrientedTripleInclusion`,
  `finiteOrientedTripleGenerators`, `finiteOrientedTripleTopology`,
  `orientedTripleBaseChange`, `finiteOrientedTripleBaseChange`,
  `qcqsOrientedTriplePresentation` and its canonical generator interface.
* `Sheaf.CategoryTheory.Sites.OrientedProductLargeSites` (publicly available through the
  preceding module): `CategoryTheory.OrientedProduct.largeTriples`, `largeGenerators`,
  `largeTopology`, and `universalWithLargeSites`. The `OrientedEtaleTriples` and
  `orientedEtaleTopology` specializations are those of the recorded framework.
* `WeilConjectures.CategoryTheory.ColimitSites`: `CategoryTheory.exists_colimit_site`,
  with its imported `Cat.arrows`, finite precoverage API and filtered category-colimit
  declaration. The authoritative current module was read with `scompile.py --source`.
* Mathlib `CategoryTheory.Limits.pullback`, its `fst`, `snd`, universal property;
  `AlgebraicGeometry.Scheme.Etale`, `smallEtaleTopology`, `smallEtalePretopology`;
  `CategoryTheory.presheafToSheaf`, `sheafificationAdjunction`, and `yonedaEquiv`.
  Both convention dependencies are rendered directly, as their records require.
* The stated proof-dependency modules are imported privately: directed reindexing, affine
  limits, finite etale data descent, separatedness descent, qcqs finitary etale sites,
  pseudofunctor split-family strictification, left-exact site inverse images, and ordinary
  etale inverse-image composition/units. They are the plan for stage 3. The theorem docstring
  follows all twelve DAG proof steps, including the pullback-target encoding of cross arrows
  and explicit type-(c) right pullback, rather than assuming finite presentation of f,g.

Edge cases checked before and during writing:

* The empty index is excluded exactly by `IsCofiltered`, as in the node; empty finite lists
  (`n=m=0`) and empty covering families (`n=0`) remain quantified over.
* A one-object identity system reduces to the same triple site up to its specified model
  equivalence. The coherence equations compare actual projection maps to identities.
* Empty component schemes and nonempty-stage objects with empty limit are allowed. No
  nonemptiness of schemes, surjectivity of transitions, or nonempty family hypothesis appears.
* Identity type-(c) covers and non-surjective type-(c) covers are retained by the recorded
  three-type generators. They are not interpreted as ordinary surjective scheme maps.
* Non-poset cofiltered categories with parallel arrows are retained throughout. The proof
  uses slice equalization and an actual arrow back to the fixed initial stage.
* Structural arrows of arbitrarily large finite-presentation complexity remain allowed;
  cross-arrow descent is over X or Y with a pulled-back etale target.
* Sites keep object/hom universe bounds distinct from the actual triple-site hom universe;
  no equality of scheme-site universes was added.

Searches made for this item (actual `msearch.py` records are retained in `searches.jsonl`):

* LeanFinder: “finite presentation etale triple sites descend along cofiltered affine inverse
  limits with colimit objects arrows and finite covering families” — eight hits, concerning
  affine-transition/global-section descent and `Algebra.Etale.finitePresentation`; none
  states oriented triple-site descent or its colimit/geometric identification.
* Loogle: `CategoryTheory.Cat.objects, CategoryTheory.Cat.arrows,
  AlgebraicGeometry.Scheme.Etale` — no hits; it reports Cat.arrows as unknown because that is
  a project declaration. The actual declaration was then read in the published source.
* Mathlib grep through msearch: `oriented.*[Tt]riple|[Tt]riple.*[Ll]imit`, CategoryTheory — no hits.
* LeanSearch: “Oriented etale triple sites commute with cofiltered inverse limits of qcqs
  schemes with affine transition maps” — eight hits, including ordinary etale topologies,
  affine-transition section descent and filtered-colimit/finite-limit commutation; no match.
* `rg` of the exact item id and `orientedTripleLimit|tripleLimitDescent` in upstream
  `WeilConjectures` and side `lean/Sheaf` found no existing statement. Broader oriented/triple
  searches found the dependency's concrete base-change and finite triple site, which are reused.
* Searches for finite-composition precoverage closure in Mathlib, upstream CategoryTheory,
  side modules and DAG nodes found the finite-composition AXIOM and the recorded three-type
  generators, but no construction of this precise finite-tree precoverage. The same-node
  helper is their lattice-theoretic closure, without a new independent mathematical object.

No statement correction, dependency replacement, new DAG node or disputed statement is used.

## Second reading by Q07

Author's explicit self-check, not an independent review; the maintainer supplies the independent
reading under this dispatch brief. I reopened the DAG statement and matched each hypothesis and
clause against the definitions listed above. The check found and corrected two draft issues:
using finite topological covers instead of membership in the precise finite-composition
precoverage, and failing to require finiteness before mapping a model presieve along an
object-noninjective equivalence. The present `finiteTripleCompositePrecoverage`, `stageCovers`
and `limitCovers` retain both distinctions. I also checked that coherence uses the actual three
scheme projections and that δ is fixed by the section formula and unit mate, including identity
and arbitrary-adjoint cases. All declarations use the recorded notions; no private notation,
local instance, hidden `let` in the theorem signature, auto-bound universe, or extra geometric
hypothesis is present. No mathematical mismatch remains in this reading.

Validation: every delivered module is compiled separately with the prescribed `scompile.py`
wrapper; the final dry run and delivery run invoke the maintainer's preflight and compiler again.
