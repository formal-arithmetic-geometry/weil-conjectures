## Worker report

This is stage 2, not a reopening of Q91's accepted stage-1 split. The current
coord/brief-stage2.md §0 explicitly permits this handoff. The base node has no
Lean record and coord/queue.tsv lists it in stage 2. No released repair note exists.
The accepted statement, proof, proof dependencies, and stage-1 review are preserved.

The delivery states `AlgebraicGeometry.AlgebraicSpace.fppfSpaceDatumSheafRealization`
in `Sheaf.AlgebraicGeometry.FppfSpaceDatumSheafRealization`. Its only theorem proof is
`sorry`. Its docstring gives the node's nine-step natural-language proof, including
local lifting, the quotient presheaf, sheafification, local isomorphisms, and the two
natural comparisons. Nothing about global algebraicity is asserted.

Hypothesis and clause matching:

- The base scheme is `{S : Scheme.{u}}`. Explicit universes `u w` and `autoImplicit false`
  implement the size convention. The sheaf and algebraic-space universes agree with
  the recorded `AlgebraicSpace S` definition; `I : Type w` is unrestricted, including
  an empty or large index set. No equality of index and scheme universes is imposed.
- `X : AlgebraicSpace S`, `Xᵢ : I → AlgebraicSpace S`, and `a : ∀ i, Xᵢ i ⟶ X`
  give exactly the objects and maps. These are the existing full subcategory of
  fppf sheaves, so their arrows are natural transformations.
- `hflat : ∀ i, MapIsFlat (a i)` and
  `hlfp : ∀ i, MapIsLocallyOfFinitePresentation (a i)` use the published chart-test
  definitions. `MapIsLocally` tests every compatible pair of representable étale
  scheme charts and uses Mathlib `Flat` and `LocallyOfFinitePresentation`.
- `hsurj : IsJointlySurjective (fun i ↦ (a i).hom.hom)` is exactly joint surjectivity
  on field-valued point classes. Its definition lifts any representative after a
  field extension, equivalently the union-of-point-images condition.
- The descent category is `SpaceCoverSheafDescent a`. `localObject i : Over (Xᵢ i).obj`
  and `local_algebraic i` encode algebraic spaces `Vᵢ → Xᵢ`. `transport` is natural on
  every generalized sheaf point with equal base images; `self` and `cocycle` encode
  invertible overlap maps and their triple-overlap cocycle. This is an equivalent
  direct encoding of the stated overlap isomorphisms, not a requirement of extra
  representability or a chosen atlas. On the universal overlap point, transport
  supplies the forward overlap map; reverse transport supplies its inverse. The
  cocycle proves their composites are identities. Conversely, overlap maps induce
  these transports by composition. The identity law follows from the node's
  invertible cocycle on repeated indices, so it adds no hypothesis.
- `SpaceCoverSheafDescent.Hom.map` gives maps over each `Xᵢ`; `Hom.comm` is precisely
  compatibility with overlap maps. Identities and composition are componentwise.
- `IsLocallyAlgebraicSpaceSheaf a` is an `ObjectProperty (Over X.obj)`. Its predicate
  is algebraicity of every `(Over.pullback (a i).hom).obj F`. Its `FullSubcategory`
  therefore gives exactly the stated full category of sheaves over X. It imposes
  no algebraicity on F itself.
- `spaceCoverSheafRestriction a` is the specified canonical functor, constructed
  from Mathlib's actual sheaf pullback, not an arbitrary functor. Its transport
  keeps the F coordinate and changes the covering coordinate using `pullback.lift`.
  Morphisms are `(Over.pullback (a i).hom).map f.hom`.
- The first conjunct `(spaceCoverSheafRestriction a).IsEquivalence` gives the
  equivalence for that precise functor.
- The second conjunct gives, for every datum D, a sheaf F in the full subcategory
  and `Nonempty (D ≅ (spaceCoverSheafRestriction a).obj F)`. A datum isomorphism
  comprises all local isomorphisms and their transport compatibility, hence induces
  exactly the specified transitions. Its orientation is immaterial by inversion.
- The last conjunct is `Function.Bijective` on the functor's actual map between
  the indicated Hom sets. Since the domain is full, this is exactly the desired
  correspondence between sheaf maps over X and compatible local families.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology`; slice topology is `.over S`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsAlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `IsSurjective`. Their full signatures and
  docstrings were read; the sheaf coefficient category is `Type u`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`, with its affine and stalkwise
  interpretation; `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsFlat`, `MapIsLocallyOfFinitePresentation`. The already landed owner node
  `def-sfb-space-morphism-properties` is added to stmt_deps under §5's permission
  for additional landed statement dependencies. This reuses its exact definitions.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`;
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`: `IsJointlySurjective`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`.
  This is the dependency's site component, not an alternative sheaf definition;
  sheaves remain Mathlib `Sheaf` on the recorded fppf topology.
- Proof-only imports retain `Sheaf.CategoryTheory.Sites.SheafificationPlusTheorem`,
  `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`, and Mathlib
  `CategoryTheory.Sites.Sheafification`, as recorded by the proof dependency nodes.
  `lem-sfb-space-fppf-covering-calculus` has no published Lean record, so no import
  for it can yet be added. Its role remains explicit in the proof docstring.
- The new definition module uses Mathlib `Over`, `Over.pullback`, sheaf limits,
  `ObjectProperty.FullSubcategory` and `Limits.pullback.lift`. All construction
  data is explicit; structural category/functor laws are checked proofs.

Sources checked: local `literature/stacks-project/spaces-descent.tex`,
lemma-descent-data-sheaves (Tag 0ADT), statement and entire proof; local
spaces-topologies.tex, definition-fppf-covering (Tag 03Y8). The first source
asserts the displayed equivalence and local identifications. Its separate
algebraicity/effectivity clause (2) is deliberately outside this node's scope.

Edge cases checked before retaining the statements: an identity cover recovers
an ordinary sheaf over X; repeated indices have identity self-transport and
inverse reverse transport; empty local spaces give empty fibres without any
inhabitedness assumption; an empty family forces X to have no field-valued
points, hence to be empty, and the empty-cover sheaf condition handles its
realization and maps. There is no nonempty, finite, quasi-compact, separated,
finite-type, or representability assumption on the covering maps. Generalized
points range over all sheaves in the same coefficient universe, hence include
the universal overlap sheaves and do not make the cocycle vacuous.

Searches: prescribed msearch.py queries (results retained in searches.jsonl):

- LeanFinder: `Fppf descent data of algebraic spaces realized as sheaves equivalence
  of categories` returned 8 generic pseudofunctor stack/descent equivalence results.
- LeanSearch: `Descent data of algebraic spaces over a family of maps and locally
  algebraic fppf sheaves` returned 8 generic pseudofunctor descent results.
- Loogle: `CategoryTheory.DescentData, CategoryTheory.Functor.IsEquivalence` returned
  no hits (unknown unqualified CategoryTheory.DescentData).
- grep: `DescentData|descentData|descent.*[Ee]quiv` in Mathlib CategoryTheory returned
  generic descent interfaces, whose signatures were opened. The generic theorem
  `Pseudofunctor.isEquivalence_toDescentData` assumes a supplied stack and topology;
  it does not construct this algebraic-space cover specialization.
- rg in live `lean/WeilConjectures` and `lean/Sheaf` found no matching
  `SpaceCoverSheafDescent`, `spaceCoverSheafRestriction`, or theorem. The exact
  blueprint-id grep in WeilConjectures also found nothing.
- Searches for descent/sheaf equivalences found `FppfSchemeDataSheafGluing` and
  `FppfSheafRepresentabilityDescentData`; these assume scheme covering members and
  scheme base, so cannot state this algebraic-space cover theorem.
- DAG exact-name searches found no category-definition owner;
  `tools/blueprint_refs.py search 'descent data sheaves'` returned zero blueprint
  nodes. `ancestor` returned None, matching the inherited creation chain, whose
  explicit source anchor is preserved in the new node's `blueprint.from.place`.

No statement correction and no STATEMENT-DISPUTED fault. No dependency records
were replaced. The existing CompactObject example module is withdrawn; its node
now points to the upstream `WeilConjectures.CategoryTheory.CompactObject`, which
was read for the declaration/header convention.

Validation: scompile.py compiled both modules separately in dependency order on
2026-10-23, including private overlay and library-name checks. Exit status 0;
no unexpected warnings or errors. Each source is at most 100 columns. The node
signatures are extracted verbatim from the files, and all variables/universes are
explicit. Delivery dry-run and push results follow in the wrapper output.

## New nodes

`def-sfb-space-cover-sheaf-descent-categories` owns
`Sheaf.AlgebraicGeometry.SpaceCoverSheafDescent`: the descent datum/category,
its compatible maps, the full subcategory of locally algebraic sheaves, the
canonical pullback transport, and canonical restriction functor. These are the
two categories and functor explicitly introduced in Tag 0ADT and needed to state
the item; the theorem does not take them as unspecified input. The definition
uses existing algebraic-space and sheaf definitions. Its search records contain
the raw LeanSearch, LeanFinder and Mathlib grep results and the project/DAG search.
There is no existing exact owner or declaration. Its data contains no sorry and
it postpones no theorem. Its statement and module include no fppf-cover assumption,
since the categories and functor exist for every family; the theorem assumes
the cover properties exactly where the source does. It is cited directly in the
item's stmt_deps. The original stage-1 proof and split are unchanged.

Dry-run schema repair: preflight requires `import_flags`; the new definition node
now has the empty list. No mathematical or module changes were needed.

## Second reading by Q122

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
