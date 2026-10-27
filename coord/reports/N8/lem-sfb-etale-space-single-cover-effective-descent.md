## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleSpaceSingleCoverEffectiveDescent` states the
node in three named theorems, each with `sorry` and a source/proof docstring:
`AlgebraicGeometry.AlgebraicSpace.etaleSpaceSingleCover_effective`,
`AlgebraicGeometry.AlgebraicSpace.etaleSpaceSingleCover_bijective`, and
`AlgebraicGeometry.AlgebraicSpace.etaleSpaceSingleCover_unique`.
The only definition, `singleCoverSheafObject`, embeds a space over the base in the
already defined locally algebraic sheaf category. Its data are `Over.mk f.hom` and
the fibre-product algebraicity proof from the recorded dependency. It chooses no
realization and introduces no new independent notion.

Hypothesis and clause correspondence:

- The base scheme is `{S : Scheme.{u}}`, with an explicit arbitrary universe `u`.
  The base and covering algebraic spaces are `{M U : AlgebraicSpace S}`. The
  category is the dependency's full subcategory of fppf sheaves; no replacement
  definition of an algebraic space is introduced.
- The covering map is `(a : U ⟶ M)`. Its étaleness is
  `ha : MapIsLocally (@Etale) a`, the existing test in all compatible étale scheme
  charts. Its surjectivity is `hsurj : IsJointlySurjective
  (fun _ : Unit ↦ a.hom.hom)`. This means lifting each field-valued representative
  after a field extension, exactly surjectivity on point classes for a singleton.
  It does not mean surjectivity on the sections of every test scheme.
- The local algebraic space and map `v : V → U` are `(D.localObject ()).left` and
  `(D.localObject ()).hom`, with algebraicity `D.local_algebraic ()` supplied by
  the existing `SpaceCoverSheafDescent (fun _ : Unit ↦ a)`. The binder `hv` tests
  this very map with `MapIsLocally (@Etale)`, after bundling its source using the
  supplied algebraicity proof. Conversely every algebraic space `V` and morphism
  `V → U` can be this local object; this encoding restricts neither of them.
- The overlap isomorphism theta is `D.transport` at the universal pair of
  generalized points in the sheaf pullback `U ×_M U`. Its naturality recovers
  transport at every other pair. `D.self` is restriction to the diagonal being
  the identity, and `D.cocycle` is exactly transport 12 followed by transport 23
  equalling transport 13 on the triple pullback. Reverse transport is inverse,
  so this is an isomorphism, not an arbitrary noninvertible map. This is the
  already landed transport-form interface of Tag 0ADT, not a second descent
  datum definition. The singleton `Unit` contains all ordered pairs/triples of
  points of U, not merely pairs of distinct covering indices.
- Effectivity concludes `∃ (N : AlgebraicSpace S) (f : N ⟶ M),
  MapIsLocally (@Etale) f ∧ Nonempty (D ≅ R.obj (singleCoverSheafObject a f))`,
  where R denotes, here in prose only, `spaceCoverSheafRestriction
  (fun _ : Unit ↦ a)`. The restriction's local object is the actual sheaf
  pullback `N ×_M U → U`, with transport preserving the N coordinate.
  The component of the inverse datum isomorphism is the requested display
  `N ×_M U ≅ V` over U. Being a datum isomorphism says precisely that this
  display induces theta. Both existence of N and its chartwise étaleness are
  conclusions; neither is assumed or supplied by a chosen existence theorem.
- The bijectivity theorem quantifies two arbitrary algebraic spaces `N₁,N₂`
  over M with their respective chartwise étale maps `f₁,f₂`. Its function is
  the actual `spaceCoverSheafRestriction.map`. The domain, morphisms between
  `singleCoverSheafObject a f₁` and `singleCoverSheafObject a f₂`, consists of
  all sheaf maps over M; algebraic spaces are a full subcategory of sheaves.
  Its codomain consists of `SpaceCoverSheafDescent.Hom`: precisely maps over U
  commuting with the canonical overlap transports. `Function.Bijective`
  supplies existence and uniqueness of descent of these maps.
- The uniqueness theorem takes the same datum D, both global étale spaces and
  their displayed datum isomorphisms `e₁,e₂`. It asserts `∃! e`, an isomorphism
  over M, with `R.mapIso e = e₁.symm ≪≫ e₂`. This equation is exactly compatibility
  with the two displays. Fullness of the enclosing subcategory means the
  isomorphism is an actual isomorphism of algebraic spaces over M.
- There is no quasi-compactness, finite-type, separatedness, finite presentation,
  nonemptiness, or auxiliary universe-equality hypothesis in any statement.

Dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`; their full definitions were read.
- `def-weil-size-convention`: a metatheoretic convention, rendered by explicit
  `universe u` and the recorded `AlgebraicSpace S` site universe; no declaration
  is available or required.
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace`, `IsAlgebraicSpace`, `IsRepresentableWith`,
  and `IsEtale`. Their signatures/docstrings were read. In particular its
  presheaf `IsEtale` requires representability by schemes and is appropriate
  for charts. It would add a hypothesis to use that predicate for the node's
  arbitrary chartwise étale maps. This delivery uses the existing general chart
  test instead; it does not alter or copy the representable-chart predicate.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`. The recorded `IsEtale` name is a deprecated alias;
  the current `Etale` is the affine-local étale ring map definition read in
  this file, so `@Etale` states precisely the dependency's scheme property.
- `lem-trf-space-fibre-products-etale-covers`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`,
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace`. Its first
  conjunct gives exactly the sheaf pullback algebraicity in the helper. The
  theorem, docstring and other two recorded declarations were read. We do not
  use its stronger representable-étale covering clause for a general chartwise
  étale covering.
- Added the already landed `def-sfb-space-cover-sheaf-descent-categories` to
  stmt_deps: `Sheaf.AlgebraicGeometry.SpaceCoverSheafDescent`,
  `SpaceCoverSheafDescent`, its `Hom`, `IsLocallyAlgebraicSpaceSheaf`,
  `spaceCoverPullbackTransport`, and `spaceCoverSheafRestriction` in namespace
  `AlgebraicGeometry.AlgebraicSpace`. Full signatures and docstrings read.
- Added the already landed `def-sfb-space-morphism-properties`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`,
  `AlgebraicGeometry.AlgebraicSpace.MapIsLocally`, with the existing scheme
  property `@Etale`. Its definition tests all compatible pairs of étale
  scheme charts, exactly as requested by this node.
- Added the already landed `def-trf-algebraic-space-jointly-surjective-family`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`,
  `AlgebraicGeometry.AlgebraicSpace.IsJointlySurjective`, full signature and
  field-extension lifting docstring read. It is publicly exposed through the
  fibre-product module.
- Plain proof imports are the recorded modules
  `Sheaf.AlgebraicGeometry.FppfSpaceDatumSheafRealization` and
  `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`. Their theorem
  statements and docstrings were read. The other two proof dependencies,
  `lem-sfb-fppf-space-atlas-bootstrap` and
  `lem-sfb-representable-fppf-etale-open-descent`, have no Lean record on the
  read base and do not define anything needed in these statements. Their
  future proof imports remain for the maintainer when those nodes are stated.
  No unstated notion needed in this delivery is left missing.

Sources checked directly in the local Stacks source: `bootstrap.tex`,
`lemma-descend-algebraic-space` (0ADV), statement and proof of part (1);
`spaces-descent.tex`, `lemma-descent-data-sheaves` (0ADT), equivalence and proof
of the canonical restriction; `lemma-descending-property-etale` (042B),
statement and proof of fpqc locality. The singleton is countable automatically.
The bootstrap conclusion is an algebraic space, not necessarily a scheme, and
042B descends chartwise étaleness. This is why no scheme-representability of the
arbitrary morphisms is imposed. The node's statement is unchanged.

Edge cases checked: identity cover (self transport gives the same local space),
empty M/U and empty V (no Nonempty assumptions exclude them; the empty-cover
sheaf condition controls sections), disconnected and nonseparated local/global
spaces, non-quasi-compact covers and maps, arbitrary base scheme, and unit index
pairs/triples with repeated points. No finite-type shortcut from 0ADV(2) is used.
No hypotheses are hollow: chartwise étaleness and point-class surjectivity are
actual conditions on a; `hv`, `hf₁`, and `hf₂` are actual conditions on local or
global maps, rather than identity maps forced by construction.

Searches made for an existing statement (actual wrapper calls):

- LeanFinder, query `Pullback gives effective descent of etale algebraic spaces
  along a surjective etale morphism`: eight results, scheme Etale pullbacks,
  scheme flat descent and ring Etale facts; no algebraic-space result.
- Loogle, query `"AlgebraicSpace", "descent"`: zero hits.
- Mathlib grep, query `AlgebraicSpace|Etale.*[Dd]escent|[Dd]escent.*Etale`,
  subdirectory `AlgebraicGeometry`: one hit, the import of ring Etale descent
  in `Morphisms/LocalFlatDescent.lean`; no matching statement.
- LeanSearch, query `Effective descent for etale algebraic spaces under a single
  surjective etale cover`: eight hits, ring Etale facts and scheme etaleTopology;
  none states this node.
- `rg` in `lean/WeilConjectures/AlgebraicGeometry` for descent, and the prescribed
  grep for this item id in `lean/WeilConjectures`: scheme descent files and no
  item match. Read `EffectiveDescent/Basic.lean`; its scheme-level descent
  requires schemes and often quasi-compactness, so it is not this statement.
- `rg` in `lean/Sheaf/AlgebraicGeometry` for effective descent, overlap and
  `spaceCoverSheafRestriction`: found the existing sheaf descent categories and
  sheaf realization theorem, which are reused; also scheme representability
  glue and invertible-module descent, neither equal to this statement.
- Name collision search for `singleCoverSheafObject` and `etaleSpaceSingleCover`
  in `lean/Sheaf`, `lean/WeilConjectures`, and `dag/lean_names_upstream.json`:
  no matches before writing. DAG search for the existing transport category
  identified `def-sfb-space-cover-sheaf-descent-categories`, which is cited;
  no duplicate notion/node was created.

Validation: the required scompile.py command compiled the delivered file both
in sandbox and its library module name, each in about 3.5 seconds. No errors or
warnings were emitted. All variables and universes are explicitly bound, and
`autoImplicit false` is set. Only the three named theorem proofs use `sorry`.
No statement correction, disputed statement, dependency-module repair or new
node is necessary.

## Second reading by N8

This is a separate self-audit of the finished file against the node and Stacks
source, not an independent agent review: the dispatcher explicitly forbids
starting other agents and assigns independent review to the maintainer.

I reopened the node and the module and checked each binder and conclusion.
The potentially significant mismatch was using the representable-chart
`IsEtale` predicate for arbitrary maps of spaces. The finished statement uses
`MapIsLocally (@Etale)` throughout, retaining general algebraic spaces. The
helper only uses the fibre-product closure part of the dependency and imposes
no property on a or f. Checking the datum isomorphism direction shows that its
inverse local component is exactly the displayed `N ×_M U ≅ V`, with the
requested theta rather than an unspecified local isomorphism. Checking
`SpaceCoverSheafDescent.Hom.comm` shows that the bijection's codomain requires
the actual overlap compatibility. Checking `mapIso e = e₁.symm ≪≫ e₂` shows
unique compatibility of realizations, rather than an unmarked uniqueness up
to isomorphism. Singleton transports include every generalized pair/triple,
and all variables and universes remain explicit. No added finiteness or
representability assumption remains. No further change was needed after the
clean server compile.
