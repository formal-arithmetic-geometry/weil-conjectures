## Worker report

The module `Sheaf.Paper.EtaleHypercoverProduct` states
`AlgebraicGeometry.isEtaleHypercover_prod`, with its only proof `sorry`.
The accompanying definition module supplies the unrestricted all-degree hypercover
predicate missing from the recorded finite-split structure. No statement correction
and no dependency replacement is needed.

Clause-by-clause correspondence:

- The base scheme is `(X : Scheme.{uP})`; quasi-compact and quasi-separated are
  `[CompactSpace X] [QuasiSeparatedSpace X]`.
- The two augmented simplicial objects with terms étale over X are
  `(U V : SimplicialObject X.Etale)`. A functor into schemes over X includes
  its structure maps to X, including the degree-zero augmentation; functor laws
  impose all simplicial identities.
- Their matching maps are étale coverings in every degree: `hU : IsEtaleHypercover U`
  and `hV : IsEtaleHypercover V`. The predicate quantifies over every `n : ℕ`,
  requires compatible matching projections, their universal property on all `T : Over X`,
  and an arrow μ whose composites are exactly the simplex maps. `Surjective μ.left`
  is the covering clause: every arrow of X.Etale is already étale.
- The termwise fibre product W, with induced face and degeneracy maps, is `U ⨯ V`
  in the functor category. Mathlib's functor-category limits are computed pointwise.
  Products in X.Etale are fibre products over X: `Scheme.Etale.forget X` preserves
  finite limits into `Over X`, whose products are scheme pullbacks.
  As with the DAG's chosen fibre product, this uses the standard categorical choice;
  the product universal property fixes the faces and degeneracies.
- W is a simplicial object of the small étale site by the type of `U ⨯ V`;
  the conclusion `IsEtaleHypercover (U ⨯ V)` imposes its matching-cover condition
  in every degree.
- The two termwise projections being morphisms of augmented simplicial schemes is
  already part of the product construction: `prod.fst U V : U ⨯ V ⟶ U` and
  `prod.snd U V : U ⨯ V ⟶ V` are natural transformations in that functor category.
  Their components are the degreewise product projections and commute with every
  simplex map and every structure map to X. Thus there is no separate assertion
  about arbitrary projections, nor an extra hypothesis imposing their naturality.

Dependency declarations read and used:
`Mathlib.AlgebraicGeometry.Sites.Etale`, `Scheme.smallEtaleTopology` and
`Scheme.Etale`; `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
`Scheme.Etale.forget` and its finite-limit-preservation instance;
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `pullback`,
`pullback.fst`, `pullback.snd`, `pullback.lift`, and `pullback.map` (the scheme
fibre products underlying products in the slice);
`Sheaf.Paper.FiniteSplitEtaleHypercover`, `FiniteSplitEtaleHypercover`:
read the complete structure, especially its matching projections and universal property.
That structure cannot be the input type here because it additionally requires splitting
and finiteness. The new predicate uses that exact lower-simplex matching diagram, without
privately redefining schemes, the site, augmented simplicial objects or fibre products.
The conventions dependency is explicitly a convention record without a declaration.
`Mathlib.CategoryTheory.Limits.FunctorCategory.Basic` supplies the product limit
instance and pointwise evaluation of limits.

Edge cases checked before writing: degree zero has no lower simplex, so the universal
property makes M terminal over X, precisely X, and μ the augmentation. Degree one has
two vertices and yields U₀ ×_X U₀. Degenerate lower simplices are included with their
compatibility equations, so the matching diagram imposes no extra independent data.
The empty scheme and empty terms are allowed; no Nonempty, finite, split, or nonzero
condition is introduced. The scheme and test schemes use the same universe, as in the
recorded matching universal property. The qcqs assumptions on X are retained even though
the product argument does not use them.

Searches: `msearch.py leanfinder`, query “The termwise product of two etale simplicial
hypercovers is a hypercover”, returned eight truncated pre-zero/pre-one hypercover
intersection or homotopy results, no all-degree result. `msearch.py loogle`, query
“SimplicialObject, Limits.prod”, returned zero hits, unknown identifier SimplicialObject.
`msearch.py grep`, query `IsHypercover|EtaleHypercover|hypercover.*prod` in CategoryTheory,
returned four comments about coproducts of 0- or 1-hypercovers.
`msearch.py leansearch`, query “etale simplicial hypercover matching objects all degrees”,
was unavailable (Internal Server Error). `msearch.py leanfinder`, query “An etale
simplicial hypercover with matching maps surjective in every degree”, returned eight
truncated hypercover declarations. Direct searches of Mathlib, WeilConjectures, and
lean/Sheaf for `IsEtaleHypercover|isEtaleHypercover_prod` found no declaration.
The upstream node-id grep found no match. Searching the project for matching and
hypercover notions found only the finite-split structure relevant here.
DAG grep and `tools/blueprint_refs.py search hypercover` found the existing finite-split
node and hypercover statements, no definition node for the unrestricted predicate.
`blueprint_refs.py ancestor` identified lem-weil-pbc-hypercover-refinement.

The literature checkout lacks hypercovering.tex on this machine, so read the primary
source at https://stacks.math.columbia.edu/tag/01GI and
https://stacks.math.columbia.edu/tag/01GH, with the hypercover definition at
https://stacks.math.columbia.edu/tag/01G5. The full four-step natural-language proof
from the item's DAG is carried in the theorem docstring.
Both modules compiled together cleanly with lcompile.py. No disputed statement found.

## New nodes

`def-weil-pbc-etale-hypercover` defines `AlgebraicGeometry.IsEtaleHypercover` for an
arbitrary simplicial object in X.Etale. Source: Stacks 01G5 and the matching-scheme
clause of def-weil-pbc-finite-split-hypercover. It packages precisely the existence of
matching objects and surjective canonical matching arrows, with no splitting or finite
summands. The existing finite-split node carries those matching data only as fields of
a stricter structure, and neither Mathlib nor upstream defines the unrestricted
predicate. Its recorded searches are the LeanSearch failure, the LeanFinder truncated
results, and the Mathlib/upstream/Sheaf/DAG grep results above. It adds no axiom or sorry.

## Second reading by K1

Independent second reader: read the base node, both sandbox modules, the new
node, and the signatures and definitions of all four original statement
dependencies. Read Stacks Hypercoverings 01GI, 01GH and 01G5 on the official
site, then fetched hypercovering.tex into the item's scratchpad and read the
corresponding labels, including the surrounding section assumptions.
01GI assumes a site with fibre products; the node specializes it to
representable simplicial objects in the small étale site. No extra source
hypothesis is missing. The node's qcqs restriction is retained.

Object/hypothesis/conclusion inventory and correspondence (all pass):

1. Base X is a scheme, quasi-compact and quasi-separated:
   `(X : Scheme.{uP}) [CompactSpace X] [QuasiSeparatedSpace X]`.
   No Noetherian, separated, field, finite-type or characteristic assumption.
2. U and V are augmented simplicial X-schemes with all terms étale over X:
   `(U V : SimplicialObject X.Etale)`. I opened `Scheme.Etale` in
   Mathlib/AlgebraicGeometry/Morphisms/Etale.lean: its objects are étale
   arrows to X and its arrows are X-morphisms. Thus each structure arrow is
   present, and functoriality gives every simplicial identity. The unique
   augmentation to X is already encoded by these objects and arrows.
3. Every matching map of U and V is a surjective étale morphism:
   `(hU : IsEtaleHypercover U) (hV : IsEtaleHypercover V)`.
   Unfolding the new predicate gives `∀ n : ℕ`, a matching object M,
   compatible projections π, and μ with `μ ≫ π ... = U.map θ.op` and
   `Surjective μ.left`. The instance for every arrow of X.Etale in
   Morphisms/Etale.lean supplies étaleness. Neither μ nor the matching
   projections are arbitrary unconstrained arrows.
4. W has terms U_n ×_X V_n and induced simplicial maps:
   `U ⨯ V`. I read FunctorCategory/Basic.lean's pointwise limit
   construction, `Scheme.Etale.forget` and its finite-limit preservation
   instance, and the recorded `pullback`, projections and universal
   property in Pullback/HasPullback.lean. The categorical product has
   precisely the node's scheme fibre-product terms, up to the canonical
   choice isomorphism, with induced faces and degeneracies.
5. W belongs to the small étale site and has matching covers in every
   degree: its type is `SimplicialObject X.Etale`, and the conclusion is
   `IsEtaleHypercover (U ⨯ V)`. The degree quantifier is unrestricted.
6. Both termwise projections are morphisms of augmented simplicial
   X-schemes: `prod.fst U V` and `prod.snd U V` are morphisms in this
   functor category, hence natural transformations of X-schemes. This
   clause is supplied by the construction itself; no additional existential
   or naturality hypothesis is needed. The theorem docstring records it.

New-node reading: `def-weil-pbc-etale-hypercover` is the representable
specialization of Stacks 01G5, without splitting or degreewise finiteness.
Its Lean is exactly its statement: the lower-simplex diagram runs over
`Δ.len < n` and every `θ : Δ ⟶ SimplexCategory.mk n`; compatibility uses
all maps α between these lower simplices. Its `∃! f` tests all `T : Over X`,
not only étale T, so M is the scheme matching limit. The same diagram and
universal property occur in the landed `FiniteSplitEtaleHypercover`
structure; that structure additionally requires a splitting and finite
nondegenerate summands, so it cannot encode the arbitrary inputs here.
There is no standalone matching predicate there to reuse. The new node's
fields, cited dependencies, chapter/unit, ancestor/via, searches and Lean
record meet the extra-definition-node rule. No dependency replacement
module is included or needed. No statement correction is present or needed.

Edge cases: n = 0 makes the diagram empty; the universal property makes M
terminal in Over X, namely X, and μ is the augmentation. At n = 1 the two
maps [0] → [1] give the two vertex projections, with matching scheme
U_0 ×_X U_0. For higher degrees degenerate maps factor through proper
faces and compatibility forces their values, so they impose no stronger
condition than the matching diagram. Empty X and empty terms are allowed;
an empty term over a nonempty matching scheme correctly fails surjectivity.
There is no empty-index-set exclusion, Nonempty assumption or zero-object
condition. All characteristics are covered. `universe uP` is arbitrary;
test schemes are in the same Scheme universe as X and M, matching the
recorded dependency, without a smaller independent test universe.

Independent searches used different terms from the first reader:
`msearch.py leanfinder "A simplicial object with surjective maps to its
coskeleton in every degree"` returned eight coskeleton/coskeletal results,
including `SimplicialObject.cosk` and `IsCoskeletal`, neither a hypercover
predicate nor this theorem. `msearch.py loogle "CategoryTheory.SimplicialObject"`
returned twelve simplicial-object/truncation/augmentation declarations,
no hypercover theorem. `msearch.py leansearch "The product of hypercoverings
of a site is a hypercovering"` was unavailable (Internal Server Error).
Direct rg searches for coskeleton/cosk/hypercover/matching-object in
Mathlib sites and simplicial objects, WeilConjectures and lean/Sheaf found
only truncated site hypercovers, upstream relative presentations of
0/1-hypercovers, and the landed finite-split structure. DAG searches and
`tools/blueprint_refs.py search hypercover` found no definition of this
unrestricted representable predicate; the semi-representable DAG notions
concern formal families, not the present simplicial schemes. No equivalent
existing declaration or name collision was found. Checked upstream-overlaps
for the relevant names as well.

No mathematical mismatch was found; both Lean modules and node statements
were left unchanged. Only this independent second-reading report was added.
The definition has an explicit Prop-valued body and no sorry. The theorem
has exactly the single named sorry permitted at this stage. Both docstrings
carry their source and blueprint id; the theorem gives the node's four proof
steps with their dependencies. No private copies, local notation, let/show
binders or unbound variables/universes occur. Both node `lean.statement`
strings were checked verbatim against their file signatures. Both modules
compiled together with lcompile.py: exit 0, 1.9 seconds, no warnings.
