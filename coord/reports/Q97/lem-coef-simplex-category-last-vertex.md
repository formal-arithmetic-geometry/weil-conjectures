## Worker report

The node states: (i) a small simplicial set `K`; (ii) its category of simplices `E(K)`,
with objects `([n],x)` and arrows represented by monotone maps carrying the target
simplex to the source simplex; (iii) the nerve `NE(K)`; (iv) for a chain
`([n_0],x_0) -> ... -> ([n_p],x_p)`, the monotone last-vertex map
`v(i)=a_p ... a_{i+1}(n_i)`; (v) the simplex `K(v)x_p`, giving a natural map
`lambda_K : NE(K) -> K`; and (vi) that this map is a weak homotopy equivalence.

The Lean renders these items as follows. `SSet.simplexCategory K` is the canonical
`K.Elementsᵒᵖ`, whose objects and morphisms are exactly the displayed objects and
arrows. `SSet.simplexCategoryLastVertexOrderFun` computes the image of the last
vertex under the chain's arrow to its terminal object, and
`simplexCategoryLastVertexOrder` packages it as an order homomorphism.
`simplexCategoryLastVertexApp` applies `K` to its opposite and to the terminal
simplex; `simplexCategoryLastVertex` packages these degreewise maps. The named
`simplexCategoryLastVertexApp_naturality` theorem supplies all simplicial operators,
and `simplex_category_last_vertex` states
`Enhanced.IsWeakHomotopyEquivalence (simplexCategoryLastVertex K)`.

The dependency declarations are Mathlib's `SSet` (recorded by
`def-weil-pbc-simplicial-set`) and `SSet.KanQuillen.right_proper_kan_quillen` from
`Sheaf.AlgebraicTopology.KanQuillenRightProper`. No dependency module was needed.
The proof docstring records the bisimplicial resolution, the two augmentation
weak equivalences, the diagonal theorem, the maximum homotopy, and two-out-of-three,
including the empty simplicial set and degree zero.

Edge cases checked against the source: `K = ∅` gives an empty category and empty
nerve; `K = Δ⁰` has the expected terminal simplex; `p = 0` gives the identity last
vertex; repeated vertices and omitted final objects are covered by naturality; and
no nonempty, Kan, finiteness, characteristic, or universe-equality hypothesis is
introduced.

Searches for an existing declaration used LeanFinder/LeanSearch/Loogle via the
recorded stage-1 searches, and `rg` over Mathlib, `WeilConjectures/`, and `lean/Sheaf`
for `last vertex`, `category of simplices`, `simplexCategory`, and
`simplex_category_last_vertex`. Mathlib's `SSet.S` is explicitly only a preorder,
while its documentation identifies `K.Elementsᵒᵖ` as the actual category of
simplices; no last-vertex map or weak-equivalence theorem exists. The source tree
also contains no such declaration. Thus the canonical `Elementsᵒᵖ` notion is reused
and only the missing map/theorem are supplied.

## Earlier second reading (a previous round; superseded)

I read the complete node statement and the source place (Kerodon 01N8,
Construction the project server and Corollary the project server) against the module. Every object,
hypothesis, and conclusion listed above is present with the same quantifier order.
The category is the full category of elements with the opposite orientation, not
Mathlib's preorder `SSet.S`; the terminal simplex and the composite arrows have the
source's directions. The formula uses the terminal simplex `x_p` and sends each
chain index to the image of `n_i` under the tail composite. The map is typed as a
simplicial-set morphism, so naturality is exactly the node's naturality clause, and
the theorem's conclusion is precisely the recorded weak homotopy equivalence.

One implementation mismatch was repaired: an initial draft treated the degreewise
formula as a plain function and used the nonexistent field `SimplexCategory.Hom.op`.
It now uses the canonical `Opposite.op` and category morphisms `↾fun`, with the
separate named monotonicity and naturality theorems required by the no-hollow-
definition rule. The category itself was changed to the canonical `K.Elementsᵒᵖ`
interface after checking Mathlib's declaration, avoiding a second definition.
Compilation with `scompile.py` is clean; only the two postponed theorem proofs are
`sorry`. No statement correction, extra hypothesis, or dependency change was made.

## Second reading by Q97

I independently opened the sandbox node, the entire Lean module, both statement
dependency records, their declarations, all three other proof-dependency records
and modules, and the actual category-of-elements and nerve definitions. I read
Kerodon [01NA](https://kerodon.net/tag/01NA), Construction the project server,
[02QS](https://kerodon.net/tag/02QS), Corollary the project server, and their surrounding
subsection [01N8](https://kerodon.net/tag/01N8). This node cites Kerodon, not a
Stacks .tex result. The construction and corollary assume only a simplicial set;
the surrounding discussion introduces no standing Kan or infinity-category
hypothesis on this corollary. The source warning distinguishes this map from the
subdivision last-vertex map.

My object/hypothesis/conclusion checklist, recorded before repairs:

1. A small simplicial set K, without additional hypotheses. Lean: `(K : SSet.{u})`.
   I opened `SSet` in Mathlib's SimplicialSet/Basic.lean: it abbreviates the
   contravariant functor category from SimplexCategory to Type u, as recorded by
   `def-weil-pbc-simplicial-set`. Verdict: exact, no extra instances.
2. E(K) has pairs ([n],x), x in K_n, and **every** monotone arrow a with K(a)y=x.
   Lean: `simplexCategory K := K.Elementsᵒᵖ`. I opened `Functor.Elements` and
   `categoryOfElements`: the sigma type gives precisely these objects, and taking
   the opposite reverses a morphism in SimplexCategoryᵒᵖ to the required ordinal
   arrow. Its subtype condition is exactly K(a)y=x. Identities/composition come
   from Mathlib. Verdict: exact, with all degenerate simplices and all arrows;
   it is not the preorder `SSet.S` or the nondegenerate face poset.
3. NE(K) has p-chains and restriction operators. Lean: `nerve (simplexCategory K)`.
   I opened `CategoryTheory.nerve`: its degree is `ComposableArrows C p`, a functor
   from Fin (p+1), and its map is `whiskerLeft` with the ordinal operator.
   Verdict: exact, including repetitions and deletion of the terminal object.
4. The tail-composite formula v(i)=a_p...a_(i+1)(n_i) is monotone. Lean:
   `simplexCategoryLastVertexOrderFun` applies `(F.map (homOfLE (Fin.le_last i)))`
   to `Fin.last` of the i-th ordinal, using `.unop.val.unop.toOrderHom` for the
   underlying forward arrow. `simplexCategoryLastVertexOrderFun_monotone` states
   the inequality and `simplexCategoryLastVertexOrder` packages it. Verdict: exact.
5. The degreewise output is K(v)x_p and defines a simplicial map. Lean:
   `simplexCategoryLastVertexApp` applies `K.map (Opposite.op
   (SimplexCategory.Hom.mk ...))` to the terminal object's simplex `.unop.2`;
   `simplexCategoryLastVertexApp_naturality` gives every operator square and
   `simplexCategoryLastVertex` assembles the natural transformation. Verdict:
   exact, with no data supplied by sorry or arbitrary choices.
6. The map is natural in arbitrary simplicial maps K→L. This was **missing**:
   operator naturality in item 5 does not express this clause. I added
   `simplexCategoryLastVertex_naturality {K L : SSet.{u}} (f : K ⟶ L)` asserting
   `nerveMap f.mapElements.op ≫ simplexCategoryLastVertex L =
   simplexCategoryLastVertex K ≫ f`. I opened Mathlib's `NatTrans.mapElements`:
   it sends ([n],x) to ([n],f_n x) and preserves the underlying ordinal map.
   Thus no helper category/functor was duplicated. Verdict after repair: exact.
7. For every K, this specified map is a weak homotopy equivalence in the recorded
   sense. Lean: `simplex_category_last_vertex` concludes
   `Enhanced.IsWeakHomotopyEquivalence (simplexCategoryLastVertex K)`. I opened
   `Enhanced.IsWeakHomotopyEquivalence` in EnhancedDiagramsCones: it says
   realization is bijective on path components and on every positive based
   homotopy group, at every point of the realization. KanQuillenRightProper uses
   precisely this predicate in `weakEquivalenceStructure` and its main theorem.
   Verdict: exact, without changing the weak-equivalence convention or quantifiers.

Edge cases: empty K has no objects in K.Elements and no nerve simplices, so all
maps/formulas still type without any inhabitance assumption. For chain degree
p=0, the tail composite is identity and the output is the **last vertex of x₀**,
not x₀ itself when x₀ has positive degree. For an ordinal of length zero,
`Fin.last 0` is its unique vertex. For K=Δ[0], ([0],*) is terminal in E(K);
degenerate higher-dimensional simplices remain present. Degeneracies and omitted
last objects are covered by the universal operator naturality statement; arbitrary
maps, including identities and empty-source maps, by the added naturality theorem.
The category's objects live in Type u and arrows in Type 0; its nerve lies in
SSet.{u}. The universe u is arbitrary, with no site/object equality or independent
smaller test universe. Rings, characteristic, schemes and zero modules play no
role here. The prior report's phrase “p=0 gives the identity last vertex” is
clarified by this check.

Independent searches (2026-10-17), using words different from the first worker:

- `msearch.py ... leanfinder "simplicial replacement category of elements
  augmentation weak equivalence natural transformation"`: eight hits about
  augmented simplicial objects, coskeleta and Cech nerves; none is this map.
- `msearch.py ... loogle '"mapElements"'`: found the existing
  `CategoryTheory.NatTrans.mapElements`, whose source I opened and reused for
  the missing functor on simplex categories; no last-vertex theorem.
- `msearch.py ... leansearch "The natural augmentation from the nerve of
  simplices to a simplicial set commutes with maps"`: face/degeneracy naturality,
  augmented standard simplices and enriched simplicial nerves; no matching map.
- Independent `rg` in Mathlib, WeilConjectures/, lean/Sheaf and the upstream-name
  inventory for last vertex, simplexCategory and category/categories of elements:
  Mathlib's full notion is K.Elementsᵒᵖ; `SSet.S` explicitly warns it is a
  different preorder. The project's subdivision/Ex last-vertex maps have different
  domains (the distinction in Kerodon Warning the project server). The Bousfield--Kan
  comparison cites this node's theorem in its proof rather than declaring it.
  No existing declaration gives the map or statement being delivered. DAG searches
  show the present node already owns this notion, so no new node is appropriate.

Further repairs: the monotonicity theorem lacked its natural-language proof;
I supplied the factorization/last-vertex inequality argument from node step 1.
I made the operator-naturality proof explicit for a general restriction and its
remaining tail. I expanded the main theorem's compressed proof docstring into
all seven node steps, including W's actual initial-ordinal formula, both
augmentations, the two different contractible fibres, both diagonal clauses,
the max homotopies' end-face compatibility, and basepoint paths/two-out-of-three.
I added ordinary (non-public) imports of the three stated proof dependencies
BisimplicialDiagonalEquivalence, NerveNaturalHomotopyEquivalence and
RealizationFiniteLimits; KanQuillenRightProper was already imported. The main
signature and all correct constructions are unchanged. The lean record now lists
the new naturality declaration and copies the main signature verbatim.

No new definition node or dependency module was needed; no statement correction,
target change or citer audit applies. Every theorem remains `by sorry`, as stage 2
requires. The four postponed statements are monotonicity, operator naturality,
naturality in K, and the weak-equivalence conclusion; all are explicit clauses of
this node or its first proof step and carry its source/blueprint docstrings. The
previous-round report's count of two is superseded by this complete inventory.

Validation: `scompile.py Q97 lem-coef-simplex-category-last-vertex` compiled the
only delivered module in both sandbox and library contexts cleanly (1.5 s and
1.6 s), with no errors or warnings. All variables/universes are explicitly bound;
all lines satisfy the 100-character limit. Delivery preflight is run separately
through the prescribed deliver2.py wrapper.
