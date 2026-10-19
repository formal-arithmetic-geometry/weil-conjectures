## Worker report

The module `lean/Sheaf/CategoryTheory/PointwiseEquivalences.lean` states
`SSet.Enhanced.pointwise_equivalences`. It imports the enhanced simplicial-set
conventions and the already stated prism-extension theorem. The theorem uses one
fixed universe `u`, a simplicial set `K`, a quasicategory `C`, diagrams
`F G : K ⟶ C`, an edge `τ` of the internal hom `(ihom K).obj C`, and endpoint
hypotheses identifying its two faces with `diagramVertex F` and
`diagramVertex G`. Its conclusion is the stated equivalence between `τ` being an
`IsEquivalenceEdge` in the internal functor simplicial set and every vertex
component `(evaluation K C k).app _ τ` being an `IsEquivalenceEdge` in `C`.
The proof is `sorry`, as required for stage 2.

The Lean rendering of each hypothesis is:

- “`C` is a quasicategory” is the typeclass binder `[Quasicategory C]`.
- “`F,G : K → C` are diagrams” is `(F G : K ⟶ C)`.
- “`τ` is an edge of `Fun(K,C)`” is
  `(τ : ((ihom K).obj C) _⦋1⦌)`.
- “the endpoints are `F` and `G`” is respectively
  `hτ₁ : ((ihom K).obj C).δ 1 τ = diagramVertex F` and
  `hτ₀ : ((ihom K).obj C).δ 0 τ = diagramVertex G`.
- “`τ` is an equivalence edge” is
  `IsEquivalenceEdge ((ihom K).obj C) τ`.
- “the component at every vertex is an equivalence edge” is
  `∀ k : K _⦋0⦌, IsEquivalenceEdge C ((evaluation K C k).app _ τ)`.

The statement dependency used is `def-cbc-enhanced-diagrams-cones`, via
`Sheaf.CategoryTheory.EnhancedDiagramsCones`; the declarations used are
`SSet.Enhanced.IsEquivalenceEdge`, `diagramVertex`, and `evaluation`. The
stated proof dependency `lem-cbc-invertible-prism-extension` is imported from
`Sheaf.CategoryTheory.InvertiblePrismExtension` as the planned dimension-two
and dimension-three horn extension. The inner-anodyne pushout-product proof
input is the Mathlib match `SSet.innerAnodyneExtensions_pushoutObjObjι'`,
imported from
`Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct`.

I checked the edge cases covered by the statement: an empty `K` makes the
vertex condition vacuous and the internal hom is terminal; `K = Δ⁰` reduces to
the equivalence-edge criterion in `C`; `K = Δ¹` retains the full coherent
transformation rather than independent endpoint choices; discrete targets
force the available components to be identities; and an empty target has no
nonempty diagrams, with the empty-shape case still covered. No finiteness,
nonemptiness, nerve, or invertibility assumption on `K` was added.

Searches for an existing declaration were made as follows:

- `msearch.py ... leanfinder "an edge in a functor quasicategory is an
  equivalence exactly when all vertex components are equivalences"`: returned
  only ordinary nerve and two-truncated homotopy declarations, so no match.
- `msearch.py ... loogle "Quasicategory, IsEquivalenceEdge, evaluation, ihom"`:
  no hits (the service reported `Quasicategory` as unknown).
- `msearch.py ... grep "pointwise|vertex.*equivalence|IsEquivalenceEdge"
  AlgebraicTopology/Quasicategory`: no hits.
- `rg` over `WeilConjectures/` and `lean/Sheaf/` found no declaration named
  `pointwise_equivalences`. It did find the broader
  `SSet.Enhanced.ComponentwiseEquivalence` in
  `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`; that declaration is a
  universal predicate used inside a larger theorem whose proof closure reaches
  this item, and it does not state the endpoint-indexed theorem itself, so it
  cannot be used as an acyclic existing replacement.

No `STATEMENT-DISPUTED` flag or node fault was found.


Recovery checks on 2026-10-17: the shared current node has no `lean` record;
Q27's reviewed split is stage 1 and does not supersede this stage-2 statement.
The saved node differs from the current base only in `lean`. There is no
`coord/repair-notes/lem-coef-infinity-pointwise-equivalences.json`.
The signature record was checked against the file, excluding the proof delimiter,
and the Mathlib pushout-product proof import was added. No statement or DAG
field other than `lean` was changed; there are no new or dependency modules.

Fresh searches repeated during recovery:

- LeanFinder, “An edge in the simplicial internal hom into a quasicategory is an
  equivalence if and only if its evaluation at every vertex is an equivalence”:
  eight hits concerning nerve edges and two-truncated edge homotopy, no match.
- Loogle, `NatTrans.isIso_iff_isIso_app`: no hits; the service reports the short
  identifier unknown. Direct reading of Mathlib `CategoryTheory/NatIso.lean`
  finds `CategoryTheory.NatTrans.isIso_iff_isIso_app`; its binders are ordinary
  functors between ordinary categories, so it does not state the current node.
- LeanSearch, “A natural transformation between coherent diagrams in a
  quasicategory is an equivalence if and only if every vertex component is an
  equivalence”: eight ordinary-category equality/equivalence and bicategory
  transformation hits, no quasicategorical criterion.
- Mathlib grep via `msearch.py`, `pointwise|vertex.*equivalence|IsEquivalenceEdge`
  in `AlgebraicTopology/Quasicategory`: zero hits. Reading
  `Quasicategory/StrictBicategory.lean` and `TwoTruncated.lean` confirms that
  their constructions do not supply the criterion.
- Direct `rg` of `WeilConjectures/` for
  `pointwise_equivalences|pointwiseEquivalence|IsEquivalenceEdge`, and direct
  `grep -rn` for the item id: zero hits. The same name/concept search of
  `lean/Sheaf/` finds the previously noted `ComponentwiseEquivalence` predicate
  and its inclusion in the larger `enhanced_functor_cone_calculus` theorem.
  The predicate asserts no theorem by itself. The larger theorem cannot replace
  this item: its dependency closure contains
  `lem-cbc-enhanced-functor-cone-calculus` →
  `lem-cbc-terminal-boundary-extension` →
  `lem-coef-infinity-right-fibration-fibers` →
  `lem-coef-infinity-isofibration-exponentiation` → this item.

The source was reopened at <https://kerodon.net/tag/01DK>, Theorem the project server:
its arbitrary simplicial indexing set, quasicategory, two diagrams,
transformation, and vertexwise if-and-only-if are exactly those of the node.
A common arbitrary universe `u` is the existing dependency's `SSet.{u}`
convention; it imposes no dimension, cardinality, nonemptiness, or categorical
nerve condition on the indexing simplicial set.

## Earlier second reading (a previous round; superseded)

This is the replacement worker's independent reading of the saved earlier
worker's statement, with the current node and the dependency source open.
The dispatcher's final second reader still owns delivery; nothing was pushed.

I matched every hypothesis and clause again: `(K C : SSet.{u})` gives the
arbitrary simplicial indexing set and target, `[Quasicategory C]` gives exactly
the target horn-filling assumption, `(F G : K ⟶ C)` gives the two diagrams,
and `τ` is an actual degree-one simplex of the existing internal hom.
`δ 1 τ = diagramVertex F` is its source and
`δ 0 τ = diagramVertex G` is its target: the face order is correct.
The left side uses the dependency's two inverse-triangle predicate on `τ`.
On the right, `evaluation K C k` is the existing restriction map, and
`∀ k : K _⦋0⦌` tests exactly all vertices, with the same inverse-triangle
predicate in `C`. Thus the conclusion is the full biconditional, with no
independent choice of pointwise inverse replacing a coherent transformation.

I read the full signatures and docstrings of `IsEquivalenceEdge`,
`diagramVertex`, `evaluation`, and `invertible_prism_extension`, as well as the
Mathlib quasicategory class and pushout-product theorem. The empty-shape,
point-shape, interval-shape and empty-target cases are retained. The declaration
has one explicit universe, no auto-bound implicit, one `sorry` proof, and no
new definition. Its proof docstring follows all five DAG steps: internal-hom
horn filling, evaluation of inverse witnesses, the first triangle by a
2-prism extension, the second triangle for the same inverse by a 3-prism
extension, and the equivalence-edge conclusion.

No mathematical mismatch was found. Recovery fixed the missing proof-dependency
import and the missing review section, and checked the signature record.
`scompile.py NA lem-coef-infinity-pointwise-equivalences <module>` completed
successfully for both its sandbox check and library-path check (1.2 seconds
each), with no errors or non-sorry warnings.

## Second reading by NA

I independently read the node statement against Kerodon Tag 01DK, Theorem the project server. The objects are an arbitrary simplicial set `K`, a quasicategory `C`, two diagrams `F G : K ⟶ C`, and an edge `τ` of the internal hom `((ihom K).obj C)`; the endpoint equalities identify its faces with `diagramVertex F` and `diagramVertex G`. The conclusion is the biconditional that `τ` is an `IsEquivalenceEdge` exactly when every vertex component `(evaluation K C k).app _ τ` is an equivalence edge in `C`. The Lean declaration renders these as `(K C : SSet.{u})`, `[Quasicategory C]`, `(F G : K ⟶ C)`, the degree-one simplex binder, `hτ₁`, `hτ₀`, and the stated biconditional. Every hypothesis and quantifier is present with the same direction and order; no stronger assumptions or weaker conclusions occur.

Edge cases are covered: an empty `K` makes the vertex condition vacuous and leaves the internal-hom statement intact; a point-shaped `K` reduces to the target criterion; `K = Δ¹` retains coherent transformation data; no finiteness or nonemptiness is imposed; and the empty-target situation is not excluded. The single universe `u` is shared by `K` and `C`, matching the enhanced simplicial-set dependency.

I repeated the existing-declaration searches with `msearch.py` (LeanFinder, Loogle, and Mathlib grep) and searched both `WeilConjectures/` and `lean/Sheaf/` using `rg`. Results only concern ordinary natural isomorphisms, nerves, or truncated homotopy; no declaration states this quasicategorical vertexwise criterion. The similarly named `ComponentwiseEquivalence` is a predicate, not this theorem, and using the larger theorem containing it would create a dependency cycle. The dependency declarations `SSet.Enhanced.IsEquivalenceEdge`, `diagramVertex`, and `evaluation` were read and match the node's notions; the prism-extension proof dependency is the stated Kerodon lifting interface.

No mathematical mismatch was found. I repaired the delivery report by adding this required second-reading section. The module already had the required imports, source and blueprint docstrings, explicit universe and `autoImplicit false`, and exactly one postponed theorem proof. The recorded node statement and Lean signature are whitespace-equivalent; no statement or DAG field required changing.
