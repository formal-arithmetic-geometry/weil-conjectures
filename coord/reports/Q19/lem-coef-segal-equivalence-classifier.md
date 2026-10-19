## Worker report

This delivery states `SSet.SegalSpace.segal_equivalence_classifier` in
`lean/Sheaf/AlgebraicTopology/SegalEquivalenceClassifier.lean`. Its sole postponed proof
is that theorem's `sorry`. The helper definitions construct the walking-isomorphism
source and its canonical restriction, evaluation, postcomposition and collapse maps.
Every helper has real data, a source/blueprint docstring and a `lean.declarations` entry.
There are no new nodes, dependency repairs or statement corrections.

On resuming the earlier attempt, I found the published `def-coef-segal-space` module,
which already supplies the strict mapping-fibre and equivalence-arrow notions. I removed
the earlier attempt's six duplicate definitions (`simplexFiber`, `simplexFiberRestriction`,
`identityVertex`, `Composes`, `IsInvertibleEdge`, `equivalenceSubspace`) and reused that
recorded interface. The existing landed nodes `def-coef-segal-space` and
`lem-coef-segal-cartesian-exponent` are added to `stmt_deps`; their node records are
unchanged. The theorem uses the former's two-index encoding, with `Functor.curry` giving
exactly the simplicial-object encoding for the latter's existing cartesian exponential.

Source read: [Rezk, A model for the homotopy theory of homotopy theory](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/rezk-segal-spaces.pdf),
Sections 2.3, 4, 5.1--5.8, Theorem 6.2 and Section 11, including the alternating-word
pushouts and outer-horn lemma. The node agrees with the source. The statement is not
disputed. All seven steps of the node's proof are retained in the theorem docstring,
including the inverse-limit boundary lift in dimension zero.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Small simplicial spaces `V : Δᵒᵖ → sSet` | `V : CategoryTheory.SegalSpace.Space.{u}` is the two-index functor `Δᵒᵖ × Δᵒᵖ ⥤ Type u`. `Functor.curry.obj V` is exactly a functor `Δᵒᵖ ⥤ SSet.{u}`. No direction is discarded. |
| Reedy fibrant with consecutive-edge weak equivalences for every `n ≥ 2` | `CategoryTheory.SegalSpace.IsSegal V` contains both the actual opposite-injective matching-map Kan fibrations and `∀ n, 2 ≤ n → Enhanced.IsWeakHomotopyEquivalence (segalMap V n)`. Its `chains` construction is the strict iterated edge pullback. |
| Objects of `hV` are vertices of `V₀` | The recorded interface uses `(CategoryTheory.SegalSpace.row V ⦋0⦌) _⦋0⦌`, without quotienting the objects or imposing nonemptiness. |
| `M_V(x,y)` is the strict fibre of `(d₁,d₀)` | `CategoryTheory.SegalSpace.mappingSpace V x y` is the actual `pullback (endpoints V) (SSet.const (x,y))`, with `endpoints` the pair of outer faces. |
| Morphisms are `π₀ M_V(x,y)` and identity is `s₀` | The interface's `SameMappingComponent` compares `SSet.π₀.mk` of strict-fibre lifts. Its inverse equations compare the triangle long edges with the actual `σ 0` degeneracies in those fibres. |
| Composition is given by degree-two Segal comparison and `d₁` | `CategoryTheory.SegalSpace.IsEquivalenceArrow` requires two outer triangles whose consecutive edges are the arrow and its inverse; the long edges are compared to identity components. For Segal spaces, the strict degree-two Segal map is a trivial fibration, so these conditions express precisely both inverse equations in `hV`. |
| `V_eq` is the union of components representing isomorphisms | The theorem uses `CategoryTheory.SegalSpace.equivalenceArrows V`, without redefining it. This is the full subcomplex on vertices in components containing `IsEquivalenceArrow` vertices. Its `.ι` is the genuine inclusion into `V₁`. |
| `F(n)` is outer representable, discrete in the inner direction | The recorded `SSet.SegalSpace.discreteRepresentable n` is `stdSimplex.obj ⦋n⦌ ⋙ Functor.const SimplexCategoryᵒᵖ`. |
| `cK` is constant in the outer direction | The recorded `SSet.SegalSpace.constant K` is `(Functor.const SimplexCategoryᵒᵖ).obj K`. |
| Cartesian internal hom has bidegree maps `A × F(n) × cΔ[q] → V` and precomposition operators | The imported `instMonoidalClosed` is Mathlib's complete-functor-category cartesian closed construction. Its adjunction and Yoneda give the displayed formula. `mappingObject A V` is its actual outer-degree-zero simplicial set; `mappingRestriction` is `MonoidalClosed.pre` in that degree. |
| `I[1]` has two objects and exactly one arrow between every ordered pair; `E` is its ordinary nerve discrete inward | Mathlib's `WalkingIso` is `Codiscrete (ULift Bool)`. Its nerve is `SSet.coherentIso`, reused in `walkingIsomorphism` by applying `Functor.const` in the inner direction. |
| `a` selects `0 → 1`, and `e₀,e₁` select the two objects | `walkingArrow` uses the Yoneda map of `coherentIso.hom.edge`; `walkingEndpoint false/true` use those of `coherentIso.x₀/x₁`. Their maps are discretized by whiskering with `Functor.const`. |
| Restriction along `a` lands in `V₁` | `edgeRestriction` composes actual restriction with `representableEvaluation`. Evaluation uses the exponential counit at the identity outer simplex, giving the canonical Yoneda identification with `V₁`. |
| A weak equivalence `ε_V : (V^E)₀ → V_eq` factors that restriction | The family `ε V hV` has exactly this source and target and satisfies `Enhanced.IsWeakHomotopyEquivalence (ε V hV)` and its inclusion composite equals `edgeRestriction (Functor.curry.obj V)`. The weak equivalence includes bijectivity on realization components and every positive based homotopy group. |
| Natural for every map of Segal spaces | For every `f : V ⟶ W`, the supplied `φ` on equivalence subspaces is fixed by its inclusion composite being the degree-one component of `Functor.curry.map f`. The equality `ε V hV ≫ φ = mappingObjectMap ... (Functor.curry.map f) ≫ ε W hW` is the naturality square. Monicity of the inclusions fixes these maps uniquely and gives their identity/composition laws. |
| Over `V₀²`, with endpoints given by restrictions along `e₀,e₁` | Two equalities compose the classifier inclusion with the outer faces `δ 1` and `δ 0`, respectively, and identify them with `endpointRestriction ... false/true`. These are equalities of simplicial maps in all inner degrees. |
| Collapse `E → F(0)` induces `V₀ → (V^E)₀`, and the composite is `s₀` | `collapse` curries the map `E × cV₀ → V` that ignores `E` and applies the outer constant degeneracy. The theorem requires its classifier/inclusion composite to be `(Functor.curry.obj V).map (σ 0).op`. Monicity makes this exactly the claimed identity into `V_eq`. |

The natural family is existentially packaged in a theorem; no definition chooses data
from an unproved mere existence statement. Its inclusion equations uniquely determine
both the classifier and its maps under postcomposition. There are no extra hypotheses.

Dependency signatures and docstrings read and used:

- `Sheaf.CategoryTheory.SegalSpace` (`def-coef-segal-space`): `Space`, `row`,
  `endpoints`, `mappingSpace`, `chains`, `segalMap`, `IsReedyFibrant`, `IsSegal`,
  `SameMappingComponent`, `IsEquivalenceArrow`, and `equivalenceArrows`, all in
  `CategoryTheory.SegalSpace`. This is the canonical strict-fibre interface reused
  directly in the theorem, rather than a second definition of those notions.
- `Sheaf.AlgebraicTopology.SegalCartesianExponent`: `SSet.SegalSpace.SimplicialSpace`,
  `instMonoidalClosed`, `discreteRepresentable`, `constant`, and `cartesian_exponent`.
  Its separate `IsSegal` predicate is not copied or substituted for the canonical
  two-index predicate in this theorem. Currying and the matching definitions give
  the equivalent encoding for the cartesian-exponent proof dependency.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.fullSubcomplex` through
  `equivalenceArrows`, and `SSet.Enhanced.IsWeakHomotopyEquivalence` directly.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `SSet.KanQuillen.right_proper_kan_quillen`, including the boundary-lifting criterion
  with `n=0`, imported for the proof plan.
- `Sheaf.CategoryTheory.ReedyModelStructure`: `HomotopicalAlgebra.Reedy.MatchingIndex`,
  `matchingProjection`, `matchingFrom`, `relativeMatching`, `rightClass`,
  `model_structure`, and `simplex_reedy_structure`. The actual matching maps are used
  by the canonical Segal definition; the module is also imported for the proof plan.
- Mathlib `AlgebraicTopology.SimplicialSet.CoherentIso`: `CategoryTheory.WalkingIso`,
  its `zero`, `one`, `iso`, and `SSet.coherentIso`, `coherentIso.x₀`, `x₁`, `hom`.
  Mathlib `PiZero`: `SSet.π₀`, `π₀.mk`, and `mapπ₀` through the canonical definitions.
  `stdSimplex.objEquiv`, `yonedaEquiv`, `ihom.ev`, `MonoidalClosed.pre`, and
  `MonoidalClosed.curry` construct the actual maps; their source signatures were read.

The other proof dependency, `lem-coef-segal-equivalence-outer-horn`, has no Lean record
or module yet. Its future proof-only import is not invented; its use stays explicit in
the theorem's proof docstring. The downstream `RezkExplicitCompletion` module defines
an entire groupoid resolution, rather than this classifier. It is not imported because
it cites this classifier in its proof plan; the existing Mathlib walking nerve is used.

Edge cases checked from the constructions and binders:

- The empty Segal space is allowed. Both its walking-isomorphism mapping space and
  equivalence subspace are empty; no nonemptiness or chosen base point is assumed.
- Discrete nerves of arbitrary small categories are allowed, including categories
  with noninvertible arrows. Their equivalence subspace selects exactly isomorphisms;
  completeness or groupoidness is not required.
- Both endpoint orders are retained: `δ 1` gives object zero, `δ 0` object one.
  Invertibility requires both triangle equations in the strict endomorphism fibres.
- Components are taken in the entire arrow simplicial set when forming `V_eq`, while
  inverse equations use components in strict mapping fibres. Moving endpoints along
  inner paths therefore does not incorrectly shrink the equivalence subspace.
- All inner dimensions, including zero, are covered. The proof docstring explicitly
  includes boundary lifting in dimension zero and hence component surjectivity.
- `universe u` and every variable are explicitly bound. Currying covers all small
  two-index diagrams and excludes no universe or finite/discrete special case.

Searches, repeated on 2026-10-17:

1. `msearch.py ... leanfinder` with “For a Reedy fibrant Segal simplicial space the
   mapping space from the walking isomorphism classifies the invertible components of
   its space of arrows” returned eight strict-Segal spine and ordinary-nerve results,
   none stating the classifier for Reedy fibrant simplicial spaces.
2. `msearch.py ... loogle '"Segal"'` returned twelve strict-Segal simplicial-set
   declarations. These are not this two-direction weak-equivalence theorem.
3. `msearch.py ... grep 'SegalSpace|[Rr]ezk|coherentIso' AlgebraicTopology` returned six
   references to `CoherentIso.lean` and `NerveCodiscrete.lean`. Their walking nerve is
   reused; neither states this classifier.
4. The earlier recorded LeanSearch query “Segal simplicial spaces mapping space walking
   isomorphism equivalence arrows” returned strict-Segal and ordinary-category results.
   The sandbox `searches.jsonl` records that search and the repeated wrapper searches.
5. Upstream `rg` for `Segal|simplicial space|SimplicialSpace` and grep for the item id
   found no classifier in `WeilConjectures`. Searches of `dag/lean_names_upstream.json`
   likewise found no declaration with the delivered names.
6. Searching `lean/Sheaf` by concept and helper names found the published cartesian
   exponent, the path-model `HomotopySegalSpace`, and the strict-fibre `SegalSpace`.
   I read the latter's full module and DAG record and reused it, removing the earlier
   attempt's duplicate strict-fibre constructions. The homotopy-Segal path model is
   a different notion. `RezkExplicitCompletion` supplies a different downstream theorem.

Validation: the earlier attempt compiled cleanly on 2026-10-17 before duplicate removal.
The revised module compiled cleanly through `scompile.py` as both the sandbox probe
(1.7 seconds) and the actual library path (2.3 seconds), with no errors or warnings.
The signature is verbatim, the declaration inventory is complete, and every Lean line
is at most 100 characters. `deliver2.py --no-push` runs the required server preflight
and repeats per-file compilation. No second-reading section is written by the author;
nothing is pushed.

## Second reading by Q19

I read the item record, Rezk Theorem 6.2 (pp. 14--15), and the proof in Section 11
(pp. 24--27), then matched each introduced object and clause against the delivered
signature.

* The small simplicial space is `V : CategoryTheory.SegalSpace.Space.{u}`; this is
  `Δᵒᵖ × Δᵒᵖ ⥤ Type u`, and `Functor.curry.obj V` is the required simplicial object.
* Reedy fibrancy and all consecutive-edge weak equivalences for `n ≥ 2` are exactly
  `CategoryTheory.SegalSpace.IsSegal V`, whose definition uses the recorded matching
  maps and `segalMap`.
* Vertices, strict mapping fibres, `π₀` mapping components, degeneracy identities,
  degree-two composition, inverse triangles, and the union of equivalence components
  are rendered by the dependency declarations `row`, `mappingSpace`,
  `SameMappingComponent`, `IsEquivalenceArrow`, and `equivalenceArrows`; no private
  replacement is introduced.
* `F(n)`, constant `cK`, the cartesian internal hom, and precomposition are rendered
  by `discreteRepresentable`, `constant`, Mathlib's `ihom`, and `mappingRestriction`.
  `mappingObject` is its actual outer degree-zero simplicial set.
* The walking groupoid `I[1]`, its selected arrow `a`, and endpoints `e₀,e₁` are
  rendered by Mathlib `WalkingIso`/`SSet.coherentIso`, `walkingArrow`, and
  `walkingEndpoint`; `edgeRestriction` and `endpointRestriction` use the canonical
  Yoneda evaluation `representableEvaluation`.
* The existential family `ε` has exactly the source and target in the node, factors
  restriction through `equivalenceArrows`, and is required to be the recorded
  realization-based weak homotopy equivalence. The two endpoint equations are the
  `δ 1`/`δ 0` clauses in the node's order, and the collapse equation is the `σ 0`
  clause. `collapse` is an explicit curry of the constant degeneracy map.
* Naturality quantifies over every pair of Segal spaces and every map `f`; its `φ`
  has the stated inclusion equation and the mapping-object naturality square.

No hypothesis is added: there is no completeness, nonemptiness, chosen vertex, or
finiteness assumption. No conclusion is weakened or strengthened. The empty Segal
space is allowed; `n=0` and all inner degrees are covered by the explicit functor and
SSet binders, and the Kan weak-equivalence convention includes the empty boundary in
dimension zero. Both endpoint orders and both inverse equations remain present.

I searched with `msearch.py` LeanFinder and Loogle, `rg` in Mathlib, the source
`WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`. The searches found
only Mathlib's `SSet.coherentIso` and unrelated strict-Segal, homotopy-Segal, or
categorical-equivalence declarations. The existing `SegalSpace` and
`SegalCartesianExponent` modules were read in full and reused. No exact classifier
exists elsewhere. The two recorded statement dependencies added by the worker,
`def-coef-segal-space` and `lem-coef-segal-cartesian-exponent`, are necessary and their
interfaces match the node; no dependency repair or statement correction is needed.

The only change made in this second reading is this audit section. The module and
signature were already correct; `scompile.py` compiled the module and its sandbox copy
with no errors or warnings other than the permitted theorem `sorry`. The item has no
new nodes, no dependency modules, and no statement change.

## Maintainer review fix (cc reviewer, 2026-10-17)

The delivered helpers `mappingObject`, `mappingObjectMap` and `mappingRestriction` were
definitional copies of the recorded `SSet.SegalSpace.mappingSpace`, `mappingSpacePost` and
`mappingSpacePre` of `lem-coef-simplicial-space-reedy-cartesian`
(`Sheaf.AlgebraicTopology.SimplicialSpaceReedyCartesian`, on the delivery's base). Under H4
the fix removes the three copies, imports that module, and uses the recorded declarations
in the helpers and in the theorem signature. Nothing else changes; the statement says the
same thing. The fixed module compiles cleanly through `nt_compile.py`. The walking-isomorphism
helpers stay: the parallel `SSet.Segal.E`/`intervalArrow`/`endpoint` of
`lem-coef-segal-categorical-equivalence-dk` cannot be imported, because that node's proof
depends on this item, so importing it would make a module cycle in stage 3.
