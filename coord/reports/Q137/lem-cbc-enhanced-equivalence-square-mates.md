## Worker report

The module `Sheaf.CategoryTheory.EnhancedEquivalenceSquareMates` states
`SSet.Enhanced.SquareMates.enhanced_equivalence_square_mates`, with proof `sorry`.
Its helper definitions construct the transformations, three-factor mate, compatibility
map, homotopy fiber, identity and pasted squares, and relative parameter spaces used
in that statement. All data are explicit. The only postponed theorem is the item itself.
The namespace for all new declarations is `SSet.Enhanced.SquareMates`.

Source read: the node's entire statement and five proof steps; the opening of
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/thm-cbc-finite-level-proetale.proof.md`.
The blueprint opening supplies transport context, rather than an independent proof of
this generic mate theorem; the module preserves the node's agent-extracted attribution.
The node is not a blueprint unit statement. No mathematical statement correction is made.

Hypotheses and clauses, in their order in the node:

| Node text | Lean rendering |
| --- | --- |
| Fixed simplicial/enhanced size convention | Explicit `universe u`, `SSet.{u}`, and `set_option autoImplicit false`. All categories range over arbitrary simplicial sets in that universe; their enhanced-category condition is `[Quasicategory ...]`. |
| Four enhanced categories | The four `A B A' B' : SSet.{u}` binders and four Quasicategory instances in the main square assertion. |
| Specified adjoint equivalences L, R and L', R' | `e : AdjointEquivalence A B` and `e' : AdjointEquivalence A' B'`. The structure's `left` and `right` are actual simplicial maps. |
| Specified natural-equivalence units and counits | `unit : transformations (𝟙 A) (left ≫ right)` and `counit : transformations (right ≫ left) (𝟙 B)`, in degree zero; `unit_equivalence` and `counit_equivalence` use the dependency's `IsEquivalenceEdge`. This retains inverse edges and both inverse-triangle witnesses existentially, exactly as the dependency's definition does. |
| Both specified coherent adjunction triangles | `leftTriangle` and `rightTriangle` are actual degree-two simplices in the appropriate functor simplicial sets. Their three face equations specify the whiskered unit, whiskered counit, and degenerate identity edge. They are not equations merely in a homotopy category. |
| U, V arbitrary coherent functors | `Square.upper : B ⟶ B'` and `Square.lower : A ⟶ A'`. Neither field has an equivalence condition. |
| Specified alpha : L' V ≃ U L | `Square.comparison : (transformations (lower ≫ e'.left) (e.left ≫ upper)) _⦋0⦌`, together with `comparison_equivalence`. Lean composition is in traversal order, opposite the node's right-to-left displayed notation. |
| The displayed formula for theta | `mate c e e' s` first whiskers `e'.unit` by `e.right ≫ s.lower`, then `s.comparison` by `e.right` and `e'.right`, then `e.counit` by `s.upper ≫ e'.right`. Nested `compose` applies these in that order. Its endpoints are `e.right ≫ s.lower` and `s.upper ≫ e'.right`. |
| Theta is a coherent natural equivalence | `IsEquivalenceEdge ((ihom B).obj A') (mate c e e' s).1`. |
| Apply L', then postcompose with epsilon' U | `compatibilityMap` is `whisker (𝟙 B) e'.left ...`, followed by pairing with the constant vertex `epsilon' U`, then genuine composition in `Fun(B,B')`. Its codomain is `transformations (e.right ≫ s.lower ≫ e'.left) s.upper`. |
| Specified right side U epsilon after alpha R | `compatibilityTarget` composes the whiskered `s.comparison` first and the whiskered `e.counit` second, in the same codomain. |
| The compatibility space means the specified homotopy fiber | `compatibleMates` is exactly the dependency's `homotopyFiber (compatibilityMap ...) (compatibilityTarget ...)`. Its simplices retain the entire compatibility path and all its higher simplices. |
| That space is contractible | `KanComplex (compatibleMates ...) ∧ IsContractible (compatibleMates ...)`; `IsContractible` is the dependency's realization weak-contractibility convention, including nonemptiness via components. |
| Formula plus its mate homotopy is a point | An existential `p` in degree zero of `compatibleMates` with `(mateProjection ...).app _ p = mate ...`. The first coordinate is constrained to the formula; the second coordinate is its actual compatibility path. |
| Identity square and identity of R | `identitySquare e` uses identity U, V and the degenerate identity comparison on L. The identity clause supplies `p q` in this SAME compatibility fiber, projecting to the formula and `identity e.right`, with `Nonempty (Path p q)`. |
| Second square and third adjoint equivalence | The six-category clause binds `e e' e''`, `s : Square e e'`, and `t : Square e' e''`, all six Quasicategory instances. |
| Pasted upper comparison alpha'' = U' alpha after alpha' V | `pastedComparison` first whiskers `t.comparison` by `s.lower`, then `s.comparison` by `t.upper`. The existential `h` proves this actual composite is an equivalence; `paste ... h` supplies the resulting square. It is not an extra hypothesis. |
| Lower pasting theta' U after V' theta | `pastedMate` first post-whiskers `mate ... s` by `t.lower`, then pre-whiskers `mate ... t` by `s.upper`. The two points `p q` project to the pasted-square formula and this explicit pasted mate, and `Path p q` lives in their common compatibility fiber. |
| All finite strings, including units | `n : ℕ`, category families on `Fin (n+1)`, and `Intervals n` include every pair i ≤ j, including zero-length intervals. `finiteMates` is the product of the actual interval compatibility spaces, retaining all witnesses. Composite squares are permitted among `s`; allowing arbitrary interval squares also covers these specified composites. |
| All associativity and higher comparisons relative to earlier comparisons | `RelativeExtensions (finiteMates ...)` quantifies every parameter simplicial set K, every boundary dimension r, and EVERY boundary map. The extension equation fixes the entire boundary. Dimension zero provides choices, dimension one compares them, dimension two fills associativity boundaries, and all higher dimensions retain the already prescribed lower faces. The identity and binary-pasting points from the preceding clauses can be used in these boundaries. |
| Naturality in coherent parameter families, with varying targets | `finitePaths` and `finiteProjection` are the products of the dependency's actual mapping-path replacements and their final-endpoint projections. `RelativeLifts (finiteProjection ...)` accepts an arbitrary varying target `b : K ⊗ Δ[r] ⟶ finiteTargets ...` and a prescribed boundary lift a over it; the extension t must satisfy both exact boundary restriction and `t ≫ finiteProjection ... = b`. Thus the target family in proof step 5 is not frozen at a vertex. The categorical assertions also apply with the target categories themselves functor categories, so parameter-dependent U, V and alpha can be treated as coherent functors and transformations into these functor categories. No invertibility is imposed on parameter arrows. |

Composition is auxiliary presentation data, not an additional input hypothesis.
The theorem begins `∃ c : Calculus, c.Valid ∧ ...`. `Composition.Valid` says that its
sections are sections of the actual spine restrictions, that its pinch comparison
has the canonical prism formula in every degree, and that its unpinch is a homotopy
inverse. `Composition.comp` is the long edge of that spine composition transported
between the two mapping-space models. It is not an unconstrained operation.
The coherent-composition assertion is included for all the functor categories used;
all higher comparisons retain relative boundary data rather than asserting strict
associativity of a chosen binary operation. No object is chosen from a mere
unproved existence theorem. The proofs inside `identity` and `identitySquare` only
verify the simplicial laws required by their explicitly degenerate data.

Dependencies read and reused:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.mappingSpace`,
  `mappingSpaceMap`, `diagramVertex`, `IsEquivalenceEdge`, `homotopyFiber`,
  `commaSubcomplex`, and `IsContractible`. The entire dependency module and
  docstrings were read; no private replacement of its enhanced notions is introduced.
- `Sheaf.CategoryTheory.SimplicialCompositionSpine`: `SpineSectionFamily`,
  `spineRestriction`, `spineComposition`, `AreSpineHomotopyInverses`,
  `HasCoherentComposition`, and `simplicial_composition_spine`.
  Its public import `Sheaf.CategoryTheory.RightPinchComparison` supplies
  `arrowMappingSpace`, `arrowMappingSpaceInclusion` and `rightPinchPrism`.
- `Sheaf.AlgebraicTopology.KanFibrationFiberCriterion`: `mappingPath`,
  `mappingPathProjection` and `kan_fibration_fiber_criterion`.
- `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`, proof-only import:
  `enhanced_functor_cone_calculus` with its Quasicategory, Kan mapping-space and
  functor-equivalence assertions.
- Mathlib's `ihom`, simplicial standard simplices and boundaries, categorical
  products, `MonoidalClosed.pre`, and simplicial face/degeneracy identities.

The item's `stmt_deps` gains the already recorded
`lem-cbc-simplicial-composition-spine` and
`lem-cbc-kan-fibration-fiber-criterion`, because the statement interface uses their
composition and mapping-path constructions. There are no new nodes or dependency
repairs. The statement, proof and proof-dependency fields are unchanged.

Edge cases checked: empty quasicategories (an adjoint equivalence still requires
actual maps; functor identities remain valid); nerves of ordinary categories, where
the formula reduces to ordinary mates and their unique counit-compatible value;
noninvertible vertical U and V; identity U, V and alpha; a string of length zero;
zero-length intervals; r = 0 with empty boundary, so existence is not vacuous;
r = 1 with prescribed endpoints; r = 2 with prescribed compatibility boundary;
empty and nonempty parameter K; arbitrary u without identifying two independent
site universes or restricting to ordinary categories. Composition auxiliary choices
are quantified existentially, never required of the user.

Searches retained from the interrupted turn in `searches.jsonl`:

- `msearch.py ... leanfinder`: “Coherent mates of squares along enhanced equivalences
  contractible space of counit compatible transformations and higher pasting”.
  Eight hits headed by `CategoryTheory.mateEquiv_square`, the bicategorical analogue,
  and `CategoryTheory.mateEquiv`; no enhanced mapping-space statement.
- `msearch.py ... loogle`: `"mateEquiv"`. Twelve ordinary mate-correspondence hits.
- `msearch.py ... grep`: `mateEquiv|[Mm]ate|[Aa]djointEquivalence` in
  `CategoryTheory/Adjunction`; hits in `Mates.lean`, `Basic.lean`, etc.
- `msearch.py ... leansearch`: “Homotopy coherent adjoint equivalence mates with
  contractible fibers of counit compatibility”. Eight ordinary/bicategorical hits.
- Read Mathlib `CategoryTheory/Adjunction/Mates.lean`, including the full
  `mateEquiv` definition, counit compatibility and vertical composition signature;
  read the corresponding bicategorical signatures in `Bicategory/Adjunction/Mate.lean`.
  These concern ordinary 2-cells, with no contractible enhanced transformation
  fiber or all higher relative comparisons, so none states this node.
- `rg` in upstream `WeilConjectures` and side `lean/Sheaf/CategoryTheory` for mate
  and adjoint-equivalence names found ordinary derived/base-change mate modules.
  Their categories and conclusions differ from this node's quasicategories.
- Exact `SquareMates`/`EnhancedEquivalenceSquareMates` searches in upstream,
  `dag/lean_names_upstream.json`, and the side library found no existing declaration.
  Exact node-id grep in upstream found none. Searches for `RelativeLifts` and
  `RelativeExtensions` in Mathlib, upstream and the side library found no competing
  declaration. The owning-node namespace prevents collision with generic helper names.

Validation uses only the prescribed `scompile.py` wrapper, one file at a time.
The first recovered draft compiled cleanly. The added varying-target projection
initially resolved `Pi.map` as the function operation; it was replaced by the
explicit categorical `Pi.lift` of each product projection followed by
`mappingPathProjection`, preserving the intended canonical map. Final validation
and the required delivery dry run are recorded by the delivery tool.

## Second reading by Q137

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
