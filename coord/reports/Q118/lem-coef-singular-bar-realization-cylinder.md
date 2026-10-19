## Worker report

The module `Sheaf.AlgebraicTopology.SpanBarRealizationCylinder` states
`SSet.BousfieldKan.span_realization_cylinder`, with one postponed proof. It defines only
the specialized realized span, its strict transformation, and the prescribed value of
a bar representative. All definition data are explicit; the small commuting-square
proofs in the span transformation follow from existing functoriality and naturality.
No homeomorphism or comparison map is chosen from an unproved existence statement.

Clause-by-clause reading:

- The small simplicial sets are `SSet.{u}`, with an explicitly bound arbitrary universe.
  The ordinary walking span is Mathlib `WalkingSpan`: `left = a`, `zero = c`,
  `right = b`, with `WalkingSpan.Hom.fst` and `.snd` its nonidentity arrows.
- Every strict diagram is quantified as `U : WalkingSpan ⥤ SSet.{u}`. Its bar is
  the dependency's `SSet.BousfieldKan.BK WalkingSpan U`, without a replacement model.
  A simplex `z` has chain `z.1` and initial-object simplex `z.2`.
- `spanRealization U` has objects `|U.obj left|`, `|U.obj right|`, `|U.obj zero|`
  and arrows `toTop.map (U.map fst)` and `toTop.map (U.map snd)`.
- `Space (spanRealization U)` is the existing `Quot (Rel ...)` of the three
  summands `A ⊕ ((C × Set.Icc 0 1) ⊕ B)`, with the stated product, sum, and
  quotient topologies. Its two relation constructors attach 0 by the left arrow
  and 1 by the right arrow. No compact-generation modification is introduced.
- Barycentric coordinates are `s : stdSimplex ℝ (Fin (n.len + 1))`.
  A realization class `[σ,s]` is rendered directly by
  `toTop.map (yonedaEquiv.symm σ) (n.toTopHomeo.symm s)`.
- `spanSimplexValue` matches `z.1.left`. At `a` or `b` it inserts that realization
  class into the corresponding endpoint quotient summand. At `c` it inserts the
  same class into the cylinder. `Eq.ndrec` only transports the initial simplex
  along the matched equality of diagram objects.
- The sum `∑ j, if z.1.obj j = WalkingSpan.zero then s.1 j else 0` is precisely
  `w`. The last object `z.1.right` selects `w/2` for `a`, `1-w/2` for `b`, and
  `1/2` for `c`. `Set.projIcc` bundles these numbers into the interval. This does
  not alter the formula: every summand is nonnegative, and the central sum is
  bounded by the sum of all barycentric coordinates, namely one. Thus `0 ≤ w ≤ 1`,
  all three displayed times lie in `[0,1]`, and `Set.projIcc_of_mem` fixes them.
- The existential family `Ψ` consists of actual homeomorphisms. Its first conjunct
  prescribes the formula on every realization representative, asserting that the
  formula is well defined and gives exactly those homeomorphisms. This is stronger
  than merely supplying an unrelated homeomorphism and equivalent to the node's
  specified formula because realization representatives cover the realization.
- The second conjunct quantifies every strict natural transformation `φ : U ⟶ V`
  and every point of the source realization. The source map is the dependency's
  `bkMap φ`, which preserves the chain and applies the initial component to its
  simplex. The target map is `TopCat.DoubleMappingCylinder.map (spanRealizationMap φ)`:
  the realized components at `a,c,b`, with unchanged interval coordinate. Its
  equality is exactly the naturality square in the node.
- There are no Kan, nonemptiness, injectivity, separation, or connectedness
  hypotheses. The empty cases are included by the unrestricted quantifiers.

Dependency declarations used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: the dependency uses Mathlib's
  `SSet`, `SSet.toTop`, and the ordinary quotient realization convention directly.
  Its full module and recorded cone declaration were read; the cone machinery is
  not needed by this particular topological statement.
- `Sheaf.AlgebraicTopology.BousfieldKanComparisonCalculus`:
  `SSet.BousfieldKan.BKObj`, `BKMap`, `BK`, `bkMapApp`, and `bkMap` provide the
  actual chain-indexed bar and its canonical map. Their signatures and docstrings
  were read, as was the recorded `comparison_calculus` theorem.
- `Sheaf.Topology.DoubleMappingCylinder`: `Span`, `Hom`, `Raw`, `Rel`, `Space`,
  `mk`, `rawMap`, and `map` provide the existing cylinder construction. The landed
  owning node `lem-coef-double-cylinder-weak-equivalence-gluing` is added to
  `stmt_deps`, as allowed for existing landed notions. No dependency is repaired.
  Its dependency closure was checked not to reach this item.
- `Mathlib.AlgebraicTopology.SimplicialSet.TopAdj`: `SimplexCategory.toTopHomeo`
  provides the standard representative-coordinate identification.
- Proof imports are `Sheaf.AlgebraicTopology.RealizationFiniteLimits` and
  `Sheaf.AlgebraicTopology.RealizationCylinder`, corresponding to the two remaining
  recorded proof dependencies. The theorem docstring carries the full four-step
  chain decomposition, formula, inverse-continuity, and naturality proof.

Edge cases checked before writing: degree zero at each of the three objects;
all-central chains give the midpoint; pure endpoint chains give their endpoint;
a mixed `c→a` or `c→b` edge runs from the midpoint to the correct end; zero central
weight attaches by the correct realized arrow; repeated vertices and zero weights
respect the same sum; an empty central value gives the disjoint union of endpoints;
an empty endpoint forces an empty central value by its given arrow; the completely
empty diagram has empty bar and empty cylinder. No new hypothesis is needed.

Searches performed:

- `msearch.py ... leanfinder`: “The geometric realization of a walking span
  Bousfield Kan bar is homeomorphic to its double mapping cylinder”. Eight hits
  concerned abstract model-category cylinders or homological cylinders, no match.
- `msearch.py ... loogle`: `WalkingSpan, SSet.toTop`; no hits (unknown identifier
  `WalkingSpan` in that service).
- `msearch.py ... grep`: `Bousfield.?Kan|double.?mapping.?cylinder` in
  `AlgebraicTopology`; no Mathlib hits.
- `msearch.py ... leansearch`: “Walking span bar construction realization double
  mapping cylinder”; eight hits including `span`, `spanHomMk`, `spanIsoMk`, and
  `WalkingSpan`, but no realization theorem.
- `rg` over the upstream `WeilConjectures`, this project's `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the item id and proposed names found only
  the downstream singular-span module's proof reference. Searches for double
  cylinders found the existing cylinder module, which is reused. The downstream
  singular-span theorem specializes to singular diagrams and a weak-equivalence
  map; it does not state this arbitrary simplicial-diagram homeomorphism and is
  not imported. Its general realization-point and central-weight helper names
  are not redefined: the corresponding expressions are inline in the formula.

The source blueprint file and the item's entire four-step proof were read. The
blueprint paragraph itself gives the derived adjunction rather than the expanded
bar topology argument; that expansion is recorded as agent-origin proof in the
node. No statement correction or mathematical dispute is required.

## Second reading by Q118

A second, sequential reading by the author compared the completed file against the
node (no other agent was started, as required by the dispatch brief). Independent
review is left to the maintainer's delivery review. I rechecked the endpoint order
and affine signs: a mixed left chain uses `w/2`, a mixed right chain uses `1-w/2`,
and a constant central chain uses `1/2`. I also rechecked the actual source of the
quotient relation, which attaches time zero to `f` and time one to `g`. The theorem
uses the precise initial-simplex BK orientation and all strict transformations,
not only objectwise weak equivalences. `projIcc` is harmless by the barycentric
bounds explained above. The first compile exposed a Lean indentation error in
the two commuting-square fields; it was repaired without changing the statement.
The dry run also parsed an unparenthesized realization notation bar as an equation
branch; parenthesizing the homeomorphism type resolved that parser ambiguity without
changing its Lean type. There are no missing hypotheses or clauses, no arbitrary
map assumptions, and no new nodes or dependency modules.
