## Worker report

Item: `lem-coef-operadic-active-incidence-comparison`, stage 2, group N7.
Module: `Sheaf.CategoryTheory.OperadicActiveIncidenceComparison`.
Main declaration: `SSet.Enhanced.Operadic.operadic_active_incidence_comparison`.
One theorem is postponed, with the entire five-step DAG proof in its docstring. Every
helper is an explicit definition, abbreviation or predicate; no construction chooses
an unspecified object from an unproved existence theorem. Only the item's `lean`
field changes. There are no new nodes, dependency repairs or statement corrections.

Read the complete item statement, source, proof and all four statement dependencies,
their recorded declarations and source docstrings. Also read the relevant proof
interfaces. The source comparison was checked against Higher Algebra, proof of
Theorem the project server(1), printed pp. 336–337
(https://people.math.harvard.edu/~lurie/papers/HA.pdf), and Gepner–Haugseng,
Definitions A.3.1–A.3.3 and Theorem A.3.4(2)
(https://arxiv.org/html/1312.3178v4). The generalized nonsymmetric formulation retains
the endpoint incidence data and the explicitly required global stationary lifts.

### Hypotheses and objects

- Small family over `Delta^op × Delta^n`: `P : Operadic.Family (Δ[n] : SSet.{u})`.
  This is the dependency's actual categorical fibration and relative incidence-limit
  structure, not a private replacement operad. `hn : 1 ≤ n` is the stated bound.
- Constancy over arity zero on every parameter edge: `hconstant : HasConstantZeroEdges P`.
  `familyZeroProjection` is the restriction to the actual arity-zero fibre;
  `edgeZeroProjection P a` is its actual pullback to the edge `a`. Each such projection
  is a cocartesian fibration, with an actual transport cylinder and equivalence of
  its endpoint fibres. Cocartesianness here is tested inside that edge restriction,
  just as in `IsConstantOverZero`; it is not silently promoted to the whole family.
- Space zero-fibres: `hzero` asks for `KanComplex (fiber (familyZeroProjection P) z)`
  at every parameter vertex. These are spaces, not sets or discrete fibres.
- Stationary inert lifts globally cocartesian: `hglobal : HasGlobalStationaryInert P`.
  Every fibrewise inert edge is tested for `IsCocartesianEdge` under the full product
  projection `lift P.operadicBase P.parameter`. The formulation is independent of
  chosen inert lifts: any two fibrewise cocartesian lifts of the same arrow are
  equivalent, so requiring the property for all of them expresses the stated lift
  condition without adding chosen data.
- `A = P_0`: `initialFamily P` is the dependency's strict parameter fibre at zero;
  `initialProjection P` is its operadic projection.
- `b in P_t`, with `t>0`: the first conjunct quantifies `t : Fin (n+1)`, `ht : 0<t.val`,
  `b : P.M _⦋0⦌`, and fixes its parameter and arity by the two displayed equalities.
- `b_i` are any chosen consecutive inert restrictions: `bs` and `es` specify actual
  fibre edges, both endpoints, their base maps `monoidalRho i`, and cocartesianness
  in the fibre. The full-family condition is supplied by `hglobal`.
- `J_b`: `familyActiveSlice P b` is the active full subcomplex of the actual pullback
  `A ×_P joinSlice (const b)`. `familyActiveSource` and `familyActiveToSlice` are its
  literal source evaluation and complete fixed-target join simplex. For an active
  target diagram, the triangle endpoint calculation in proof step 2 ensures that
  source-change edges between active cones are themselves active. Thus using a full
  subcomplex gives exactly the node's wide-active slice, not extra source arrows.
- `sigma : Delta^d -> P_{1,...,n}`: `σ : Δ[d] ⟶ P.M` with the vertexwise positive-
  parameter condition in the second conjunct. Since the parameter target is the
  nerve of the ordinal, this is exactly factorization through its final full face.
  `IsActiveDiagram P.operadicBase σ` is the recorded activity condition.
- `X_sigma`: `familySourceComma P σ` is `A ×_P joinSlice σ`. Its second projection
  keeps the complete map `Δ[k] ⋆ Δ[d] -> P`, and its first projection evaluates source.
- `X_sigma^a`: `activeFamilyComma P σ` tests `firstMixedEdge` at every source vertex.
  That edge is the restriction of the complete join extension to the source vertex
  and the first vertex of `σ`. This is exactly all mixed edges specified by the node;
  the full-subcomplex construction supplies the corresponding condition in every degree.

### Conclusions

- (i), cutting equivalence: existential maps `R i : J_b -> J_(bs i)` satisfy
  `IsFunctorEquivalence (Pi.lift R)`. This is a quasicategorical equivalence, with
  coherent inverse equivalences, to the degreewise product, including its empty case.
- The maps are the cutting maps: `IsFamilyCut` specifies `c`, `cs i` by the complete
  canonical induced-cone formula `IsFamilyActiveCone` in every degree. `H i` is a
  coherent transformation from `c` to the pulled-back `cs i`. Its apex is exactly
  `es i`, and its source boundary is `L i` in `A`. The endpoints of `L i` are exactly
  the original source diagram and `R i` followed by the factor source diagram.
  Its edges are stationary inert edges. These conditions force the square of active
  arrows to be the original arrow factored through the specified inert restrictions;
  an unrelated product equivalence cannot satisfy this interface.
- Ordered concatenation including the base map: `HasOrderedCutBases` writes the
  source length as `m = sum_i ms i`, fixes the arity of each factor, and fixes every
  source inert map to the interval starting at `sum_(a<i) ms a` with length `ms i`.
  The cylinders and the `R i` are simplicial maps, so their naturality retains all
  source-change arrows, not merely this vertex normalization. The base is the nerve
  of a category, so these natural block maps fix the entire base diagram.
- Every inert-preserving `F : A -> V^tensor`: `IsInitialInertFunctor P q F` fixes its
  base and preserves the recorded inert edges. The first universal coefficient
  clause says these same source cylinders become monoidal inert cylinders under F.
  Together with their exact ordered base maps this is precisely the Segal-coordinate
  characterization of concatenation of the factor source diagrams.
- Induced cones whenever their specified projections are preserved: the second
  coefficient clause quantifies every `G : P.M -> V` over the base and assumes
  preservation only of the actual source cut edges and the chosen `es i`. It
  concludes that every edge of the complete cone cylinders `H i` becomes monoidal
  inert. The endpoints and all higher coherences of these cylinders were fixed by
  `IsFamilyCut`. In particular it does not impose preservation of all family inert
  edges, nor introduce a colimit assumption. This gives exactly the induced cone
  identification, including transformations of cones.
- Common endpoints: the construction uses whole simplices in `P`, their actual
  initial-fibre restrictions, and cylinders of the entire cones. Both endpoint
  legs of a length-zero block and both legs at a shared boundary remain in these
  diagrams. No reduction of the zero-fibres to discrete sets occurs. The ordered
  intervals meet at precisely the same consecutive boundary vertices.
- (i), arity zero: `r = 0 -> IsContractible (familyActiveSlice P b)` is explicit.
  `HasOrderedCutBases` then forces `m=0` and the empty tuple; every coefficient
  source lies in its arity-zero fibre, terminal by the monoidal Segal axiom.
- (ii): the existential `r` has the exact source projection, and in every degree
  its join extension is precomposition with `id ⋆ incidenceVertex d 0`. These two
  equations uniquely specify restriction to the first vertex, including when
  there are no source vertices. `modelCategoryQuillen.I.rlp r` asserts the right
  lifting property for every simplicial boundary, including `boundary 0`.
- (iii): with `f = familyCommaSource P σ ≫ F`, the conclusion is literally
  `modelCategoryQuillen.I.rlp (relativeCosliceRestrictionMap q
    (activeFamilyInclusion P σ) f)`.
  The dependency defines its domain as `coherentJoinCoslice f`, and its target as
  the pullback of the restricted coslice and the entire base coslice. A k-simplex
  is exactly an extension of `X_sigma ⋆ Δ[k]`; restriction and postcomposition are
  the canonical functions on those extensions. Its lifting property therefore
  keeps the full prescribed base and restriction and all specified boundaries.
  This uses right join-coslices, with no replacement by an unspecified lifting map.
- The negative scope sentence is respected: neither `IsRelativeColimitDiagram` nor
  operadic-colimit existence appears in the conclusion or any hypothesis.

### Dependency declarations

All names below are under `SSet.Enhanced` unless further qualified.

- `Sheaf.CategoryTheory.OperadicCorrespondence`: `Operadic.Family`,
  `Operadic.IsActiveEdge`, `Operadic.IsActiveDiagram`, `Operadic.fiberInclusion`,
  `Operadic.fiberProjection`. Read its existing `activeSlice`, `activeTargetSlice`,
  `IsInducedActiveCocone`, `Correspondence`, and `IsConstantOverZero`: those are
  restricted to an interval family and a target colour, so they cannot directly
  express the present arbitrary-arity targets and simplex parameters. The helpers
  in this item are their explicit generalizations, not copies of a usable interface.
- `Sheaf.CategoryTheory.MonoidalInfinityCategory`: `monoidalSimplexBase`,
  `monoidalBaseVertex`, `monoidalBaseEdge`, `monoidalRho`, `monoidalFiberInclusion`,
  `IsMonoidalInfinityCategory`, `IsMonoidalInertEdge`.
- `Sheaf.CategoryTheory.RelativeInfinityCone`: `rightJoinCone`,
  `rightJoinConeInclusion`; its existing ordered join is reused throughout.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `fullSubcomplex`,
  `IsFunctorEquivalence`, `IsContractible`, with their exact docstring conventions.
- `Sheaf.CategoryTheory.JoinSliceRightFibration`: `joinSlice`,
  `joinSliceProjection`, `joinPointTopSimplex`, `orderedJoinInr`.
- `Sheaf.CategoryTheory.RelativeCosliceLeftFibration`:
  `relativeCosliceRestrictionMap` and its actual `relativeCoslicePullback`.
- Proof-only imported nodes: `EnhancedFunctorConeCalculus.enhanced_functor_cone_calculus`,
  `RightFibrationMorphismSpace.right_fibration_morphism_space`,
  `InfinityCocartesianMappingCriterion.infinity_cocartesian_mapping_criterion`;
  these names are namespace `SSet.Enhanced`, not the module-name prefix displayed here.
- `CofinalRelativeJoinSliceRestriction`, `InitialPosetSliceRestriction` are public
  imports both for the published coslice interface and for their proof inputs.
  `InfinityPointwiseAdjointCriterion` and `JoinSliceRightFibration` are transitively
  imported by them. No import introduces an item-to-prerequisite cycle.
- Mathlib's `modelCategoryQuillen.I` is exactly the class of boundary inclusions;
  its `.rlp` includes dimension zero. `Pi.lift` uses the actual simplicial product.

### Edge cases and verification

Checked n=1, arbitrary repeated parameter vertices, d=0, r=0, r=1, zero-length input
blocks, empty J, and non-discrete Kan zero-fibres. No `Nonempty`, positive arity or
positive simplex dimension is added. For d=0 the formula in (ii) is the identity
restriction. For empty J the apex equation in `IsFamilyActiveCone` still fixes the
cone; neither canonical cone nor comparison maps are replaced by vacuous choices.
All universes and variables are explicitly bound; `autoImplicit` is disabled.

`scompile.py N7 lem-coef-operadic-active-incidence-comparison <module>` compiled both
its sandbox copy and its named library module in about 4–5 seconds each, without
errors or warnings. The initial product notation was corrected to the cartesian
monoidal tensor map, and a base-coordinate notation parse was repaired. A subsequent
rereading changed constancy to use cocartesianness in each actual edge restriction
and reduced the cone-preservation hypotheses to the specified projections.
The final delivery is checked again by the prescribed dry run.

### Searches

- `msearch.py ... leanfinder`, query: "In an infinity operad family active source slice
  is a product of active slices and restriction of join coslices to active arrows is
  a trivial Kan fibration". Eight hits on Quillen fibrations, strict Segal nerves
  and ordinary categorical constructions; no operadic active-incidence comparison.
- `msearch.py ... loogle`, query:
  `SSet.Enhanced.Operadic.activeSlice, SSet.TrivialFibration`. Zero hits; the first
  project identifier is unknown to the public index.
- `msearch.py ... grep`, query:
  `active.*slice|operadic.*incidence|inert.*factorization`. One unrelated Mathlib
  tactic slice file; no match.
- `msearch.py ... leansearch`, query: "Active source comma categories for operadic
  families split over inert projections and restriction of relative join coslices
  is a trivial Kan fibration". Eight generic model-category/trivial-fibration hits;
  none states this theorem.
- `rg` in the named source checkout and `lean/Sheaf/CategoryTheory` for active slices,
  active incidence, stationary lifts, `IsConstantOverZero` and concatenation.
  The nonsymmetric dependency supplies only the interval/colour active slice;
  the symmetric active-algebra slices and strict envelope concatenation concern
  different bases. No existing declaration has the present statement.
- `rg` of the item id in upstream `WeilConjectures` returned no declaration.
  Exact new helper/main names were checked in the upstream tree, the side tree and
  `dag/lean_names_upstream.json`, with no collision. Search results are also retained
  in the wrapper-generated sandbox `searches.jsonl`.

No STATEMENT-DISPUTED mathematical claim is raised. The inherited repair note has
`stage: "1"` and concerns proof subdivision, not a withdrawn stage-2 interface;
this statement delivery preserves that existing DAG proof and records no claim to
have performed stage-1 subdivision.

## Second reading by N7

A separate pass by this same worker reopened the node and the final Lean file,
expanded each helper and matched the hypotheses and all three conclusions above.
No second agent was launched: the dispatcher explicitly forbids starting agents;
the maintainer's independent delivery review remains separate.

This reading found and repaired two potential scope mismatches before delivery:
constancy is tested in the edge restriction, and induced-cone compatibility now
requires preservation only of its named source/apex projections. It also checked
that the cutting equivalence has actual canonical cone data and exact block offsets,
that the first-vertex map has its full extension formula, that the relative coslice
map is the dependency's literal canonical map, and that arity zero and dimension-zero
boundaries survive. No natural-language statement or dependency record was changed.

## Maintainer review fix

The helper predicate `IsInitialInertFunctor P q F` named in the worker report was
definitionally `SSet.Enhanced.IsLaxMonoidalInfinityFunctor (initialProjection P) q F`
(base equation `F ≫ q = initialProjection P` and preservation of
`IsMonoidalInertEdge` edges), a recorded declaration of the statement dependency
`def-coef-monoidal-infinity-category` (delivery-errors H4: a private copy). It is
removed; both coefficient clauses of the theorem now use the recorded predicate.
The statement is otherwise unchanged; the fixed module compiles clean through
`tools/nt_compile.py` with no error or warning reported.
