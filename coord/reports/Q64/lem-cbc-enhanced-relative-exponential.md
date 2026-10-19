## Worker report

The delivery states `SSet.Enhanced.enhancedRelativeExponential` in
`lean/Sheaf/CategoryTheory/EnhancedRelativeExponential.lean`. Its sole theorem has
proof `sorry`; the docstring contains all seven proof steps of the node, together
with the canonical universe transport and the descriptions of the explicit maps.
Four supporting definitions construct evaluation, uncurrying, the map represented
by an individual simplex, and the canonical fibre comparison. Their data and
naturality laws are fully constructed, without any postponed theorem or choice
of an arbitrary map. These helpers belong to this node's relative-Hom construction
and are listed in `lean.declarations`.

The source was read online: [HTT, Corollary the project server, printed p. 187](https://www.math.ias.edu/~lurie/papers/HTT.pdf),
specialized to `Y = S × A`, and [Kerodon 0472](https://kerodon.net/tag/0472),
with opposite variance. In the HTT edition served at the source URL, the printed
page 187 is zero-based PDF page 204. No source or blueprint statement is changed.

Hypothesis-by-hypothesis correspondence:

- Small quasicategories `S` and `B`: `S B : SSet.{u}` with `[Quasicategory S]`
  and `[Quasicategory B]`.
- The simplicial map: `p : B ⟶ S`.
- Cartesian fibration: `hp : cartesianFibration p`, using the recorded horn and
  prescribed-target lift definition from `InfinityFibrations`.
- A target quasicategory in a containing universe: `A : SSet.{max u v}` and
  `[Quasicategory A]`, with `u` and `v` independent. The small simplicial sets
  and `p` are transported by Mathlib's degreewise `SSet.uliftFunctor.{v,u}` into
  that universe. This is the canonical universe inclusion, with lower/up inverse
  coordinate operations; it imposes no equality of the small and target universes.
  The resulting projection is over this transported copy of the specified `S`.

Clause-by-clause correspondence:

- A simplex is the pair `(sigma,h)` in the node. The already landed
  `RelativeExponentialSimplex` has `sigma` and its natural values on the degreewise
  pullback; `naturality` is exactly the condition that these values define the
  simplicial map `h`. The existing `relativeExponentialMap` restricts these values
  along an ordinal map, and `relativeExponential` assembles them with their identity
  and composition laws. The existing `relativeExponentialProjection` forgets `h`.
  This construction is imported and reused, never copied.
- For every `K → S`, the natural displayed Hom bijection is the second and third
  conjuncts of the theorem: `Function.Bijective (relativeExponentialUncurry ...)`
  for every test map `k`, and its equality under arbitrary precomposition
  `a : L ⟶ K`. The subtype of maps `F` satisfies exactly `F ≫ q = k`, so it is
  `Hom_/S(K,Q)`. The codomain is the actual simplicial Hom from `pullback k p`
  into `A`. `relativeExponentialUncurry` is evaluation after the induced map of
  pullbacks, so the bijection is tied to the specified canonical map.
- `Q` is a quasicategory, and `q` is a cocartesian fibration: the first conjunct
  provides witnesses `hS` and `hQ` for the canonical universe-lifted base and the
  constructed `Q`, then asserts `@cocartesianFibration ... hQ hS`. The existential
  packaging supplies exactly the quasicategory structures required as arguments
  by the recorded dependency; it adds no hypothesis. In particular `hQ` is a
  conclusion, not a binder assumed from the caller.
- The fibre at `s` is `Fun(B_s,A)`: the fourth conjunct asserts
  `IsIso (relativeExponentialFiberComparison A ... (ULift.up s))` for every original
  base vertex `s`. The comparison's source is the recorded `fiber q s`; its target
  is `(ihom (fiber p s)).obj A`. It is currying of the restriction of evaluation to
  the two specified fibres, not a mere existence of an unspecified isomorphism.
  Every vertex of the lifted base is `ULift.up s` for a unique `s`.
- The final conjunct quantifies every edge `e : Δ[1] ⟶ Q` and every edge
  `b : Δ[1] ⟶ pullback (yonedaEquiv.symm (yonedaEquiv e).sigma) p`.
  The `IsCartesianEdge (pullback.fst ...) b` premise is exactly cartesianness
  for the projection to `Δ[1]`. The conclusion is `IsEquivalenceEdge A` for
  `yonedaEquiv (b ≫ relativeExponentialSimplexMap ...)`. The latter map is the
  actual uncurried map associated to `e`; this tests all cartesian edges,
  including those above degenerate base edges. The iff gives both necessity
  and sufficiency, with no restriction to the identity base edge.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.InfinityFibrations`: `SSet.Enhanced.cartesianFibration`,
  `cocartesianFibration`, `IsCartesianEdge`, `IsCocartesianEdge`, `fiber` (full
  signatures and docstrings read). Both fibration predicates use Mathlib
  `SSet.InnerFibration`, and the fibre is the chosen categorical pullback with
  the point factor first.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.IsEquivalenceEdge`
  and Mathlib's `Quasicategory`, `stdSimplex`, `yonedaEquiv`, and simplicial
  internal hom `ihom` (the equivalence-edge signature and inverse triangles read).
- `Sheaf.CategoryTheory.RelativeExponentialRestriction`:
  `SSet.Enhanced.RelativeExponentialSimplex`, `relativeExponentialMap`,
  `relativeExponential`, `relativeExponentialProjection`. Its complete module,
  including construction laws and the neighbouring theorem's signature and
  docstring, was read. The theorem about restriction has the other variance
  and is not a match for this item; only its real construction is used.
  Its existing node `lem-coef-infinity-relative-exponential-restriction` is added
  to `stmt_deps` under the authorization to cite a landed node. A dependency
  traversal found no path back to this item (300 nodes inspected).

The original two statement-dependency modules are public imports. The existing
relative-exponential module is a public import. Every presently recorded proof
module is imported without `public`: `EnhancedFunctorConeCalculus`,
`EquivalenceOuterHornFilling`, `SimplicialCompositionSpine`, `JoyalModelStructure`,
`MarkedAnodyneLiftingCalculus`, and `MarkedPointCartesianModel`. The other proof
prerequisites have no recorded Lean module yet and have no import to add here.
Their absence does not affect the theorem statement and does not require
postponing or altering its objects.

Edge cases checked mathematically against the explicit construction:

- `B = ∅`: each pullback is empty, so there is a unique map to every `A`, even
  empty `A`; hence `Q` is isomorphic to `S`, the fibres are terminal, and the
  cartesian-edge test is vacuous.
- `S = Δ[0]`: `Q` is the ordinary functor simplicial set `Fun(B,A)`.
  In the pullback `Δ[1] × B → Δ[1]`, an edge is cartesian precisely when its
  `B` component is an equivalence. Testing the edges with identity `B` component
  gives pointwise equivalence of the transformation. Naturality and preservation
  of equivalences give the converse for every cartesian edge. Thus the criterion
  says that the edge in the functor quasicategory is an equivalence, not that
  arbitrary transformations are cocartesian.
- `p = 𝟙 S`: `Q` is isomorphic over `S` to `S × A`; its fibre is `A`, and a
  transport edge is cocartesian exactly when its `A` component is an equivalence.
- An empty exponent fibre gives `Fun(∅,A)` terminal, including for empty `A`.
  A nonempty exponent fibre with empty target gives no functor and thus no
  vertex above which an outgoing cocartesian lift would need to be chosen.
- `S = ∅` forces `B = ∅` and gives empty `Q`; the vertex and edge clauses
  have no instances, while the empty-test-object Hom bijection remains a
  bijection between singleton sets.
- The edge test quantifies the constant maps `[1] → [1]` as well as the identity;
  the canonical evaluation map supplies their images without a vacuous equality
  premise. Independent `u,v` retain the strict larger-target case.

Searches made (all wrapper searches also appear in sandbox `searches.jsonl`):

- LeanFinder query `relative exponential of a cartesian fibration is a cocartesian
  fibration with functor fibres`: eight ordinary categorical-fibration hits,
  including `CategoryTheory.Functor.IsCocartesian` and `.map_isHomLift`; none is
  a statement about simplicial relative exponentials.
- Loogle query `"Quasicategory", "InnerFibration"`: eight hits for
  `quasicategory_of_innerFibration` and internal-hom restriction, including
  `instInnerFibrationAppPreOfMonoOfQuasicategory`; none has the relative
  cocartesian-fibration or edge-criterion conclusion. The earlier unquoted
  comma-separated name query was rejected by Loogle's parser; this successful
  query replaced it.
- LeanSearch query `Relative exponential of simplicial sets over a cartesian
  fibration is a cocartesian fibration with functor category fibres`: eight
  ordinary categorical or Kan-fibration hits; no match.
- Mathlib grep `relativeExponential|RelativeExponential|cocartesianFibration`
  in `AlgebraicTopology`: no hits.
- The same grep in the upstream `WeilConjectures` tree: no hits. Direct `rg`
  and the exact item-id grep likewise found no upstream statement.
- Project grep with the same expression: seven reported hits, finding the
  existing `RelativeExponentialRestriction` construction and fibration predicates;
  no theorem stating this item's cartesian-to-cocartesian assertion. Direct `rg`
  additionally located the canonical constructors and their full source was read.

No new DAG node and no dependency-interface repair were needed. The node's
statement, source and proof remain unchanged; only `lean` and the addition of the
already landed construction node to `stmt_deps` change. There is no
`STATEMENT-DISPUTED` flag and no silent source correction.

Validation: every delivered file is compiled through the prescribed `scompile.py`
wrapper, including its real library module name. The complete final module is
clean, with the single expected `sorry` theorem and no other warnings. No global
build, direct Git command, live-file edit, delivery push or second-reader section
was performed. The worker's final action is the required dry run; its result is
reported in the handoff response.

## Second reading by Q64

I reread the unit node, its source place, the two recorded dependency nodes, and the complete
module. The node introduces small simplicial sets/quasicategories `S` and `B`, a map `p : B ⟶ S`,
a cartesian-fibration hypothesis on `p`, and a target quasicategory `A` in a containing universe.
The Lean binders rendering these are `(S B : SSet.{u})`, `(A : SSet.{max u v})`,
`[Quasicategory S] [Quasicategory B] [Quasicategory A]`, `(p : B ⟶ S)`, and
`(hp : cartesianFibration p)`. The independent universe `v` permits the strict containing-universe
case. The canonical universe lift `SSet.uliftFunctor.{v,u}` transports `S`, `B`, and `p` before
forming the relative exponential, so this is the same construction with no equality of universes
assumed.

The node's first conclusion clause (the relative exponential `Q` is a quasicategory and its
projection `q` is cocartesian) is rendered by the existential witnesses `hS`, `hQ` and the
`@cocartesianFibration ... hQ hS` conjunct. The second clause, the displayed natural Hom bijection
for every `K ⟶ S`, is rendered by `Function.Bijective (relativeExponentialUncurry ... k)` on the
subtype of maps over `k`, followed by the explicit precomposition equation for every
`a : L ⟶ K` and every such `F`; the `pullback.map` is the canonical restriction map. The fibre
clause is rendered by `IsIso (relativeExponentialFiberComparison ... (ULift.up s))` for every
vertex `s`, where the comparison is the explicitly defined currying of evaluation and its target is
`(ihom (fiber p s)).obj A`. The edge clause is rendered by the final `∀ e` and the exact `↔`
quantifying every `b` over the pulled-back interval, with `IsCartesianEdge` for the projection and
`IsEquivalenceEdge A` after the canonical `relativeExponentialSimplexMap`. Quantifier order and
both directions of the criterion agree with the node.

The dependency declarations were checked in full. `cartesianFibration`, `cocartesianFibration`,
`IsCartesianEdge`, `IsCocartesianEdge`, and `fiber` are the recorded simplicial definitions in
`Sheaf.CategoryTheory.InfinityFibrations`; `RelativeExponentialSimplex`,
`relativeExponential`, and `relativeExponentialProjection` are the canonical construction from
`Sheaf.CategoryTheory.RelativeExponentialRestriction`; and `IsEquivalenceEdge` and `ihom` are the
recorded conventions in `Sheaf.CategoryTheory.EnhancedDiagramsCones`. No private duplicate notion
was introduced. The added `lem-coef-infinity-relative-exponential-restriction` entry is the
construction dependency used by the imported module and has no path back to this item.

Edge cases were checked: empty `B` gives the unique empty-exponent map and a vacuous edge test;
empty `S` forces the corresponding empty base situation; `p = 𝟙 S` gives the product case;
`S = \Delta[0]` gives the ordinary functor simplicial set and pointwise equivalence criterion;
empty exponent fibres remain terminal even for empty `A`; and the lifted vertex map covers every
original vertex. The `n = 0` fibre and the `n = 1` edge cases are included by the definitions of
`fiber`, `yonedaEquiv`, and the horn-based edge predicates.

Searches were repeated with LeanFinder, LeanSearch, Loogle, Mathlib grep, upstream-project grep,
and project grep for relative-exponential and cocartesian-fibration terminology. They found only
the existing construction and generic categorical-fibration declarations, not this theorem.
The source was checked at HTT Corollary the project server (PDF page 204/printed page 187) and the opposite
Kerodon comparison (Tag 0472); the source hypotheses and cartesian-to-cocartesian edge criterion
agree.

The only mismatch found was representational: the worker's node copy had stored the theorem
signature as one long line, while the file uses the required multiline signature. I changed only
`lean.statement` in the sandbox node record to the exact declaration signature extracted
from the module. No mathematical statement, dependency, declaration, or source field was changed.
The prescribed `scompile.py` check passes for the module with only the expected theorem `sorry`.

Additional independent searches used the terms “dependent product”, “relative Hom”, and
“covariant fibration”: LeanFinder returned Quillen-fibration and monoidal structure declarations;
Loogle `"InnerFibration", "ihom"` returned only `SSet.instInnerFibrationMapIhom`; the
Mathlib wrapper grep `dependentProduct|DependentProduct|relativeHom|RelativeHom` returned no hits.
Direct grep in Mathlib, upstream, and project sources found right-fibration and isofibration
exponentiation modules; their signatures concern `exponentialCorner` and are not the dependent
relative exponential of this node. These checks confirm there is no exact existing theorem.

The defining simplex pair is exactly `RelativeExponentialSimplex`: `sigma` is the base simplex;
`value a z hz` evaluates `h` on the pullback pair, and `naturality` makes it a simplicial map.
`relativeExponentialMap` restricts by precomposing `a`; `relativeExponentialProjection` takes
`sigma`. This verifies the construction and its operators separately from the theorem clauses.
The four new helpers contain actual evaluation/pullback/currying constructions; the proofs inside
their definitions check the construction laws, with no postponed data. The sole theorem remains
`sorry`. The module and all five declaration docstrings name the source and blueprint, and the
theorem docstring retains all seven node proof steps. There are no new definition nodes or repaired
dependency modules in this delivery. The file has no line over 100 columns, file-local notation,
local instances, private definitions, or unbound universes/variables.
