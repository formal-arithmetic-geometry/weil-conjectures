## Worker report

The module `Sheaf.AlgebraicTopology.PushoutJoinSaturation` states
`SSet.Enhanced.pushout_join_weak_saturation`, with exactly one postponed theorem and
its complete twelve-step natural-language proof in the docstring. The helpers
`joinAugmentation`, `orderedJoinFunctor`, `pushoutJoin`, and `WeaklySaturated` belong
to the notions introduced inline by this node. All definitions have real data;
there are no assumptions supplying an arbitrary join or an arbitrary comparison.
No other DAG node is stated or changed.

Clause-by-clause rendering:

- Simplicial sets are Mathlib's `SSet.{u}` (presheaves on `SimplexCategory`), with
  the same standard simplices and horns publicly imported by the recorded dependency
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`. The declaration recorded there is
  `SSet.Enhanced.coneCategory {K C : SSet.{u}} (F : K ⟶ C) : SSet.{u}`; its full
  module and the signatures/docstrings of its helper declarations were inspected.
  Its cone objects are not needed here; the node calls only for its simplicial primitives.
  The proof dependency `def-weil-pbc-simplicial-set` is a Mathlib leaf: its `SSet`
  declaration in `Mathlib.AlgebraicTopology.SimplicialSet.Basic` is used directly.
- Weakly saturated is `WeaklySaturated P`, defined by
  `MorphismProperty.isomorphisms SSet.{u} ≤ P`, `P.IsStableUnderCobaseChange`,
  `P.IsStableUnderTransfiniteComposition.{u}`, and `P.IsStableUnderRetracts`.
  Thus all four clauses are present, and ordinal indexing is small in the universe
  of the simplex sets. Mathlib's transfinite-composition predicate quantifies over
  well-ordered successor index types with a bottom and continuous chains.
- Inner anodyne means Mathlib's `SSet.innerAnodyneExtensions`, from
  `Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic`.
  Its docstring and full definition were read: it is the LLP of inner fibrations.
  The same file proves its equality with retracts of transfinite composites of
  pushouts of coproducts of inner horn inclusions
  (`innerAnodyneExtensions_eq_retracts_transfiniteCompositions`). Together with
  its isomorphism and closure instances, this is exactly the node's generated
  weakly saturated class; coproducts can be attached by a small transfinite sequence.
- The ordered join is the actual bifunctor `orderedJoinFunctor`, built using
  Mathlib's `AugmentedSimplexCategory.tensorObj/tensorHom` (ordered concatenation),
  `Functor.ran`, `externalProductBifunctor`, `Functor.lan`, and restriction.
  `joinAugmentation` is right Kan extension along `inclusion.op`. At the empty
  ordinal the right-Kan indexing category is empty, so the value is a singleton;
  on the nonempty ordinals full faithfulness recovers the original presheaf.
  No mere unproved existence or `Nonempty` choice is used.
- To check that this gives the exact simplex formula, the left-Kan colimit in degree
  `r` has representatives `(p,q,α,x,y)`, with `p,q` augmented ordinals,
  `α : [r] → p ⊗ q`, `x` in the augmented `X_p`, and `y` in the augmented `Y_q`.
  The inverse image of the first block is an initial segment and that of the second
  is a final segment. Restrict `α` to these blocks and apply the operators of `X,Y`.
  This normalizes every representative to its unique cut of `[r]`, with the two
  restricted simplices. Empty first block gives exactly `Y_r`, empty second gives
  exactly `X_r`, and otherwise the cut has sizes `a+1,b+1`, with `a+b+1=r`, giving
  `X_a × Y_b`. These data are invariant under each generating colimit relation;
  their normal representatives give the inverse. Thus no extra identifications
  occur. Precomposition acts by restriction to the two ordered blocks, exactly as
  in the node. On maps the external-product and Kan-extension functors act by the
  maps of `X,Y` on these coordinates. The categorical opposite monoidal structure
  preserves the order of the two tensor factors (read `monoidalCategoryOp`);
  this is the ordered `X`-then-`Y` join, with no symmetry imposed.
- The displayed comparison is `pushoutJoin i k`. Its domain is explicitly
  `pushout (join(A,k)) (join(i,K))`, i.e.
  `(A ⋆ L) ⨿[A ⋆ K] (B ⋆ K)`, and its codomain is `orderedJoinFunctor.obj (B,L)`.
  The body is the canonical `pushout.desc` of `join(i,L)` and `join(B,k)`;
  compatibility is the existing naturality equation of the curried bifunctor.
- The fixed second monomorphism is `∀ {K L} (k : K ⟶ L), Mono k → ...`.
  Its class is literally `fun i ↦ Mono i ∧ innerAnodyneExtensions (pushoutJoin i k)`.
  The fixed first monomorphism and its class are the second conjunct with `i,k`
  interchanged in their roles. There are no extra hypotheses on either map, on
  the simplicial sets, on fibrancy, or on the Kan-extension construction.

Sources: opened the complete proof of [Kerodon Tag 018J](https://kerodon.net/tag/018J),
Proposition the project server. The two weak-saturation reductions are the node's source;
the node supplies the expanded degreewise proof, reproduced in the theorem docstring.
The existing enhanced-diagram module uses precisely the standard Mathlib primitives.
No dependency repair or statement correction is necessary.

Edge cases checked: at `r=0` there are no mixed summands and the join vertices are
`X_0 ⨿ Y_0`. With `X` empty, only the pure `Y` terms survive; with `Y` empty,
only the pure `X` terms survive; with both empty there are no representatives.
A zero-size block contributes a singleton augmented simplex, not an extra vertex.
For two points, the normal forms give the ordered standard one-simplex. No
nonemptiness of a simplicial set or of a mixed-summand index is assumed. An
isomorphism in either arrow variable fills every mixed component of the pushout,
so the comparison is an isomorphism. Zero-length ordinal composites are included
by the isomorphism clause. Arbitrary small ordinals, including nonzero limits,
are retained; there is no countability or finite-dimension restriction.
All variables and the universe `u` are explicitly bound, with auto implicits disabled.

Searches performed for this attempt (via the prescribed `msearch.py`, group NM,
item `lem-coef-infinity-pushout-join-saturation`):

- LeanFinder: `Ordered join of simplicial sets and weak saturation of the pushout
  join in either variable`. Eight hits: generic subcomplex colimits,
  `SSet.modelCategoryQuillen.J/I`, monomorphism closure, and `SSet.hasColimits`;
  no ordered join or saturation theorem.
- Loogle: `SSet.join, SimplexCategory.join`. No hits; `SSet.join` is unknown.
- Mathlib grep: `joinFunctor|def join|pushout.?join|ordinalSum` under
  `AlgebraicTopology`. No hits.
- LeanSearch: `Simplicial join as Day convolution over the augmented simplex
  category and pushout join weak saturation`. Eight hits including generic
  `DayConvolution`, augmented simplex category, its inclusion, and simplicial
  augmentation. Read the full generic interfaces; these supply the construction
  tools, not a pre-existing simplicial join or this theorem.
- Direct `rg` of Mathlib simplicial-set/category-theory sources, upstream
  `WeilConjectures`, project `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  no pre-existing declarations named `joinAugmentation`, `orderedJoinFunctor`,
  `pushoutJoin`, `WeaklySaturated`, or `pushout_join_weak_saturation`; no upstream
  declaration bears this blueprint id. Broader join/Leibniz searches found
  `PushoutObjObj` and the augmented-simplex ordinal concatenation, which were read.
  The cartesian pushout-product results concern a different bifunctor.

The earlier sandbox attempt was redone: its `JoinSimplexFormula` only constrained
cardinalities, omitted simplicial operators, and its arbitrary `theta` even had
source `A` and target `B`. Those interfaces have been removed. The delivered
statement constructs the exact objects and canonical map from the node.

Validation: `scompile.py NM lem-coef-infinity-pushout-join-saturation` compiles this
single module in isolation and under its library module name, cleanly within the default
60-second limits. An initial dry run caught that `lean.statement` must exclude the
`:=` delimiter; the record was repaired to match the preflight parser. The required
`deliver2.py --no-push` dry run is repeated after this metadata and documentation edit. The independent second reading is left to the assigned second worker.
There is no `STATEMENT-DISPUTED` flag and the node changes only in `lean`.

## Second reading by NM

I independently reread `dag/nodes/sec-six-functors/lem-coef-infinity-pushout-join-saturation.json`, its Kerodon source place (Proposition the project server, tag 018J), the dependency record for `def-cbc-enhanced-diagrams-cones`, and `Sheaf/AlgebraicTopology/PushoutJoinSaturation.lean`.

Object and hypothesis checklist:

- The node's simplicial sets and standard horns are rendered by `SSet.{u}` and the imported Mathlib simplicial primitives; the enhanced-diagram dependency is imported as `Sheaf.CategoryTheory.EnhancedDiagramsCones`.
- The node's weak saturation notion (isomorphisms, pushouts, transfinite compositions, retracts) is rendered by `SSet.Enhanced.WeaklySaturated P`, namely `MorphismProperty.isomorphisms SSet ≤ P`, `P.IsStableUnderCobaseChange`, `P.IsStableUnderTransfiniteComposition.{u}`, and `P.IsStableUnderRetracts`.
- The ordered join is rendered by the actual `SSet.Enhanced.orderedJoinFunctor`, constructed from `joinAugmentation` (right Kan extension at the augmented empty simplex), external product, left Kan extension along augmented ordinal concatenation, and restriction. This is the canonical ordered join; its pure and mixed degree-
  `r` summands and ordered simplicial operators are documented in the definition and agree with the node's displayed formula, including empty and pure summands.
- For maps `i : A ⟶ B` and `k : K ⟶ L`, `SSet.Enhanced.pushoutJoin i k` is the canonical `pushout.desc` from the categorical pushout of the two join maps, with codomain `orderedJoinFunctor.obj (B, L)`. Thus it renders exactly `((A ⋆ L) ⨿[A ⋆ K] (B ⋆ K)) ⟶ (B ⋆ L)`.
- The first conclusion clause is exactly `∀ {K L} (k : K ⟶ L), Mono k → WeaklySaturated (fun i ↦ Mono i ∧ innerAnodyneExtensions (pushoutJoin i k))`.
- The second conclusion clause is exactly `∀ {A B} (i : A ⟶ B), Mono i → WeaklySaturated (fun k ↦ Mono k ∧ innerAnodyneExtensions (pushoutJoin i k))`.
- `innerAnodyneExtensions` is Mathlib's inner-horn LLP class; Mathlib records its equality with the retracts of transfinite compositions of pushouts of coproducts of inner horn inclusions, so it is the node's weakly saturated inner-anodyne class. No extra fibrancy, finiteness, characteristic, or universe equality is assumed.

Edge cases checked: `u` is explicitly bound; empty simplicial sets and zero-dimensional simplices are allowed; `r = 0` gives the pure vertex coproduct with no mixed summand; empty factors give only the opposite pure summands; both empty factors give the empty join; zero-length and limit ordinal transfinite composites are included by Mathlib's closure predicate; isomorphisms in either variable give an isomorphism pushout join. The index type of the mixed summands is internal to the augmented simplex construction, so no independent universe or nonemptiness assumption is introduced.

Independent searches were performed with `rg` over Mathlib, `WeilConjectures/`, project `lean/Sheaf/`, and the DAG's upstream-name records for `orderedJoinFunctor`, `joinAugmentation`, `pushoutJoin`, `WeaklySaturated`, and `pushout_join_weak_saturation`; there were no existing declarations. I also inspected Mathlib's `innerAnodyneExtensions_eq_retracts_transfiniteCompositions` and `innerAnodyneExtensions_eq_retracts_transfiniteCompositionsOfShape`, and the dependency declaration `SSet.Enhanced.coneCategory`. No mismatch was found, so no Lean or node repair was needed. The module compiles cleanly with the required `scompile.py` wrapper.
