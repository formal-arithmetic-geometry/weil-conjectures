## Worker report

The module `Sheaf.CategoryTheory.RelativeInfinityCone` defines relative coherent colimit and
limit diagrams for an arbitrary simplicial functor between quasicategories. Its primary
declaration is `SSet.Enhanced.IsRelativeColimitDiagram`; its dual is
`SSet.Enhanced.IsRelativeLimitDiagram`. There are eight declarations, all real definitions
or abbreviations. There is no theorem or `sorry` in this delivery.

The node statement is unchanged. Only `lean` and `stmt_deps` change. The latter gains the
three already stated nodes that own the reused join, inclusions, and path-pullback helpers:
`lem-coef-infinity-pushout-join-saturation`,
`lem-coef-infinity-slice-right-fibration`, and `lem-coef-infinity-source-gluing`.
This is allowed by brief-stage2 §5, “STMT_DEPS MAY GAIN LANDED NODES.” No other DAG node
is stated, copied, or modified. No new nodes or dependency repairs are needed.

Source checked online: [Kerodon Proposition the project server, condition (2)](https://kerodon.net/tag/02X1)
and [Definition the project server](https://kerodon.net/tag/02KG). The former tests every comparison
diagram, using incoming mapping spaces for limits; the latter specifies both cone
orientations and relative universality for an arbitrary functor. The colimit predicate
uses the dual variance. No isofibration or existence condition is imposed.

Clause-by-clause rendering:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Fixed sufficiently large universe; small simplicial sets | Explicit `universe u`, with every simplicial set in `SSet.{u}`. No nonemptiness or finiteness condition. |
| Existing quasicategory, functor-simplicial-set and right-pinched conventions | `Quasicategory`, `(ihom K).obj D`, `diagramVertex`, `mappingSpace`, and `mappingSpaceMap` from the recorded dependencies. |
| Functor objects are quasicategories and their mapping spaces are Kan | Imported `enhanced_functor_cone_calculus`, including its `QuasicategoryMappingSpaceAssertions`. These are the already stated well-definedness facts, not new assertions here. |
| Unique augmented degree -1 simplex | Existing `joinAugmentation`, the right Kan extension to the augmented simplex category; the empty ordinal has an empty indexing category, hence a singleton value. |
| Ordered join degree formula and operators, including pure factors | Existing `orderedJoinFunctor`, the left Kan extension of the external product of the terminal augmentations along ordinal concatenation. Its normal form restricts to the inverse images of the two blocks: the pure factors and the mixed summands with `i+j+1=n`. This is the same join, not a second join construction. |
| Right cone `K ⋆ Δ⁰` and left cone `Δ⁰ ⋆ K` | `rightJoinCone K` and `leftJoinCone K`, abbreviating precisely those two objects of `orderedJoinFunctor`. |
| Pure-factor inclusions of `K` | `rightJoinConeInclusion K := orderedJoinInl K Δ[0]`; `leftJoinConeInclusion K := orderedJoinInr Δ[0] K`. |
| Strict square `f,h,g,k` | `homotopyPullbackComparison f g h k w`, with `w : f ≫ h = g ≫ k`. |
| Path pullback `B ×[D,ev₀] Fun(Δ¹,D) ×[ev₁,D] C` | Existing `simplicialHomotopyPullback h k`, literally `pullback (pullback.snd h ev₀ ≫ ev₁) k`. Both endpoint equations are imposed on entire simplices by the pullbacks. |
| Canonical comparison, with the constant interval at `hf(a)=kg(a)` | The two nested `pullback.lift`s have coordinates `f`, `g`, and `f ≫ h ≫ constantDiagrams Δ[1] D`. Their endpoint equalities use the evaluation/constant-diagram identity and `w`. The comparison is constructed, never chosen. |
| Square is homotopy Cartesian iff that comparison is a weak equivalence | `IsHomotopyPullbackSquare f g h k := ∃ w, IsWeakHomotopyEquivalence (homotopyPullbackComparison f g h k w)`. Existence of the commuting-square proof merely internalizes strict commutativity; proof irrelevance makes the comparison independent of its proof. |
| The square consists of Kan complexes | For the four mapping spaces used by the relative predicates, this follows from the recorded calculus theorem and the two quasicategory hypotheses. The generic square formula is also defined on arbitrary simplicial sets, without adding any condition to the relative predicates. |
| Arbitrary functor `p : D → B` between quasicategories | Explicit `{K D B : SSet.{u}} [Quasicategory D] [Quasicategory B] (p : D ⟶ B)`. |
| Given right-cone diagram `q`, test every right-cone diagram `t` | `(q : rightJoinCone K ⟶ D)` and `∀ t : rightJoinCone K ⟶ D` in `IsRelativeColimitDiagram`. |
| Upper-left corner `Map_Fun(K▷,D)(q,t)` | Source of both first and second `mappingSpaceMap`s. |
| Upper-right corner `Map_Fun(K,D)(q|K,t|K)` | Target of the first map, equivalently source of the third map. The restricted vertices reduce to `diagramVertex (rightJoinConeInclusion K ≫ q)` and similarly for `t`. |
| Lower-left corner `Map_Fun(K▷,B)(pq,pt)` | Target of the second map, equivalently source of the fourth map. Postcomposition vertices reduce to `diagramVertex (q ≫ p)` and similarly for `t`. |
| Lower-right corner `Map_Fun(K,B)(pq|K,pt|K)` | Common target of the third and fourth maps. Associativity of diagram composition identifies these exact endpoints. |
| Horizontal maps are restriction | `mappingSpaceMap ((MonoidalClosed.pre (rightJoinConeInclusion K)).app D)` and the corresponding map with target `B`. |
| Vertical maps are postcomposition by `p` | `mappingSpaceMap ((ihom (rightJoinCone K)).map p)` and `mappingSpaceMap ((ihom K).map p)`. |
| Every such square is a homotopy pullback | The body of `IsRelativeColimitDiagram` applies `IsHomotopyPullbackSquare` to exactly these four maps. |
| Limit dual: left cone and `(t,q)` in place of `(q,t)` | `IsRelativeLimitDiagram` uses `leftJoinCone`, `leftJoinConeInclusion`, and the two vertices in the order `diagramVertex t`, `diagramVertex q` throughout. The four axes and path orientation otherwise stay the same. |
| No existence assertion | Both definitions accept an already supplied `q` and return a predicate; neither selects a diagram or assumes global (co)completeness. |

Dependency declarations read and used (names in namespace `SSet.Enhanced` unless qualified):

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `diagramVertex`, `mappingSpace`,
  `mappingSpaceMap`, `evaluation`, `constantDiagrams`, `IsWeakHomotopyEquivalence`.
  Their source signatures and docstrings were read in full. In particular the mapping
  space fixes the entire initial face and appends the last vertex in its operators.
- `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`:
  `enhanced_functor_cone_calculus`, `QuasicategoryMappingSpaceAssertions`. The complete
  theorem signature and its proof docstring were read. Its functor-category and Kan
  clauses supply the facts cited in the node's opening paragraph.
- `Sheaf.AlgebraicTopology.PushoutJoinSaturation`: `joinAugmentation`,
  `orderedJoinFunctor`. Their full definitions and normal-form docstrings were read.
- `Sheaf.CategoryTheory.JoinSliceRightFibration`: `orderedJoinInl`, `orderedJoinInr`
  and their underlying `joinEmptySimplex`, `joinGenerator`; their actual construction
  fixes the pure summands, so no arbitrary inclusion is introduced.
- `Sheaf.CategoryTheory.SourceAttachmentGluing`: `simplicialHomotopyPullback`.
  Its two actual pullbacks and endpoint evaluations have precisely the required order.
- Mathlib: `SSet`, `SSet.Quasicategory`, the standard simplex, internal homs,
  `MonoidalClosed.pre`, `ihom.map`, and `Limits.pullback.lift`.

Edge cases checked before writing:

- `K` empty: either join is a point, and the test is the relative initial/final
  condition, with no assumption that `K` has vertices.
- `K = Δ[0]`: either join is the ordered interval. Right cone adds the final vertex;
  left cone adds the initial vertex. The inclusion orientation matches the node.
- Empty `D` (and a supplied `q`): no right/left cone map into empty `D` exists, as it
  should; this is not excluded by an extra hypothesis on `K`, `D`, or `B`.
- Empty Kan mapping complexes are allowed. The path model uses no basepoint choice
  and no forced inhabitance. Degree zero keeps the entire interval and both endpoints.
- `p` the identity: the square has identity vertical maps, so its canonical comparison
  is the usual equivalence to its path pullback; no extra restriction on `q` results.
- `B = Δ[0]`: the lower row is terminal and the condition reduces to the ordinary
  (co)limit mapping-space criterion. No completeness hypothesis has been introduced.
- Pure join simplices and operators with an empty inverse-image block use the
  terminal augmentation already built into `orderedJoinFunctor`; degree zero consists
  of the two pure vertex sets.

Searches for duplicate notions:

1. `msearch.py ... leanfinder "relative colimit diagram homotopy pullback mapping spaces
   quasicategory"`: eight hits, headed by `SSet.RelativeMorphism.HomotopyClass` and
   relative homotopies. These concern homotopies of maps of pairs, not the node's
   relative universal mapping-space square. No exact match.
2. `msearch.py ... loogle "SSet.Enhanced.simplicialHomotopyPullback, orderedJoinFunctor,
   IsWeakHomotopyEquivalence"`: zero hits; the service does not index the project's
   `SSet.Enhanced.simplicialHomotopyPullback`. Direct source search supplies that exact
   reusable construction.
3. `msearch.py ... grep "relative.*[Cc]olimit|[Cc]olimit.*relative|[Hh]omotopy.*[Pp]ullback"
   AlgebraicTopology`: two hits in Mathlib's `ModelCategory/RightHomotopy.lean`, about
   composition of right homotopies and their ordinary pullback. No relative cone predicate.
4. `rg` across the upstream `WeilConjectures`, Mathlib, and project `lean/Sheaf`, plus
   `dag/lean_names_upstream.json`, for all eight proposed declaration names and the
   file name: no name collisions. The node id also has no upstream source match
   (`grep -rn` as requested).
5. Concept searches of `lean/Sheaf` for joins, path pullbacks, relative colimits and
   mapping-space restriction found the exact join/inclusions and path object reused
   here. `InfinityMappingExcision.excisionMappingRestriction` is an application of
   `mappingSpaceMap`; no duplicate wrapper was introduced. Upstream concept search
   found no relative quasicategory predicate. Mathlib's `CategoryTheory.IsUniversalColimit`
   source was inspected: it means stability of an ordinary cocone under pullbacks,
   not the present notion. `SSet.Quasicategory` is only the primitive horn class.

Validation: `scompile.py Q84 def-coef-infinity-relative-cone` compiled the final module
cleanly (sandbox and named library module; 2.4 and 2.7 seconds on the clean run).
All binders and the universe are explicit; no private declarations, file-local notation,
local instances, extra axioms, hollow data, or postponed theorem were introduced.
The required `deliver2.py --no-push` printed OK: compilation and preflight passed, with
only the independently authored second-reading section deferred as intended. Nothing
was pushed. The final rerun includes the completed module documentation list.

No `STATEMENT-DISPUTED` or statement fault was found. The stage-2 definition neither proves
nor changes any blueprint unit statement. A fresh second reader will review and deliver;
this worker has not written a second-reading section or pushed a delivery.

## Second reading by Q84

I reread the node in `dag/nodes/sec-six-functors/def-coef-infinity-relative-cone.json`,
the declarations recorded by each dependency, and Kerodon 02KG and 02X1. The item-by-item
rendering is:

* The fixed sufficiently large simplicial-set universe is `universe u`, with all objects
  in `SSet.{u}`; no finiteness or nonemptiness hypothesis is added.
* The simplicial-set, quasicategory, functor-simplicial-set, right-pinched mapping-space,
  and weak-equivalence conventions are the imported declarations `SSet`,
  `Quasicategory`, `ihom`, `mappingSpace`, `mappingSpaceMap`, and
  `IsWeakHomotopyEquivalence` from `EnhancedDiagramsCones`.
* The quasicategory and Kan assertions for functor objects and mapping spaces are supplied
  by the recorded `enhanced_functor_cone_calculus` dependency; the definition adds no
  extra class or existence hypothesis.
* The formal degree `-1` augmentation is `joinAugmentation`, and the ordered join with
  all pure and mixed summands and its operators is the existing `orderedJoinFunctor`.
  `rightJoinCone` and `leftJoinCone` render `K ⋆ Δ[0]` and `Δ[0] ⋆ K`.
* `rightJoinConeInclusion` and `leftJoinConeInclusion` are respectively the existing
  `orderedJoinInl K Δ[0]` and `orderedJoinInr Δ[0] K`, so the pure-factor orientation is
  exactly the node's.
* `homotopyPullbackComparison` takes a strict square and uses nested `pullback.lift`s with
  coordinates `f`, `g`, and the constant interval at `f(a)h = g(a)k`; its endpoint
  equations use the supplied commutativity proof. `simplicialHomotopyPullback` is the
  recorded two-endpoint path pullback.
* `IsHomotopyPullbackSquare` is exactly existence of the strict commutativity proof and
  weak equivalence of that canonical comparison. It does not add Kan hypotheses to the
  generic construction; the relative predicates use mapping spaces that are Kan under
  their quasicategory assumptions.
* For arbitrary `p : D ⟶ B` between quasicategories and supplied right cone `q`,
  `IsRelativeColimitDiagram` quantifies over every right cone `t`. Its four maps are,
  in order, restriction in `D`, postcomposition by `p` on `K ⋆ Δ[0]`, postcomposition by
  `p` on `K`, and restriction in `B`; their vertices are exactly `Map(q,t)`,
  `Map(q|K,t|K)`, `Map(pq,pt)`, and `Map(pq|K,pt|K)`.
* `IsRelativeLimitDiagram` uses the left cone, quantifies over every `t`, and reverses the
  mapping-space arguments to `Map(t,q)` in all four corners. Its restriction and
  postcomposition axes are otherwise the same. Neither predicate asserts existence.

The source check of Kerodon 02X1 confirms that limits use `Hom(g,f)` while the colimit
dual uses `Hom(f,g)`, matching these two definitions. The source Definition 02KG imposes
an arbitrary functor and no isofibration, completeness, or cocompleteness assumption.

Edge cases checked: empty `K` gives the relative initial/final condition; `K = Δ[0]`
gives the interval cone with the stated inclusion orientation; an empty `D` is allowed
but admits no supplied cone; empty mapping spaces are not forced inhabited; degree zero
retains both endpoints; identity `p` gives identity vertical maps; `B = Δ[0]` reduces
to the ordinary mapping-space criterion; and pure join factors use the existing terminal
augmentation. No universe equality, characteristic, or nonzero-index assumption is added.

Duplicate searches were repeated with LeanFinder, Loogle, and grep over Mathlib,
`WeilConjectures`, and project `lean/Sheaf` for relative cone/colimit/limit predicates,
homotopy pullback mapping-space definitions, all eight declaration names, and the node id.
Only ordinary categorical colimits, homotopy results, and the existing join/path helpers
were found; no exact notion exists elsewhere. The dependency declarations
`EnhancedDiagramsCones`, `EnhancedFunctorConeCalculus`, `PushoutJoinSaturation`,
`JoinSliceRightFibration`, and `SourceAttachmentGluing` were opened and their signatures
match the uses above.

No mismatch was found. I changed no Lean declaration or node statement. The sandbox module
compiles cleanly with `scompile.py`; all binders and universes are explicit, there are no
private or file-local declarations, and the only postponed proof is the permitted
dependency theorem. The three citers were checked: `lem-coef-infinity-parameter-cone-extension`
and `lem-coef-infinity-relative-kan-existence` use the supplied relative predicates with
the same cone orientations, and `lem-coef-infinity-kan-mapping-restriction` uses their
right-cone/left-cone clauses with the same variance. All three hold.
