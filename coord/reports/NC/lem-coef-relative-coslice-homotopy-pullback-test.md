## Worker report

Stated `SSet.Enhanced.relativeCoslice_homotopyPullback_test` in
`Sheaf.CategoryTheory.RelativeCosliceHomotopyPullbackTest`, with proof `sorry`.
Constructed its three canonical map helpers using `pullback.map`; no data is postponed.
No statement correction or disputed statement. No new nodes or dependency repairs.

Sources read: [HA Definition the project server and Remark the project server, printed pp. 318–319,
September 18, 2017](https://people.math.harvard.edu/~lurie/papers/HA.pdf), for the
actual relative restriction and its left-fibration property;
[Kerodon Proposition the project server, 01BZ](https://kerodon.net/tag/01BZ), for arbitrary
simplicial shape inclusions;
[Proposition the project server, 01NU](https://kerodon.net/tag/01NU), for the
contractible-vertex-fiber test; and
[Proposition the project server, 0329](https://kerodon.net/tag/0329), for replacing a strict
pullback by the constant-path model when one leg is Kan. The generic homotopy-pullback
formulation is the agent-written lemma in the DAG, rather than a verbatim HA statement.
The docstring follows all seven DAG proof steps and names the relevant mechanisms.

Hypothesis and clause correspondence:

- One fixed sufficiently large universe: explicit `universe u` and
  `{A B C D : SSet.{u}}`. Shapes and categories may have every size in that universe;
  none is required finite or nonempty.
- Quasicategories C and D: `[Quasicategory C] [Quasicategory D]`.
- Inner fibration q: `(q : C ⟶ D) (_hq : InnerFibration q)`.
- Degreewise injective shape inclusion: `(j : A ⟶ B) [Mono j]`. For presheaves of
  types, monomorphisms are exactly componentwise injective maps. Thus this does not
  require A and B to be nerves or to have any fibrancy.
- Diagram d and its restriction e: `(d : B ⟶ C)` and the literal composite `j ≫ d`.
  Lean composition is written in diagrammatic order.
- Arbitrary full subcategory C₀: `(P : C _⦋0⦌ → Prop)` and the already defined
  `(fullSubcomplex C P).ι`. Its simplices are exactly those whose vertices satisfy P.
- Every vertex W in C₀, with no test outside it: `_h` begins
  `∀ W : C _⦋0⦌, P W → ...`.
- The four strict apex fibers are exactly the four `fiber` expressions in `_h`, in
  upper-left, upper-right, lower-left and lower-right order. Each is explicitly
  `KanComplex`. The existing `fiber p W` is `pullback (const W) p`, with the point
  factor first; this is the same strict degreewise apex fiber in the statement.
- The two horizontal arrows are `cosliceRestrictionFiber j d W` and
  `cosliceRestrictionFiber j (d ≫ q) (q.app _ W)`. Each is `pullback.map` of the
  published `coherentCosliceRestriction`, with identity point and apex maps.
- The two vertical arrows are `coslicePostcomposeFiber d q W` and
  `coslicePostcomposeFiber (j ≫ d) q W`. Each is `pullback.map` of the published
  `coherentCoslicePostcompose`, with identity point map and apex map q. Thus all
  four arrows have the exact restriction/postcomposition formula; none is arbitrary.
- The square is a homotopy pullback: `IsHomotopyPullbackSquare` applied to those
  four maps. Its definition uses the existing internal interval functor set and
  `homotopyPullbackComparison`, which sends a simplex to its two images and the
  constant interval at their common image. The existential commutativity proof in
  this predicate has no data: proof irrelevance means it does not choose a path.
- The actual total restriction: `fullRelativeCosliceRestriction q j d P` has domain
  `pullback (fullSubcomplex C P).ι (coherentCosliceProjection d)` and codomain
  `pullback (fullSubcomplex C P).ι (relativeCosliceTheta q j d)`. The latter theta
  is the first projection from the published relative coslice pullback followed
  by the last-block apex projection. The map is `pullback.map` with identity
  first coordinate, published `relativeCosliceRestrictionMap` second coordinate,
  and identity apex map. Consequently its second coordinate is exactly the pair
  `(h|A, qh)` and its first coordinate is the prescribed C₀ simplex.
- Both apex projections restrict to the last join block: the source uses
  `coherentCosliceProjection d`, and the codomain uses `relativeCosliceTheta`.
  Structural equalities in the definitions are supplied by the existing named
  `cosliceInclusionsNatural`, functor laws and Yoneda naturality. No mathematical
  lifting lemma has been proved in the delivery.
- Conclusion: `modelCategoryQuillen.I.rlp` of that actual map. Mathlib's I is the
  family of all boundary inclusions. `HasLiftingProperty` retains both exact
  triangle equalities, including all coordinates. The family includes n = 0,
  where `boundary_zero` identifies the boundary with the empty subcomplex.
- There is no colimit existence hypothesis, no restriction outside P, no
  nonemptiness instance, and no stronger fibration or equivalence hypothesis on q.

Dependency interfaces read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `fullSubcomplex`,
  `IsWeakHomotopyEquivalence`, together with Mathlib `SSet`, `Quasicategory`,
  `KanComplex`, internal functor sets and degreewise categorical pullbacks.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`: reexports
  `Sheaf.CategoryTheory.InfinityFibrations`, whose `fiber` and inner/left/right
  fibration conventions are used. Read the full fiber and horn signatures.
- `Sheaf.CategoryTheory.InfinityJoinCoconeAssociativity`: reexports the sharp
  coslice construction from `Sheaf.CategoryTheory.RelativeCosliceLeftFibration`:
  `coherentJoinCoslice`, `coherentCosliceProjection`, `coherentCosliceRestriction`,
  `coherentCoslicePostcompose`, `relativeCoslicePullback`,
  `relativeCosliceRestrictionMap`, `relativeCosliceTheta`,
  `cosliceInclusionsNatural`. Read their complete definitions and the
  `join_cocone_associativity` signature/docstring.
- Mathlib `AlgebraicTopology.SimplicialSet.CategoryWithFibrations`:
  `SSet.modelCategoryQuillen.I` (line 38) and `MorphismProperty.rlp`;
  `Boundary.lean` lines 37–40 and 92–97 give the stated boundary and empty
  dimension-zero boundary. This is the recorded Mathlib match for
  `def-weil-pbc-trivial-kan-fibration`.
- Added the already landed node `def-coef-infinity-relative-cone` to `stmt_deps`,
  as allowed by brief-stage2 §5. Its module `Sheaf.CategoryTheory.RelativeInfinityCone`
  supplies exactly `IsHomotopyPullbackSquare` and `homotopyPullbackComparison`.
  Their whole definitions were read; they give exactly the node's stated path model.
  No definition was copied and the natural-language statement is unchanged.

All stated proof dependencies are imported without `public`:
`RelativeCosliceLeftFibration`, `OppositeSubdivisionKanZigzag`,
`RightFibrationSpaceFiber`, `KanPullbackPathComparison`, `KanFibrationFiberCriterion`,
and `RightFibrationContractibleFibers`. Their recorded interfaces were read.
The seven-step docstring keeps the opposite argument and exact vertex-fiber
identifications, including the constant-path two-out-of-three argument.

Edge cases checked before drafting and again against the final signature:

- P identically false: both total pullbacks are empty; there is no target simplex,
  so boundary lifting holds vacuously, while no exterior-apex test is requested.
- Empty A: the restricted diagram is empty and its sharp coslice is C; every map
  and fiber still uses the same construction. No inhabited shape was assumed.
- Empty B forces A empty for a map A → B; the resulting canonical comparison
  has the expected identity restriction behavior. The theorem includes this case.
- Empty C or D: diagram maps constrain the shapes as usual; no artificial vertex
  or nonempty fiber is selected.
- Empty Kan apex fibers are allowed in the four conjuncts. The weak equivalence
  condition uses components as well as positive homotopy groups, so it does not
  silently discard surjectivity or empty/nonempty distinctions.
- Identity j and identity q yield the expected canonical pullback comparisons.
- Dimension zero is retained by I.rlp, unlike a positive-boundary-only test.

Searches actually run in this session:

- `msearch.py ... leanfinder`: “Relative sharp join coslice restriction of an inner
  fibration is a trivial Kan fibration when the apex fiber squares are homotopy
  pullbacks”. Eight hits: Mathlib Kan fibration definitions and abstract model
  category lifting/right-properness results, no sharp-coslice criterion.
- `msearch.py ... loogle`: `"fibration", "pullback"`. Two hits,
  `SSet.innerFibration_pullbackObjObjπ` and `SSet.fibration_pullbackObjObjπ`.
  These concern Cartesian internal hom, not the sharp join coslice criterion.
- `msearch.py ... grep`: `coslice|left.?fibration|relative.*cocone`, restricted to
  `AlgebraicTopology`. Zero hits.
- `msearch.py ... leansearch`: “relative coslice restriction trivial Kan fibration
  homotopy pullback apex fibers”. Eight hits: abstract trivial fibrations and
  ordinary pullback cones, no matching statement.
- `rg` over project Sheaf, upstream WeilConjectures and the upstream name table:
  searched the item id and `relativeCoslice.*(homotopy|trivial)`; no matching
  statement. A broad coslice search found the published sharp coslice interface
  and its uses, which are reused here. A malformed exploratory regex was corrected
  and rerun; no conclusion was drawn from that error.
- `rg` for the four proposed full declaration names over Mathlib, upstream,
  project Sheaf and `dag/lean_names_upstream.json`: no existing declaration.
- `rg` for `IsHomotopyPullbackSquare` found the existing RelativeInfinityCone
  definition, avoiding a second definition of the path-pullback test.

Validation: prescribed `scompile.py NC <item> <file>` compiled both its sandbox and
library views cleanly on the server (2.5 seconds each). All variables and the universe
are explicitly bound; autoImplicit is disabled. The only postponed theorem is the item.
All lines have at most 100 characters. The first elaboration reported that two
pullback-map square equalities needed the reverse orientation; the structural proofs
were reversed and the final compile was clean.

## Second reading by NC

Independent maintainer second reading completed 2026-10-17 against the immutable snapshot. The item statement was matched clause by clause to `SSet.Enhanced.relativeCoslice_homotopyPullback_test`: one universe `u`; quasicategory instances for `C` and `D`; `_hq : InnerFibration q`; `[Mono j]`; arbitrary `d` and predicate `P`; four strict apex fibers with `KanComplex`; the restriction/postcomposition square using the three delivered pullback-map helpers; and the `modelCategoryQuillen.I.rlp` conclusion, which includes dimension-zero boundary lifting. The helper maps are canonical restrictions/postcomposition maps with the required apex coordinates, and `IsHomotopyPullbackSquare` is the existing constant-path internal path-pullback predicate from `RelativeInfinityCone`.

I read the item node, all five statement dependencies, the source and proof records, the module docstring, every declaration in the delivered module, and the exact signature recorded in `lean.statement`. The hypotheses introduce no finiteness, nonemptiness, colimit, or exterior-apex assumptions, and no universe equality is imposed. Empty `A`, `B`, `C`, `D`, or selected full subcategory, empty fibers, identity maps, and dimension zero are covered by the stated types and lifting property. The module has no hollow definition, no live proof beyond the permitted theorem `sorry`, no pro-etale substitute, and all declarations have source and blueprint docstrings.

I searched the project, upstream source clone, and Mathlib for duplicate declarations and for the relative-coslice homotopy-pullback criterion; no matching existing notion was found. The dependency records and proof dependency list are acyclic and match the imports. I reproduced the per-file compile with:

```
python3 /home/ubuntu/weil-launcher-nt/scompile.py NC lem-coef-relative-coslice-homotopy-pullback-test snapshot/lean/Sheaf/CategoryTheory/RelativeCosliceHomotopyPullbackTest.lean
```

The wrapper confirmed successful sandbox and library compilation (4.1 s and 3.3 s), with no errors or warnings. No lake/global build, live Lean write, mutating Git command, or delivery command was run. Finding repaired in this replacement report: the original section was not a substantive second reading; this section supplies the required checks and evidence. No mathematical or Lean defect found.
