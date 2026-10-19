# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-cartesian-matrix-model.json`: statement, now split in twelve steps. No exact Mathlib match; the recorded searches return component constructions rather than the combined assertion. The original statement is unchanged.
- No new nodes; zero new Mathlib leaves.
- `citations.json`: eleven step/cited-node pairs with verbatim statements supplying the used clauses.
- `searches.jsonl`: actual msearch queries and results. Earlier searches embedded in the inherited item are retained; the NJ queries supplement them.

## Attachments

None. Searches in the read-only slopmaster2 `WeilConjectures/` for the exact blueprint tag and for matrix/model/convolution, biclosed, graph-product and monoid-axiom terminology found no project declaration stating the item. The matrix-convolution hits in GeneralLinearGroup.lean concern evaluation of ring-valued matrices, not graph model categories. The exact master checkout was searched as reference too; it supplies no attachment.

## Wanted sources

WANTED: Fernando Muro, *Homotopy theory of nonsymmetric operads*, Algebraic & Geometric Topology 11 (2011), 1541–1599, DOI 10.2140/agt.2011.11.1541, Definitions 4.2, 9.1 and 10.1, Remark 10.2 and Proposition 10.3, for lem-coef-cartesian-matrix-model. The PDF at https://msp.org/agt/2011/11-3/agt-v11-n3-p13-p.pdf was read online, especially printed pp.1591 and 1595–1597. There is no local archival copy in the allowed literature tree. The proof is marked `by: agent`, with the blueprint ancestry document and the online verification explicitly identified. No download or literature modification was made.

## Problems in the inherited item or brief

There is no statement dispute. The source gives the same matrix product and the same two differently indexed adjoints. Its general Proposition 10.3 is unnecessary as a black-box dependency in this all-cofibrant case: the observation immediately after Definition 9.1 proves the monoid axiom from the pushout-product axiom, and the split gives this argument with the two existing lifting-closure nodes. This is the same route specialized to the item's stronger hypotheses.

The existing lem-coef-graph-product-model and lem-coef-matrix-biclosed-monoidal-structure were opened and read. They assume projective chain complexes over a commutative ring. They are not statements about arbitrary cartesian closed model categories and cannot be cited here. Their proof text was not used as if it were a more general statement. The general presentability and lifting leaves already in the DAG suffice, so no replacement or duplicate nodes were created.

The existing chapter and unit were read, including the unit's realized bindings. This item is a supporting foundation in the existing created-item chain, not a key statement of the unit. Its inherited unit/chapter, blueprint ancestor and via list are retained. The ancestor's current main-20261015 paragraph 2 is the displayed finite-level derived mapping-complex adjunction before the inverse limit. The split makes the matrix foundation needed by the fixed-object rectification ancestor explicit and does not change any chapter or unit proof route. No SGA source is used.

## Not duplicates

No new nodes. Whole-blueprint searches for `matrix convolution`, `matrix`, `biclosed`, `product model`, and `monoid axiom` found no blueprint node with this statement. The two existing chain-complex matrix nodes are strictly specialized to a different base and were not duplicated or changed. Existing general Mathlib leaves are cited directly.

## Review by NJ

I read the item's statement, the six-functors chapter, its bound biduality unit, the blueprint exceptional-adjoint statement and paragraph 2 of its proof, and Muro's online matrix-graph definition, both Hom formulas, product-model remark, monoid-axiom definition and all-cofibrant observation. I compared every conclusion, including the actual generators, the ordering of the two variables, and the empty vertex set. I also read the statements of all nine distinct cited nodes. For the five existing Mathlib leaves I checked the indicated pinned source: Presheaf.lean:90–96, LocallyPresentable.lean:93–101, HasCardinalLT.lean:199–206, LiftingProperty.lean:35–77, and TransfiniteCompositionLifting.lean:265–273. There are no new nodes whose sources or hypotheses would need separate review.

Step 1 uses only the model-category axioms explicitly stated in lem-coef-model-infinity-derived-adjunction. Products of families have no naturality conditions between distinct coordinates. I wrote both lift-detection tests: initial objects in the other coordinates for a left test map, terminal identities there for a right test map. Functorial factorizations are taken coordinatewise. This supplies both weak factorization systems and does not quietly assume a projective diagram theorem.

Step 2 uses the set-generated weak-factorization-system convention of lem-coef-combinatorial-localization-presentability. The supported-object/evaluation adjunction identifies each lifting problem, proving the claimed right classes for exactly the displayed generators. In the unused coordinates the arrow is the identity of the initial object, not an unspecified initial arrow.

Step 3 uses the ordinary presheaf clause of lem-coef-presheaf-local-presentability, not an infinity-categorical presentability theorem or a simplicially enriched diagram theorem. Its smallness, locally presentable target and pullback hypotheses hold: the index is the discrete category on the small set S squared, and a model category has all small limits.

Step 4 uses lem-coef-object-presentability-rank only for domains in the base locally presentable category, and lem-coef-small-family-regular-bound for the small family of their rank ordinals. The resulting regular cardinal is greater than every rank; a more filtered diagram is also filtered for each smaller rank. Evaluation computes colimits, so the supported domains have the same preservation property. This verifies smallness for cell chains without assuming every model category is combinatorial. The cofibrancy and pushout assertions are immediate applications of the already constructed coordinate classes and the actual all-cofibrant and left proper hypotheses of the item. No chain-complex left properness is substituted.

Steps 5–8 are written universal-property calculations. In Step 5 exponential adjunction gives preservation of colimits by either product factor, including the initial object; no claim that arbitrary finite limits commute with arbitrary colimits is used. Steps 6 and 7 use the definition in def-sfb-monoidal-category for exactly the associator, the unitors, pentagon and triangle, and prove these identities on each coproduct injection and each product projection. The labels of intermediate vertices stay fixed; no nonexistent symmetry of the convolution is assumed. Step 8 computes both Hom bijections, with inverse evaluation maps and naturality, rather than merely asserting that a biclosed structure exists. Its first currying fixes P(u,t) and forms the product over t; its second currying fixes Q(s,u) and forms the product over s. This agrees with both the item and Muro.

Step 9 identifies the actual pushout-product arrow using maps from its source to an arbitrary object. Coproduct summands with different intermediate vertices are not spuriously multiplied together. Step 10 uses the two lifting-class identities in lem-coef-model-infinity-derived-adjunction to prove the elementary coproduct closure argument explicitly. Thus it does not cite closure of weak equivalences under arbitrary coproducts, which would be an unjustified substitute. The base pushout-product axiom applies to every summand and makes every summand trivial when either graph map is trivial. Every graph, including the diagonal unit, is cofibrant, and the identity replacement verifies the unit axiom.

Step 11 cites def-coef-nonsymmetric-monoid-axiom for its finite nonempty iterated-pushout-product class and equivalent closed-class condition. The induction also covers a trivial factor that first occurs late in the list. I applied lem-coef-lifting-class-closure to the class of graph fibrations for pushouts/retracts, and lem-coef-transfinite-left-lifting to that same class for small continuous ordinal chains. These statements say precisely the closure facts required; neither is merely a definition of flatness, a definition of weak equivalence, or a theorem about a different lifting class. The resulting closed class is the graph trivial cofibrations, already contained in weak equivalences. The citations JSON quotes all these exact statements.

Step 12 checks universe sizes and the empty and singleton cases. For S empty the family category has one object and only its identity, and both generating sets are empty. For S a singleton the construction recovers the base cartesian product and exponential. For a two-element set the off-diagonal unit entries are initial, so the unitor calculation keeps exactly the expected intermediate vertex. Arbitrary infinite small S causes coproducts and products rather than finite sums; all arguments above use small versions of these. No finite-S or nonempty-S hypothesis was silently introduced. No statement had to be corrected.

I checked delivery-errors B1–B10, C1–C8, D1–D5 and E1–E7 against the source and the written steps. The statement contains no new undefined notion, no new unsplit statement carries a hidden proof, and no new-node Mathlib search is invented. Source formulas use ordinary single TeX escaping in parsed JSON. Every non-elementary borrowed fact is an existing cited statement; the remaining coordinatewise, universal-property and coproduct-lifting calculations are written explicitly and marked elementary. No whole clause was moved to a new node, no source argument was replaced by a list of references, and no citation uses another node's proof instead of its statement. The proof dependencies are exactly the union of the step citations. The five nontrivial general tools used here are already Mathlib leaves; all other cited nodes are definitions/conventions in the inherited statement, so no off-route tool declaration is needed. All twelve steps are shorter than 2000 characters; I checked the routine associator/coherence and pushout comparison computations in particular for hidden independent lemmas. No compiler, Lake command, forbidden local checker, live-project write or direct git command was run.

## Unfinished work

None for this one-level stage-1 split. The existing non-leaf convention/definition nodes retain their own proof obligations; no claim that the entire transitive DAG is proved is made.
