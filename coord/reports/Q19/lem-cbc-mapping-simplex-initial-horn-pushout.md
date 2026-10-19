## Worker report

The module `Sheaf.CategoryTheory.MappingSimplexInitialHornPushout` states the exact marked
initial-horn pushout. Its three helper definitions specialize the existing mapping simplex,
subcomplex inverse image and induced marking. The only postponed theorem is
`SSet.Enhanced.mapping_simplex_initial_horn_pushout`; its docstring gives all six proof steps
of this node. No definition uses postponed existence to choose data.

The previous run confused Q53's accepted stage-1 split with a stage-2 delivery. I read the
current node: `reviewed` names Q53's stage-1 proof review, but the node has no `lean` record.
The Q53 report is a mathematical splitting report, not a Lean statement delivery.

The theorem asserts existence of marked simplicial maps with their canonical formula,
not existence of an unconstrained attaching map. The equality on every simplex uniquely
determines `c`; the pushout commutativity and the injective horn inclusion uniquely determine
`cK` as its restriction. This packages the node's assertion that the given formula defines a
marked map and its restriction without adding a choice-based definition or separate
postponed construction lemmas.

The natural statement is unchanged. The only node changes are the `lean` record and addition
of two already landed statement dependencies supplying the initial-edge marking and induced
marking: `def-coef-infinity-marked-coanodyne` and
`lem-coef-marked-anodyne-lifting-calculus`. This is allowed by brief-stage2 section 5,
STMT_DEPS MAY GAIN LANDED NODES. There are no new nodes, repaired dependency records,
statement corrections or disputed assertions.

Each hypothesis and conclusion is rendered as follows. Write N for the natural-language
dimension, to distinguish it from the predecessor `n` used in the Lean statement.

| Natural-language hypothesis or clause | Lean rendering |
| --- | --- |
| Small simplicial sets, simplices and degreewise products | `SSet.{u}`, `Δ[n + 1]`, the imported `Marked.product` and existing `mappingSimplex`; `u` is explicitly bound. |
| N at least one | `{n : ℕ}` and dimension `n + 1`, parametrizing every positive dimension including one. |
| An arbitrary chain A_0 left-arrow ... left-arrow A_N, with its transitions | `A : SimplexChain.{u} (n + 1)`, the recorded functor `(Fin (n + 2))ᵒᵖ ⥤ SSet.{u}`. A transition is `A.map (homOfLE h).op`; no extra injectivity or fibrancy hypothesis. |
| M has pairs (alpha,a) and the specified operators | `initialEdgeMappingSimplex A` has underlying `mappingSimplex A`, exactly the recorded dependent-pair construction and `mappingSimplexOperator`. |
| T_N consists exactly of degenerate edges and [0,1] | The existing `Marked.initialMarkedSimplex n` has marking `Set.range (Δ[n + 1].σ 0) ∪ {stdSimplex.edge ... 0 1 ...}`. |
| An edge of M is marked iff its base belongs to T_N and its fibre coordinate is degenerate | `initialEdgeMappingSimplex.marking` is the conjunction of membership in `(markedMappingSimplex A).marking` and membership of its projected base in `(Marked.initialMarkedSimplex n).marking`. The first predicate is exactly degeneracy of the second coordinate. |
| K is the initial horn | `horn (n + 1) (0 : Fin (n + 2))`. |
| M_K is M times over the simplex K | `initialHornMappingSimplexSubcomplex A` is the inverse image of that horn under `mappingSimplexProjection A`. Its degreewise subtype is the canonical concrete pullback along a subcomplex inclusion; it retains exactly pairs whose base is in K. |
| M_K has the induced marking and includes into M | `initialHornMappingSimplex A` uses `Marked.inducedMarking` along the preimage-subcomplex inclusion; `Marked.inducedMarkingMap` is the third arrow of `IsPushout`. |
| D^T and K^T have the stated markings | `Marked.initialMarkedSimplex n` and `Marked.inducedMarking (Marked.initialMarkedSimplex n) (horn ...).ι`. |
| The cylinder is A_N^flat times D^T | The type of `c` uses `Marked.product (Marked.flat (A.obj (op (Fin.last (n + 1))))) (Marked.initialMarkedSimplex n)`. |
| c(a,alpha) equals (alpha,t_(N,alpha(last))(a)) in every degree | The first conjunct quantifies over every `r : SimplexCategoryᵒᵖ`, `a` and `α`, and equates `c.val.app r (a, α)` to the dependent pair with first coordinate `stdSimplex.asOrderHom α` and second coordinate the chain transition, applied to `a` in degree `r`. |
| The formula defines a marked simplicial map | `c` is quantified as a morphism of `Marked`, so it is a natural transformation preserving markings, with the exact coordinate formula imposed as an equation. |
| c restricts to a marked map c_K | The quantified `cK` has domain A_N^flat times K^T and codomain `initialHornMappingSimplex A`. The square's commutativity identifies its composite with the inclusion with the restriction of `c`. The inclusion is degreewise injective, so this uniquely specifies c_K. |
| The other span arrow is the product inclusion | `Marked.productMap (𝟙 (Marked.flat ...)) (Marked.initialMarkedHorn n)`. |
| The structure maps are the inclusion M_K to M and c | These are the third and fourth arguments of `IsPushout`. |
| Pushout in marked simplicial sets, equivalently unique extensions of compatible marked maps to every Z | `IsPushout` is instantiated in `SSet.Marked.{u}`, not in unmarked simplicial sets or a homotopy category. Its colimit condition is exactly the strict universal property with all arrows preserving markings. |
| Includes N=1, where K is vertex zero and M_K is A_0^flat | `n = 0` is allowed. The horn criterion then forces the base constant zero. The preimage subtype is exactly A_0 degree by degree, with precisely degenerate fibre edges marked. |
| Empty terms allowed | There is no `Nonempty`, chosen vertex, nonempty fibre, Kan or quasicategory binder. All definitions are formulas on existing simplices. |

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: the module documents reuse of Mathlib's
  `SSet`, `stdSimplex`, `horn` and degreewise monoidal products. Its recorded declaration
  `SSet.Enhanced.coneCategory` concerns cones; no cone data is needed in this specialization.
- `Sheaf.CategoryTheory.CartesianMappingSimplexPresentation`:
  `SSet.Enhanced.SimplexChain`, `MappingSimplexDegree`, `mappingSimplexOperator`,
  `mappingSimplex`, `mappingSimplexProjection`, `markedMappingSimplex` and their signatures
  and docstrings. Their recorded main theorem supplies presentations, which this statement
  does not assume. No second chain or mapping-simplex definition is introduced.
- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`: `SSet.Marked`, `Marked.Hom`,
  `markedCategory`, `flat`, `product`, `productMap`, with their full source definitions.
  Morphisms are subtypes of simplicial maps satisfying preservation of marked edges.
- `Sheaf.AlgebraicTopology.MarkedAnodyneLiftingCalculus`: `Marked.inducedMarking` and
  `Marked.inducedMarkingMap`, with their signatures and docstrings.
- `Sheaf.AlgebraicTopology.MarkedCoanodyne`: `Marked.initialMarkedSimplex` and
  `Marked.initialMarkedHorn`, with their signatures and docstrings. Only these exact marked
  objects and maps are used, not any coanodyne-class assertion.
- Mathlib `SSet.Subcomplex.preimage`, `SSet.Subcomplex.ι` and
  `CategoryTheory.IsPushout` (the latter in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`). I read the source of
  the preimage and `IsPushout` definitions: the latter is a commutative square with a
  colimit pushout cocone.

Edge cases checked before writing:

- N=1: T marks both constant base edges and the nonconstant interval edge; K is vertex zero,
  so the restricted marking is exactly A_0^flat. The span is the marked mapping-cylinder
  span. No N at least two assumption has slipped in.
- N=2: the only nondegenerate edge outside the horn is [1,2]. It is not selected by T, so
  neither its mapping-simplex copy nor its cylinder copy is marked, even for degenerate
  fibre coordinate. The initial edge [0,1] lies in the horn and is selected on both sides.
- N at least three: every edge is already in the initial horn; missing higher simplices
  still end at N and are supplied by the final-fibre cylinder.
- Empty A_N: any simplex outside the horn would have fibre coordinate in A_N, hence cannot
  exist. The horn restriction is the whole mapping simplex, and the cylinder is empty.
- All terms empty: all three other vertices of the pushout span are empty, and the universal
  extension is the unique map out of the empty marked simplicial set.
- Noninjective transitions: two cylinder simplices may be identified over the horn. The
  theorem imposes no mono condition on `cK`; compatibility in the pushout square handles
  precisely these identifications.
- Constant base edges: they are selected, but marking in M still requires the fibre edge
  degenerate. This avoids inadvertently marking all vertical edges.

Searches for an existing declaration:

- `msearch.py` LeanFinder: "A marked mapping simplex is the pushout of its initial horn
  restriction and the last term times the simplex". Eight hits: ordinary two-dimensional
  horn pushouts and horn maps, not this marked chain-dependent result.
- `msearch.py` Loogle: `"SSet", "IsPushout"`. Eight hits including
  `SSet.Subcomplex.BicartSq.isPushout`, the three ordinary two-horn pushouts,
  `SSet.Subcomplex.unionProd.isPushout` and relative cell-complex squares. None is the marked
  mapping-simplex attachment; in particular the attaching map here need not be injective.
- `msearch.py` LeanSearch: "The mapping simplex is the pushout of the initial horn
  restriction and the last fibre times the simplex". Eight hits, again ordinary horn
  pushouts, simplicial realization and the horn definition. No exact match.
- `msearch.py` Mathlib grep `mappingSimplex|mapping_simplex|initialHorn|initial_horn` in
  `AlgebraicTopology`: zero hits.
- Direct `rg` with those patterns in the upstream `WeilConjectures` and side `lean/Sheaf`
  trees, plus the item id in the upstream tree: no upstream declaration, and side hits are
  the existing mapping-simplex presentations, comparison, final-edge, cone-fibre,
  termwise-equivalence and descent constructions. None states this pushout.
- Direct side search for `initial.*[Hh]orn.*[Pp]ushout|[Pp]ushout.*initial.*[Hh]orn`
  found only a comment about the one-dimensional coanodyne generator, not this theorem.
- Searches for marking and restriction helpers found and reused `initialMarkedSimplex`,
  `initialMarkedHorn`, `inducedMarking` and `inducedMarkingMap`; their owning node records
  were read and added as already landed statement dependencies. No independent notion
  required a new definition node.

Source checked: Lurie's HTT Section 3.2.2, printed p. 179 (mapping-simplex definition and
Notation the project server), and the last-term cylinder reduction in the proof of Corollary the project server,
printed p. 186. The IAS URL timed out; the author's Harvard copy was readable at
https://people.math.harvard.edu/~lurie/papers/HTT.pdf. The selected-marking strict pushout is
the node's agent-written coordinate formulation of that reduction. No source correction
is required, and no file was written into the shared repository.

Validation: every delivered Lean file is checked individually with the prescribed
`scompile.py` wrapper; final compiler and dry-run results are recorded below.

Final file check: `scompile.py` returned exit code 0 for the sandbox module and its
library-path check, with no errors or warnings. All universes and variables are explicitly
bound, lines are at most 100 characters, and the theorem above is the sole `sorry`.

Delivery dry run: `deliver2.py Q19 lem-cbc-mapping-simplex-initial-horn-pushout --no-push`
printed `OK (dry run)`: preflight and per-file compilation passed for commit b17d7ecaf3.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
