## Worker report

The module `Sheaf.AlgebraicTopology.SimplexwiseCategoricalBaseChange` states
`SSet.universal_categorical_equivalence_iff_simplexwise`, with its entire proof `sorry`.
It introduces no definitions, new nodes, or dependency modules. In particular, the canonical
base-change map is rendered directly by the existing Mathlib `pullback.map`.

Hypothesis and clause correspondence:

- The fixed universe of small simplicial sets is `u`, with `{X Y S : SSet.{u}}`.
  The diagram is exactly `(f : X ⟶ Y) (p : Y ⟶ S)`, so the structure map of `X` is `f ≫ p`.
- For `(T : SSet.{u}) (t : T ⟶ S)`, `X_T` and `Y_T` are the source and target of
  `pullback.map (f ≫ p) t p t f (𝟙 T) (𝟙 S) ... ...`, namely
  `pullback (f ≫ p) t` and `pullback p t`. Mathlib's presheaf limits are degreewise limits.
  The morphism is induced by `f` on the first factor and the identity on the second factor.
  Its two square equalities use only the category identity laws.
- Condition (i) is the left-hand universal quantifier over every `T` and `t`.
- For each such induced map `g`, categorical equivalence is precisely the dependency's
  expression `∀ (C : SSet.{max u v}), C.Quasicategory →
  ((hoFunctor.map ((MonoidalClosed.pre (uliftFunctor.{v, u}.map g)).app C)).toFunctor).
  IsEquivalence`. This tests restriction on the ordinary homotopy categories of functor
  simplicial sets. The extra universe `v` permits every enlargement of the test universe.
  No realization/core-testing substitute or Kan-Quillen weak equivalence is used.
- Condition (ii) is the right-hand quantifier `(r : ℕ) (σ : Δ[r] ⟶ S)`, followed by
  exactly the same categorical-equivalence condition for the base-change map along `σ`.
  All dimensions, including zero, and all simplices, including degenerate ones, are tested.
- The logical equivalence of (i) and (ii) is `↔`.
- There are no quasicategory, fibration, monomorphism, finiteness, or nonemptiness hypotheses
  on `X`, `Y`, `S`, `f`, `p`, `T`, or `t`. The quasicategory assumption is solely on the
  testing target `C`, as required by the specified definition of categorical equivalence.

Dependencies read and used:

- `def-cbc-enhanced-diagrams-cones`: read its full Lean module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`, including the recorded
  `SSet.Enhanced.coneCategory` and its docstring. The primitives relevant here are the
  Mathlib `SSet`, `SSet.stdSimplex`, `SSet.Quasicategory`, and internal functor objects
  which that module explicitly reuses. None of its separate mapping-space or cone
  constructions is needed in this statement.
- `lem-coef-joyal-model-structure`: read the complete signature and proof docstring of
  `SSet.exists_joyal_model_structure` in `Sheaf.AlgebraicTopology.JoyalModelStructure`.
  Its second conjunct supplies exactly the displayed testing convention, including
  `SSet.uliftFunctor.{v, u}` and the test universe `max u v`. The expression is repeated
  literally because this dependency does not introduce a separately named predicate.
- Read the signatures and docstrings of Mathlib `SSet.hoFunctor`, `SSet.uliftFunctor`,
  `SSet.stdSimplex`, and `CategoryTheory.Limits.pullback.map`. The latter already gives
  the required canonical map, so no helper definition is necessary.

Edge cases checked before finalizing the statement:

- Empty `T`: both ordinary pullbacks are empty, and their induced map is an isomorphism.
- Empty `S`: maps `p` and `f` force `Y` and `X` to be empty; any test `T ⟶ S` forces `T`
  empty, while the simplex quantifier has no maps. Both conditions hold.
- Dimension zero is present as `r = 0`; vertices are not omitted. Degenerate simplices
  are included because no nondegeneracy condition is imposed on `σ`.
- The case `T = S`, `t = 𝟙 S` remains among the arbitrary tests.
- Arbitrarily large small simplicial sets are allowed; there is no finite-dimensional
  or finite-nondegenerate-simplex bound on `T`.
- No property of `f` or `p` is silently inferred as a hypothesis. The canonical map
  uses only their composability. All variables and both universe parameters are explicit.

Source check: read HTT Proposition the project server and its proof, printed p. 181 (PDF page 199),
from the author's Harvard mirror,
https://people.math.harvard.edu/~lurie/papers/HTT.pdf . The IAS URL in the node timed out
in the web reader; the mirror contains the cited proposition. It treats arbitrary
simplicial sets and explicitly handles the empty case. The module docstring supplies
its proof plan: filtered finite subsets, induction by attaching a maximal simplex,
and left properness for the resulting pushout comparison. The node's own proof list is
empty, and no proof dependencies are recorded to import.

Searches for an existing statement (the prescribed `msearch.py`, group N9 and this item):

- LeanFinder: "A map of simplicial sets over S is a categorical equivalence after every
  base change if and only if it is so after pullback along every standard simplex of S".
  Eight hits concern stable morphism properties and Kan-Quillen fibrations; none is this
  simplexwise categorical-equivalence theorem.
- LeanSearch: "Categorical equivalences of simplicial sets over a base tested after
  pullback to every standard simplex". Eight hits concern Yoneda, standard simplices,
  singular simplices and related primitives, with no matching theorem.
- Loogle: `SSet, pullback, CategoricalEquivalence` gave no hits (unknown `pullback`).
  Retried with `"SSet", "pullback"`: six hits on relative cell complexes, finite
  pullbacks and (inner) fibrations of internal homs, none matching this criterion.
- Mathlib grep: `categoricalEquivalence|CategoricalEquivalence|simplexwise|universally.*equivalence`
  in AlgebraicTopology returned zero hits.
- Project/upstream `rg -n` with the same categorical-equivalence/simplexwise names found
  no upstream match. Side-project hits include the separate core-based
  `CategoryTheory.CoherentNerve.IsCategoricalEquivalence` and mapping-simplex interfaces;
  those neither state this criterion nor use the node's requested homotopy-category
  testing convention. Additional searches for the chosen declaration name and
  `universal.*categorical|categorical.*simplexwise` found no matching declaration.
- `grep -rn` for this node id in the upstream `WeilConjectures` tree found no match.
  A name/id search of `dag/lean_names_upstream.json` also found no matching declaration.

No statement correction, statement dispute, or unusable dependency interface was found.
The source node currently has `status: unsplit` and an empty proof list; those fields are
preserved exactly as required. Only its `lean` field is added in this delivery.

Validation: the prescribed single-file compile accepts the statement. The initial compile
identified a field-notation line break, which was repaired; the next compile accepted the
type and identified two long lines, which were wrapped. The final clean compile and
`deliver2.py --no-push` results are recorded below after running them.

Final compile: `scompile.py N9 lem-cbc-simplexwise-categorical-base-change` with this
module completed successfully in both sandbox and module-path modes, with no warnings
or errors (2026-10-17 UTC).

## Second reading by N9

I independently read the current node (including its five-step proof), the sandbox module,
both statement-dependency nodes and their complete declaration signatures, the three additional
proof inputs, and HTT Proposition the project server with its surrounding text. The source is HTT, not a
Stacks result. I used the author's mirror https://people.math.harvard.edu/~lurie/papers/HTT.pdf,
printed p. 181, PDF page 199 (zero-based page 198). The proposition introduces an arbitrary
composable diagram of simplicial sets. The Cartesian-fibration assumptions of Proposition
the project server are not hypotheses of the project server. Its statement agrees with the node, including emptiness.
No statement correction is necessary; there are no new nodes or dependency repairs to review.

Object/hypothesis/conclusion checklist (written from the node before comparing the signature):

1. A fixed universe of small simplicial sets, with three objects X, Y, S:
   `{X Y S : SSet.{u}}`. PASS. These are Mathlib's actual simplicial sets, reused by
   `def-cbc-enhanced-diagrams-cones`, not enhanced categories or fibrant replacements.
2. Composable maps X -> Y -> S, with X's structure map their composite:
   `(f : X ⟶ Y) (p : Y ⟶ S)` and `f ≫ p`. PASS; neither an over-object witness nor any
   additional commutativity or geometric assumption is introduced.
3. Each arbitrary small test object and map to S: `(T : SSet.{u}) (t : T ⟶ S)` in the
   left-hand universal quantifier. PASS. No finiteness, fibrancy, injectivity, or
   nonemptiness instance is required.
4. The ordinary degreewise pullbacks X_T and Y_T and canonical induced map f_T:
   `pullback.map (f ≫ p) t p t f (𝟙 T) (𝟙 S) ... ...`. PASS. I read Mathlib's
   `pullback.map` definition in `CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean`:
   its domain is `pullback (f ≫ p) t`, its codomain `pullback p t`, and it is the
   pullback lift of `pullback.fst ... ≫ f` and `pullback.snd ... ≫ 𝟙 T`.
   The displayed equalities are just identity laws. Presheaf pullbacks compute degreewise.
5. Categorical equivalence in the specific dependency convention: for this induced map g,
   `∀ (C : SSet.{max u v}), C.Quasicategory → ((hoFunctor.map
   ((MonoidalClosed.pre (uliftFunctor.{v, u}.map g)).app C)).toFunctor).IsEquivalence`.
   PASS. This is literally the weak-equivalence test in the second conjunct of
   `SSet.exists_joyal_model_structure`, whose signature I opened. Restriction reverses
   the map: Fun(Y_T,C) -> Fun(X_T,C). Mathlib's `hoFunctor` imposes the identity and
   triangle relations on the free category of edges; it is not the core or realization.
   Its `uliftFunctor` raises each degree from u to max u v. The test-quasicategory
   hypothesis belongs only to C, not to X, Y, S, or T. Universe v is unrestricted and
   is the same on both sides, exactly as in the dependency; v = 0 includes small tests.
6. Condition (i), for every T,t: the whole left-hand `∀ T t C, ...`. PASS. The last
   quantifier is the expansion of categorical equivalence; its position introduces no
   choice of test object dependent on C.
7. Condition (ii), every dimension and every simplex: the right-hand
   `∀ (r : ℕ) (σ : Δ[r] ⟶ S) (C : SSet.{max u v}), ...`. PASS. The same canonical
   `pullback.map`, now with t = σ and `𝟙 Δ[r]`, is tested by the identical formula.
   `Δ[r]` is Mathlib's Yoneda standard simplex, as required by the dependency node.
8. Equivalence of the two conditions: the outer `↔`. PASS; neither direction is omitted.
9. No further assumptions and empty objects allowed: the entire signature has no
   instance binders restricting the input objects or maps. PASS. Pullback existence is
   supplied by the existing presheaf category instance, not a hypothesis on these maps.

Edge cases: empty T gives empty pullbacks and an isomorphism. Empty S forces X, Y and any
admissible T empty, while there are no maps from a standard simplex to S; both sides hold.
Empty X or empty Y is allowed without changing the test or replacing an empty map by a chosen
one. Zero-dimensional simplices occur at r = 0; every vertex and degenerate simplex is tested.
The identity test T = S is included. Infinite-dimensional T and T with infinitely many
nondegenerate simplices are unrestricted. There are no coefficient rings or characteristics
in this statement. The independent enlargement parameter v imposes no equality or upper bound
on u. Both universes and all variables are explicitly bound with autoImplicit disabled.

Independent duplicate searches (different queries from the first worker, through msearch.py):

- LeanFinder: "A morphism of simplicial presheaves is universally a Joyal equivalence exactly
  when its restrictions over representable simplices are categorical equivalences".
  Eight hits: Yoneda/restricted Yoneda, nerve reflectivity and simplex-category equivalences;
  none states the base-change criterion.
- LeanSearch: "Universal categorical weak equivalences are detected by base change to simplices
  of the base". Eight hits: generic model weak equivalences and over-category instances;
  none tests all simplex pullbacks.
- Loogle: `"SSet", "baseChange"`. Four hits: stability of inner fibrations, anodyne maps,
  inner anodyne maps and monomorphisms. None is this theorem.
- msearch grep: `universal.*categorical|categorical.*simplex|Joyal.*pullback`.
  Three generic categorical universal-property hits, no matching theorem.
- Direct rg over the entire upstream WeilConjectures tree and the project's lean/Sheaf:
  `universally.*categorical|universal.*categorical|simplexwise|3\.2\.2\.8`.
  No upstream match. I opened the project's `MarkedMappingSimplexDescent` declaration:
  it concerns relative marked mapping quasicategories, not this arbitrary unmarked map.
  Other hits concern Kan locally trivial realization, joins, or proof prose. The first
  attempted upstream AlgebraicTopology subdirectory does not exist; I repeated the search
  on the whole WeilConjectures tree. Mathlib AlgebraicTopology has only generic Joyal tricks
  and the existing simplicial primitives, not the criterion. No duplicate declaration found.

Mismatches and repairs:

- The worker report says the node has status unsplit and an empty proof/dependency list.
  That describes an older snapshot: the current sandbox and shared node both have status
  split and the same five-step proof. I preserved all current node fields; only `lean`
  differs from the shared node.
- H8: the old docstring did not carry the current node's five proof steps or name its
  filtered-colimit, relative-cell, and cofibrant-span inputs. It vaguely invoked left
  properness without isolating the injective legs. I replaced only the proof docstring
  with the five-step argument: finite-subset reduction, lexicographic induction with
  the empty/r = 0 cases, possibly noninjective characteristic map, degreewise pushouts,
  and the cube lemma on the boundary-to-simplex legs with all six objects cofibrant.
- Stage 2 import rule: added ordinary proof-only imports of
  `Sheaf.AlgebraicTopology.JoyalFilteredEquivalences`,
  `Sheaf.CategoryTheory.ModelCofibrantColimitComparison`, and
  `Mathlib.AlgebraicTopology.SimplicialSet.Skeleton`.
  I read their actual signatures: the filtered-colimit theorem uses the identical Joyal
  testing predicate; the cube lemma's second conjunct is exactly the required cofibrant
  span comparison; `SSet.relativeCellComplexOfMono` supplies the boundary-cell pushouts.
  They introduce no assumption in this item's signature and the imports compile together.

The Lean signature itself was already correct and is unchanged. The node's lean.statement
is verbatim equal to the file's complete theorem signature. There are no definitions, hollow
objects, private copies, auxiliary postponed statements, or proofs beyond the named theorem's
whole `by sorry`. All source/blueprint docstrings and the namespace conventions are present;
all lines have at most 100 characters.

Validation after repairs: the prescribed scompile.py command accepted the single delivered
module in sandbox and module-path modes, with no warnings or errors. It also compiled the
required JoyalFilteredEquivalences overlay dependency. Dry-run and delivery results follow.

Dry run: deliver2.py --no-push printed OK for d7a6eee3af: preflight and compilation passed;
exactly the module, item node and report were staged, and nothing was pushed.
