## Worker report

Module: `Sheaf.CategoryTheory.RelativeKanExistence`, main declaration
`SSet.Enhanced.exists_relative_pointwise_kan`. The node's natural-language statement
is unchanged. Both the relative left Kan extension and its right-hand dual are
stated, as **two separate implications**. No theorem is proved in this delivery.
The two named postponed theorems are `exists_relative_pointwise_kan` and
`existsUnique_kanSliceJoinCones`; both have source and complete proof-plan docstrings.

The earlier sandbox draft had three defects, now repaired: it required the local
colimit and limit hypotheses simultaneously, allowed arbitrary uncharacterized cone
maps, and duplicated the existing `SSet.Enhanced.IsIsofibration`. Its report also
contained a purported second reading; that section has been removed for the actual
independent second reader.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The three quasicategories are `{C D B : SSet.{u}}` with the three explicit
  `Quasicategory` instances. A single arbitrary universe `u` is the fixed sufficiently
  large universe in the statement; every universe and term variable is bound explicitly.
- The full subcategory is `(fullSubcomplex C P).toSSet`, where `P` is an arbitrary
  predicate on vertices. Its inclusion is `(fullSubcomplex C P).ι`.
- The functor `p : D ⟶ B` has hypothesis `hp : IsIsofibration p`. The imported definition
  contains inner-horn lifting and, for every base equivalence with specified source,
  an equivalence lift with that source and exactly that image. This is the node's
  source-fixed isofibration condition. Its quasicategory conjuncts repeat conditions
  already assumed, rather than imposing any further mathematical hypothesis.
- The maps `h` and `s` have exactly the domains in the node. `compat` is the literal
  equality `h ≫ p = (fullSubcomplex C P).ι ≫ s`.
- `kanSlice A c true` consists degreewise of `(n+1)`-simplices ending at `c`, whose
  entire initial face belongs to `A`. It is precisely the strict slice pullback
  `A ×_C C_{/c}`. `kanSliceSubcategoryProjection A c true` retains that entire face
  with its membership proof, giving `a_c : K_c → A`.
- `kanSliceCocone A c` is the canonical `k_c`, not an arbitrary map. Its specifying
  predicate `IsKanSliceCocone` fixes the pure slice restriction to
  `kanSliceProjection A c true`, the pure point restriction to `const c`, and its
  value on every mixed convolution generator. On a mixed `(m,n)` generator it
  restricts the stored `(m+1)`-simplex along the ordinal map that fixes the initial
  `m` block and collapses the whole last block to the new final vertex. In particular,
  when the point block has degree zero, it gives the stored slice simplex itself.
- The first implication's antecedent quantifies `∀ c, ∃ q` with exactly the three
  local requirements: `rightJoinConeInclusion _ ≫ q = a_c ≫ h`,
  `q ≫ p = k_c ≫ s`, and `IsRelativeColimitDiagram p q`. There is no compatibility
  condition between different local choices.
- Its consequent is `∃ H`, with exact restriction `A.ι ≫ H = h`, exact base
  `H ≫ p = s`, and `∀ c, IsRelativeColimitDiagram p (k_c ≫ H)`.
- In the second implication, `kanSlice A c false` instead stores a simplex starting
  at `c` with its entire final face in `A`. Its projection is `a_c` for the dual
  index `L_c`. `kanSliceCone A c` has the pure base projection, pure apex `const c`,
  and every mixed generator fixed by collapsing the whole first block to the new
  initial vertex and retaining the final block. The helper `kanSliceConeCollapse`
  expresses that ordinal map; its `eqToHom` only removes `0 + n.len` in the target.
- The second antecedent independently assumes local `IsRelativeLimitDiagram p q`
  lifts with `leftJoinConeInclusion _ ≫ q = a_c ≫ h` and `q ≫ p = l_c ≫ s`.
  Its consequent independently gives the two exact global equations and
  `∀ c, IsRelativeLimitDiagram p (l_c ≫ H)`.
- There is no completeness, cocompleteness, finiteness, or nonemptiness hypothesis.
  The universal conclusions are the strengthened pointwise conclusions explicitly
  permitted by the node, separately for the two alternatives.

Canonical construction and postponed construction proof:
`existsUnique_kanSliceJoinCones` states unique existence of precisely the two canonical
maps introduced by this node. Its docstring gives the degreewise construction on all
three normal-form summands, the compatibility with operators including when a block
becomes empty, and uniqueness. `kanSliceCocone` and `kanSliceCone` use its `∃!`
specifications, which determine the entire simplicial maps up to literal equality.
This is the explicitly permitted unique-construction use of a postponed theorem
(AGENTS.md §5), rather than selection of unspecified data from mere existence.
The construction, its specifying predicates, and its well-definedness theorem belong
to the canonical maps in this item's own statement, and are all listed in
`lean.declarations`; no independent notion or additional node is introduced.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `fullSubcomplex`,
  `IsEquivalenceEdge` (through `IsIsofibration`), `appendLast` (through slice operators).
  The module is supplied publicly by `RelativeInfinityCone`.
- `Sheaf.CategoryTheory.RelativeInfinityCone`: `rightJoinCone`, `leftJoinCone`,
  their two inclusions, `IsRelativeColimitDiagram`, `IsRelativeLimitDiagram`.
  These are exactly the recorded dependency's path-pullback mapping-space predicates.
- `Sheaf.CategoryTheory.IsofibrationExponentiation`: `IsIsofibration`; the already
  landed owning node is added to `stmt_deps` to record this reuse. Its exponentiation
  theorem is not invoked or assumed.
- `Sheaf.CategoryTheory.KanMappingRestriction`: reuse only its real slice-data helpers
  `kanSlice`, `kanSliceProjection`, `kanFace`, `kanExtend`, and `kanPrependFirst`.
  No mapping-restriction theorem is used as a hypothesis or proof input. Its theorem
  is a downstream consumer of this item, so adding a DAG dependency on that theorem
  would create a cycle. Its future proof-only import of this module must be omitted
  under stages/2-statements.md §3(7). This existing placement of definition helpers
  does not justify defining a second slice.
- The convolution generators, pure-factor inclusions, and terminal augmentation are
  `joinGenerator`, `orderedJoinInl`, `orderedJoinInr`, and `joinAugmentation` from
  `Sheaf.CategoryTheory.JoinSliceRightFibration` and
  `Sheaf.AlgebraicTopology.PushoutJoinSaturation`, publicly imported by the recorded
  relative-cone dependency. Their full types and docstrings were read.
- The stated proof dependency `lem-cbc-enhanced-functor-cone-calculus` is imported
  without `public` as `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`.
  The four other proof dependencies (arrow-join geometry, cone equivalence,
  fiberwise relative join, and equivalence prism extension) have no Lean records
  at this reading; their full proof steps are retained in the theorem docstring.
  They are not needed to type the statement; no unstated hypothesis replaces them.

Source and edge checks: read Kerodon Proposition the project server, https://kerodon.net/tag/0302,
including lifting problem (7.26), exact strictification, and the two gamma comparisons.
The left and right versions need separate assumptions and may produce different `H`.
For `A = ∅`, each index is empty and its cone has just the pure apex; the specifying
predicates still fix that map to `c`. For `C = ∅` the local hypotheses and pointwise
conclusions are vacuous and the unique empty global diagram has both exact equations.
For `A = C`, the identity slice arrows give the expected tautological extension.
For identity `p` or terminal base the relative formulations retain the expected
strict lift or ordinary universal diagram, respectively. Dimension zero, repeated
apex vertices, and disappearance of either ordered block are covered by the generator
and pure-factor rules. No source discrepancy or STATEMENT-DISPUTED remains.

Searches (all through the prescribed directories/tools):

- `msearch.py ... leanfinder "Relative pointwise Kan extension existence over an
  isofibration of infinity categories"`: eight ordinary/strict-Segal Kan-extension
  results; none states this relative quasicategorical assertion.
- `msearch.py ... leansearch` with the same query: eight ordinary categorical
  pointwise Kan-extension results; no match.
- `msearch.py ... loogle '"IsPointwiseLeftKanExtension"'`: twelve ordinary functor
  declarations. Read `Mathlib/CategoryTheory/Functor/KanExtension/Pointwise.lean`
  and the StrictSegal source `AlgebraicTopology/SimplicialSet/Coskeletal.lean`:
  their categories/limits differ from these internal relative universal diagrams.
  An earlier unquoted Loogle query returned unknown identifier; the quoted retry
  succeeds, and its result is recorded in `searches.jsonl`.
- `msearch.py ... grep 'relative.*Kan|Kan.*relative|isofibration'
  CategoryTheory/Functor/KanExtension`: zero hits.
- `rg` for relative Kan/isofibration in the upstream `WeilConjectures` source and
  this item's id there: no matching theorem. `rg` in `lean/Sheaf/CategoryTheory`
  located the usable existing `IsIsofibration` and slice helpers described above.
- Exact-name `rg` across Mathlib, upstream `WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for every newly introduced declaration: no collision.

Validation: the prescribed `scompile.py Q82 lem-coef-infinity-relative-kan-existence`
compiled this file both as the sandbox probe and its actual library module, with
no errors or warnings. The required dry-run delivery is recorded below after it runs.

Dry run: `deliver2.py Q82 lem-coef-infinity-relative-kan-existence --no-push`
printed `OK (dry run)` for commit `a4bcde115f`: compilation and preflight passed
except for the intentionally pending independent second reading. Nothing was pushed.

## Second reading by Q82

I read `dag/nodes/sec-six-functors/lem-coef-infinity-relative-kan-existence.json`, its
recorded dependency nodes, the module
`Sheaf/CategoryTheory/RelativeKanExistence.lean`, and Kerodon Proposition the project server
(0302), including the lifting problems (7.25)--(7.28), the slice diagonal, and the
two gamma comparisons. The item statement is the sufficiency assertion recorded by
the node (with its separate opposite-dual implication); the source page also records
the converse, but that converse is not part of this node's statement.

The node's objects and Lean renderings match as follows.

* `C`, `D`, and `B` are `SSet.{u}` with `[Quasicategory C]`,
  `[Quasicategory D]`, and `[Quasicategory B]`; the single explicit universe `u`
  is bound. `P : C _⦋0⦌ → Prop` and the full subcategory are
  `(fullSubcomplex C P).toSSet`, with inclusion `(fullSubcomplex C P).ι`.
* The functors are `p : D ⟶ B`, `h : (fullSubcomplex C P).toSSet ⟶ D`, and
  `s : C ⟶ B`. The hypothesis `hp : IsIsofibration p` is the recorded
  source-fixed inner-fibration/equivalence-lifting notion, and
  `compat : h ≫ p = (fullSubcomplex C P).ι ≫ s` is the exact commuting square.
* For each vertex `c`, the over-slice is the existing `kanSlice ... true`, with
  projection `kanSliceSubcategoryProjection ... true`; its right cone is
  `rightJoinCone (kanSlice ... true)` and its canonical cocone is
  `kanSliceCocone ... c`. The first antecedent quantifies a local `q` with exactly
  the three node clauses: restriction to `h`, projection to `kanSliceCocone ≫ s`,
  and `IsRelativeColimitDiagram p q`. Its consequent is `∃ H` with the exact
  restriction and base equations and the pointwise conclusion
  `IsRelativeColimitDiagram p (kanSliceCocone ... c ≫ H)`.
* The second implication uses `kanSlice ... false`, the corresponding projection,
  `leftJoinCone`, `kanSliceCone`, and exactly the three local clauses with
  `IsRelativeLimitDiagram`; its consequent has the same two exact global equations
  and the pointwise relative-limit clause.
* The module's `IsKanSliceCocone`, `IsKanSliceCone`, and
  `existsUnique_kanSliceJoinCones` specify the canonical maps on both pure factors
  and all mixed join generators. Thus `kanSliceCocone` and `kanSliceCone` are
  determined constructions, not arbitrary maps chosen from a bare existence claim.
  The only postponed proofs are the named construction theorem and the main
  statement, each with its source and step-by-step proof plan.

No hypothesis is added or omitted, no local colimit/limit assumptions are combined,
and no conclusion is weakened or strengthened. The existing `IsIsofibration`, relative
cone predicates, full subcomplex, and slice helpers are used rather than redeclared.
The dependency record for `lem-coef-infinity-kan-mapping-restriction` is not added:
its theorem is a downstream consumer, while this module reuses only its recorded slice
data helpers, so adding it would create a proof-dependency cycle. No statement or
Lean repair was needed.

Edge cases checked against the definitions and source: an empty `P` gives empty slice
indices while the canonical cones retain the apex value `c`; `C = ∅` makes the vertexwise
families vacuous and leaves the unique empty global map; `P` true gives the identity
slice case; identity and terminal-base `p` reduce to the ordinary strict and universal
formulations; empty pure or mixed join blocks are handled by the normal-form clauses;
zero-dimensional simplices and repeated vertices are included by the ordinal operators.
No characteristic, finiteness, completeness, cocompleteness, or nonemptiness hypothesis
is present or required.

I repeated the prescribed searches with `msearch.py`: LeanFinder on
"Extend a simplicial diagram over a categorical fibration from pointwise universal
cocone lifts", LeanSearch on "An extension of quasicategory diagrams with prescribed
base map exists if each slice admits a relative colimit", and Loogle on
`"IsPointwiseLeftKanExtension"`; and
`rg` over Mathlib, the upstream `WeilConjectures`, and repository `lean/Sheaf`.
The only relevant hits are ordinary categorical/StrictSegal Kan extensions and the
already recorded quasicategory/slice helpers; none states this relative theorem.
Exact-name searches found no declaration collision. The prescribed `scompile.py` run
compiled the module with no errors or warnings other than permitted postponed proofs.

Second-reader dry run: `deliver2.py Q82 lem-coef-infinity-relative-kan-existence
--no-push` printed `OK (dry run)` at `f98c84db39`, passing server preflight and
compilation with the independent reading present. The second reading changed only
this report: the Lean module and node signature were already correct.

## Maintainer review fix (2026-10-17)

H4: the canonical slice cocone `k_c : K_c^▷ → C` already exists in the project as
`SSet.Enhanced.rightConeExtension` (`Sheaf.CategoryTheory.JoinSliceDiagramIsomorphisms`,
node `lem-coef-join-slice-diagram-isomorphisms`, landed; no DAG cycle with this item): the
cone extension of a slice diagram `J → rightVertexSlice C y`, fixed by apex `y` and by
sending the cone `a^▷` over each simplex `a` to the slice simplex itself. That is exactly
`k_c` for the inclusion of `kanSlice A c true` into `rightVertexSlice C c`. The fix adds the
real inclusion `kanSliceVertexSliceInclusion` (same simplices and operators, forgetting the
membership of the face in `A`), defines `kanSliceCocone` as `rightConeExtension c` of it,
and drops the second specification `IsKanSliceCocone`. The dual `IsKanSliceCone`,
`kanSliceCone` and its uniqueness theorem (now `existsUnique_kanSliceCone`) stay, since
no left cone extension exists. The main statement is unchanged character for character.
The item's `stmt_deps` should also name `lem-coef-join-slice-diagram-isomorphisms`.
