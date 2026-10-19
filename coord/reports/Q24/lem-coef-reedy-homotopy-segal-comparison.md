## Worker report

This repairs the returned immutable head `1aca55456dcd`. The retained module is
`Sheaf.CategoryTheory.ReedyHomotopySegalComparison`; its sole declaration is
`CategoryTheory.SegalSpace.reedy_homotopy_segal_comparison`, with proof `sorry`.
The initial saved packet passed `deliver2.py --no-push` at `254e436b09`, but still
contained the mathematical defects in the return. This packet repairs those defects;
it is not an unchanged re-push. Comparing the saved node with the current shared node
found only a difference in `lean`. The repaired node starts from the current record.

The natural-language statement is unchanged. Each hypothesis and conclusion is rendered
as follows.

* The simplicial space is `X : Space.{u}`. `Space` is the dependency's functor on the
  product of opposite simplex categories, with the outer coordinate first;
  `Functor.curry.obj X` is its simplicial-object presentation. No universe is restricted.
* Vertical Reedy fibrancy is the restored hypothesis
  `hR : SSet.BisimplicialDivision.verticalFibrations (terminal.from X)`.
  The dependency tests relative division by every outer boundary, including degree zero.
  This is a genuine hypothesis, independent of levelwise Kan homotopy-Segal fibrancy.
* The homotopy-Segal hypothesis is
  `hX : SSet.HomotopySegal.IsHomotopySegalSpace (Functor.curry.obj X)`.
  This includes all columns being Kan and the constant-joining-path weak Segal maps.
* The strict-product conclusion is `IsSegal X`. Reading its definition gives actual
  matching fibrations and `IsWeakHomotopyEquivalence (segalMap X n)` for every `2 ≤ n`.
  Its `chains` are `SSet.Path` strings with target `d₀` matched to the next source `d₁`.
* The comparison is one family `c`, quantified over every pair of vertices `x y`.
  Its source is precisely `mappingSpace X x y`, the strict pullback over `(x,y)`.
  Its target is `HomotopySegal.simplexFiber (Functor.curry.obj X) 1 ![x,y]`,
  the specified path homotopy fiber. The first conjunct specifies the value of `c`
  on EVERY inner simplex: the first coordinate is `pullback.fst`, and the second is
  `SSet.const ![x,y] ≫ Enhanced.constantDiagrams Δ[1] (vertexPower ... 1)`.
  These two coordinates determine the map uniquely, including the whole endpoint
  path, so the existential is not an arbitrary weak equivalence. The finite-function
  base `![x,y]` is the dependency's encoding of the ordered pair `(x,y)`.
* Each `c x y` satisfies both `Enhanced.IsWeakHomotopyEquivalence` and
  `Function.Bijective (SSet.mapπ₀ (c x y))`. By `mapπ₀_mk`, this sends a strict arrow
  class to the same edge with its constant endpoint path, as required.
* Identity preservation is explicit: for every `x` there is a strict-fiber vertex `a`
  whose projection is `s₀ x`, and its image class is `HomotopySegal.identity ... x`.
  The strict fiber is a pullback along the terminal simplicial set; therefore the
  projected degenerate edge specifies this strict vertex uniquely. This is exactly
  preservation of the specified identity, with existence retained explicitly.
* Composition is specified on ALL component classes `f`, `g`, `h` in the three strict
  mapping fibers. Its left side is the strict composition graph: a single strict
  triangle `t` and representatives `a,b,d` of these three classes project respectively
  to `d₂ t`, `d₀ t`, `d₁ t`. Its right side is
  `HomotopySegal.Composes ... (mapπ₀ (c x y) f) (mapπ₀ (c y z) g)
    (mapπ₀ (c x z) h)`.
  The biconditional preserves AND reflects that graph. The degree-two strict Segal
  map makes this precisely strict composition. Together with the hom-set bijections
  and identity clause, these are the category-isomorphism equations. Objects are the
  same vertex type throughout, so its object function is the identity. Inverse
  bijections satisfy the same identity/composition equations. No replacement object
  set, arbitrary category structure, or choice of inverse Segal maps is introduced.
* The consequence about unions of invertible components is stated as the actual
  subcomplex equality
  `equivalenceArrows X = SSet.SegalInverse.invertibleArrows (Functor.curry.obj X)`.
  Both sides saturate the specified invertible-arrow predicate by components and then
  select simplices by all their vertices. This retains every inner degree, rather
  than only comparing membership of vertices.

Dependency declarations read and used:

* `Sheaf.CategoryTheory.SegalDKDiagonalEquivalence`:
  `SSet.segal_dk_diagonal_equivalence`, whose signature uses the recorded
  `HomotopySegal.IsHomotopySegalSpace`, mapping-fiber and composition conventions.
  This remains imported as the original statement dependency.
* `Sheaf.AlgebraicTopology.BisimplicialReedyDivisionCalculus`:
  `SSet.BisimplicialDivision.verticalFibrations`, `relativeLeft`, and
  `bisimplicial_reedy_division_calculus`. Its definition supplies the `hR` hypothesis.
* `Sheaf.CategoryTheory.SegalSpace`: `Space`, `row`, `endpoints`, `mappingSpace`,
  `chains`, `segalMap`, `IsReedyFibrant`, `IsSegal`, `SameMappingComponent`,
  `IsEquivalenceArrow`, `equivalenceArrows`. Their full definitions were read.
* `Sheaf.CategoryTheory.HomotopySegalSpace`: `IsHomotopySegalSpace`, `vertexPower`,
  `simplexFiber`, `identity`, `fiberRestriction`, `Composes`, and the underlying
  `Enhanced.homotopyFiber`/`constantDiagrams` definitions. Its already landed node
  `def-coef-homotopy-segal-space` is added to `stmt_deps` explicitly.
* `Sheaf.CategoryTheory.SegalInverseEvaluation`:
  `SSet.SegalInverse.IsInvertibleClass`, `edgeClass`, and `invertibleArrows`.
  Its already landed node `lem-coef-segal-inverse-evaluation` is added to `stmt_deps`
  because its definition supplies the path-model subcomplex. A source-only graph
  traversal confirmed that neither added dependency has a path back to this item.
* Proof dependencies are ordinary, non-public imports:
  `Sheaf.AlgebraicTopology.KanPullbackPathComparison`,
  `Sheaf.CategoryTheory.KanHomotopyPullbackInvariance`, and
  `Sheaf.AlgebraicTopology.KanQuillenRightProper`.

There is no new definition or dependency repair module. No natural-language correction,
new axiom, hollow definition, or unresolved `STATEMENT-DISPUTED` remains. The removed
invertibility assertion was a defect of the old Lean signature, not of the DAG statement.

Edge cases checked against the definitions:

* The empty simplicial space satisfies the conclusion with an empty comparison family;
  all vertex-indexed identity and composition statements remain vacuous as they should.
* Empty mapping fibers and absent arrows are allowed. The composition graph quantifies
  component classes and makes no blanket nonemptiness assumption.
* The discrete nerve of `[1]` has a noninvertible edge `0 → 1`. The returned signature
  made invertibility equivalent to having a preimage under a component bijection, so
  incorrectly made this edge invertible. That clause is removed completely. The repaired
  subcomplex equality selects identities in this example, excluding that edge on both
  sides, while the comparison still maps its noninvertible component bijectively.
* A constant outer diagram on the nerve of a nontrivial group is levelwise Kan and
  homotopy Segal, but its outer degree-one matching map is the diagonal and need not be
  a fibration. This tests why `hX` cannot replace the restored `hR`.
* Discrete groupoid nerves, identity-only categories and one-object classifying nerves
  retain their identities, compositions and invertible components. Completeness,
  connectedness and nonempty fibers are not hypotheses.
* The Reedy condition includes outer degree zero; strict Segal comparisons begin at
  degree two, as the node says. The constant-path coordinate equation includes inner
  degree zero and all higher degrees.

Searches rerun during repair (all read-only):

* `msearch.py ... leanfinder "Reedy fibrant Segal space strict mapping fiber constant
  path comparison preserves identities and composition"`: eight hits, including
  `SSet.StrictSegal.isStrictSegal`, `CategoryTheory.Nerve.strictSegal`, and
  `SSet.StrictSegal.spineEquiv`. These concern bijective spines of single simplicial
  sets, not this comparison of strict and path mapping fibers of simplicial spaces.
* `msearch.py ... loogle '"Segal"'`: twelve hits, again the strict simplicial-set
  `SSet.StrictSegal`/`IsStrictSegal` family and nerve specializations; no exact match.
* `msearch.py ... grep 'Reedy.*Segal|Segal.*Reedy|homotopy.*Segal|Segal.*homotopy'
  AlgebraicTopology`: zero Mathlib hits.
* `rg` over the named upstream `WeilConjectures` source and shared `lean/Sheaf` tree,
  for the Reedy/Segal and strict-fiber terminology: related generic fiber comparisons
  and the cited Segal modules, no theorem with this statement. In particular,
  `CompleteSegalPathFiberComparison.IsConstantComparison` specifies a map with one
  common base, and `QuasicategoryClassificationRealization.fiberComparison` concerns
  the special classifying diagram of a quasicategory. Neither states this theorem.
* Exact-name `rg` for `reedy_homotopy_segal_comparison` in both source trees, and
  `grep -rn` for the node id in upstream `WeilConjectures`: no existing declaration.

Source verification: opened Rezk at `https://arxiv.org/html/math/9811037` and read
Sections 4.1, 5.1, 5.3, 5.5, 5.7. Section 4.1 retains Reedy fibrancy; Section 5.1
uses the strict fiber and degeneracy identity; Sections 5.3--5.5 specify triangle
composition and its category; Section 5.7 takes the union of invertible components.
The strict/path extension is explicitly the agent-supplied argument in this node,
not claimed to be a verbatim theorem of Rezk.

## Second reading by Q24

Independent maintainer second reader, 2026-10-17, reviewing immutable delivery
3470cd4a3cf6a092bb6da52be95a88776db63b35. I did not write or previously second-read
this delivery. This section replaces the worker's expressly labelled self-check;
it records the independent reading actually performed, without attributing it to
a second group worker.

I read packet.md, the immutable node, all five statement-dependency nodes, the
complete delivered module and worker report, and the exact dependency definitions
in /home/ubuntu/weil-newtargets-Q24/lean/Sheaf. Source checked online:
https://arxiv.org/html/math/9811037, Rezk Sections 4.1, 5.1, 5.3--5.5, 5.7--5.8.
These specify Reedy fibrancy, strict spines/fibers, degeneracy identities, triangle
composition, and invertible components. The path comparison is correctly identified
as an agent-supplied consequence, not a quotation from Rezk.

Hypothesis and conclusion audit:

1. `X : Space.{u}` is the uncurried simplicial space, outer coordinate first.
   `hR` is exactly verticalFibrations of the terminal map, whose boundary tests
   include zero. `hX` is the recorded levelwise Kan homotopy-Segal condition on
   Functor.curry.obj X. Neither completeness nor any extra size assumption occurs.
2. `IsSegal X` contains every actual matching fibration and every weak strict
   spine map in degree at least two. `chains` uses Mathlib Path: d1 is source,
   d0 is target, and adjacent endpoints are identified in the correct order.
3. The family c has source the strict endpoint pullback and target simplexFiber
   at the ordered finite tuple ![x,y]. Its displayed equation specifies both
   the edge and the entire constant tuple path for every inner simplex. Proof
   irrelevance makes this a unique map into the path-fiber subtype; this is not
   an arbitrary weak equivalence. The finite tuple and cartesian pair are the
   same endpoint product up to the canonical coordinate identification.
4. Weak equivalence and bijectivity of mapπ₀ are explicit for every x,y. The
   coordinate equation implies the required same-arrow formula on classes.
5. The identity clause projects to s0 x and maps its class to the dependency's
   specified identity. The strict pullback over a point has a unique such lift.
6. The composition biconditional quantifies all f,g,h and uses a single strict
   triangle with faces d2,d0,d1. HomotopySegal.Composes is exactly the graph of
   these restrictions on the triangle homotopy fiber. The degree-two strict
   Segal map is a trivial fibration, so the strict graph is total and functional
   on components. These graph equations and the hom-set bijections specify the
   identity-on-objects category isomorphism, including its inverse.
7. The final equality is equality of subcomplexes, not just of vertices.
   SegalSpace.equivalenceArrows and SegalInverse.invertibleArrows both saturate
   the corresponding two-inverse-equation predicate by arrow components, then
   use Enhanced.fullSubcomplex. Thus all inner degrees are included.

I checked the eight proof steps against the division theorem's all-monomorphism
criterion, KanPullbackPathComparison.kan_pullback_path_comparison,
Enhanced.kan_homotopy_pullback_invariance, and KanQuillen.right_proper_kan_quillen.
The spine restrictions give the required fibrations; induction inserts constant
joining paths over the last target. Two-out-of-three gives strict Segal maps.
All-vertex fibers compare by constant paths, naturally under face restriction.
Boundary lifting includes dimension zero and realizes any given composable pair.
Mapping-component bijections then preserve identities, compositions and inverses.
No missing independent prerequisite or universe transport is needed.

Edge cases: the empty space; empty off-diagonal fibers; x=y and identities;
degree-zero matching; first Segal degree two; every inner degree; discrete nerve
of [1] with its noninvertible arrow; discrete groupoid nerves, including a
one-object nontrivial group without completeness. A constant outer diagram on a
nontrivial group nerve tests that hR cannot be dropped. No inhabitedness,
connectedness, or equality of independent universes is imposed.

Independent duplicate searches on 2026-10-17:

* LeanSearch (lean_lsp MCP), query: "For a Reedy fibrant homotopy Segal simplicial
  space the strict mapping fibers are weakly equivalent to path homotopy fibers
  preserving identities and composition". Eight hits: truncated/untruncated
  StrictSegal.spineEquiv, StrictSegal.rec, spine_spineToSimplex, isStrictSegal,
  quasicategory', isCoskeletal, and liftOfStrictSegal.f₂.congr_simp. Their types
  concern a single strict Segal simplicial set, not this theorem. I read
  Mathlib/AlgebraicTopology/SimplicialSet/StrictSegal.lean:39--59 and Path.lean.
* Loogle (lean_lsp MCP), query: `"Segal"`. Twelve hits, all StrictSegal,
  IsStrictSegal, StrictSegalCore, their spine constructions, or category nerves;
  no exact match.
* rg over Mathlib/AlgebraicTopology and upstream WeilConjectures with
  `Reedy.*Segal|Segal.*Reedy|homotopy.*Segal|Segal.*homotopy`: no hits.
  Broader strict/path and constant-path/fiber searches over the side Sheaf tree
  found the recorded generic comparisons and CompleteSegalPathFiberComparison.
  I opened its IsConstantComparison and theorem: it requires completeness and
  concerns invertible fibers/object paths, not this general comparison. No new
  definition or duplicate theorem is warranted.

Mechanical checks: the JSON lean.statement is exactly the module signature
from `theorem` to before `:=`; autoImplicit is false; universe u is bound;
maximum line width is 93; the sole proof is `by sorry`; no new definitions or
axioms. Module/theorem docstrings have source and blueprint markers and all eight
proof steps. The only node differences against the read-only group baseline are
lean and two already-landed statement dependencies; neither has a dependency path
back to this item. No statement_change or citer audit is necessary.

Compile reproduced directly from the immutable file with:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q24
lem-coef-reedy-homotopy-segal-comparison
snapshot/lean/Sheaf/CategoryTheory/ReedyHomotopySegalComparison.lean`.
Exit 0, no diagnostics: sandbox 1.7 s, library 2.4 s. The installed wrapper now
uses the server side overlay with wire confirmation; it supersedes the older
local-wrapper implementation description. No direct SSH, global build, live Lean
write, or repository mutation was performed by this reader.

Findings repaired here: H11 (the old second-reading section admitted it was a
self-check), and H4's search-record omission of LeanSearch. The delivered Lean and
node are substantively correct and unchanged. The complete replacement report is
the only maintainer fix.
