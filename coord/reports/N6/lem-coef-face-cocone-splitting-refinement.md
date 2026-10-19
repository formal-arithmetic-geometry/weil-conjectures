## Worker report

Repair of L's independent stage-2 return at immutable head `4d759f78ddcf`.
The saved packet was inspected first and its prescribed dry run passed at
`e0ffe0e0cf`. That mechanical pass did not resolve the maintainer's collision
finding. Comparing the saved source with current main's
`Sheaf.AlgebraicTopology.FaceCoconeEvaluation` confirmed every reported collision.

The repair removes every local construction, not merely the five colliding names.
It imports and uses the existing face-cocone interface instead. Thus the module
now declares only `SSet.FaceCocone.splitting_refinement`, with its complete
five-step proof docstring and sole `sorry` proof. No declaration has been renamed
to conceal duplication. The item's `lean.declarations` now lists only that theorem.
The item cites the already landed `def-coef-face-cocone-evaluation` in `stmt_deps`,
as authorized for existing landed definitions. No new node or dependency repair
is needed. The natural-language statement, proof and proof dependencies are
unchanged; no statement correction or dispute is needed.

I read the entire landed definition module and its definition node, and confirmed
its current published source with `scompile.py --source
Sheaf.AlgebraicTopology.FaceCoconeEvaluation`. I also reopened the two original
statement-dependency records and the signatures and docstrings of
`pinched_cube_latching` and `simplicial_interval_lifting`. The existing sibling
`FaceCoconeEvaluationSimplicial` uses precisely this shared interface and states
simplicial-operator compatibility, rather than refinement invariance.

Hypothesis and clause correspondence for the repaired statement:

- Finite nonempty linearly ordered V is `{V : Type u} [LinearOrder V] [Finite V]
  [Nonempty V]`. All universes and variables are explicitly bound.
- The small simplicial category is `D : SCat.{u}`. The family and strict cocone
  are now bundled together in `f : Data V D`. Its `faces` is the given family;
  `nonempty` says every member is nonempty; `singleton` includes every singleton;
  `downward` includes every nonempty subset of a member. These replace the
  separate face-family hypotheses of the returned signature without adding or
  removing assumptions.
- `f.functor F hF` is the enriched functor on the coherent ordered face F, using
  Mathlib `SimplicialThickening F`. `f.compatible` says literal equality with
  composition along `inclusion h` for every inclusion. Its orientation is the
  symmetric version of the former local equality and expresses the same strict
  compatibility, including object functions.
- `d_v` is the existing `f.vertex v`, exactly the singleton face's value.
  `f.normalizedMap` uses strict singleton compatibility to identify endpoints;
  no object equality or choice of isomorphisms is an extra hypothesis.
- The endpoint inequality is `hij : i < j`; `q : ℕ` includes zero.
  `S : Flag i j q` is `ComposableArrows (SimplicialThickening.Path i j) q`.
  The underlying subset at t is `(S.obj t).I`; `S.map` supplies nesting.
  Every path object contains i and j and lies in `[i,j]` by its `left`, `right`,
  `left_le` and `le_right` fields. Thus the former `in_interval`, `left` and
  `right` arguments are now intrinsic to the flag, not dropped. Conversely any
  nested chain in the statement determines such a functor: an inclusion poset
  has exactly the required morphisms and their functor laws are automatic.
- `R : Splitting S` is an increasing enumeration of the finite splitting set.
  `R.length` is the number of blocks, `R.joint` is an order embedding,
  `R.first`/`R.last` fix i and j, and `R.mem_initial` puts every joint in S_0.
  Increasing enumerations exactly represent the finite splitting subsets, with
  no order, repetition or extra splitting choice permitted.
- The support `T_b = S_q ∩ [a_{b-1},a_b]` is the existing `R.support k`.
  `f.IsAdmissible R` means every such support belongs to `f.faces`.
- `R.blockFlag k` is the restricted flag inside that support: its t-th subset
  is the support's elements belonging to `(S.obj t).I`, precisely the stated
  intersection since nesting puts S_t inside S_q. `f.blockValue R hR k`
  applies the face map to this flag, with singleton-normalized endpoints.
- `f.evaluation R hR` is the existing ordered composite `E_R(S)`.
  `orderedComposite` composes block images in increasing order. Its left
  association differs syntactically from the removed helper's right association,
  but both mean the node's ordered composite by enriched associativity.
  The codomain is `(hom D (f.vertex i) (f.vertex j)) _⦋q⦌`.
- The first conjunct quantifies over any R, R' and admissible R. The subset
  condition is `Set.range R.joint ⊆ Set.range R'.joint`. Both splitting sets
  already lie in S_0 and contain the endpoints. The conclusion is admissibility
  of R' and `f.evaluation R' hR' = f.evaluation R hR` for every admissibility
  proof hR'. There is no extra assumption on the refinement.
- The second conjunct compares arbitrary admissible R and R', without requiring
  nesting, and gives the requested evaluation equality.
- The third conjunct, conditional on an admissible R, supplies C with
  `C.IsCanonical`, meaning exactly `Set.range C.joint = (S.obj 0).I`, its
  admissibility hC, and equality with R's evaluation. Thus the statement includes
  the canonical splitting and its value and never asserts unconditional existence
  of an admissible splitting.

Dependency declarations reused:

- `Sheaf.AlgebraicTopology.FaceCoconeEvaluation`,
  `SSet.FaceCocone.Data`, `Flag`, `Splitting`, `Data.IsAdmissible`,
  `Data.evaluation`, and `Splitting.IsCanonical`, together with their real
  constructions `inclusion`, `Data.vertex`, `Data.normalizedMap`,
  `Splitting.support`, `Splitting.endpoints`, `Splitting.blockFlag`,
  `Data.blockValue`, and `orderedComposite`. None is redeclared.
- `Sheaf.AlgebraicTopology.PinchedCubeLatching`,
  `SSet.PinchedCube.coherentSimplex`, using Mathlib's subset-path nerve model;
  its `pinched_cube_latching` theorem supplies the original DAG interface.
- `Sheaf.AlgebraicTopology.SimplicialIntervalLifting`,
  `SSet.Bergner.simplicial_interval_lifting`, with the imported
  `CategoryTheory.CoherentNerve.SCat` and `hom` and Mathlib's enriched composition.
  Their factorization and quotient conclusions are not new hypotheses here.

Edge cases rechecked on the shared interface: q=0 remains a one-entry flag;
repeated flag entries and identity refinements are permitted; every block has
both endpoints, including a block with no interior vertices. A one-element V
has no i<j. The singleton-only family has no admissible splitting joining
strictly distinct endpoints, so all conclusions correctly remain conditional.
No mapping-space fibrancy, discreteness or existence assumption is introduced.
For the canonical clause, finiteness gives the unique increasing enumeration of
S_0, which is nonempty because the endpoints belong to every path object.

Search evidence retained from the saved packet:

- `msearch.py ... leanfinder "Compatible simplicial enriched functors on faces
  evaluate subset flags independently of refinement of splitting vertices"`:
  eight hits, including `SimplicialThickening.functor`, but no refinement theorem.
- `msearch.py ... loogle '\"SimplicialThickening\", \"comp\"'`: five hits,
  `comp_I`, `compFunctor`, `compFunctor_obj`, `functor_comp`, `comp_app`.
  They supply union composition and functoriality, not the requested theorem.
- `msearch.py ... grep 'face.*cocone|splitting.*refin|SimplicialThickening'
  AlgebraicTopology`: Mathlib's existing subset model, which is reused.
- `msearch.py ... leansearch "Refining a splitting of a flag of subsets leaves
  unchanged the composite of compatible simplicial enriched face functors"`:
  eight hits about distinct simplicial-object splitting notions.
- The saved packet's source and DAG searches preceded landing the shared
  face-cocone definition; their claim that no shared construction existed is now
  superseded. During this repair, `rg -n 'FaceCocone|splitting_refinement'
  lean/Sheaf/AlgebraicTopology` found `FaceCoconeEvaluation` and its simplicial
  compatibility sibling, and no existing refinement theorem. The analogous
  upstream AlgebraicTopology directory does not exist. A repair-time repeat over
  the entire upstream `WeilConjectures` tree for `FaceCocone`,
  `splitting_refinement`, and the exact item id returned no matches.
- The shared definition was read in full both locally and via the current-source
  `scompile.py --source` command. This directly confirms the exact declarations
  named in the return and provides all required constructions without copies.

## Second reading by NN

This is the dispatcher's requested self-check; no other agent was started.
With the node, the repaired theorem and the full shared definition open, I
matched every hypothesis and clause as detailed above. The returned module's
local `Data` lacked the family axioms, whereas the shared `Data` bundles them;
therefore I removed the separate family binders instead of accidentally keeping
redundant assumptions or constraining a second family. The old order-hom flag
and separate endpoint/interval proofs are exactly the shared `Flag` object.
The splitting range, admissibility, evaluation and canonical conclusions now
refer directly to the shared notions. The argument packaging changes no
mathematical statement, and the sibling's composition direction confirms that
the imported evaluation is the intended increasing ordered composite.

All five reported duplicates, plus all other local evaluation helpers, have
been removed. The only newly declared name is the requested theorem. The node's
`lean.statement` is extracted verbatim from the actual signature, and its only
non-lean delta is the added landed definition dependency. No statement mismatch
or disputed edge case remains.

## Validation

The initial saved-packet dry run passed at `e0ffe0e0cf`; this was recorded before
repair and is not evidence for the repaired file. The repaired module compiled
through the prescribed `scompile.py NN lem-coef-face-cocone-splitting-refinement`
wrapper without errors or warnings: sandbox 1.4 s and library 1.6 s. A structural
self-check confirmed exactly one declaration, one `sorry`, no line over 100
characters, a verbatim recorded signature, and only `lean`/`stmt_deps` node deltas.
The final repaired dry run is recorded below.

Repaired delivery dry run: `deliver2.py NN
lem-coef-face-cocone-splitting-refinement --no-push` printed
`OK (dry run): commit c3cfbf787a passes the preflight and compiles; nothing pushed`.
The packet contains exactly the repaired theorem module, its item node and this
report. The delivery wrapper refreshes the base and constructs the commit on the
current `newtargets-dag`; no shared checkout was directly edited.

## Second reading by N6

Independent maintainer reading, 2026-10-17, of immutable delivery
`c0cd8bd4074e316b795bdf826e8441a1b5ea59b2`. The reviewer did not write or
previously second-read this delivery. This section replaces the delivered
placeholder; the historical NN self-check above is retained as historical evidence.
The immutable module and node need no mathematical or Lean changes.

I read packet.md first, the item node, all three statement-dependency nodes and
Lean records, the delivered module and report, and the exact dependency declarations
and their docstrings in the read-only N6 clone. In particular I read the entire
FaceCoconeEvaluation module, the coherent simplex construction and
pinched_cube_latching signature, the simplicial_interval_lifting signature, and
SCat/hom in CategoryTheory.CoherentNerveInfrastructure. I read Mathlib
AlgebraicTopology/SimplicialNerve.lean:54–208 and Enriched/Basic.lean:299–310.

The source checked is Lurie's HTT, Definitions 1.1.5.1 and 1.1.5.3, printed
pp.20–22, and the opening boundary-description paragraph of the proof of
Theorem 2.2.5.1, printed p.90:
https://people.math.harvard.edu/~lurie/papers/HTT.pdf .
The refinement lemma is correctly identified as an agent auxiliary expansion,
not a verbatim theorem from HTT. Its elementary argument uses the source's
subset-path nerves, union composition and direct-image face inclusions.

Hypotheses and conclusions checked independently:

- `{V : Type u} [LinearOrder V] [Finite V] [Nonempty V]` gives exactly the
  finite nonempty ordered ambient set. `D : SCat.{u}` is the recorded small
  simplicial category, with its actual enriched mapping simplicial sets.
- `f : Data V D` bundles the family of nonempty subsets, every singleton,
  downward closure under nonempty subsets, and the enriched functor on each
  face. Its `compatible` field is equality of enriched functors along the
  actual face inclusion, including object functions. It adds no condition on D.
- `i j`, `hij : i < j`, `q : ℕ`, and `S : Flag i j q` give the required strict
  endpoints and chain. Mathlib Path carries the two endpoints and the interval
  bounds; ComposableArrows carries precisely the nesting, including repetitions.
- `Splitting S` carries a strictly increasing finite enumeration, the first
  and last endpoint, and membership in the initial flag entry. Its support is
  exactly the last flag entry intersected with the corresponding closed interval.
  `Data.IsAdmissible` requires each such support to be a face.
- `normalizedMap` transports endpoint objects using equality forced by singleton
  compatibility. `blockFlag` restricts the chain to the support. `blockValue`
  applies this actual enriched map. `orderedComposite` recursively uses enriched
  identity and composition, and `evaluation` transports the endpoint equalities.
  None of these is an arbitrary map, a chosen nonempty witness, or hollow data.
- The first conjunct assumes only admissibility of R and inclusion of joint
  ranges. It concludes admissibility of R' and the required equality for every
  admissibility proof. Proof irrelevance makes this equivalent to the node's
  unannotated evaluation equality.
- The second conjunct compares every pair of admissible splittings, including
  incomparable ones. The third produces a splitting with joint range S_0,
  its admissibility, and its equality with the original evaluation. Finite linear
  orders have a unique increasing enumeration of that endpoint-containing set,
  so the existential packaging is exactly the canonical-splitting clause.

I checked the five proof steps: endpoints persist in every entry; each refined
support is a nonempty subface of an old support; at one inserted joint the two
restricted flags have the old flag as their union composite; functoriality and
strict compatibility identify the two factor values; finite insertion induction
and comparison with the increasing enumeration of S_0 give all conclusions.
No unstated mathematical prerequisite or dependency repair is needed.

Edge cases: q=0, repeated entries, identity refinements, blocks with no interior
vertices, and incomparable admissible splittings are covered. Strict endpoints
exclude zero-block splittings. Empty and singleton ambient sets have no i<j;
nonemptiness is explicitly in the node. For the singleton-only face family,
there is no admissible splitting between distinct endpoints, and the theorem
correctly makes no unconditional existence assertion. No Kan, fibrancy,
discreteness or mapping-space nonemptiness assumption occurs. All binders and
the universe u are explicit. The small-category size convention is the recorded
SCat convention, with no new size constraint; a finite V can be represented in
any required common universe.

One-definition checks: the existing shared definitions are imported, with only
splitting_refinement declared here. I inspected the worker's LeanSearch,
LeanFinder/Loogle and grep evidence and the returned exact Mathlib declarations;
I also independently searched the N6 AlgebraicTopology tree, upstream
WeilConjectures tree, and Mathlib AlgebraicTopology tree for FaceCocone,
splitting_refinement, face-cocone and refinement/subdivision variants. The sibling
evaluation_simplicial concerns simplicial restriction, not refinement. No
independent existing refinement declaration was found. The clone's copy of this
same delivery is not an independent earlier theorem.

All three statement dependencies are recorded and publicly imported. The two
proof dependencies are imported and equal the union of the proof steps' uses.
There are no new definition nodes, dependency modules or statement corrections;
therefore no new-node gates or statement-change citer audit is needed. I also
checked the parent boundary-cube use of this lemma, Step 4, against the two
admissible-splitting and refinement clauses.

The module and theorem docstrings give source places and the exact blueprint id;
the theorem docstring carries all five proof steps. The sole theorem has exactly
`by sorry`. There are no local helper proofs or definitions. The normalized
signature is verbatim equal to lean.statement; lean.declarations lists precisely
SSet.FaceCocone.splitting_refinement. Maximum line length is 98. No pro-etale
substitute or live Lean write is involved.

Compiler reproduction used the immutable file:

    python3 /home/ubuntu/weil-launcher-nt/scompile.py N6 lem-coef-face-cocone-splitting-refinement /home/ubuntu/weil-launcher-nt/reviews-stage2/N6__lem-coef-face-cocone-splitting-refinement__c0cd8bd4074e/snapshot/lean/Sheaf/AlgebraicTopology/FaceCoconeSplittingRefinement.lean

Exit status 0, no errors or warnings: sandbox 1.3 s; library 1.4 s. The installed
scompile.py currently routes the side-overlay check through its server wrapper
(the script's earlier local behavior has changed). Output identified the private
`/dev/shm/nt-tmp/nt-local-compile-6bw50dnt/.lbuild` overlay. Each invocation retained
the 60-second file limit. No separate SSH command, global build, delivery wrapper,
preflight command, or repository mutation was performed by the reviewer.

Finding and repair: H11 (and the substantive report-section requirement of H1):
the delivered exact N6 section merely said that no worker second reading occurred.
The older NN self-check cannot supply the requested substantive exact N6 section.
This complete report replacement supplies the independent reading and compiler
evidence above. No fault in the statement or mathematics was found. The original
worker report and historical validation are preserved. Verdict: FIX, report only.
