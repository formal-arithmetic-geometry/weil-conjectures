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
