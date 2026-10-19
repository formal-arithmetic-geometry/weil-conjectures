## Worker report

The module `Sheaf.CategoryTheory.FilteredPosetConeTest` states
`SSet.Presentability.isKappaFiltered_iff_poset_cone_extension`, with its whole proof
postponed by `sorry`. It introduces no definitions and changes only the item's
`lean` field. There is no statement correction or disputed assertion.

Source checked: Lurie, Higher Topos Theory, Remark the project server, printed p.383,
PDF page index 400, at https://people.math.harvard.edu/~lurie/papers/HTT.pdf.
The remark explicitly states the equivalence for poset nerves, including the
cofinal-poset replacement references for countable and uncountable regular cardinals.
The PDF was read online; it has not been archived or written to the shared repository.

The statement's hypotheses and clauses match as follows:

- The small universe U is `u`, and the containing universe is `max (u + 1) v`.
  Every universe and variable is explicitly bound; `autoImplicit` is disabled.
- The infinite regular cardinal in U is `(κ : Cardinal.{u}) (hκ : κ.IsRegular)`.
  Mathlib's `Cardinal.IsRegular` includes `aleph0_le`, so infinitude is retained.
- The quasicategory in the containing universe is
  `(E : SSet.{max (u + 1) v}) [Quasicategory E]`.
- The left side of the equivalence is the recorded definition
  `IsKappaFiltered κ E`. Its tests count nondegenerate simplices and include the
  empty simplicial set. This is not ordinary-category filteredness.
- Every small partially ordered set of size below κ is expressed by
  `∀ (B : Type (max (u + 1) v)) [PartialOrder B], HasCardinalLT B κ → ...`.
  This permits representatives in the containing universe. It does not relax the
  smallness requirement: Mathlib `HasCardinalLT.small` proves `Small.{u} B` from
  that very hypothesis. Conversely any U-small poset has such a representative,
  after universe lift, with the same cardinal bound and nerve. Order transport
  does not affect the extension condition. No extraneous `Nonempty B` is imposed.
- `B` with a new maximum is the existing Mathlib type `WithTop B`, with its
  `PartialOrder`. The coercion preserves the old order and every old element is
  strictly below the newly adjoined top, even when B already has a maximum.
- Every simplicial map is `∀ (p : nerve B ⟶ E)`.
- Its extension is `∃ (pbar : nerve (WithTop B) ⟶ E), ...`.
- Exact restriction to p is
  `nerveMap (WithTop.coeOrderHom (α := B)).monotone.functor ≫ pbar = p`.
  Here the functor is the actual inclusion of B into WithTop B; the nerve map
  applies that inclusion to every chain. The equality is of simplicial maps,
  retaining all simplices and compatibility conditions.
- The two conditions are joined by `↔`, with no colimit existence or universality
  hypothesis or conclusion. Empty-poset nonemptiness is encoded by the universal
  quantifier itself, rather than an additional conjunct.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.PresentableInfinityCategory`:
  `SSet.Presentability.IsKappaFiltered` (and its underlying `IsKappaSmall`).
  The full signatures and docstrings were read. This is the recorded
  `def-coef-presentable-infinity-category` interface, used without alteration.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.coconeCategory`, reached by the public import of the previous
  module and used inside `IsKappaFiltered`; Mathlib `SSet.Quasicategory` and
  `CategoryTheory.nerve` give the other recorded notions. The cocone definition
  uses the coherent comma simplicial set, not an ordinary cocone.
- Proof-only import `Sheaf.CategoryTheory.JoinSliceCoconeComparison`:
  `SSet.Enhanced.join_slice_cocone_comparison`. Its full signature/docstring was
  read and the theorem is referenced in the proof docstring for both directions.
- `lem-coef-infinity-poset-nerve-cofinal-replacement` currently has neither a
  Lean record nor a Mathlib match in the shared DAG. It is a proof dependency,
  not a missing statement notion, and is documented in the proof docstring;
  there is therefore no module to import yet. No dependency module is needed
  to state the present equivalence.
- Mathlib `CategoryTheory.nerve`, `CategoryTheory.nerveMap`,
  `Monotone.functor`, `WithTop.coeOrderHom`, `HasCardinalLT`,
  `HasCardinalLT.small`, and `Cardinal.IsRegular` were inspected in their sources.

Edge cases checked mathematically before writing:

- Empty B: its nerve is empty and WithTop B is the singleton poset. Extension
  of the unique empty diagram is precisely a vertex of E; neither side holds
  when E is empty. The formula does not discard this test.
- Singleton B: WithTop B is a two-element chain; the extension is an edge from
  the given object, and its identity edge is permitted.
- Two discrete objects: the extended nerve asks for a coherent common cocone.
  For the chain `0 < 1` it includes the required compatibility 2-simplex.
- κ = aleph_0: `HasCardinalLT B κ` means B is finite. Its strictly increasing
  chains, counted in every degree, are finite in total. Thus the finite test
  agrees with the recorded nondegenerate-simplex smallness convention.
- Uncountable regular κ: infinite B has |B| finite strict chains in total,
  preserving the cardinal bound. Countable infinite chains are not excluded
  when κ is uncountable.
- E terminal: every extension exists and every diagram has a cocone. No
  colimit property was used. A B with an existing greatest element still gains
  a distinct new greatest element in WithTop B.

Searches for an existing statement (actual wrapper results are also retained in
`searches.jsonl` in the sandbox):

- `msearch.py ... leanfinder` query: "A quasicategory is kappa filtered if and
  only if each map from a small poset nerve extends to the nerve with a top
  element". Eight hits: quasicategory and nerve basics, finite-presentability,
  and ordinary nerve results; no poset-cone criterion.
- `msearch.py ... loogle` query:
  `SSet.Quasicategory, CategoryTheory.IsCardinalFiltered`. Zero hits.
- `msearch.py ... leansearch` query:
  "Cardinal filtered quasicategory cones on small poset nerves". Eight hits
  concern `CategoryTheory.IsCardinalFiltered` and ordinary filtered cocones.
  Reading `Mathlib/CategoryTheory/Presentable/IsCardinalFiltered.lean` confirms
  that it quantifies over ordinary functors, not simplicial coherent diagrams.
- `msearch.py ... grep` query `IsKappaFiltered|filtered.*poset|poset.*filtered`,
  subdirectory `AlgebraicTopology`: zero hits.
- `rg` over upstream `WeilConjectures/`, shared `lean/Sheaf/`, and
  `dag/lean_names_upstream.json` for
  `filtered.*[Pp]oset|[Pp]oset.*[Cc]one|lem-coef-filtered-poset-cone-test`:
  only incidental ordinary-poset discussion and proof plans; no declaration
  of this equivalence. A direct recursive grep for the item id over upstream
  `WeilConjectures/` returned no matches.
- Direct Mathlib source inspection found the reusable nerve, order inclusion,
  cardinal-bound and WithTop infrastructure, so none of these is redefined.

Validation: prescribed `scompile.py Q28 lem-coef-filtered-poset-cone-test ...`
compiled both the sandbox probe and library module, with no errors or warnings
(1.4 seconds and 1.5 seconds respectively). The statement is the only theorem,
with `sorry` as its entire proof. Delivery dry run follows; the independent
second reading is left to the designated second reader.

## Second reading by Q28

I independently read the sandbox node and module, the two statement-dependency
nodes and their recorded modules, and the recorded join/slice comparison module.
There is no repair note for this item. The delivered node differs from the shared
node only in `lean`; there are no new nodes, dependency modules, or statement
correction to audit. No mathematical or interface mismatch was found, so the
Lean source and node record are unchanged. This section is the second reading's
only edit.

Source first: I opened the actual HTT PDF at
https://people.math.harvard.edu/~lurie/papers/HTT.pdf and read Definition the project server
(printed p.382), Remark the project server (printed p.383, zero-based PDF page 400), and
Variants the project server--the project server (printed pp.255--256). The remark states this exact
poset-nerve lifting criterion. The definition assumes a regular cardinal and a
quasicategory, and tests arbitrary small simplicial diagrams, including empty
ones. The remark does not inherit the existence-of-filtered-colimits hypothesis
of the separate Remark the project server. The finite and uncountable cofinal replacements
are precisely the two variants cited by the node. This node has an HTT source,
not a Stacks tag, so there is no corresponding Stacks .tex source to substitute.

Objects, hypotheses, and conclusion, listed before comparing the signature:

1. A small universe contained in a larger universe: `universe u v`, with small
   cardinal universe `u` and ambient universe `max (u + 1) v`. Verdict: exact.
   This allows every larger containing universe and retains arbitrary `u`.
2. An infinite regular cardinal in the small universe:
   `(κ : Cardinal.{u}) (hκ : κ.IsRegular)`. Verdict: exact. I read
   Mathlib `Cardinal.IsRegular`: its first field is `aleph0_le`, so no separate
   infinitude hypothesis is missing and no finite regular cardinal is admitted.
3. A quasicategory in the containing universe:
   `(E : SSet.{max (u + 1) v}) [Quasicategory E]`. Verdict: exact; no ordinary
   category, local-smallness instance, accessibility, or colimit assumption.
4. Cardinal filteredness in the specified coherent sense: `IsKappaFiltered κ E`.
   Verdict: exact. I read `PresentableInfinityCategory.lean`, in particular
   `IsKappaSmall` and `IsKappaFiltered`: the former bounds the sum of the sets of
   nondegenerate simplices in all degrees; the latter requires a vertex of
   `Enhanced.coconeCategory F` for every such diagram. It also tests empty shapes.
   In `EnhancedDiagramsCones.lean` I checked `diagramVertex`, `constantDiagrams`,
   `commaSubcomplex`, `comma`, and `coconeCategory`. The `false` endpoint branch
   gives an arrow from F to the constant diagram, with an actual apex in E and
   all simplicial compatibility conditions. This is the dependency's cocone,
   not an ordinary-category cocone or a chosen colimit.
5. Every small partially ordered set of cardinality below κ:
   `∀ (B : Type (max (u + 1) v)) [PartialOrder B], HasCardinalLT B κ → ...`.
   Verdict: exact. I read the cross-universe definition of `HasCardinalLT` and
   `HasCardinalLT.small`: the bound implies `Small.{u} B`. Conversely, any
   small-universe poset has an ambient representative by `ULift`, preserving
   order, nerve, and the bound (`hasCardinalLT_ulift_iff`). Quantifying over
   ambient representatives therefore neither adds large tests nor loses small
   ones. There is no `Nonempty`, linear-order, directedness, or finiteness
   instance on B.
6. B with its old order and a distinct new greatest element: `WithTop B`.
   Verdict: exact. I read `WithTop.coeOrderHom`, its `some` formula and order
   reflection, and the WithTop/WithBot dual order infrastructure. It adjoins a
   fresh element rather than selecting an old maximum; old elements are strictly
   below top, even if B already has a greatest element.
7. Every simplicial diagram: `∀ (p : nerve B ⟶ E)`. Verdict: exact. I read
   Mathlib's `nerve` and `nerveMap`: simplices are composable chains and operators
   restrict chains. The canonical category of a preorder has precisely the
   order arrows, so this is N(B), with no additional categorical structure on B.
8. Existence of an extension: `∃ (pbar : nerve (WithTop B) ⟶ E), ...`.
   Verdict: exact; the quantifier is after B, its size bound, and p. It asks for
   an arbitrary coherent extension, with no universal or colimiting property.
9. Exact restriction on the entire nerve:
   `nerveMap (WithTop.coeOrderHom (α := B)).monotone.functor ≫ pbar = p`.
   Verdict: exact. I read `Monotone.functor` and checked that this map sends each
   object to its old-element inclusion and each inequality to the corresponding
   inequality. Equality is of simplicial maps in every degree, not merely on
   objects or up to a freely chosen equivalence.
10. Equivalence of both conditions: the outer `↔`. Verdict: exact, both
    implications retained. Empty B is included by the unrestricted quantifier;
    there is no additional nonemptiness or colimit hypothesis/conclusion.

Edge cases: for empty B the unique empty diagram must extend to the singleton
nerve, so E must have a vertex; for empty E both sides fail. For a singleton B,
the identity edge gives the expected cone extension. Two incomparable objects
require a common apex and legs; a two-element chain additionally retains the
compatibility 2-simplex. Terminal E satisfies both conditions. When κ is aleph0,
`hasCardinalLT_aleph0_iff` makes B finite, including empty, and its strictly
increasing chains are finite in total. For infinite B below an uncountable κ,
finite strict chains in all degrees still have cardinality |B|, giving precisely
the required bound. No case of an existing maximum is lost. Degree zero is
included by both the nerve and the nondegenerate-simplex sum. Rings, zero
modules, schemes and characteristics are not objects of this statement. The
independent universe parameters are explicitly bound, and the ambient max is
the dependency node's containment convention, not an equality restriction.

Independent H4 searches, with different phrasing from the first reader:

- `msearch.py Q28 lem-coef-filtered-poset-cone-test leanfinder`:
  "An infinity category admits cones over every small poset nerve exactly when
  it is filtered". Eight hits, all ordinary `IsFiltered`/`IsCofiltered` cocone
  criteria or siftedness; no coherent simplicial criterion.
- The same wrapper with `leansearch`:
  "quasicategory filtered extension of diagrams indexed by partially ordered
  sets". Eight hits: `SSet.Quasicategory`, ordinary `IsCardinalFiltered`, and
  filtered-colimit infrastructure for ordered sets; no exact statement.
- The same wrapper with `loogle`, query `"nerve", "WithTop"`: zero hits.
- Direct `rg -n -i` for
  `kappafiltered|filtered.*nerve|nerve.*filtered|poset.*cone|cone.*poset` over
  upstream `WeilConjectures/`, shared `lean/Sheaf/`, Mathlib's
  `AlgebraicTopology/` and `CategoryTheory/`, and `dag/lean_names_upstream.json`.
  The hits include the recorded filteredness definition, ordinary filtered-nerve
  weak contractibility, cardinal-directed-poset constructions, and proof plans;
  none states this equivalence. I opened Mathlib
  `CategoryTheory/Presentable/IsCardinalFiltered.lean`: its tests are ordinary
  functors and ordinary cocones, so it cannot replace the present declaration.
  The reusable nerve, cardinal-bound, order functor, and WithTop notions are
  already used directly; this delivery introduces no duplicate definition.

H5/H6/H8/H9: no definitions or hidden choices occur in this module. The single
public theorem has exactly `sorry` as its proof. Its source/blueprint docstring
covers both proof steps: counting strict chains, the join/coherent comparison,
the blockwise nerve/join identification, cofinal replacement, fixed-apex
mapping-space equivalence and nonemptiness via path components, including the
empty shape. I read the actual `join_slice_cocone_comparison` signature and its
source/proof docstring: it supplies the comparison equivalence over E and the
fixed-apex comparison needed in those steps. The cofinal-replacement dependency
currently has no recorded Lean module; it is only a proof prerequisite, so no
unstated object is needed to type this theorem and no import can yet be added
for it. The enhanced-diagram statement dependency is publicly imported through
`PresentableInfinityCategory`; the comparison is a nonpublic proof import.
There is no private notation, local instance, hidden `let`/`show`, unbound
variable, or over-100-character line. The namespace is `SSet.Presentability`.
A direct comparison confirms `lean.statement` is verbatim the file's complete
signature before `:= by`.

Validation: I reran the prescribed `scompile.py Q28
lem-coef-filtered-poset-cone-test` on the only delivered file. Both its sandbox
check (1.7 seconds) and library-module check (1.8 seconds) passed with no errors
or warnings. No source or node repair was necessary. The required delivery dry
run and push are performed after recording this independent reading.
