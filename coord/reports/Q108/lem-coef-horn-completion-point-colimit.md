## Worker report

The module `Sheaf.AlgebraicTopology.HornCompletion` constructs the specified countable horn completion and states `SSet.horn_completion_point_colimit`. Its theorem has `sorry` as its entire proof; all eight construction helpers have real data. The node copy changes only `lean`. There is no statement correction, new independent notion, dependency repair, or STATEMENT-DISPUTED issue.

Source read: Cisinski, *Higher Categories and Homotopical Algebra*, [Proposition 2.1.9, Construction 2.4.36 and Section 3.1](https://cisinski.app.uni-regensburg.de/CatLR.pdf), especially printed pp. 31 and 64–65. Construction 2.4.36 specifies evaluation from the coproducts of all attaching maps, its pushout, successor iteration and the final colimit. The PDF was read online through the browser; the node already records that the local archival copy is wanted.

The clauses and their Lean renderings are:

- Arbitrary small input, with a containing universe: `universe u`, `K : SSet.{u}`. The endofunctor acts on all simplicial sets in that universe; no Kan, inhabitedness, cardinality bound or extra hypothesis is imposed on K. `SSet.{u}` itself lies in a containing universe.
- All positive horns, including the outer horns: `HornCompletion.generators (a : Σ n : ℕ, Fin (n + 2))` is exactly `Λ[a.1 + 1, a.2].ι`. Writing m = n+1 gives precisely m ≥ 1 and 0 ≤ i ≤ m, once each. There is no dimension-zero generator.
- Simultaneous attachment at a successor: `HornCompletion.step` is `terminalArrow ⋙ SmallObject.functor generators ⋙ Arrow.leftFunc`. Read `SmallObject.FunctorObjIndex`, `functorObjTop`, `functorObjLeft`, `functorObj` and `ιFunctorObj` in Mathlib's `CategoryTheory/SmallObject/Construction.lean`. For K → terminal, the bottom simplex map is unique, and the square equation is automatic. Thus these indices are canonically the triples (m,i, horn-map into K), with one simplex for each triple, rather than arbitrary chosen fillers. The top map is evaluation, the left map is the coproduct of the horns, and the result is their pushout.
- K₀ = K: `HornCompletion.stage 0` reduces to the identity functor. Kₙ₊₁ attaches all horns into Kₙ: its `Nat.rec` successor is `F ⋙ step`. Its transition is `whiskerLeft (stage n) stepInclusion`.
- The countable colimit and functoriality: `HornCompletion.tower : ℕ ⥤ (SSet.{u} ⥤ SSet.{u})` uses `Functor.ofSequence` with exactly these transitions, and `HornCompletion.functor := colimit tower`. Taking the colimit in the endofunctor category supplies an actual endofunctor, not an existentially chosen fibrant replacement. Functor-category colimits are computed pointwise twice: at K, and at a simplex degree. The existing `CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation` gives each comparison. Consequently these are precisely degreewise set colimits. The same pointwise fact applies to the attachment coproducts and pushouts.
- The natural comparison: `HornCompletion.inclusion : 𝟭 SSet.{u} ⟶ HornCompletion.functor` is the stage-zero colimit inclusion `colimit.ι tower 0`. It is natural by its type, with no added naturality assumption.
- Monomorphism: `Mono (HornCompletion.inclusion.app K)`.
- Kan anodyne extension: `SSet.anodyneExtensions (HornCompletion.inclusion.app K)`. Read its definition and the cellular characterization `anodyneExtensions_eq_retracts_transfiniteCompositions` in Mathlib's `AlgebraicTopology/SimplicialSet/AnodyneExtensions/Basic.lean`. This is exactly the closure in the statement, not inner-anodyne or only a lifting assertion without the closure identification. The characterization includes coproducts of positive horn inclusions; a small coproduct attachment can also be well-ordered as a small transfinite sequence of pushouts, and conversely these operations belong to the saturated class.
- Weak homotopy equivalence: `SSet.Enhanced.IsWeakHomotopyEquivalence (HornCompletion.inclusion.app K)`, the dependency's exact realization convention. It is bijective on path components and on every positive based cubical homotopy group, for every source base point. This is not a substitution of a model-category weak-equivalence class.
- Small Kan target: `KanComplex (HornCompletion.functor.obj K)`. Smallness is built into the target type `SSet.{u}`, not assumed as an additional proposition. `KanComplex` is Mathlib's all-positive-horn filling condition, including outer horns and imposing no zero-dimensional horn condition.
- Empty simplicial set: `IsIso (HornCompletion.inclusion.app (⊥_ SSet.{u}))`. Since the source is initial, this says precisely that the canonical completion of the empty simplicial set is empty up to its canonical isomorphism. A categorical construction by chosen colimits has this canonical-isomorphism meaning of “sends to itself.” It does not assert literal equality between chosen representatives.

The sole statement dependency is `def-cbc-enhanced-diagrams-cones`. I read its full node, its `lean` record, and the recorded `SSet.Enhanced.coneCategory` signature/docstring in `Sheaf.CategoryTheory.EnhancedDiagramsCones`, together with the definitions actually used: `componentsMap`, `homotopyGroupMap`, and `IsWeakHomotopyEquivalence`. That module imports the existing Mathlib primitives `SSet`, `stdSimplex`, `horn` and `KanComplex`; these are reused directly. No copy of a dependency notion is introduced. `HornCompletion.generators`, `terminalArrow`, `step`, `stepInclusion`, `stage`, `tower`, `functor` and `inclusion` are helpers of this node's own specified construction, recorded in `lean.declarations`, as authorized by the missing-helper rule. The node has six proof steps and proof dependencies `def-cbc-enhanced-diagrams-cones` and `lem-coef-kan-quillen-model-right-proper-core`. The former's module is publicly imported because the statement uses its weak-equivalence definition. The latter currently has no recorded Lean declaration or module, so there is no proof-only import to add yet. The second reader aligned the theorem docstring with these six steps for stage 3.

Edge cases checked before writing:

- K empty: every positive horn has a vertex (including both one-dimensional horns), so none maps to K. The attachment index is empty, the pushout remains empty, and so does every stage and the colimit. This is the explicit final conjunct.
- Dimension one: n=0 in the index gives `Fin 2`, hence both endpoint inclusions, not just the inner horns. The construction may add vertices to a nonempty input; it never inserts a vertex through a dimension-zero horn.
- Stage zero: the recursion starts at the identity and the comparison is its colimit inclusion, so no initial completion step is silently substituted for K.
- An already Kan input still receives every horn attachment as specified; no assertion that its completion equals it is made.
- All maps and all simplicial degrees are included. A horn has finitely many nondegenerate simplices, which is the required finite-presentability property despite the infinitely many degenerate simplices. This explains why countably many rounds suffice.
- Universe u is arbitrary. The countable horn family and the horn-map indexing sets, degreewise coproducts/pushouts, and countable colimits all stay in u. No equality of independent universes or additional size restriction is used.

Searches for an existing statement (all queries through the prescribed `msearch.py`; raw results are also in sandbox `searches.jsonl`):

- LeanFinder: “Countable simultaneous horn attachment yields a functorial Kan completion of a simplicial set”: eight hits, `SSet.cosk`, `SSet.KanComplex.hornFilling`, `CategoryTheory.Nerve.quasicategory`, `SSet.instQuasicategoryOfKanComplex`, `SSet.Truncated.cosk`, `SSet.modelCategoryQuillen.horn_ι_mem_J`, `SSet.modelCategoryQuillen.J`, `SSet.Quasicategory`. None constructs or states this countable completion and its weak comparison.
- LeanSearch: “The countable colimit of iterated simultaneous positive horn attachments is a Kan complex weakly equivalent to the original simplicial set”: eight hits, including general small-object iteration colimits, `SSet.KanComplex`, `SSet.hasColimits`, and finite-colimit results. No hit states this specified horn completion or its realization weak equivalence.
- Loogle: `SSet.KanComplex, CategoryTheory.SmallObject.functor`: zero hits.
- Mathlib grep: `hornCompletion|horn_completion|Kan.*completion|completion.*Kan`, restricted to `AlgebraicTopology`: zero hits. Reading `SmallObject/Construction.lean` identified the existing simultaneous attachment functor, which is reused instead of reimplemented. Reading `AnodyneExtensions/Basic.lean` identified the existing anodyne predicate and saturation theorem.
- `rg` on the project's `lean/Sheaf` and the upstream `WeilConjectures`, with `hornCompletion|HornCompletion|horn_completion|horn-completion-point-colimit`: no existing declaration of this construction or theorem. A broader Kan/horn-completion search finds only the separate cofibrant homotopy-groupoid completion module, concerning enriched categories rather than this horn construction. Searching the upstream source for the literal node id and checking `dag/lean_names_upstream.json` found no match. The new namespace and full declaration names do not conflict with existing names.

Validation: the final module passed `scompile.py Q108 lem-coef-horn-completion-point-colimit` in sandbox and library mode with no errors or warnings, approximately 1.2 and 1.3 seconds respectively under the unchanged 60-second file limit. No global build, source-checkout edit, or direct git command was run. The prescribed `deliver2.py --no-push` dry run is the final validation; the second reader supplies the independent reading and pushes the delivery.

## Second reading by Q108

I independently opened the sandbox node and `HornCompletion.lean`, the live node,
`def-cbc-enhanced-diagrams-cones` and its full recorded module, the six proof steps
and their Kan–Quillen core dependency, and the relevant Mathlib definitions. There
is no repair note for this item. There are no new definition nodes, dependency
modules or statement corrections to audit.

My object/hypothesis/conclusion checklist, with the corresponding Lean and verdict:

1. Arbitrary small simplicial set K in a containing universe, with no extra
   hypothesis: `universe u` and `∀ K : SSet.{u}`. The type of objects of the
   category is in a containing universe; its degreewise sets remain in u.
   No inhabitedness, finiteness, connectedness or fibrancy instance is required.
   Verdict: exact, including u = 0.
2. Standard simplices, positive horns and Kan condition of the dependency:
   `Λ[a.1 + 1, a.2]`, `Δ[a.1 + 1]`, `KanComplex`. I read Mathlib's horn and Kan
   interfaces and the dependency's statement, which includes both outer horns
   and excludes a zero-dimensional filling requirement. The index
   `Σ n : ℕ, Fin (n + 2)` gives every m >= 1 and every 0 <= i <= m exactly once.
   Verdict: exact; all these notions are reused, with no private versions.
3. Simultaneous attachment of one simplex for every horn map into the current
   stage: `HornCompletion.step` composes `terminalArrow`,
   `SmallObject.functor generators`, and `Arrow.leftFunc`. I opened
   `SmallObject.FunctorObjIndex` (i, top map t, bottom map b, commutativity),
   `functorObjSrcFamily`, `functorObjTgtFamily`, `functorObjTop`,
   `functorObjLeft`, `functorObj`, `ιFunctorObj`, `functorMap` and `ε` in
   `Mathlib.CategoryTheory.SmallObject.Construction`. Over the terminal object
   b is unique and commutativity automatic. Thus the index is precisely the
   specified horn-map index; top is evaluation, left is the coproduct of horn
   inclusions, and the object is their pushout. Verdict: exact real data.
4. K_0 = K, K_(n+1) the attachment to K_n, and the canonical transitions:
   `stage := Nat.rec (𝟭 _) (fun _ F ↦ F ⋙ step)` and the `whiskerLeft`
   transitions of `tower`. Verdict: exact; the recursion does not repeatedly
   attach only the original input's horns.
5. Countable colimit computed degreewise: `tower : ℕ ⥤ (SSet.{u} ⥤ SSet.{u})`
   and `functor := colimit tower`. Functor-category colimits are pointwise;
   evaluating first at K and then at a simplex degree gives the set colimit.
   The same applies to the coproducts and pushouts of step 3. Verdict: exact.
6. Functoriality in K and natural initial comparison: `functor` is an actual
   endofunctor, and `inclusion : 𝟭 _ ⟶ functor` is `colimit.ι tower 0`.
   Mathlib's square reindexing postcomposes t and uses the same generator
   simplex, as the node prescribes. Naturality is part of the data, with no
   extra hypotheses on maps. Verdict: exact canonical construction.
7. The natural map is monic: `Mono (HornCompletion.inclusion.app K)`.
   In simplicial sets this is precisely degreewise injectivity. Verdict: exact.
8. The natural map is Kan anodyne in the stated saturated sense:
   `anodyneExtensions (HornCompletion.inclusion.app K)`. I read its lifting
   definition, positive horn class J, and
   `anodyneExtensions_eq_retracts_transfiniteCompositions` (Basic.lean:111).
   The characterization is retracts of transfinite composites of pushouts of
   coproducts of J. Small coproducts themselves expand into well-ordered
   single-horn pushouts, so this agrees with the node's listed closure.
   Verdict: exact, including the outer generators.
9. The map is a realization weak homotopy equivalence:
   `Enhanced.IsWeakHomotopyEquivalence (HornCompletion.inclusion.app K)`.
   I opened `componentsMap`, `homotopyGroupMap` and this predicate in
   `EnhancedDiagramsCones.lean`: bijectivity on path components and, for every
   positive degree and every source realization basepoint, on the induced
   cubical homotopy classes. This is the node's exact convention, also for
   inputs which are not Kan. Verdict: exact.
10. Small Kan output: `KanComplex (HornCompletion.functor.obj K)` together
    with output type `SSet.{u}`. Verdict: exact; smallness is encoded in the
    construction's type, not assumed about a separately supplied object.
11. No dimension-zero attachments and empty input remains empty:
    positive-only `generators`, and
    `IsIso (HornCompletion.inclusion.app (⊥_ SSet.{u}))`. Initial simplicial
    sets are degreewise empty, so the last conjunct says that the canonical
    inclusion identifies the empty input with its completion. Chosen colimit
    representatives are appropriately compared by this canonical isomorphism.
    Verdict: exact; no unintended literal representative equality is needed.

Source comparison: I read the online Cisinski PDF at the node's recorded URL,
Proposition 2.1.9 (printed p. 31), Construction 2.4.36 (pp. 64–65), and the
positive-horn Kan/anodyne conventions in Section 3.1. There is no Stacks source
for this item. The construction starts with a set of monomorphisms, uses the
coproduct evaluation and pushout, iterates at successors and takes colimits at
limits. Specializing to positive horns gives exactly the Lean step. The general
source allows a sufficiently long ordinal: the node's finite face-generator
argument proves that omega suffices here, without an extra hypothesis. The
source imposes no nonempty or Kan assumption on K. The weak-equivalence step
of this DAG node uses the already recorded Kan–Quillen core statement, which
explicitly has the same realization convention. No hidden ambient ring,
characteristic or scheme hypothesis applies.

Edge cases: empty K gives no positive horn maps, hence no cells, and its
inclusion is an isomorphism. n = 0 in the generator index means the two
one-dimensional horns, both nonempty; it does not introduce a zero horn.
Stage zero is the input itself. A point, a disconnected input and an already
Kan input are all included; the construction can still add vertices via
one-dimensional horns and makes no claim that every Kan input is fixed.
The attaching index can be empty; Mathlib's empty coproduct and pushout cover
that case. Universe u is arbitrary and shared only by the input and output
sets; ℕ and the finite horn indices and small horn-map sets stay in u. There
is no forced equality of independent site or coefficient universes. Zero
objects, empty schemes and characteristic conditions are not notions in this
statement.

Independent duplicate searches, using different formulations from the worker:

- `msearch.py ... leanfinder "Iterating the endofunctor that adjoins fillers for
  all horns and taking its omega colimit is fibrant replacement in simplicial
  sets"`: eight hits, skeleton/coskeleton and Kan–Quillen generator/class
  declarations. None gives this endofunctor or theorem.
- `msearch.py ... leansearch "Anodyne fibrant replacement by the sequential
  colimit of the functor attaching a simplex for every horn map into a
  simplicial set"`: eight hits, including `KanComplex.hornFilling`, generic
  model-category cofibrant replacement and `SSet.hasColimits`. They assume
  fillers or describe another replacement and do not state this construction.
- `msearch.py ... grep
  "fibrantReplacement|fibrant_replacement|horn.*[Cc]ell|[Cc]ell.*horn"`:
  five hits in `AnodyneExtensions/RelativeCellComplex.lean`. I opened that
  module: it constructs a relative cell complex from an existing pairing and
  rank function, not the simultaneous countable completion.
- Direct `rg` over the named upstream `WeilConjectures` tree and the project's
  `lean/Sheaf` for horn completion and fibrant replacement found only unrelated
  fixed-object cofibrant replacements, Brown Reedy replacement, and a
  filtered-section theorem's inner-horn proof plan. I opened the latter two:
  neither declares this all-positive-horn functor or its theorem. Searching
  the proposed full names and `dag/lean_names_upstream.json` found no conflict.
  Existing Mathlib small-object and anodyne notions are already reused.

Mismatches repaired: the worker report incorrectly said that proof/proof_deps
were empty, although the node has six steps and two dependencies. I corrected
that sentence. The theorem docstring had replaced step 5 by a direct CW
compactness argument and omitted the explicit coproduct-closure and
face-generator arguments. I replaced only its proof paragraph with all six
node steps and their named dependencies. The proof-only Kan–Quillen core node
currently has no recorded Lean module, so there is no missing import of it to
add now; the enhanced-diagram dependency is already publicly imported. The
Lean statement, definitions and node fields needed no change.

H5/H6/H8/H9 checks: all eight helper definitions contain real construction
data; their small structural proofs contain no sorry. The sole theorem has
exactly `by sorry`. Every declaration has its source and blueprint docstring.
There is no private definition, local notation/instance, unbound variable,
extra hypothesis or line exceeding 100 columns. I checked that lean.statement
is verbatim the theorem signature. After the docstring repair, the prescribed
single-file scompile.py passed both sandbox and library modes without errors
or warnings (1.8 and 1.7 seconds). No source checkout or shared-library file was
edited and no global build was run.
