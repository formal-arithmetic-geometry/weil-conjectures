## Worker report

The module `Sheaf.CategoryTheory.IsofibrationPullbackLimit` states
`SSet.Enhanced.isofibration_pullback_limit` and supplies the two canonical helper maps used
by its comparison. `coreMap` is the simplicial map induced on the full core by a simplicial
map; its data transports the inverse edge and both triangular witnesses. `pullbackCoreComparison`
is the map from the core of the coherent functor pullback to the path-space pullback, built
from `SSet.Enhanced.homotopyPullbackComparison` and the constant path in the base. The theorem
has a `sorry` proof, as required at stage 2; neither helper contains postponed data.

The theorem signature renders the node clause by clause:

* `{E B T : SSet.{u}}` gives the three small simplicial sets in one fixed simplicial-set
  universe.
* `[Quasicategory E]`, `[Quasicategory B]`, and `[Quasicategory T]` are exactly the three
  quasicategory hypotheses.
* `p : E ⟶ B` and `g : T ⟶ B` are the displayed maps, and
  `hp : IsIsofibration p` is the only fibration hypothesis; there is no hypothesis on `g`.
* `Quasicategory (pullback g p)` is the assertion that the degreewise simplicial pullback
  `D = T ×_B E` is a quasicategory.
* `∀ (Q : SSet.{u}) [Quasicategory Q]` quantifies precisely over every small test
  quasicategory. `pullbackCoreComparison p g Q` has source
  `core ((ihom Q).obj (pullback g p)).toSSet` and target
  `simplicialHomotopyPullback (coreMap ((ihom Q).map g))
  (coreMap ((ihom Q).map p))`, the stated path-space pullback of the two core functor maps.
  Its construction inserts the constant path between the equal composites, and the final
  clause `IsWeakHomotopyEquivalence ...` is the stipulated equivalence of spaces.

The statement dependencies and declarations used are:

* `def-cbc-enhanced-diagrams-cones`, module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`, declarations `SSet.Enhanced.core`,
  `SSet.Enhanced.IsEquivalenceEdge`, `SSet.Enhanced.ihom`, and the core/functor-space
  primitives used in the helper types.
* `lem-coef-infinity-isofibration-exponentiation`, module
  `Sheaf.CategoryTheory.IsofibrationExponentiation`, declaration
  `SSet.Enhanced.IsIsofibration`.
* `def-coef-infinity-relative-cone`, module
  `Sheaf.CategoryTheory.RelativeInfinityCone`, declaration
  `SSet.Enhanced.homotopyPullbackComparison` (added to `stmt_deps` because the canonical
  comparison helper is part of the stated map).
* `lem-coef-kan-pullback-path-comparison`, module
  `Sheaf.AlgebraicTopology.KanPullbackPathComparison`, imported as a non-public proof-plan
  dependency. The open proof dependency `lem-coef-infinity-core-kan-fibration` has no Lean
  record yet, so it cannot contribute an import; its use remains in the theorem proof plan.

The six proof clauses in the node's docstring are preserved: inner-horn filling for the
strict pullback; exponential functor objects and the induced isofibration; passage to Kan
cores; identification of the core of the strict functor pullback with the strict pullback of
cores; the constant-path comparison; and naturality in `Q` together with the mapping-space
criterion for a categorical pullback.

Edge cases checked were `E = ∅`, `T = ∅`, an empty strict pullback, `Q = ∅` (with its
quasicategory instance), `p = 𝟙`, and the absence of any condition on `g`. No nonemptiness
hypothesis or hidden fibration hypothesis was introduced. An inner fibration without the
recorded equivalence-edge lifting can fail the claimed core comparison, so `IsIsofibration`
is retained exactly as the dependency defines it.

Searches for an existing declaration were made with:

* `msearch.py Q23 lem-coef-infinity-isofibration-pullback-limit leanfinder "strict pullbacks
  of quasicategorical isofibrations compute categorical pullbacks via mapping spaces"`;
  results were ordinary finite pullbacks, strict-Segal and Quillen-fibration declarations,
  with no matching quasicategorical mapping-space theorem.
* `msearch.py Q23 lem-coef-infinity-isofibration-pullback-limit loogle "SSet.Quasicategory,
  SSet.InnerFibration, pullback, KanComplex"`; no matching declaration (the service also
  reported `pullback` as unknown in that query).
* `msearch.py ... leanfinder` for the strict pullback, core/Kan-fibration, and homotopy
  pullback formulations; candidates were inspected and none had the stated conclusion.
* `rg`/`grep` over Mathlib's `AlgebraicTopology/Quasicategory`, the upstream
  `WeilConjectures` tree, and `lean/Sheaf`; these found only ordinary pullbacks, inner
  fibration closure, and the project's generic core/path infrastructure.

No existing declaration has the complete statement, no new definition node was needed, and
there is no `STATEMENT-DISPUTED` finding. `scompile.py` succeeds with no errors or warnings.

## Earlier second reading (a previous round; superseded)

I reread the copied node and module after the repair. The three quasicategory instances, the
maps `p` and `g`, and the source-fixed `IsIsofibration p` hypothesis occur verbatim. The first
conclusion is exactly the quasicategory assertion for the degreewise pullback. The quantified
map now binds `[Quasicategory Q]`, matching the node's “every small quasicategory” clause.
`coreMap` preserves the inverse edge and both triangle equations; `pullbackCoreComparison`
uses the two pullback projections and `homotopyPullbackComparison`, so its third coordinate is
the constant path at the equal composites. The target therefore has exactly the two core
functor factors and the path coordinate specified by the node. No condition on `g`, no
nonemptiness condition, and no extra conclusion was added. The module compiled through
`scompile.py` after adding the stated Kan-comparison import.

## Second reading by Q23

I independently opened the item node, its sandbox module, each statement-dependency node
and its recorded source module, and the stated Kan-comparison proof dependency. There is
no repair note for this item, no `statement_change`, no new definition node, and no delivered
dependency module. I checked the actual online source: [Kerodon 033R](https://kerodon.net/tag/033R)
assumes an isofibration on one leg of the strict pullback; [01H4](https://kerodon.net/tag/01H4)
provides the quasicategory assertion, including an empty pullback. Proposition the project server and
Remark the project server in [032Y](https://kerodon.net/tag/032Y) give the mapping-core criterion and
explicitly allow testing just quasicategories. These are Kerodon references, not Stacks
references. There are no ambient scheme, coefficient, characteristic or finiteness hypotheses.

The list I extracted from the node, matched against Lean, is:

1. A fixed universe of small simplicial sets, with a larger ambient infinity category:
   `universe u` and `SSet.{u}` uniformly for `E`, `B`, `T`, and the test `Q`. The conclusion
   spells out the mapping-space universal property, so it needs no separately chosen
   model of the larger infinity category. No size equality beyond the fixed small
   universe in the node is imposed. Verdict: exact.
2. Three small quasicategories: `{E B T : SSet.{u}}` and `[Quasicategory E]`,
   `[Quasicategory B]`, `[Quasicategory T]`. I opened Mathlib's quasicategory primitives
   through `EnhancedDiagramsCones`: these are simplicial sets with inner-horn filling.
   Verdict: exact.
3. The maps and the sole fibration hypothesis: `(p : E ⟶ B) (g : T ⟶ B)` and
   `(hp : IsIsofibration p)`. I read `IsofibrationExponentiation.IsIsofibration`:
   it requires both quasicategories, inner-horn lifting, and an outgoing equivalence
   edge lifting with prescribed source and exact image. The target of the lift is
   unrestricted. This is precisely the dependency node's convention. Its repeated
   quasicategory propositions add no hypothesis beyond the three specified above.
   There is no fibration condition on `g`. Verdict: exact.
4. The degreewise strict pullback `D = T ×_B E` is a quasicategory:
   `Quasicategory (pullback g p)`, the first conjunct. Mathlib's presheaf pullback
   has the stated projections and degreewise pullback universal property. It is
   not a pullback of homotopy categories or an object-only fiber product. Verdict: exact.
5. Every small test quasicategory, after fixing the cospan:
   `∀ (Q : SSet.{u}) [Quasicategory Q], ...` in the second conjunct. No existence,
   finite-dimensionality or nonemptiness condition is imposed on `Q`. Verdict: exact.
6. The source mapping space `Fun(Q,D)^≃`:
   `(core ((ihom Q).obj (pullback g p))).toSSet` in `pullbackCoreComparison`.
   The internal hom is Mathlib's existing `CategoryTheory.ihom`, re-exported by the
   enhanced-diagram module, not a new `SSet.Enhanced.ihom` declaration (the worker
   report's qualified spelling there was inaccurate). The recorded `core` keeps
   exactly simplices whose edges have both inverse-triangle witnesses. Verdict: exact.
7. The two target factors and their maps to `Fun(Q,B)^≃`:
   `simplicialHomotopyPullback (coreMap ((ihom Q).map g))
     (coreMap ((ihom Q).map p))`. I unfolded its definition in
   `SourceAttachmentGluing`: the first factor is pulled back against endpoint zero
   of `Fun(Δ[1], core Fun(Q,B))`, then endpoint one against the second factor.
   This is the node's path-space model, in its specified endpoint order. Verdict: exact.
8. The canonical comparison, with the constant path at the two equal composites:
   `pullbackCoreComparison` uses the core maps of both strict-pullback projections,
   and `homotopyPullbackComparison` from the recorded `RelativeInfinityCone` module.
   I read the latter's body: its path is postcomposition with
   `constantDiagrams Δ[1]`, not an arbitrarily chosen path. The commutativity proof
   in the delivered helper is induced by `pullback.condition` and the internal-hom
   functor. `coreMap` maps the inverse edge and both triangle witnesses through the
   supplied simplicial map; all six face/degeneracy equations use naturality.
   Neither helper assumes any horn-filling theorem or chooses unspecified data.
   Verdict: exact.
9. Equivalence of spaces, hence the projection square is a pullback in `Cat_∞`:
   `IsWeakHomotopyEquivalence (pullbackCoreComparison p g Q)` for every `Q`.
   I read the recorded predicate: it is bijectivity on realized path components
   and all positive based homotopy groups, for every source base point. This is
   the node's equivalence convention. The node states the explicit mapping-space
   criterion as the meaning of the categorical pullback, and the Lean gives that
   criterion in full. There is no missing separate conclusion. Verdict: exact.

Edge cases: empty `E` or `T` and a strict pullback with no vertices remain permitted;
no `Nonempty` is requested. With `Q` empty, the functor objects are points, so the
comparison still states the correct equivalence. With `p` an identity the map is the
usual strict-to-path comparison. An empty base forces empty source factors and remains
covered. Dimension-zero simplices are retained by the construction, while Kan and inner
horn conventions do not demand a dimension-zero filler or inhabitants. There is no
`n`, coefficient ring, zero object, scheme or characteristic parameter to restrict.
The single freely polymorphic universe is the fixed small universe of the node.

I repeated independent searches with wording different from the worker's:

* LeanFinder: “Pulling back a categorical fibration of quasi-categories yields a limit
  detected by maximal subgroupoids of functor categories”. The eight hits concern
  ordinary fibration base change, fibered categories and finite simplicial pullbacks.
  None states the mapping-core comparison.
* Loogle: `"InnerFibration", "pullback"`. It returns
  `SSet.innerFibration_pullbackObjObjπ`. I opened
  `Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/Inner/PushoutProduct.lean`:
  this only gives inner lifting for an exponential corner, not equivalence lifting
  or the categorical pullback conclusion.
* LeanSearch: “The strict fiber product along an isofibration of infinity categories
  represents the pullback of mapping spaces”. The eight hits are ordinary/topological
  pullbacks and model-category base change, without the desired quasicategorical statement.
* `rg` over Mathlib's algebraic topology tree, all upstream `WeilConjectures`, the
  project's `lean/Sheaf`, and `dag/lean_names_upstream.json`, using `maximal`,
  `subgroupoid`, `categorical.*pullback`, `coreMap`, and the two orders of
  `isofibration`/`pullback`. The core and path infrastructure already used in the module
  is present; no existing complete theorem or restriction-to-core map was found.
  Ordinary category cores and unrelated “Core” data structures are different notions.

I found no H3 mismatch and made no mathematical statement correction. I repaired two
H8 documentation defects: the source/title block was an ordinary leading comment rather
than a module docstring after imports, and the theorem's proof plan compressed away
important intermediate arguments. It now has a proper module docstring, a standard
copyright header, a precise source place for `coreMap`, and six numbered proof steps
including the map-to-point Kan argument, both inclusions identifying the cores, and
uniqueness of the constant-path comparison. The theorem signature and both helper
constructions are unchanged. No new notion or dependency repair is needed.

The existing `stmt_deps` addition of `def-coef-infinity-relative-cone` is justified by the
canonical comparison actually used; its recorded construction is reused without a private
copy. All recorded statement modules and the stated Kan-comparison proof module are
imported. `lem-coef-infinity-core-kan-fibration` currently has no Lean record, so there is
no module to import for that remaining proof-plan citation.

Validation: `scompile.py Q23 lem-coef-infinity-isofibration-pullback-limit
lean/Sheaf/CategoryTheory/IsofibrationPullbackLimit.lean`, run from the sandbox, compiled
both wrapper sandbox and library module successfully (3.0 s and 3.7 s), with no warnings
or errors. I checked all binders and the freely bound universe by eye, checked that every
line is at most 100 characters, and checked that `lean.statement` is the file signature
verbatim after whitespace normalization. There is one `sorry`, the named item theorem;
its complete proof plan is documented. No theorem is proved and no definition has
postponed data.
