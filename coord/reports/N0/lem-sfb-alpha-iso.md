# Worker report: lem-sfb-alpha-iso

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-sfb-alpha-iso.json`: existing statement, marked split with one proof step; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement quotes for both existing nodes cited by step 1.
- `report.md`: this report. `searches.jsonl` is the exact log from the required Mathlib searches.

## Attachments

None. The exact-id, declaration-name, and notion searches in
`/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` found no declaration of
`AlgebraicGeometry.ProEtale.isIso_condensedPullbackHom` or an equivalent
sorry-free project theorem. The similarly named declaration in
`/home/ubuntu/weil-newtargets-master/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Basic.lean`
is upstream reference material and is not an attachment. The current slopmaster2
source has no corresponding `condensedPullbackHom` declaration.

## WANTED

None. The item proof follows the current blueprint and uses only existing DAG statements.

## Corrections and blueprint comparison

The statement agrees with
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-prop-sfb-cartesian-coefficients/lem-sfb-alpha-iso.md`:
it quantifies over a condensed ring and an arbitrary scheme morphism and asserts that
the canonical alpha morphism is an isomorphism. The imported proof's argument is
valid, but its `uses` list omitted `def-sfb-alpha`, even though the phrase “By
definition, alpha_f” takes that node's statement. I added that citation and its
proof dependency, added the required proof source location, and set the item to
`split`. No child node is justified: the sole argument is exactly the item's proof,
not a separate restatement.

The nearest blueprint ancestor is the item itself, so its imported `blueprint.is`
and `blueprint.from` are retained; the whole-blueprint search found no alternate
`same_as`, recorded as `[]`. The imported node has no chapter/unit binding in this
snapshot; I did not invent maintainer-owned metadata or edit any unit record.

## Not duplicates

No new nodes were created. The existing `def-sfb-alpha` and
`def-sfb-pullback-from-point-comp-iso` nodes are cited directly; neither was copied
or restated.

## Review by N0

I read the item's current blueprint statement and proof, the full statements of
`def-sfb-alpha` and `def-sfb-pullback-from-point-comp-iso`, and the cartesian
coefficients section (`sk-prop-sfb-cartesian-coefficients/_section.md`). The alpha
definition states that alpha_f is the component at Lambda of the natural
isomorphism `f^* p_Y^* ≅ p_X^*`; the comparison definition states that this is a
natural isomorphism of sheaf functors. Step 1 cites both statements and uses no
unstated construction: a component of a natural isomorphism is invertible. Its
hypotheses are exactly the item's arbitrary condensed ring and arbitrary scheme
morphism. The two citation quotes in `citations.json` are copied verbatim from
those node statements and exceed the delivery tool's minimum length.

I checked the source route against the blueprint paragraph: it is the complete
one-paragraph proof, with no hidden Stacks or Mathlib theorem. The required
LeanSearch, LeanFinder, Loogle, and Mathlib grep searches were run through
`msearch.py`; returned declarations were generic scheme/sheaf pullback facts and
did not state this condensed coefficient result. A second semantic LeanSearch
phrasing was also run. No source declaration in slopmaster2 is available to attach,
and no external literature is needed.

Against delivery-errors B–E, the statement and hypotheses are unchanged, no
new node duplicates or restates the item, the proof dependency list is exactly the
union of step uses, every non-elementary fact is backed by a cited node statement,
and the graph edge is acyclic. I tested the edge cases conceptually: for the
identity morphism the comparison is the identity component, and for an arbitrary
morphism the terminal-point equality still gives the same natural-isomorphism
component; no openness, smoothness, finiteness, or coefficient restriction was
introduced. No Lean file, compiler, Lake build, or live project was written.

## Unfinished work

None for this one-level split. The second reader should perform the independent
review and delivery.


## Earlier second reading (a previous round; superseded)

- Item statement: checked hypothesis by hypothesis against current-blueprint `sk-prop-sfb-cartesian-coefficients/lem-sfb-alpha-iso.md` (order 1565), its proof paragraph 1, and the containing unit and chapter sections; PASS. The ring is any condensed ring, the schemes and morphism are arbitrary, and the conclusion concerns precisely the canonical morphism. There is no Stacks tag in this item's source and no SGA route.
- Step 1: opened the full DAG statements and current-blueprint source files `sk-def-sfb-coefficient-morphisms/def-sfb-alpha.md` (order 1559) and `sk-def-sfb-pullback-from-point-comp/def-sfb-pullback-from-point-comp-iso.md` (order 1556); PASS after expansion. The former identifies the component, the latter supplies the natural isomorphism for every scheme morphism. Its inverse evaluated at the same coefficient object has exactly the required reverse type, and evaluation of its two inverse identities proves both composites are identities. This is elementary; no proof internal to either dependency is borrowed, and no additional theorem is used. Both `citations.json` quotes remain verbatim and support the repaired step.
- New nodes: none; B1–B7 and new-node source, small-case, duplicate, and Mathlib-leaf checks are vacuous. The existing definitions are used directly, without duplicating them or adding an auxiliary statement of the conclusion.
- Edge cases and hypotheses: PASS for the zero condensed ring (the inverse identities still hold), a discrete field as condensed coefficients (no finite or torsion assumption), the empty source scheme and the empty-to-empty morphism (evaluation still gives inverse arrows), and the identity morphism. The identity case requires no assertion that a chosen comparison is definitionally an identity. There is no integer parameter or $n=0,1$ restriction to test.
- Independent source/Mathlib search: PASS. Exact-id, declaration-name and `upperStarFromPoint|pullbackFromPoint|condensed.*pullback|pullback.*condensed|alpha.?iso` searches of slopmaster2 and its Comparator found no attachment. Upstream master `Basic.lean` lines 343–407 was read as reference only: its comparison, component definition and generic isomorphism instance agree with this argument; no master declaration is treated as a completed proof. The independent, broader LeanFinder query “Every component of a natural isomorphism of functors is an isomorphism”, Loogle query `"hom_app_isIso"`, and CategoryTheory grep were run through `msearch.py` and logged exactly. They found `CategoryTheory.NatIso.hom_app_isIso` in `Mathlib/CategoryTheory/NatIso.lean` lines 99–101; lines 55–101 were opened and show precisely the elementary inverse argument. No separate generic Mathlib leaf is necessary for this few-line definition-level step. The whole-blueprint `blueprint_refs.py search alpha` and ancestor command were also run; the bundled ring-object definition and parent cartesian-coefficients proposition add structure or clauses and are not used as circular substitutes for this proof.

Changes made in the second reading:

- Expanded step 1 into the explicit inverse and both composite identities and marked it elementary, so the proof's entire categorical inference is visible (C1, C2, E5).
- Replaced the invalid `IsIso condensedPullbackHom` Loogle record, which returned an unknown-identifier error, with the successful independent name query; added the actual broader LeanFinder and grep results. The original raw search log is retained, including failed queries, without claiming that a query error proves absence (B7).
- Updated the split summary to describe the explicit argument. Preserved the item statement, both existing dependencies, citation quotes, and all first-worker sections, including `## Review by N0`. No new nodes or Mathlib leaves were introduced.

## Second reading by N0

- Item statement: checked every hypothesis and the conclusion against the current blueprint node `lem-sfb-alpha-iso` (order 1565) and its proof paragraph; PASS. It has an arbitrary condensed ring and arbitrary scheme morphism, with exactly the assertion that the canonical `alpha_f` is an isomorphism.
- Step 1: checked the explicit inverse construction against the complete statements of `def-sfb-alpha` and `def-sfb-pullback-from-point-comp-iso`; PASS. The first node identifies `alpha_f` as the component of the natural isomorphism supplied by the second, and evaluating both natural inverse identities gives the two displayed composites. The step is elementary and uses no unstated fact or proof internals.
- Existing dependencies: checked both node statements, their definitions, and the citation quotes in `citations.json`; PASS. Each quote is verbatim and long enough for the delivery checker, and `proof_deps` equals the step's `uses`.
- New nodes: none. B1–B7, duplicate searches, source checks, and Mathlib-leaf checks are vacuous; no node restates the item or duplicates an existing fact.
- Small cases and hypotheses: checked zero and discrete-field condensed rings, empty schemes, the identity morphism, and arbitrary morphisms; PASS. The inverse identities remain valid without finiteness, smoothness, nonemptiness, or characteristic assumptions; there is no integer parameter requiring an `n=0` or `n=1` case.
- Independent searches: checked the recorded LeanSearch, LeanFinder, Loogle, and grep entries in `searches.jsonl`; PASS. The only matching generic result is `CategoryTheory.NatIso.hom_app_isIso`, which is an elementary step fact and does not warrant a new node. No finished slopmaster2 declaration or blueprint duplicate exists.
- Delivery shape: checked `coord/delivery-errors.md` B–E, the source files, and the sandbox contents; PASS. No Lean/compiler/build tools or live project files were touched.

Changes made in this second reading: none. The prior explicit inverse expansion, corrected search records, dependency citations, and preserved review sections already satisfy the checks.
