## What changed

The signature and visibility of
`AlgebraicGeometry.Scheme.GaloisCover.sectionEvaluation_bijective_of_section`
are unchanged. Its proof now constructs ordinary evaluation by forgetting the
subtype's equivariance proof, derives its pointwise restriction law from alpha's
naturality, and applies ordinary normalized graph coordinates. Cancellation of an
injective graph evaluation proves alpha bijective.

Two new proof imports are added: `Sheaf.ConstructibleSheaf.TorsorGraphEvaluation`
and `Sheaf.ConstructibleSheaf.TorsorNormalizedGraphEvaluation`. The graph module
proves its theorem completely, using the existing proved
`CategoryTheory.FinitaryPreExtensive.isIso_sigmaDesc_lift_comp` from
`WeilConjectures.Mathlib.CategoryTheory.Extensive`. Swapping the torsor pullback
projections and base changing along f produces an isomorphism from the coproduct
of copies of W to W times_V Y. Its components are translates of the graph.
Surjectivity on points and equivariance prove injectivity of graph evaluation.

The remaining constant-sheaf argument is isolated for an ordinary linear family
beta, with restriction compatibility and diagonal normalization, but WITHOUT
any equivariance assumption. It concerns only values on the graph. The parent
supplies this family explicitly, rather than choosing any data from an unproved
existence statement. The parent node's proof and dependencies match this route.
No existing interfaces or definitions are changed, and no forced adaptations are
needed. All three modules compile together without warnings through lcompile.py.

## Proved and sorry left

Closed in the item:
`AlgebraicGeometry.Scheme.GaloisCover.sectionEvaluation_bijective_of_section`
(node `lem-weil-pbc-torsor-section-evaluation-local`). Its proof has no sorry.

Proved new theorem:
`AlgebraicGeometry.Scheme.GaloisCover.graphEvaluation_injective`
(node `lem-weil-pbc-torsor-graph-evaluation`). Its proof has no sorry and does not
use the new ordinary graph-coordinate theorem.

Added and remaining sorry:
`AlgebraicGeometry.Scheme.GaloisCover.ordinaryGraphEvaluation_bijective`
(node `lem-weil-pbc-torsor-normalized-graph-evaluation`), the only sorry in the
three delivered modules. Its entire proof is `by sorry`, and its docstring and
node give the localization, constant-function and normalization argument.

This is a reduction: one original hole closed and one strictly local ordinary
coordinate hole added, hence net zero holes before the ledger computes the actual
import closure. The torsor translate step is proved, and the remaining statement
requires no equivariance, no extension to translates, and no descent to objects
without f. It is not a proof of the full target free of sorry dependencies.

Edge cases: empty W has a unique locally constant function and a unique sheaf
section (empty covering); graph injectivity is vacuous. The zero module and the
identity torsor satisfy the same formulas. ConnectedSpace Y supplies nonemptiness,
which is essential to identify the constant coefficient module with F(Y).

## No longer needed

No original imports removed and no existing node or module pruned. The original
proof's extension of functions to every translate, and therefore surjectivity of
graph evaluation, is not needed: injectivity suffices for cancellation. The earlier
sandbox attempt's proposed graph-bijectivity hole is replaced by a completely
proved injectivity theorem. Existing connectedness, inverse-image, constant-sheaf
and section-representation dependencies remain needed through the new local
ordinary coordinate node; they are not claimed pruned.

`Sheaf.ConstructibleSheaf.TorsorDiagonalEvaluation` is not imported. Its theorem
states existence of an abstract presheaf isomorphism, without an equation for its
components identifying it with the concrete graph map needed here. The ordinary
evaluation existence and ordinary evaluation equivariance modules are also not
imported: beta is constructed directly from alpha, and alpha is already equivariant.
These were not original imports, so they count as avoided work, not removed imports.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox had an empty graph module, no new nodes and no report. Its
parent proof referred to graph bijectivity and a new normalized-composite theorem;
that attempt could not be delivered. This delivery completes the geometric part
and records the remaining local constant-coordinate part explicitly.

The DAG's full graph bijectivity plan is stronger than necessary. The final proof
only needs injectivity; composite surjectivity then gives alpha surjectivity.
The existing unit statement and realized steps are preserved.

Mathlib and both project roots were searched before writing the reduction. Searches
are recorded in searches.jsonl. LeanSearch was unavailable (HTTP Internal Server
Error), not a negative search result. Loogle, LeanFinder and local grep ran.
The referenced Stacks statements were read in the available local source mirror:
0DV5 is lemma-locally-constant-on-connected, 0DV6 is
remark-functorial-locally-constant-on-connected, 0A3R is lemma-pullback-filtered,
04TR is lemma-glue-sheaves and 04TS is lemma-mapping-property-glue. These provide
the surrounding finite monodromy/descent argument; the arbitrary-module graph
coordinate statement is an explicit local argument extracted from the parent's
plan, not a verbatim assertion of 0DV5.

## New nodes

`lem-weil-pbc-torsor-graph-evaluation`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-torsor-graph-evaluation.json`, records
proved injectivity of graph evaluation for an arbitrary representation on a finite
torsor admitting f. Its module is
`lean/Sheaf/ConstructibleSheaf/TorsorGraphEvaluation.lean`.

`lem-weil-pbc-torsor-normalized-graph-evaluation`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-torsor-normalized-graph-evaluation.json`,
records ordinary normalized graph coordinates without equivariance. Its module is
`lean/Sheaf/ConstructibleSheaf/TorsorNormalizedGraphEvaluation.lean`. This is the
one new proof item left for another worker. No change records are needed because
all existing signatures, definitions and visibility remain unchanged.


## Second reading by H2

1. Interface check: PASS. Diffed the existing module against the repository. Its
   complete theorem signature, visibility, original public imports and definitions
   are byte for byte unchanged. Only two plain proof imports and the proof replace
   the original sorry. Both other modules and their declarations are new; no
   statement or definition change record is required.
2. Kernel check: PASS for the stated decomposition. All three modules compiled
   cleanly in import order through lcompile.py. A scratch module printed the axioms
   of all three public theorems: graphEvaluation_injective has only propext,
   Classical.choice and Quot.sound; ordinaryGraphEvaluation_bijective and the parent
   additionally have sorryAx. The sole delivered sorry is the named ordinary graph
   theorem, with its docstring argument and matching node. Scanned the delivered
   sources for prohibited declarations and attributes; none occur. Beta is an
   explicit linear map obtained from alpha, not data chosen from an existence hole.
3. Split check: PASS. The ordinary theorem drops equivariance altogether and asks
   only for ordinary graph coordinates. The parent supplies its natural linear
   family explicitly and combines composite bijectivity with separately proved
   graph injectivity. Thus the hole is a strictly smaller constant-coordinate step,
   rather than the parent under another name. Tested empty W (empty-cover gluing),
   zero coefficients, the identity torsor, and disconnected W (open constant fibres).
   ConnectedSpace c.P excludes empty Y and supplies precisely the nonemptiness
   needed to identify coefficients with global sections. The graph theorem needs
   neither connectedness nor primality. Repeated LeanFinder, Loogle and Mathlib grep
   searches with different phrases, and searched both local library roots. The
   existing constantSheaf_sections_locallyConstant is for AddCommGrpCat in the
   scheme universe and only the identity object; it supplies neither this arbitrary
   ModuleCat coefficient universe nor restriction/normalization on all W. The proved
   TopCat.constantSheaf_locallyConstant_comparison concerns the open-set site, not
   the small etale site. Neither is a duplicate or a one-line solution. The existing
   diagonal presheaf isomorphism supplies no identification with this graph map.
   Closing the remaining hole requires the etale constant-sheaf comparison and its
   normalization compatibility; it is not a few-minute proof repair.
4. Route and pruning check: PASS. Read the torsor representation and associated
   module definitions and the proved FinitaryPreExtensive base-change lemma.
   Projection swapping supplies its required IsIso instance, pullback congruence
   identifies the base, and the sigma open cover and equivariance prove pointwise
   graph injectivity. Function.Bijective.of_comp_left then gives exactly the desired
   cancellation. Existing public imports support signatures; new proof-only imports
   are plain imports. No old import or module is removed. The old direct proof_deps
   def-weil-connected-scheme, def-weil-pbc-constant-sheaf and
   def-weil-pbc-inverse-image move to the ordinary-coordinate node; they remain
   needed transitively and are not pruned. The fourth old dependency,
   def-weil-pbc-torsor-section-representation, remains direct. Read sk-thm-p1's
   realized statement and all four realized step lists: this local node is below
   them, and their route is preserved unchanged.
5. Node check: PASS. Compared the parent node against the repository: only proof,
   proof_deps and proof_origin change. Matched the new graph and ordinary-coordinate
   statements hypothesis by hypothesis and conclusion by conclusion to their Lean.
   The new nodes have source, proof sketch, search evidence, creation, blueprint,
   chapter/unit and Lean records. Their proof_deps equal the union of step uses.
   The parent records the explicit forgetful family and injective cancellation;
   the graph node records the proved torsor splitting; the ordinary node records
   precisely the localization and constant-coordinate argument still open. Read
   the cited Stacks connected local-system and pullback passages in the local
   source mirror; these are the surrounding route, not verbatim arbitrary-module
   assertions.

Second-reading changes: clarified that f is etale because it is a morphism between
etale V-objects, so W belongs to the small etale site upstairs; made each new node's
lean.statement literally match its multiline Lean signature; added the independent
search, axiom, route and edge-case review above. No proof, signature, import or
hole count changed. This remains one original hole closed and one hole added,
a decomposition with net zero holes before ledger measurement.
