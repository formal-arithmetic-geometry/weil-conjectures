# Q27: lem-coef-right-decalage-augmentation-prism

## Files written

- `dag/nodes/sec-six-functors/lem-coef-right-decalage-augmentation-prism.json`: statement, split; no exact Mathlib match. Six explicit elementary steps replace the empty proof. The statement and its two statement dependencies are unchanged.
- `citations.json`: nine exact statement quotations, one for each step/node citation.
- `report.md`: this report. `searches.jsonl` records the six Q27 searches actually executed. `write_split.py` and `check_ordinals.py` are sandbox-only preparation and finite edge-case scripts, not delivery nodes.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter record was changed.

## Attachments

None. Searches of the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` (also Comparator), the upstream master project declarations, and `dag/lean_names_upstream.json` for the item id, decalage/décalage and last-vertex variants found no declaration stating the item. The upstream reference is not treated as proof evidence. The item has no Lean audit declaring an existing proof.

## Sources and WANTED

WANTED: Jacob Lurie, Higher Topos Theory, Lemma 6.1.3.17 and proof of Proposition 6.1.3.19, printed pp.554–556, for lem-coef-right-decalage-augmentation-prism (the source recorded in the item). No HTT file is archived in literature/. I did not download it or claim to read it. This delivery supplies an agent-written calculation rather than attributing that calculation to the unread source.

Read: `literature/scholze-six-functor-formalisms.pdf`, Lecture II, Definitions 2.1–2.2 and following conventions, printed pp.13–15; the nerve, simplex, simplicial-map and internal-Hom definitions used in the proof are those spelled out in `def-cbc-enhanced-diagrams-cones`. Read both cited DAG statements in full, and the right-shift use in steps 12 and 15 of `lem-coef-space-geometric-descent`. Read the current-main-20261015 blueprint statement and proof of `prop-coef-integral-exceptional-adjoint` under `sk-thm-sf-package`, especially its second proof paragraph computing the mapping-complex adjunction. The item's historical ancestry and unit binding are retained; no alternative biduality or purity route is introduced and no SGA source is used.

## Problems corrected

The item was unsplit with an empty proof. Its statement is well-typed and its two natural transformations have the stated orientations: taking opposites reverses their components. The source notation for a nerve of an opposite is understood by its canonical chain description, without reversing the prism time coordinate. There is no statement dispute and no hypothesis was added. The previous searches were retained, and the Q27 actual queries/results were appended. In particular, no generic homotopy-equivalence theorem was cited just for a construction hidden inside its proof.

The entire content here is a finite-ordinal calculation and the direct definition of a nerve prism. The general-looking construction in step 3 is elementary: its formula gives both objects and all arrows, checks the only two mixed composition cases, and checks every simplicial operator by precomposition. It does not appeal to an unproved coherence or horn-filling theorem. Making that definition-level construction a new node would create the elementary-node fault prohibited by the brief.

## Unfinished work

None in this stage-1 item. This is a natural-language DAG split, not a Lean proof. The unarchived HTT source is requested above; the independent explicit calculation is complete without it.

## Searches and reuse

Whole-DAG and blueprint searches covered decalage, last vertex, original elements, augmentation prism, the source numbers 6.1.3.17 and 6.1.3.19, and the nearest blueprint ancestor. `blueprint_refs.py search` returned no same-statement blueprint node for the relevant phrases; `ancestor` confirmed `prop-coef-integral-exceptional-adjoint`. The related geometric-descent node uses this item and must not be cited back. `lem-coef-nerve-natural-homotopy-equivalence` concludes continuous homotopies and weak equivalences of realized nerves, not the asserted indexing prisms; I read its statement and did not cite its proof as a theorem. `lem-coef-simplicial-extra-degeneracy-prism` is about ordinary-category combinatorial homotopies with extra degeneracy and is not this assertion.

Q27 ran leanfinder twice (right-decalage construction, then the more general natural-transformation/nerve formulation), loogle once, leansearch once, and grep twice, all through the prescribed msearch.py. Every service answered successfully. The hits were read in Mathlib: `SimplicialObject/Basic.lean` lines 397–428 and 504–522, `ExtraDegeneracy.lean` lines 242–279, and `SimplicialSet/Nerve.lean` lines 35–57. Ordinary `SimplicialObject.augment` constructs a comma-category augmentation under an equality condition in an ordinary target category; `StandardSimplex.shift` prepends a vertex in a particular standard-simplex construction; `nerveMap` applies a functor to chains. None is an exact match or one-line specialization giving this item's two arbitrary-quasicategory prisms and all of their stated identifications. They are useful primitives, not a Mathlib leaf for the whole item. All actual query text and returned summary records are in the item's mathlib_searches and the command's searches.jsonl.

## Not duplicates

No new nodes and hence no new/existing source-tag pairs. The two existing prerequisite nodes are reused. No Stacks tag is claimed to state this specific quasicategory-valued ordinal construction.

## Review by Q27

I checked B–E of delivery-errors against the actual statements and the cited definitions. There are no unsplit child statements or new definition nodes to audit. All imported fields and the full original statement were preserved, including the assertion about all higher simplices and the absence of a colimit assertion. Each of the six steps is shorter than 2000 characters. None conceals a geometric, model-category, realization, or colimit lemma.

Step 1 uses the index-calculus statement's definitions of j and U: extending an ordinary monotone map fixes the new last element and agrees on old elements. The two composites evaluated at every old element both equal f(x), which proves eta's naturality including the empty-source case. This uses neither the adjunction conclusion nor a property of the target quasicategory.

Step 2 uses the index-calculus statement's definition of all D morphisms as last-point-preserving monotone maps. This is essential: D also allows an old element to map to the added last element. The proof uses only preservation of the added point, so it covers those maps too. I checked that the unique singleton-source map is precisely the ordinary map l_J after U, that its empty component is the identity, and that taking opposites gives a transformation toward the constant empty ordinal. This establishes equality of the indexing transformations, not an unsupported equality inferred from target edges.

Step 3 uses the exact nerve definition in def-cbc-enhanced-diagrams-cones (simplices are functors and operators are restriction) and its internal-Hom definition. A natural transformation determines the mixed-arrow formula, and the two possible mixed composition cases are explicitly checked. An m-simplex of the product is precisely a chain together with a monotone time coordinate. Restricting both by any ordinal map commutes with applying the interval functor. That proves the entire simplicial prism from definitions and avoids using a node whose statement gives only a realized homotopy. Smallness is supplied by the item's fixed universe and the finite-ordinal categories of the cited index statement; no colimit existence or larger index category enters.

Step 4 uses both cited statements: the opposite transformations of step 2 and the defined meaning of cocone as a coherent transformation into a constant diagram. Their interval functors coincide on constant and mixed arrows; applying the nerve and then Z therefore gives exactly the same value on every (chain,time-coordinate) simplex. This is the required whole-prism identification. The singleton identity is a degenerate edge and any simplicial map preserves it, which proves the apex identity even for a target with nontrivial higher simplices.

Step 5 uses j's explicit extension formula to identify all right-shift operators, not just H_n's objects. I checked the singleton case J=[0] (H_0=Z_1 with the last endpoint map), the empty ordinal (source value Z_0 and identity leg), and every arrow to the empty ordinal in the opposite category. The augmented diagram and cocone use the same last-point maps on chains, so they agree with all higher restrictions. No assumption that Z is a groupoid object is used.

Step 6 uses eta's opposite, the nerve/internal-Hom definition, and the identities s=Uj and Z=overline Z N(q^op). For a nonempty J the inclusion omits the new last element, so contravariance restricts to the first vertices, with the stated source and target. For empty J there is just one map into its added singleton, giving the original augmentation and not a newly chosen arrow. The explicit (chain,time-coordinate) formula verifies all restrictions simultaneously. No equivalence between componentwise data and coherent data is asserted without that formula.

I additionally ran the sandbox's finite calculation for ordinals of sizes 0 through 4. It checked eta naturality for all 126 ordinary monotone maps in those sizes and last-point/unique-arrow naturality for all 251 D morphisms, including old elements sent to the added last point. The mathematical proof handles arbitrary sizes by exactly the same elementwise equations. With the terminal target the prisms are uniquely constant; for a general target only preservation of simplicial operators is needed, so no invertibility, Kan or groupoid hypothesis is hidden. An empty target admits no such diagram and gives no exceptional construction case. I checked every citations.json quote as an exact substring of its node's current statement, verified proof_deps is the union of step uses, and compared the delivered statement and stmt_deps with the repository copy: both are unchanged.
