# Stage-1 delivery: lem-coef-coherent-vertex-equivalence-lifts

## Files written

- `dag/nodes/sec-six-functors/lem-coef-coherent-vertex-equivalence-lifts.json`: existing statement, now split in five steps; full assertion not found in Mathlib. Statement, statement dependencies, source, creation record, unit and inherited ancestry are preserved. Six actually executed Q59 search records are appended to the inherited searches.
- `citations.json`: eight step/node records with verbatim portions of the existing node statements.
- `report.md`: this report. `searches.jsonl` is produced by the prescribed search command and is retained verbatim.

There are **0 new nodes and 0 new Mathlib leaves**. The existing Mathlib pushout-product leaf is reused.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the exact blueprint tag, item id, vertex equivalences, isofibration, normalized lifts and equivalence-path lifting found no declaration stating this item. The exact item and concepts were also searched in upstream master, as reference material only. No Lean declaration or sorry proof is treated as an attachment.

## Wanted literature

WANTED: Jacob Lurie, Higher Topos Theory, Sections 2.1.2 and 2.4.6, for the imported source context of lem-coef-coherent-vertex-equivalence-lifts; online PDF inspected, not archived in literature/.

WANTED: archival Kerodon Corollary 4.4.5.3 (Tag 01F3) and Proposition 4.4.3.7 (Tag 01EZ, also in Subsection 4.4.3, Tag 01CZ), for the restriction-isofibration and core-Kan-fibration inputs. The first was read online at its tag; the direct 01EZ URL timed out, so its statement and proof were read through the indexed 01CZ subsection. Kerodon tags are not Stacks tags.

WANTED: archival Hovey, Model Categories, Propositions 3.2.2–3.2.3 and Theorems 3.6.4–3.6.5, the source of the existing Kan--Quillen-model node used in Step 4. The delivery uses the existing node's statement as a black box, not a purported new reading of Hovey.

## Corrections and scope

The imported item is mathematically correct. No STATEMENT-DISPUTED and no change to the statement is needed. Its original source correctly says this is an extracted argument, not a verbatim HTT theorem. I replaced the empty proof by the actual boundary-lifting argument. In particular, the endpoint diagram is not fixed, the full path e rather than its endpoints alone is fixed, and the first parameter value is exactly d.

The source of the blueprint ancestry was read at `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`, paragraph 2. This is a below-unit foundation for its inverse-limit mapping-space calculation. The chapter and `sk-prop-sf-biduality-general` unit records were read; this item is not their key statement, so no realized fields or unit bindings are edited. No SGA source is used by this split. The unit/chapter reference lists are inherited context, not proof citations in this delivery.

## Searches and reuse

Whole-DAG statement searches for Kan fibrations, isofibrations, restriction, lift spaces and pushout-products found all the needed existing nodes. Whole-blueprint searches with `tools/blueprint_refs.py search` for `coherent vertex equivalence lifts`, `vertex equivalence`, `isofibration` and `anodyne` returned no blueprint statement duplicating the item. The ancestor command returns `prop-coef-integral-exceptional-adjoint`; its inherited place and via chain are retained, and same_as is empty.

All Q59 Mathlib searches used `/home/ubuntu/weil-launcher-nt/msearch.py`; no direct ad hoc Mathlib search was used for discovery. The first LeanFinder phrasing returned basic quasicategory horn-filling and nerve results; the second phrasing returned KanComplex, fibration-class declarations and an abstract model-category path-object result. These types have no restriction of quasicategory diagram cores and no theorem about the specified lift space. LeanSearch returned ordinary categorical cocone equivalences and commutative-square congruences. Loogle and the first grep had no hits. The second grep found `SSet.fibration_pullbackObjObjπ` and `SSet.anodyneExtensions_pushoutObjObjι` (and their inner analogues). I read pinned `AnodyneExtensions/PushoutProduct.lean` lines 60–112, including the actual statements at 70–72 and 95–97; these are already represented by existing nodes. They are proof tools, not a one-line specialization proving the full item. The core restriction still needs the existing isofibration and core theorems. All six searches succeeded; no outage is recorded as no match. The old Q117 search records remain untouched.

## Not duplicates

No new node is created. In particular, no new specialization of `lem-coef-infinity-isofibration-exponentiation`, `lem-coef-infinity-core-kan-fibration`, `lem-coef-sset-anodyne-pushout-product` or `lem-coef-kan-quillen-model-right-proper-core` is introduced. The normalized-lift boundary argument remains in the item's own steps rather than being moved to a restatement node.

## Review by Q59

I read delivery-errors B through E in full, the item statement and source description, its parent section/limit node, the blueprint ancestor proof and all the cited node statements. I read online Kerodon 01F3 and the 01CZ subsection for the first step, and the local Stacks `simplicial.tex` definition `definition-trivial-kan` (Tag 08NL, lines 5533–5545) and neighboring Lemma 08NM for the boundary convention. I read the pinned Mathlib pushout-product declarations for Step 3. There are no new nodes requiring separate source or small-case reviews.

Step 1 uses the definition of internal functor simplicial sets and cores from `def-cbc-enhanced-diagrams-cones`, the explicit “In particular” restriction clause of `lem-coef-infinity-isofibration-exponentiation`, and the map-of-cores assertion in `lem-coef-infinity-core-kan-fibration`. These are statements, not constructions borrowed from their proofs. The only hypothesis on the indexing map is degreewise injectivity; this is proved by recovering the indexing vertex from each constant simplex. The target D is the given quasicategory. Both nodes are in the item's unit and neither requires fullness, discreteness of all of J, or a finite set of vertices.

Step 2 uses the displayed definition of Fun(K,C) in `def-cbc-enhanced-diagrams-cones`. The family/map correspondence is checked degreewise by evaluation on (id_[m],s), and its inverse is restriction along each simplex of T; no exponential theorem is silently invoked. This is elementary unpacking, including compatibility with every operator. I corrected the draft notation for the initial restriction to say explicitly “constant at d”, avoiding an ill-typed composition with the projection to T.

Step 3 uses exactly the monomorphism/anodyne pushout-product assertion in `lem-coef-sset-anodyne-pushout-product`. The initial endpoint is the horn Lambda^1_0={0}, so it is anodyne by the definitions of Kan fibration and anodyne in that node; no weak-equivalence assertion about a non-Kan interval is needed. The boundary is monic in every degree. The two prescribed maps agree on the intersection, and their images agree with the fixed e because e(0)=r(d). The Kan fibration is precisely r from Step 1. The filler therefore keeps the starting diagram and the entire vertex path fixed. All gluing is degreewise; this is not rectification or an equivalence-only replacement. This step is 1227 characters, with its single lifting square fully written.

Step 4 uses the exact all-boundaries, including n=0, characterization of trivial fibrations in `lem-coef-kan-quillen-model-right-proper-core`. That node's model structure explicitly uses the geometric-realization weak equivalences required here. Hence the resulting map is both a Kan fibration and a weak equivalence. `def-cbc-enhanced-diagrams-cones` explicitly defines “contractible” to mean weakly contractible, so no stronger topological contractibility is claimed. A fibration to a point gives the Kan-complex assertion by the horn definition. This is a use of the same-unit model theorem as stated, not of its proof or a definition alone.

Step 5 uses the core definition from `def-cbc-enhanced-diagrams-cones`: an edge in the core is an equivalence in the functor quasicategory. The equalities rh=e and r(d')=e(1) follow by endpoint restriction. The higher restrictions are explicitly precomposition by Delta(alpha) times id_I and satisfy exactly the same equations. This is elementary and does not invoke a separate theorem about compatibility. It does not assert that a fiber with a separately fixed terminal diagram is contractible.

Every uses entry has a verbatim quote in citations.json, checked as a literal substring of the current cited statement. proof_deps is exactly the union of uses; no obsolete imported proof dependency or citation has been retained. The definition dependency stays the single original one. The statements used as generic tools are already in the unit, or are Mathlib leaves, so split_report.tool_uses is empty.

For edge cases: n=0 has empty boundary and its pushout-product domain is exactly {0}, so it really gives a vertex. n=1 says any two lifts admit a comparison with the required normalization; no connectedness assumption has been smuggled in. If J is empty, A is empty and the functor simplicial sets and lift space are one-point simplicial sets. If J is discrete, r is an isomorphism and the only lift is the prescribed e. If D is empty, a given d exists only when J is empty; the assertion is otherwise vacuous. If e is constant, the terminal diagram can still vary within the strict restriction fiber; its based path space, not that fiber itself, is the claimed contractible space. These checks also explain why fixing the terminal diagram would be an incorrect strengthening (a space with nontrivial loops gives noncontractible based-loop spaces).

All proof steps are shorter than 2000 characters. There is no hidden auxiliary subclaim moved into a long step, no new clause-restatement node, and no new definition. The mathematical proof is complete at one DAG level; the existing cited foundations remain their owners' work. Nothing is written to the shared repository, source checkouts or launcher. No Lean, compiler, Lake, build, agent or local preflight command is run.

## Unfinished work and validation

No mathematical clause remains unfinished. Required server dry run and direct delivery are performed after writing this report; their actual outcomes are reported by deliver.py. The independent maintainer review remains the project's delivery review gate.
