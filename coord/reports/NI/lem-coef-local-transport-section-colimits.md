# Worker report

Item: lem-coef-local-transport-section-colimits. Group NI. Stage 1 only, 2026-10-17.

## Files written

- dag/nodes/sec-six-functors/lem-coef-local-transport-section-colimits.json: item, statement unchanged, split into six steps; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-local-fiber-relative-colimit-test.json: one new statement-only unsplit node, HTT Proposition 4.3.1.10; no Mathlib match.
- citations.json: 19 entries, one for every citation of every proof step, copied verbatim from the cited statements.
- report.md: this report. searches.jsonl is the genuine msearch log. draft_split.py is sandbox-only drafting material and is not part of the delivery.

There are 1 new node and 0 Mathlib leaves. No unit record was changed.

## Attachments

None. Searched the read-only slopmaster2 WeilConjectures tree for the blueprint tag and id, locally cocartesian fibrations, relative colimits, and section colimits. The id/tag searches found no declaration; the relative-colimit hits in CategoryTheory/Pro/Basic.lean concern ordinary pro-category presentations, and the section/colimit hits concern ordinary monoidal modules and sheaf sections. None states this quasicategorical theorem, so no attachment is claimed. The exact upstream master source is reference material only and supplied no completed proof claim.

## WANTED

WANTED: Lurie, Higher Topos Theory, Proposition 4.3.1.10 and proof (printed pp. 265-266), for lem-coef-local-fiber-relative-colimit-test and the first step of the item. Read the official PDF online at https://www.math.ias.edu/~lurie/papers/HTT.pdf; no archive under literature/ was found.

WANTED: Lurie, Higher Algebra (September 2017), Lemma 3.2.2.9 and proof (printed pp. 362-363), for the item's relative-colimit assembly route. Read the official PDF online at https://people.math.harvard.edu/~lurie/papers/HA.pdf. The proof below spells out a boundary-lifting version rather than introducing that entire assembly assertion as another unsplit node.

WANTED: archived Kerodon sources 02WS (7.1.5.17), 02XB (7.1.6.13), 01F1 (4.4.5.1), 0077 (1.5.5.14), 05YH (4.6.4.9), and 02HM (4.7.3.14), for the existing foundational nodes used in this split. Each was read online. These identifiers are Kerodon tags, not Stacks Project tags. There is no Stacks tag for local transport and relative colimits in quasicategories, so no unrelated Stacks tag is attached to these assertions. Nothing was downloaded into or written to literature/.

## Findings and changes

The imported item had a correct statement and sources but no proof. It is not a target node, and its statement does not change any target's coefficient category or base-change morphism. No STATEMENT-DISPUTED correction was needed.

I retained the categorical-fibration hypothesis and the locally cocartesian, diagram-specific hypotheses exactly. In particular I did not replace the local fibration by a globally cocartesian fibration, assume existence of all K-colimits, or restrict K to weakly contractible shapes. Those would miss the point of this item. I also did not identify the section category with a full subcategory of Fun(S,E): it is the strict fiber over id_S, including all higher simplices over that constant base diagram. This matters for bases with nontrivial natural endomorphisms.

The single added node is the generic fiber criterion. The construction and universality of a section cocone remain arguments in the item itself: an induction over the relative skeletal filtration builds the coherent lift, and a second induction on the inclusion boundary(Delta^n) times S into Delta^n times S proves initialness in its cocone category. Each omitted cell in the second induction projects surjectively onto Delta^n, so its initial vertex is at time 0 and is one of the prescribed relative-initial vertices. This is the reason all higher coherence problems have the required fillers.

The main-20261015 ancestor proof was read in literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md. Its second paragraph is the finite-level mapping-complex adjunction before the inverse limit. This item is a foundation in the inherited module-operadic-colimit-detection chain for that paragraph, not a substitute proof of adjunction or biduality. The chapter and unit records were read; their route, realized fields and historical unit binding were not edited.

## Mathlib searches

Ran all searches through /home/ubuntu/weil-launcher-nt/msearch.py NI lem-coef-local-transport-section-colimits, using separate plain-language queries for the item and the new generic criterion. For each there are LeanFinder, LeanSearch, Loogle and source-grep calls; both semantic queries were rephrased before deciding there was no match. All ten calls succeeded. The JSON records use the exact tool and query strings and the actual log records, not invented results.

Read the returned declarations and their source contexts: CategoryTheory/Limits/FunctorCategory/Basic.lean:127-184 (combineCocones, combinedIsColimit, pointwiseIsColimit), Limits/Shapes/Grothendieck.lean:33-60 and 155-182 (ordinary Grothendieck construction and isColimitCoconeOfFiberwiseCocone), Limits/VanKampen.lean:38-51 (IsUniversalColimit is stability under ordinary pullbacks), and AlgebraicTopology/Quasicategory/InnerFibration.lean:55-93 (horn lifting). The ordinary constructions have category instances and Hom-set universal properties; the quasicategory declaration only supplies inner-horn lifting. None states either local transport's relative-colimit criterion or coherent assembly of section colimits. Other hits on Comma, ordinary Kan extensions, presheaf cocones and colimits of types likewise have ordinary-category binders. No candidate is an exact or one-line specialization for our objects.

## Not duplicates

lem-coef-local-fiber-relative-colimit-test vs lem-coef-local-transport-section-colimits: the new node tests relative universality of one cocone in one fiber; it contains no section category, no existence of a coherent assembly and no detection theorem for cocones of sections. Steps 2-4 carry the assembly and universality argument, so the item has not been moved into this node.

lem-coef-local-fiber-relative-colimit-test vs lem-coef-cocartesian-section-colimits: the existing node asserts colimits in section categories for a globally cocartesian fibration, weakly contractible K, and all fiber colimits preserved by all transports. It does not characterize relative colimits for a locally cocartesian fibration and a single specified cocone.

lem-coef-local-fiber-relative-colimit-test vs lem-coef-marked-sections-pointwise-limits: the existing node concerns absolute limits of marked sections of a globally cocartesian fibration, not relative colimits of one fiber diagram. Its limit assertion cannot supply the needed outgoing-transport colimit criterion.

lem-coef-local-fiber-relative-colimit-test vs lem-coef-infinity-relative-kan-existence: the existing node assembles relative pointwise Kan extensions once relative local cone lifts are supplied. It gives no test of whether a fiber cocone is relative-universal. It therefore cannot replace the new criterion.

lem-coef-local-fiber-relative-colimit-test vs lem-coef-infinity-relative-cone-constant-test: the existing node tests relative universality using mapping-space squares, but contains no identification of that test with all local edge transports. That identification is the non-elementary HTT theorem being isolated.

lem-coef-local-fiber-relative-colimit-test vs lem-coef-module-operadic-colimit-detection: the existing parent applies this item to module sections; its citation of HTT in a source/review field is not a statement of the generic relative-colimit criterion.

Searched the whole DAG for the theorem number and key concepts, and used tools/blueprint_refs.py search with 'section colimit', 'relative colimit', 'locally cocartesian', 'fiber colimit', '4.3.1.10', 'colimits of sections', and 'relative colimit fiber'. No imported blueprint node states the new criterion or the item in another form. Both same_as lists are empty. The new id was searched before creation and did not exist. Its nearest ancestor is the ancestor command's prop-coef-integral-exceptional-adjoint; its via list prepends the item to the item's inherited via list.

## Review by NI

I reread delivery-errors B through E in full with the statements open. For B, the new node introduces E,S,q,s,K,c and transport explicitly, imports the relative-colimit definition and the fibration definition, and is statement-only with empty proof and proof_deps. It has the actual HTT source place rather than an invented Stacks tag. I checked the full statement against Proposition 4.3.1.10: inner locally cocartesian is enough; the fiber cone is tested by every outgoing edge, including degenerate ones; no supply of other colimits is required. The statement was checked on an identity fibration, a map to a point, a base with one nonidentity edge, empty K, and empty fibers. In the empty-K case it tests whether the chosen fiber-initial object remains initial after every transport, which is precisely relative initialness. No proof or clause of the section theorem appears in the new node.

For Step 1, I opened the statements of join-cone-calculus, relative-cone-equivalence, enhanced-functor-cone-calculus and the new criterion. The first gives the fixed-boundary equivalence with coherent cones, and clause (4) of the second supplies opposite quasicategories, opposite isofibrations and opposite joins. Applying the left-cone comparison to K^op and E_s^op therefore gives the needed right-cone comparison with the original boundary P_s fixed. Enhanced-functor-cone-calculus supplies equivalence invariance via its cocone mapping criterion. The new node says exactly that all outgoing transports being colimiting makes the chosen join cocone q-relative-colimiting. The given c_s and its transports are all that is used.

For Step 2, I checked relative-cone-initial-corner's statement, including its isofibration clause and its explicit map u |-> (u|K,qu). These match r exactly. Isofibration-exponentiation supplies r^S with the empty-to-S inclusion, not a claim that the section fiber is full. Its hypotheses hold because all displayed targets are quasicategories and q is categorical. The equations defining h are the two equations of the original diagram of sections, so the chosen x_s lies strictly over h(s). Fibers are quasicategories directly by solving their inner horns in the isofibration with constant base.

For Step 3, the boundary-cells node supplies the actual relative skeletal filtration, with nondegenerate cells and their full boundary; it is not merely the existence of a colimit of simplicial sets. The relative-initial-boundary node supplies full boundary fillers in every positive dimension with the specified first vertex. All vertices of S were assigned before the induction, so no dimension-zero filler is invoked, and each remaining cell has such a relative-initial first vertex. Degenerate simplices are forced by the simplicial structure; cell overlaps lie in the preceding skeleton. Taking the union retains the exact boundary and base equations. This proves the missing coherence instead of asserting that independently chosen fiber colimits automatically form a functor.

For Step 4, I checked the same two statements again for the different inclusion boundary(Delta^n) times S into Delta^n times S. A simplex outside this subset must hit all n+1 vertices in its Delta^n-coordinate; consequently its first vertex is at time zero. That is exactly where the boundary data equal f and hence have r-initial values. The positive-dimension requirement holds because n>0. After filling, the resulting map is over the fixed h, so it is a simplex of the strict fiber Z. Applying the boundary criterion to Z -> point proves initialness, and the dual fixed-boundary join comparison identifies Z with the coherent cocone category. I also read Kerodon 02WS, 02XB, 01F1, 0077 and 05YH online to check these uses against the sources. This avoids an uncited blanket claim about relative colimits commuting with exponentiation.

For Step 5, I checked that enhanced-functor-cone-calculus gives equivalence of two colimiting cocones on the SAME diagram P_s. Applying the existing transport functor takes this to an equivalence of cocones on a_!P_s; it does not need to preserve arbitrary colimits. The comparison cocone a_!c_s is the one assumed colimiting. The new criterion and initial-corner node then give r-initial vertices for the arbitrary candidate D, allowing exactly the argument already proved in Step 4. This proves detection as well as existence without silently adding a transport hypothesis for all diagrams.

For Step 6, the sole cited node gives the contractible category of initial objects and the cocone criterion. If C and D are both colimiting in sections, their equivalence lives in the same cocone category. Evaluating a simplicial equivalence carries its inverse and inverse homotopies to the fiber, so no conservativity or fullness assertion about Gamma(q) is used. Since C_s is already equivalent to c_s, its evaluated equivalent D_s is colimiting. This last step is elementary from that cited statement and the definition of a functor.

For C1/C4 I checked all 19 citations against the actual statements and generated verbatim quotations in citations.json, then independently confirmed every quote occurs literally. No step cites a proof where its statement would not suffice. Existing steps may refer to the constructions established in previous steps; no hidden additional theorem is assigned to a definition. For C6 I traversed every proposed dependency's statement/proof closure locally as a read-only inspection and none reaches the item; the authoritative server checks remain required. The one off-unit black box is enhanced-functor-cone-calculus, explicitly declared in split_report.tool_uses for its generic cone/mapping-space facts. The other proof tools are in the inherited unit.

For D I checked that there is no new section-assembly node, no pointwise-detection restatement, and no circular proof: the single new criterion is applied before the assembly construction. All assembly and universal-property work is written in Steps 2-4; the candidate-cocone test is proved in Steps 5-6. Elementary rearrangements, fibers of an inner fibration and evaluation preserving inverse witnesses are written out as steps, not new nodes.

For E I tested K empty (initial objects preserved under local transports), K a point (a cocone with equivalence legs), S empty (terminal section category), S a point (the original fiber colimit), and S=Delta^1 (a map of the transported source colimit to the target colimit). The product-skeleton argument still works for noncontractible or disconnected K because its cell dimensions concern the transformation parameter Delta^n and S, not a contraction of K. For a locally but not globally cocartesian fibration it never composes chosen transports: their role ends with the fiber criterion, and the coherent section maps are produced by lifting. I found no missing hypothesis, source error, or statement dispute. No SGA source is used.

## Unfinished work

No part of the requested one-level split is left unfinished. The new HTT criterion remains unsplit by design. Source archival requests are listed above. No Lean file was written and no compiler, Lake, build, local DAG-check, local review_split or local preflight command was run. The required server dry run is the final check; this worker does not push or deliver.

## Second reading by NI

- New node `lem-coef-local-fiber-relative-colimit-test`: checked against HTT Proposition 4.3.1.10 (pp. 265–266), including the locally cocartesian hypothesis, every outgoing edge including identities, and the empty-shape case; verdict correct, self-contained, statement-only, and needed because the existing cocartesian-fibration specialization is strictly narrower.
- Step 1: checked the opposite join/cone comparison, equivalence invariance, and the new HTT criterion against the cited node statements; verdict supplies exactly the relative-colimit input for each chosen fiber cocone.
- Step 2: checked the corner map, exponential isofibration, strict fibers, and section fiber against `lem-coef-infinity-relative-cone-initial-corner` and `lem-coef-infinity-isofibration-exponentiation`; verdict hypotheses and exact base equations match.
- Step 3: checked the relative skeletal filtration and initial-vertex boundary fillers against the cited cell and boundary nodes; verdict gives the coherent lift over the fixed base, including all degeneracies and overlaps.
- Step 4: checked the product filtration for `\partial\Delta^n\times S\subseteq\Delta^n\times S`, the surjective-projection argument, and the fixed-boundary join identification; verdict proves initialness in the strict section fiber without an unlisted colimit or global cocartesian assumption.
- Step 5: checked transport of equivalences of cocones, the fiber criterion, and the initial-corner characterization against every cited statement; verdict proves pointwise-to-section detection using only the specified transported cocones.
- Step 6: checked uniqueness of initial objects and evaluation of equivalences against the cocone mapping criterion; verdict proves the converse and handles empty `K` and empty `S`.
- Duplicate and Mathlib audit: searched the full DAG and all recorded Mathlib results. `lem-coef-infinity-fiber-relative-colimit-criterion` is only the global cocartesian special case, so it cannot replace the local theorem; no exact declaration or one-line specialization was found.
- Changes made: appended this second-reading record only. No mathematical or node-file repair was required; the existing item proof, dependency closure, citations, blueprint ancestry, and search log passed the server preflight, DAG check, and split review.
