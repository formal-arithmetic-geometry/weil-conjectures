# Stage-1 report: lem-coef-simplicial-local-equivalences-accessible

## 1. Files written

- `dag/nodes/sec-six-functors/lem-coef-simplicial-local-equivalences-accessible.json`: statement, split in twelve steps; no exact Mathlib match. The statement and its two statement dependencies are unchanged.
- `citations.json`: one verbatim statement quotation for every citation of every proof step.
- `report.md`: this report. `searches.jsonl` contains the five new searches actually run with the prescribed search command. The item's earlier search records are retained.

There are **0 new nodes and 0 new Mathlib leaves**. Every non-elementary input is an existing cited node. No Lean or compiler work was done. No repository, launcher, unit or chapter file was changed.

## 2. Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item tag and accessibility/local-equivalence terminology found no project declaration stating this result. The generic strict Bousfield localization code in `Mathlib/CategoryTheory/Localization/Bousfield.lean` is not the homotopy-local assertion here.

## 3. WANTED

WANTED: Barwick, *On left and right model categories and left and right Bousfield localizations*, https://webhomes.maths.ed.ac.uk/~cbarwick/papers/complete.pdf, Notation 3.32 and Lemma 3.33 (printed pp. 34), Lemmas 4.5--4.6 (printed p. 43), for this item. Read online, absent from local literature.

WANTED: Lurie, *Higher Topos Theory*, https://people.math.harvard.edu/~lurie/papers/HTT.pdf, Proposition A.1.2.5, Corollaries A.2.6.7--A.2.6.8 and the proof of Proposition A.3.7.3 (printed pp. 790--791, 820--821, 908--910), for this item. Read online, absent from local literature.

No document was downloaded. No Stacks tag is asserted for these homotopical accessibility results. The item's proof is marked agent-written: the exact direct argument and simultaneous monomorphism test below are supplied here, using the cited existing interfaces. It is not presented as a verbatim proof of Barwick 4.6.

## 4. What needed correction or explanation

The item is true as written; no STATEMENT-DISPUTED or statement correction is needed. Its imported source already distinguishes Barwick's all-local-equivalence result from the additional monomorphism restriction. A direct citation of Barwick 4.6 alone would not establish that restriction.

The existing `lem-cbc-homotopy-local-equivalences-accessible` is a generalization of the all-local-equivalence clause, but cannot be used here: its dependency on `lem-coef-cosimplicial-frame-mapping` reaches this item through hammock localization, simplicial inversion, coherent-nerve comparison, Segal DK comparison, completion, cartesian exponent, interval localization, bounded lifting and bounded generation. The similarly tempting `lem-coef-model-weak-equivalences-accessible` and `lem-coef-simplicial-model-nerve-localization` also reach this item. The submitted proof cites none of them and does not introduce a replacement node restating their statements.

Instead, the proof constructs local replacement using a specified small set of maps in the original Reedy category, detects local equivalences after replacement by elementary homotopy inverse tests, and uses a second accessible factorization to detect original weak equivalences by right lifting. Monicity is encoded separately by representable fold maps; the product category packages both lifting requirements. This avoids an unjustified intersection theorem and avoids any localized model structure.

I corrected the initial draft's overly short explanation of the added localizing generators: boundary lifting against `Map(f square cb_m,Z)` is lifting against `b_m square b_l` for `Map(f,Z)`. This map is monic, so the original trivial-fibration lifting axiom applies. I also made the passage from weak equivalences of Kan mapping sets to bijections on edge components explicit, citing the existing Kan Whitehead-inverse node.

## 5. What remains

The one-level split is complete. Its cited nodes retain their own current DAG statuses; no claim is made that the whole dependency closure has been formalized. The independent second reader must review this split and deliver it. This worker runs only the no-push dry run.

## Not duplicates

No new node was created, so there are no new/existing pairs to distinguish. Whole-DAG searches included accessibility of local equivalences, Barwick, accessible intersections, inverse images, small lifting classes, Reedy generating maps and Whitehead detection. Whole-blueprint searches via `tools/blueprint_refs.py search` for `accessible`, `local equivalences`, `monomorphism`, `fibrant replacement`, `right lifting`, `Whitehead` and `homotopy inverse` yielded no blueprint node stating this item. The existing general homotopy-local accessibility node is recorded above rather than duplicated. The blueprint ancestor command returned `prop-coef-integral-exceptional-adjoint`; the existing ancestry and its detailed place are retained.

## Review by Q07

I read the stage-1 standing brief, stage document, SETUP's three blueprint levels, GOAL, dag-sync, the worker role, the item's chapter/unit records and delivery-errors B--E. The unit concerns coefficient biduality, and this node is a model-categorical descendant supporting the coherent-adjunction infrastructure. Neither its geometric route nor the unit/chapter metadata is changed. The ancestor's paragraph-2 derived coefficient adjunction and its derived-limit calculation were read in the archived blueprint. This accessibility argument is explicitly an auxiliary descendant, not text attributed to that ancestor.

For the item I read Barwick 3.32--3.33 and 4.5--4.6 online and the HTT small-object and accessibility passages above. Barwick supplies the all-local-equivalence accessibility context and the Reedy generating-map formulas; HTT explains accessible factorization, small lifting tests and inverse images. The proof supplies all of the specialization and injectivity arguments. There are no new nodes requiring separate source verification.

I opened the complete statements of every node cited by each step, not merely their titles or proofs. The quotations in `citations.json` are whole statements so the reviewer can check all relevant clauses without losing hypotheses.

1. `lem-coef-presheaf-local-presentability` supplies local presentability of set-valued presheaves on any small category. Here the index is the small category Delta x Delta. Currying and disjoint unions give the three other ambient categories; no large diagram is used.
2. `lem-coef-simplicial-space-reedy-cartesian` defines F(n) and pushout products; `lem-galois-yoneda-hom-bijection` gives actual evaluation bijections, not just full faithfulness; `lem-coef-reedy-model-structure` states the matching-object and trivial-fibration characterizations; `lem-coef-kan-quillen-right-proper` supplies precisely the horn and boundary tests. The written square correspondence identifies all four maps, so both I_R and J_R have the asserted right classes, including n=0.
3. The cartesian Reedy statement identifies all cofibrations with monomorphisms and supplies its weak-equivalence pushout-product clause. The Kan statement says horns are trivial cofibrations; the Reedy statement says weak equivalences are objectwise. Therefore every J_R generator is a trivial cofibration and its mapping restriction into a fibrant object is trivial. No combinatorial-Reedy assertion is inferred from a node that only defines Reedy structure.
4. The cartesian mapping axiom makes Map(f,Z) a fibration since f is monic. The Kan boundary criterion makes localness equivalent to boundary lifting. The tensor--mapping adjunction is the defining universal property of the stated mapping sets. For the added generators I checked a second boundary test explicitly via b_m square b_l; the domain is a union of subsets and hence monic. The lifting axiom for trivial Kan fibrations applies with no finiteness or nonempty-source assumption. This establishes the generator property used in step 6.
5. `lem-coef-accessible-small-object-factorization` explicitly asserts preservation of sufficiently filtered colimits for its middle-object functor, as well as functoriality and the two factorization classes. Its category is locally presentable by step 1 and J_f is a small set including the single given f and countably many boundaries. Terminal-arrow formation preserves filtered colimits because their indexing categories are nonempty and connected. Thus R is accessible, with no silently fixed rank.
6. The Kan boundary criterion and the explicit tensor--mapping adjunction translate the mapping test into left lifting against the displayed cotensor restriction arrows. `lem-coef-lifting-class-closure` supplies pushout and retract closure, and `lem-coef-transfinite-left-lifting` supplies exactly the continuous-transfinite closure. Coproduct lifting is independent lifting on summands. Thus every small-object unit induces a trivial mapping fibration into every local Z. No inverse-limit theorem or unidentified saturation assertion is invoked.
7. The Reedy model statement gives the original trivial-cofibration/trivial-fibration factorization of a weak equivalence and all model lifting axioms; the cartesian statement gives all objects cofibrant and the trivial mapping restriction along the first factor. The section of the second factor and its homotopy are obtained by the explicitly written two lifting squares. `lem-cbc-simplicial-homotopy-equivalence-weak` applies to these ordinary simplicial mapping sets, with no Kan assumption required by that lemma.
8. Naturality of eta and Kan two-out-of-three transport the local test to Ru. For the converse, both local endpoints are Reedy fibrant, so the cartesian statement makes their mapping sets Kan. `lem-cbc-kan-whitehead-inverse` turns each weak equivalence of those mapping sets into a simplicial homotopy equivalence and hence a bijection on edge components. Testing the two endpoints supplies a left inverse and forces the right inverse up to homotopy. Two-horn fillers concatenate or reverse the resulting paths. Evaluating homotopies at each outer degree and applying the homotopy-equivalence lemma proves exactly the objectwise equivalences required by the Reedy statement. No infinity localization is used.
9. The same accessible small-object node is applied to J_R, not to a hypothetical localized model. The lifting-closure and transfinite nodes imply its left factors are original trivial cofibrations, and the Reedy weak factorization system identifies the class. The explicit I_R test from step 2 detects trivial fibrations; thus p_Ru detects precisely local equivalences. Both its source and target preserve sufficiently filtered colimits, and the maximum of the two regular bounds works for the composite.
10. The full Yoneda evaluation statement turns a fold square into two bidegree elements with equal images. A filler exists exactly when those elements agree, proving injectivity and not surjectivity. This is a short elementary step, not a new lemma node.
11. Product-category lifting and colimits are componentwise. Each auxiliary component is the identity of the empty presheaf, which has a unique lift against every map. The constructed functor G and set S therefore encode both clauses exactly, rather than assuming accessibility survives arbitrary intersections. This step uses only the constructions and equivalences already proved in steps 8--10.
12. `lem-coef-small-right-lifting-accessibility` asserts ambient closure and small generation, not merely accessibility of an unrelated category of chosen fillers. `lem-coef-accessible-full-inverse-image` explicitly permits an arbitrary functor between arrow categories; the more restrictive endpoint-induced inverse-image node is not used. Both ambient categories are locally presentable and G preserves sufficiently filtered colimits, so all its hypotheses hold. Its conclusion includes the exact lambda-filtered closure, generation and repleteness required by the item.

Small cases checked: n=0 has empty outer boundary; m=0 has empty inner boundary and tests existence of a vertex; horn indices always have positive dimension; f an identity makes every Reedy fibrant object local and recovers monomorphic Reedy equivalences; the empty X and Y are allowed throughout; representable fold lifting is vacuous on empty element sets and fails on a genuinely noninjective map. For an arbitrary u, neither its source nor target is assumed fibrant before applying R. All factorization and cardinal choices depend on f and the fixed universe only.

For B1--B10: no new node has a hidden proof, false source tag or unrun search; all five queries are in the command's log, and the returned generic declarations were read. In particular OrthogonalReflection.lean:95--103 treats strict Hom-set orthogonality, not these homotopy-local equivalences. Existing search and ancestry metadata were retained. For C1--C8: all non-elementary inputs have explicit existing citations and verbatim quotes; no fact is borrowed from a cited node's proof. The only off-unit statements used as generic tools are the Yoneda evaluation, simplicial homotopy equivalence and Kan Whitehead inverse, declared in split_report.tool_uses. For D1--D5: the twelve steps carry the construction and proof, with zero new restatement nodes. For E1--E7: the original mapping sets, boundary/horn conditions, universes, fibrant endpoint tests, and exact product lifting conditions were checked as above. No source error or statement dispute was found. Every proof step is below 2000 characters, and the comparisons and squares are written out rather than hidden by transport language.

## Validation

The required command `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q07 lem-coef-simplicial-local-equivalences-accessible --no-push .` printed `OK (not pushed)` and reported that server preflight passed. It saved the durable dry-run receipt for the independent second reader. The same command is run once more after this validation paragraph is written, so the accepted sandbox includes the final report. No delivery is pushed.


## Second reading by Q07

Independent second reader, 2026-10-17. The maintenance recovery condition is false:
this is Q07 / lem-coef-simplicial-local-equivalences-accessible, its stage-1 JSON is
present, and no retained stage-2 packet exists at the named Q07/item path. This is
a stage-1 reading; no Lean was written and no compiler or Lake command was run.
The original worker report and `## Review by Q07` above are preserved.

I compared the unchanged item statement with Barwick, *On left and right model
categories and left and right Bousfield localizations*, 3.31--3.33 (printed p. 34)
and 4.5--4.6 (printed p. 43), read online in full at those places. Barwick 4.6
asserts accessibility for all local equivalences in a combinatorial model
category; it does not itself assert the monomorphism restriction. The packet
correctly identifies that restriction as its own specialization. I also read HTT
A.1.2.5(1)--(2) and its proof (printed pp. 790--791), Definition A.2.6.2,
Proposition A.2.6.5, Corollaries A.2.6.7--8 and their proofs (pp. 818--821), and
the local replacement argument in the proof of A.3.7.3 (pp. 908--910). These
supply precisely the ambient-colimit meaning of accessibility and the
small-object/inverse-image route used here. The argument is correctly marked
agent-written. No Stacks tag or forbidden SGA route is claimed for this result.

The hypotheses remain a single fixed monomorphism f in the fixed universe,
the original Reedy structure, and the stated ordinary mapping simplicial sets.
The conclusion includes repleteness, closure in the ambient arrow category,
and generation by a small family, all at one sufficiently large regular small
cardinal. No left properness or localized model structure is needed by this
particular proof. I read the chapter and unit records and the main-20261015
ancestor proof, paragraph 2: its derived coefficient adjunction is provenance
for this auxiliary descendant, not a source asserting the accessibility theorem.

Each line below records a check of the actual cited statements, not of their
proofs. All twelve dependency statements were opened, and all 30 citation
quotations equal the current entire statements verbatim.

1. Step 1: checked presheaf-local-presentability for Set and a small index;
   D, D times [1]^op and their disjoint unions are small. Currying gives the
   claimed categories with componentwise colimits. PASS.
2. Step 2: checked Yoneda's evaluation and naturality clauses, the cartesian
   node's F(n), the Reedy node's matching and trivial-matching criteria, and
   the Kan node's horn/boundary criteria. The outer boundary specifies all
   proper faces and hence the matching limit; the displayed square is exactly
   the matching-map square. Both right-class equalities follow. PASS.
3. Step 3: checked the cartesian node's identification of cofibrations with
   monomorphisms and its pushout-product/mapping clauses, with Kan horns and
   Reedy objectwise weak equivalences. The constant horn map is trivial and
   all objects are cofibrant. PASS.
4. Step 4: checked the same mapping axiom applies because f is monic and Z
   fibrant. Kan boundary lifting detects the required trivial fibration.
   For an added generator the iterated test is b_m square b_l; that is monic,
   so lifting follows from the original trivial-fibration axiom. PASS.
5. Step 5: checked accessible-small-object-factorization actually asserts
   a functorial middle object preserving sufficiently filtered colimits.
   J_f is small, and terminal-arrow formation preserves filtered colimits
   because the indexing category is nonempty and connected. PASS.
6. Step 6: checked the cartesian internal hom and boundary adjunction convert
   trivial mapping fibrations to the indicated left lifting class. The two
   lifting nodes provide pushout/retract/transfinite closure; coproducts use
   independent fillers. Made containment of all isomorphisms explicit via
   the filler u a^{-1}, completing the weak-saturation check. PASS after edit.
7. Step 7: checked the Reedy model axioms allow factorization with i trivial
   cofibrant and p trivial fibrant; two-out-of-three supplies the second
   adjective. Cofibrancy gives a section, and the cylinder boundary is monic.
   Expanded the induced mapping homotopy using its common simplex parameter;
   ps is strictly the identity. The cited simplicial-homotopy-equivalence
   statement needs no Kan/nonemptiness assumption. PASS after edit.
8. Step 8: checked naturality of eta and Kan two-out-of-three, then both
   endpoint tests Map(v,A) and Map(v,B). The endpoints are local fibrant,
   so these mapping sets are Kan. Kan-Whitehead-inverse gives bijections on
   edge components; surjectivity supplies s and injectivity gives vs homotopic
   to the identity. Two-horn fillers compose and reverse edge paths. Evaluating
   both homotopies in every outer degree satisfies the homotopy-equivalence
   node, and Reedy weak equivalence means exactly these row equivalences. PASS.
9. Step 9: checked the second factorization uses J_R in the original category,
   and the lifting-closure nodes plus the Reedy weak factorization system make
   its left map trivial cofibrant. Thus I_R lifting detects W_R by
   two-out-of-three. The source and target of p_v preserve sufficiently
   filtered colimits, so the arrow functor and its composite with R do too.
   A larger regular bound preserves both preservation properties. PASS.
10. Step 10: checked the full Yoneda bijection identifies a fold square with
    exactly two elements having the same image. The diagonal exists iff they
    agree. This elementary calculation tests injectivity, not surjectivity.
    PASS; correctly not made a new node.
11. Step 11: checked componentwise squares in M times M. A square against
    1_0 always has its unique auxiliary filler; hence the product test imposes
    exactly the monicity and I_R-lifting tests, with no extra condition.
    The previous steps supply accessibility of G. PASS; elementary packaging.
12. Step 12: checked small-right-lifting-accessibility gives ambient closure
    and small generation for S^square, and accessible-full-inverse-image
    explicitly allows the arbitrary arrow-category functor G. The domains
    are locally presentable and G preserves sufficiently filtered colimits.
    The conclusion is exactly the item, including possible enlargement of
    the cardinal and repleteness. PASS.

New nodes: none; zero new Mathlib leaves. Thus there is no statement-only,
definition-dependency, duplicate, source-tag or new-node edge-case defect to
repair. I independently searched with msearch.py using the different phrase
"Weak equivalences for localization at a set of maps in a simplicial model
category form an accessible full subcategory of morphisms" (LeanFinder), and
an accessibility/weakEquiv/localEquiv expression in AlgebraicTopology (grep).
Both actual records are in searches.jsonl and the item's mathlib_searches.
LeanFinder returned generic cofibrant-object localization and inherited
weak-equivalence structures, with no accessibility conclusion; grep returned
zero hits. I read the relevant CofibrantObjectHomotopy and
CategoryWithCofibrations source declarations and OrthogonalReflection.lean:
95--103. Strict Hom-set orthogonality and preservation by its inclusion do
not state homotopy-local equivalence accessibility. The existing general
homotopy-local accessibility node was read as a candidate, not duplicated or
cited through its cyclic infrastructure. The three generic off-unit inputs
remain requests in split_report.tool_uses for the maintainer's route review;
no maintainer-owned tool_uses field was installed.

Edge cases: n=0 makes the outer boundary empty; m=0 makes the added boundary
empty and genuinely tests existence of vertices. For f an identity every
Reedy fibrant object is local. For f from the empty space to the terminal
space the m=0 generator forces vertices where required, rather than making
localness vacuous. Empty sources and targets, empty sets of elements in the
fold test, and disconnected Kan mapping sets are permitted. No replacement
step presupposes that its input is fibrant.

Changes: expanded the isomorphism-lifting argument in step 6 and the
mapping-space homotopy in step 7, to expose the two short arguments behind
the closure and precomposition assertions. Added the two actual independent
search records and this second-reading section. Statement, statement
dependencies, proof dependencies, sources, ancestry, all existing citations,
and the worker's report sections are preserved. The changes require no new
citation: they are explicit computations from the previously cited definitions
and lifting axioms. Backups of the original report and item JSON are retained
in the sandbox with suffix .second-reader.bak.

Validation: the second reader runs the required deliver.py --no-push command
after this complete report and all packet edits, awaits its exit, and pushes
only after its OK result. The server performs the DAG and split preflight;
those tools are not run on this machine.
