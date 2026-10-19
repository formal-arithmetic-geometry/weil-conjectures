## Worker report

Files written:
- `dag/nodes/sec-six-functors/lem-coef-dg-abc-cone-homotopy.json`: item, statement unchanged, split into nine explicit algebraic steps; no Mathlib match.
- `citations.json`: the verbatim statement quote for the sole external proof citation (step 1).
- `report.md`: this report.

New nodes: none. New Mathlib leaves: none. The supporting computations are short calculations from the supplied splitting identities; creating nodes for them would violate the elementary-node rule.

Attachments: none. Searched the exact blueprint tag and the admissible/cone/homotopy notions under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/`. There was no declaration for this arbitrary-dg-category statement. The existing homotopy-category material concerns ordinary complexes or module-derived categories. The upstream master snapshot is not being claimed as evidence of a finished proof.

WANTED: none.

What was wrong or incomplete: the item was statement-only. It was correct as stated, but its existence and invertibility clauses needed actual formulas and homotopies. In particular, invoking a triangulated cone theorem here would be circular: this item is an input to the dg triangulation theorem. The split now proves the needed square-zero relation directly. No statement, chapter, unit, or proof route was changed.

Unfinished mathematical work: none at this one-level split. The required dry run printed OK (not pushed); its final verification is described below. This worker does not push or deliver; the fresh second reader will do so.

## Sources and existing-node searches

Read `literature/stacks-project/dga.tex`: Tag 09P6 (`lemma-get-triangle`, equations (1)-(7)); Tag 09P7 (`lemma-cone`, the cone-map formula and differential); Tag 09QP (`lemma-triseq`, strictification followed by the biproduct null-product calculation); Tag 09QT (`lemma-analogue-third-isomorphism`, inverse square and square-zero correction); and Tag 09QU (`lemma-cone-homotopy`, part (1), comparison maps and homotopy). Verified all five tags in `literature/stacks-project/tags/tags`. These are sources for computations in the item's proof, not uncited theorems used as black boxes.

Read the chapter record `sec-six-functors`, unit `sk-prop-sf-biduality-general`, and both snapshots of `prop-coef-integral-exceptional-adjoint`. The current main-20261015 file contains its statement only. Paragraph 2 with the three derived Hom objects belongs to the historical master blueprint proof; the ancestry records that historical place. The current ancestor DAG proof implements this mapping-complex infrastructure in steps 4--6. Read the statements and proofs of the intermediate dg triangulation and module-cone nodes in the recorded ancestry. This item supplies generic infrastructure below that route; it does not replace any geometric step of the unit. No SGA source is used.

Searched the whole DAG for 09P7, 09QT, 09QU, 09QP, dg admissible sequences, cone homotopy and square-zero endomorphisms. Ran `tools/blueprint_refs.py ancestor lem-coef-dg-abc-cone-homotopy`, and blueprint searches for `cone homotopy`, `09QP`, and `admissible`. There is no imported blueprint node stating this arbitrary-dg-category comparison. The parent triangulation theorem cites the item and cannot be used to prove it. `blueprint.same_as` remains empty, with its precise ancestry place retained.

Ran logged msearch queries for the item using LeanFinder twice, Loogle, grep, and LeanSearch; all services returned hits. Their exact queries and assessed results are appended to `mathlib_searches`. Read `Mathlib/Algebra/Homology/HomotopyCategory/Pretriangulated.lean` lines 96-125 and `DegreewiseSplit.lean` lines 28-100. The closest declarations are `CochainComplex.mappingCone.mapOfHomotopy`, its triangle compatibility lemmas, and the degreewise split triangle constructions. They are about `CochainComplex C Z`, whereas the item is about an arbitrary dg category and arbitrary cones satisfying (C). A dg representation and reflection argument would be an additional proof, not a one-line specialization. Accordingly this item is not a Mathlib leaf.

## Not duplicates

No new nodes, hence no new/existing-node pairs.

## Source error

In the local text of Tag 09P7, the printed cone formula ends with `a_2 h b`, although the projection in the setup is `b_1`; its later differential uses `b_1`. Also its parenthetical sentence writes `d(pi_1) = f_1 b_1`, while the preceding boundary identity and the displayed differential require the negative sign. The proof here uses the typed term `i_2 h P_1` and the identity `partial rho_1 = -f_1 P_1`, which follows directly by differentiating the biproduct equations. These are repairs to source-proof typos, not changes to the item. The printed target triangle in that source lemma also repeats the first triangle's objects; our map has the correctly typed target cone throughout.

## Review by NS

I checked B through E with the node and the five Stacks source passages open. There are no new statements to test or source to obtain. All objects and hypotheses of the item remain unchanged: the category is small over the integers, the morphism complexes are cochain complexes, splittings are only graded, and the cones are any choices supplied by (C). In particular I did not assume an abelian underlying category, closed splitting maps, a strict commuting initial square, or triangulatedness. The module-category specialization in Mathlib cannot silently supply these hypotheses.

Step 1 cites only `lem-coef-dgcat-model-structure`. I opened its statement: its sentence saying that a small dg category has cochain morphism complexes and associative unital chain-map compositions is exactly what gives the graded Leibniz rule. It is copied verbatim in citations.json. I use none of its model-structure, cofibrancy or replacement assertions. The quotient and equivalence observations in step 1 are immediate from the definition of boundaries and the definition of homotopy equivalence already in the item.

Step 2 differentiates the five given splitting equations. I checked that neither pi nor s is assumed closed and that the proof of closedness of D uses the actual left inverse pi of a. Step 3 spells out how the shifts change the degrees: the cone section becomes degree minus one and the projection degree plus one. The equalities partial S = i f and partial rho = -f P follow from the cone boundary being f[1]. The negative target-shift differential is retained. These are explicit calculations from (B),(C) and step 2, not an appeal to a theorem about cones.

Steps 4 and 5 substitute those identities. I checked the types of e, t and H and all three signs in partial H. Direct expansion gives te-1 = partial(-S pi rho). The last diagram equation follows from partial(pi rho) = -D b rho - P, so the minus sign on the cone projection is necessary. It is not inferred from a previously available triangulated structure.

Step 6 uses the given homotopy partial h = b f_1 - f_2 a. The three differential contributions cancel exactly, and the two compatibility equations hold strictly because rho_1 i_1 = 1, P_1 i_1 = 0, P_2 S_2 = 1 and P_2 i_2 = 0. This construction works before imposing equivalence of a,b. The shifted equation restores a[1], so no source/target shift was lost.

Step 7 expands, rather than cites, the substantive null-product argument of 09QP. Here I checked the operations with the shifts restored: k and l both have degree minus one; rho and sigma have degree zero but need not be closed. Taking the differential of k rho and sigma l makes the required left and right composites vanish because i and p are closed. The biproduct identity then makes v_L v_R strictly zero. The explicit primitive K v + v_L L proves v squared is a boundary. Thus 1-v is inverse to 1+v in H^0 over the integers, with no division by two and no general triangulated lemma.

Steps 8 and 9 use only step 6 and ordinary multiplication of classes. I checked both directions of the inverse square, the shifted inverse equation, and both composite endomorphisms. The left and right inverse formulas are typed at the correct cone, and their equality is proved by L = L(cR) = (Lc)R. Closed representatives of their common class meet precisely the definition of homotopy equivalence. There is no self-citation: step 8 uses an earlier explicit formula, not the conclusion still being proved.

All steps after step 1 cite no external nodes because they display their full algebraic arguments. Marking them elementary refers to these displayed differentiations and multiplications, not to an unexplained assertion that cone equivalences are standard. No new node restates a clause of the item, no auxiliary proof is hidden in a statement, and no cycle has been introduced. The sole proof dependency is also the pre-existing statement dependency.

For edge cases I checked a split sequence with D = 0, a = 1 with z = 0, and the zero cone: the same formulas give respectively the ordinary split comparison, a contraction of the identity cone, and zero maps satisfying the identity equations of the zero object. For f_1 = f_2 = 0 and identity vertical maps with h = 0, step 6 is i rho + S P = 1 for identical cone choices. With arbitrary h it adds a closed off-diagonal term, whose square is zero. If only one endpoint is a zero object the identities still type and no cancellation by a nonzero object is used. The square-zero inverse works in characteristic two as well as over Z; it uses only additive inverses. These checks support the arbitrary-cone and all-characteristic scope of the statement.

The corrections made during this reading were to use the typed projection P_1 in the source's cone formula, keep its differential sign negative, write the comparison homotopy explicitly, and expand the null-product argument with its primitive. The item's statement needed no correction. This is the first worker's signature; the independent second reading and actual delivery remain for the next worker.

## Completion of earlier attempt by NS

This is a continuation of the assigned first-worker task, not the independent second-reader delivery. I reread the item and all nine proof steps, the sole cited statement, the five complete Stacks passages identified above, the chapter/unit records, both blueprint snapshots of the ancestor, and the ordinary-complex Mathlib candidates. No new node or mathematical statement change was needed.

I checked the delicate computations directly. In step 5, differentiating $-S\pi\rho$ gives exactly $-ia\pi\rho-SDb\rho-SP=te-1$; the projection relation uses $\partial(\pi\rho)=-De-P$. In step 7, $\partial(K)i=\partial(Ki)=\partial k$ and $p\partial(L)=\partial(pL)=\partial l$, so the proposed strictifications work even though $\rho,\sigma$ are not closed. Expanding $\partial(Kv+v_LL)$ gives $(v-v_L)v+v_L(v-v_R)=v^2-v_Lv_R=v^2$. Thus the key invertibility argument is supplied explicitly and does not import an uncited triangulation or five-lemma assertion. Steps 8--9 then construct both one-sided inverse classes and identify them. The zero, identity, split, and characteristic-two tests in the review remain valid.

I repeated the attachment search in the project Lean sources; there is no exact declaration to attach. I reran the logged msearch LeanFinder queries in two phrasings, Loogle, grep in Algebra/Homology, and LeanSearch. All returned successfully. The five new search records contain the exact logged query texts and result summaries; each returned type concerns ordinary complexes, not the arbitrary dg category in this item. The earlier search records are retained. No service failure has been counted as absence.

I corrected one reporting/provenance error in the inherited attempt: it claimed that the three-Hom proof paragraph was in main-20261015. That file is statement-only; the paragraph is in the historical master snapshot. The item's from.place and split_report.blueprint now distinguish that historical ancestry from the current statement. Its ancestry ids, chapter, unit, statement and proof route are unchanged. I removed the inherited heading that purported to be an independent second reading: this handoff still needs the fresh second reader specified in the brief.

The sole citation quote was verified as a literal substring of lem-coef-dgcat-model-structure.statement. All nine steps are explicit computations from the stated dg and splitting hypotheses; proof_deps is exactly the union of their uses. No external fact is used through a definition-only citation. B--E require no new-node, duplicate-pair, or smallness repair because there are no new nodes and no additional existence constructions.

## Dry run

The required command is `python3 /home/ubuntu/weil-launcher-nt/deliver.py NS lem-coef-dg-abc-cone-homotopy --no-push .` from this sandbox. The first run printed `OK (not pushed) deliver/NS/lem-coef-dg-abc-cone-homotopy at 262e2cc8b6: preflight passed`. After the search-record and provenance/report corrections above, the same command is rerun on the final files. No push or delivery is authorized for this worker; leave these files for the second reader.

## Second reading by NS

I opened `literature/stacks-project/dga.tex` at Tags 09P6 (`lemma-get-triangle`), 09P7 (`lemma-cone`), 09QP (`lemma-triseq`), 09QT (`lemma-analogue-third-isomorphism`), and 09QU (`lemma-cone-homotopy`), and compared the item statement clause by clause. The zero object, binary dg sums, shifts with the stated sign, admissible splittings, arbitrary cones, both cone-map identities, and the homotopy-equivalence conclusion all match the source's Situation ABC over the specialized ring $\mathbf Z$; no hypothesis is added or dropped. The zero, identity, split, and characteristic-two cases remain well typed.

Step 1 was checked against the statement of `lem-coef-dgcat-model-structure` and the dg Leibniz rule; it uses only the stated cochain complexes, chain-map composition, and the definition of $H^0$ homotopy equivalence. Steps 2--3 were checked against 09P6 and 09P7, including the signs $\partial\pi=-Db$, $\partial S=if$, and $\partial\rho=-fP$ after the explicit shift identifications. Steps 4--5 were expanded and checked term by term against 09QU: $e$, $t$, and $H=-S\pi\rho$ have the required degrees, $et=1$, $te-1=\partial H$, and $De+P=-\partial(\pi\rho)$ gives the shifted square. Step 6 was checked against 09P7: the three terms in $c$ have degree zero, their differentials cancel using $\partial h=bf_1-f_2a$, and both cone compatibilities hold strictly after restoring shifts. Step 7 was checked against 09QP and 09QT: the strictifications $v_L,v_R$ kill the two split summands, $v_Lv_R=0$, and the displayed primitive gives $\partial(Kv+v_LL)=v^2$ with the correct Leibniz signs. Step 8 was checked for the inverse square and both composites $c'c$ and $cc'$; Step 9 was checked for the left/right inverse formulas and their equality. No step relies on a triangulated axiom or on a proof hidden in a cited node; only Step 1 cites the pre-existing model-structure statement, with its verbatim quote in `citations.json`.

There are no new nodes, so B1--B7, duplicate-node, and Mathlib-leaf checks are vacuous. I searched the DAG for the five Stacks tags and the cone/homotopy terminology, and searched Mathlib with the recorded LeanFinder, LeanSearch, Loogle, and grep queries. The ordinary `CochainComplex` declarations do not state this arbitrary-dg-category result, so no Mathlib leaf or duplicate node is appropriate. I also checked that the node's source, statement dependency, blueprint ancestry, proof dependency, and citation quote remain consistent. No file or statement needed repair in this second reading.

I changed only this report by adding this independent second-reading record, preserving the worker's sections and the item proof. The final dry run is executed after this addition; delivery is attempted only after the server preflight reports `OK`.
