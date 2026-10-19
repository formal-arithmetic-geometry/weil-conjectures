# Repair report: lem-coef-dgcat-equivalence-cell-calculus

## Files written

- `dag/nodes/sec-six-functors/lem-coef-dgcat-equivalence-cell-calculus.json`: statement and Lean record unchanged; original step 4 replaced by three short steps; all other steps retained, with two numerical references adjusted. Status split.
- `dag/nodes/sec-six-functors/lem-coef-dgcat-cell-comparison-functors.json`: new statement-only, unsplit. Comparison dg functors for an arbitrary closed arrow after adjoining a contraction of its formal cone. Mathlib verdict: no match.
- `dag/nodes/sec-six-functors/lem-coef-dgcat-cone-word-normal-form.json`: new statement-only, unsplit. Generation of all old-object words by the four entries of the freely adjoined contraction. Mathlib verdict: no match.
- `citations.json`: complete verbatim statements for every cited node in each of the twelve numbered steps.
- `searches.jsonl`, `new-search-results.txt`: actual search records and printed results. No Mathlib leaves.

## Attachments

None. Read-only searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item tag, coherent homotopy equivalence, dg interval, Kontsevich, cone contraction and the two extracted notions found no complete project declaration. Upstream master was searched as reference, not proof evidence. The stage-2 record in the item is preserved; its existence is not a finished proof.

## WANTED

WANTED: Gonçalo Tabuada, *Théorie homotopique des DG-catégories*, arXiv:0710.4303, Chapter 1, Proposition 1.7, Lemma 1.10 and Proposition 1.13, printed pp. 27–32, for the item and both new nodes. I read the PDF online at https://arxiv.org/pdf/0710.4303; there is no local archive. No literature download or change was made. There is no corresponding Stacks tag and no SGA source is used. The proof retains its agent origin because its explicit calculations are not all supplied in the source.

## Return repaired

The human's single numbered issue was that original step 4 (2023 characters) was non-elementary and concealed lemmas. The copied sandbox node was exactly equal, key by key, to the current shared node when inspected. There was no report or search log in this sandbox and no active delivery process. I retained that proof, the complete statement, source fields, earlier searches, all Lean metadata, and all other steps. The previous NW report is retained below as historical context, not as my signature.

Original step 4 contained (1) construction of both comparison functors via cone coordinates and extension to a free contraction, and (2) expansion of arbitrary words through the cone, needed to conclude their second composite is the identity. These are now two separate unsplit nodes. They are stated for any small dg category and any closed arrow, and neither asserts quasi-isomorphisms, essential surjectivity or prescribed lifting. In the item, new step 4 cites the construction, step 5 verifies the first composite on free generators, and step 6 invokes the word-generation lemma for the other composite. Their lengths are 707, 336 and 410 characters. All twelve steps are shorter than 2000 characters; the other nine arguments and the source route remain intact. This is not an unchanged re-push.

## Not duplicates

Whole-DAG searches used cone/contraction, matrix entries, old-object words, inverse maps, the new ids, and source arXiv:0710.4303/Lemma 1.10. Whole-blueprint `blueprint_refs.py search` searches for `cone contraction`, `matrix entries`, `inverse maps old-object words`, `strict identification morphism complexes`, `adjoining contraction`, and `free dg category` found no equivalent imported statement. The nearest blueprint ancestor remains prop-coef-integral-exceptional-adjoint, and the via list prepends this item without changing its inherited unit. The main-20261015 ancestor proof's finite mapping-complex adjunction paragraph and the chapter/unit records were read.

The delivery tag matcher can mistake the arXiv prefix 0710 for a Stacks tag. I opened the statements of all five existing source matches; the following lines distinguish them from each new node.

lem-coef-dgcat-cell-comparison-functors vs lem-coef-dgcat-equivalence-cell-calculus: the new lemma constructs comparison functors for an arbitrary already-existing closed arrow, without proving the composites are identities, a quasi-isomorphism, or a lift; it does not restate any of (a), (b), (c).

lem-coef-dgcat-cell-comparison-functors vs lem-coef-dgcat-formal-cone-enlargement: the latter supplies the unextended labelled cones and entrywise functor extension, but no freely adjoined contraction, comparison from a coherent-inverse presentation or return functor.

lem-coef-dgcat-cell-comparison-functors vs lem-coef-dgcat-free-cell-calculus: the latter supplies general free-arrow constructions and word filtrations, but no functors comparing contraction-of-cone and coherent-inverse presentations.

lem-coef-dgcat-cell-comparison-functors vs lem-weil-pbc-extension-by-zero-stalks: the latter concerns stalks of sheaf extension by zero, not dg-category presentations; the apparent tag overlap is the arXiv prefix.

lem-coef-dgcat-cell-comparison-functors vs lem-amb-etale-sum-stalks: the latter concerns étale sheaf direct-sum stalks, not freely contracting cones; the apparent tag overlap is the arXiv prefix.

lem-coef-dgcat-cone-word-normal-form vs lem-coef-dgcat-equivalence-cell-calculus: the new lemma is graded word generation for any already-existing closed arrow, without asserting quasi-isomorphisms or lifting; the item must still identify its pushout, construct inverse functors, and run the contraction filtration.

lem-coef-dgcat-cone-word-normal-form vs lem-coef-dgcat-formal-cone-enlargement: the latter gives the graded coordinate identities before adjoining h; the new lemma gives generation after freely adjoining h and deleting the cone label, for arbitrary-length words.

lem-coef-dgcat-cone-word-normal-form vs lem-coef-dgcat-free-cell-calculus: the latter gives words with coefficients incident to Z; it does not eliminate Z or prove generation by the four matrix entries through graded shifted coordinates.

lem-coef-dgcat-cone-word-normal-form vs lem-weil-pbc-extension-by-zero-stalks: sheaf stalks are unrelated to graded word generation; the apparent source-tag overlap is the arXiv prefix.

lem-coef-dgcat-cone-word-normal-form vs lem-amb-etale-sum-stalks: étale sheaf stalks are unrelated to graded word generation; the apparent source-tag overlap is the arXiv prefix.

The two new nodes differ: the first asserts existence of actual dg comparison functors, with their differentials and values; the second is a generation/equality criterion for arbitrary graded linear functors and does not construct either comparison. Neither depends on this item or the model theorem above it. No off-unit tool is introduced.

## Unfinished work

Both new nodes intentionally remain statement-only, with empty proof/proof_deps and null proof_origin. Their eventual splits should construct F from the four entries of h, construct the extension G-tilde by sending h to the displayed contraction, and restrict to representables. For the word node, take a free-arrow word and insert the cone's graded identity at every incidence with Z; coefficients then reduce to Hom modules of A and h to its four entries. Induction on word length and finite distributivity gives generation; functor equality follows termwise. These are the exact obligations extracted by the human return, not unfinished steps hidden in the repaired item. No stage-2 or stage-3 work is performed.

## Review by Q94

I read Tabuada's online PDF, Chapter 1, §1.2 (module maps and Yoneda), Proposition 1.7 on printed p. 27 (cone/contraction coordinates), Lemma 1.10 on pp. 29–30 (L_0 through L_3, both comparison functors and the word filtration), and the end of Lemma 1.12 and Proposition 1.13 on pp. 31–32 (lifting a contraction). The two new statements make precise exactly the functor construction and inverse verification in the middle of Lemma 1.10. Their general closed-arrow formulation requires no triangularity of A: triangularity is used only later by the item to make Hom(X,Z) contractible. Arbitrary commutative R, smallness, closed degree-zero u, h of degree -1 with dh=1, and the four graded coordinate degrees are explicitly included. The source's informal matrix is converted to the item's cochain convention with upper-row negatives. The item statement and Lean record were compared programmatically and are unchanged.

For step 1 I read the free-cell statement's signed Leibniz rule and free presentation: choosing v,a,b uses precisely the definition of H^0-invertibility, and dz=0, d(b+zv)=uv-1, d(za)=ua-(b+zv)u follow with the sign for |z|=-1. Step 2 cites the cone node's actual graded matrices and commutator differential; the four entries are -db+uv, -dw+ua-bu, -dv, vu-da. It does not take full faithfulness as a substitute for the Yoneda formula.

Step 3 uses the free-cell word description and the cone node's original-Hom identification. With H new and s pointing only into H, there are no words from H to an old object, and Hom(X,H)=s Hom(X,c); hence s_* is an actual isomorphism, without flatness. New step 4 uses the comparison statement's explicit F,G and generator values, and the free-cell presentation identifies B with E: L_0 already contains exactly C,H,s, so adjoining v,a,b,w is precisely adjoining g,r_0,r_1,t of the original pushout. The prescribed differential of w is closed, since d(ua-bu)=u(vu-1)-(uv-1)u=0. New step 5 checks GF on every original coefficient and the four free generators and extends along words. New step 6 uses the word node's explicit equality criterion, not its future proof: FG fixes A and its four specified matrix entries, so it is the identity on T_0. This proves a strict morphism-complex identification, needed by the later filtration.

Step 7 uses exactly the free-cell node's arbitrary-degree filtration with s=t=Z, |h|=-1, dh=1. Each tensor factor and the length-zero term match that statement. Step 8 cites the cone node's Hom(h_X,C_s) formula, computes k(a,b)=(0,a), and verifies dk+kd=1; on T tensor Cone(1), the sign (-1)^|q| cancels the two dq terms. No preservation of an acyclic complex by tensor is assumed. Step 9 explicitly reduces a cycle's finite top length and proves cohomology surjectivity and injectivity; it needs no convergence theorem. Step 10 uses the free-cell object's bookkeeping and displayed boundaries gf-1 and fg-1 to exhibit inverse H^0 classes. Z is temporary and omitted, whereas H remains a distinct new label.

Step 11 uses the cone node's four shifted entry modules and functoriality: original Hom-surjectivity gives cone endomorphism-surjectivity in each degree independently, including when x=x'. Step 1 supplies h_0 for the fixed u; the bottom data supply its specific h_D. Step 12 computes e=dk-1, de=0, P(e)=0 and h=k-h_0e, so dh=1 and P(h)=h_D; the cone dictionary and free presentation give the specified filler. No object-surjectivity or quasi-isomorphism hypothesis on p is inserted. Every citation is copied verbatim from the actual node's statement in citations.json. The proof-dependency list is exactly the union of uses.

I checked both new nodes against B–E. They introduce all categories, labels, homogeneous arrows, coordinate maps and hypotheses, cite both definition/construction interfaces, have no proof sketches in their statements, and have empty proofs. Their source is an actual theorem place, with no invented Stacks tag. I read all printed search hits and the relevant source contexts in Mathlib HomotopyCofiber.lean:13–36, HomotopyCategory/Pretriangulated.lean:90–95 and Limits/Shapes/Biproducts.lean:980–1021. Ordinary complex cones and ordinary degree-zero biproduct matrix reconstruction do not supply the free dg-category comparison or old-object word generation in one specialization. Both nodes have two substantive semantic phrasings plus successful Loogle, grep and LeanSearch queries in their recorded searches; the log is the command's own output. Some additional exploratory Loogle requests returned unknown identifiers; they are not used as the evidence for a Mathlib match or absence. No unavailable service is described as a successful absence search.

Small cases checked for the comparison node: u=1, u=0, x=y, zero coefficient ring, characteristic two, and nonflat/torsion Hom modules. A zero u may force representables contractible in B and T but does not obstruct either free construction. The labels remain distinct even over the zero ring; the construction adds Z as a separate labelled cone, not an assumed shift object. For the word node I checked length zero (an A coefficient), length one (four entries after two coordinate decompositions), and length two (the middle cone coefficient decomposes into A coefficients); the same finite expansion works for arbitrary length. The graded coordinate maps need not be closed and no step assumes they are. Empty A has no selected arrow, so both quantified statements have no such instance. These checks found no statement defect. The prior source object-count slip is retained in the historical report below; it requires no change to the already-correct item statement.

The return is addressed by genuine lemma extraction and short cited steps, not by changing elementary flags, reducing prose alone, or moving all of (b) into a child. Other arguments, the unit route and Lean record are preserved. No Lean was written or compiled, no repository git command was run, and no source/library/tool file was modified.

## Historical report retained from NW

The following is the earlier report on the original split, copied from the read-only repository for provenance. Its ten-step numbering predates this repair; the current proof and Q94 review above govern this delivery.

# Stage-1 report: lem-coef-dgcat-equivalence-cell-calculus

## Files written

- `dag/nodes/sec-six-functors/lem-coef-dgcat-equivalence-cell-calculus.json`: original statement unchanged; split in ten steps. Mathlib searches: no exact match.
- `dag/nodes/sec-six-functors/lem-coef-dgcat-formal-cone-enlargement.json`: one new statement-only node, unsplit. Strict dg Yoneda and small labelled cone enlargement with all graded Hom matrices and functorial extension. Mathlib verdict: no match, no Mathlib leaves.
- `citations.json`: one entry for every citation in every numbered proof step, quoting the complete statement of the cited node verbatim.
- `searches.jsonl`: actual command-maintained search records; all services returned successful responses for the recorded searches.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the blueprint id and dg-category, Kontsevich, quasi-equivalence, formal cone and homotopy-equivalence notions, and searched the upstream declaration-name map. No project declaration gives the interval presentation, its pushout calculation, or the prescribed lifting assertion. The ordinary homotopy-category results found do not state this item. Master is reference material, not attachment evidence.

## WANTED

WANTED: Gonçalo Tabuada, *Théorie homotopique des DG-catégories*, arXiv:0710.4303, Chapter 1, Proposition 1.7, Lemma 1.10 and Proposition 1.13, printed pp. 27–32, for lem-coef-dgcat-equivalence-cell-calculus and lem-coef-dgcat-formal-cone-enlargement. Read the PDF online at https://arxiv.org/pdf/0710.4303; no local archive was found. In accordance with the brief, I downloaded nothing and changed no literature files; the item's proof is marked `by: agent`. No Stacks tag supplies these dg-category constructions, so no tag is invented. No SGA source is used.

## Corrections and scope

The second dry run flagged genuine matrix row separators immediately followed by a letter or TeX command as doubled command backslashes. I inserted whitespace after every matrix row separator, preserving the mathematics and keeping every TeX command singly escaped, and regenerated the verbatim citation quotes.

The item was unsplit and had no project Lean declaration. Its statement, including arbitrary commutative R and the specified closed arrow u in (c), is correct and unchanged. The proof now supplies the inverse-homotopy correction in (a), the strict pushout identification and exhaustive filtration in (b), and the simultaneous correction of a prescribed contraction in (c). No model structure or derived Yoneda theorem is assumed. In particular, this does not use the parent dg-category model theorem, which depends on this item.

The current main-20261015 proof of prop-coef-integral-exceptional-adjoint was read, along with the chapter and assigned unit records. This item is an auxiliary construction below that ancestor's second paragraph, the finite mapping-complex adjunction. The historical ancestry and maintainer-owned unit are retained. Nothing changes either upper blueprint level.

## Source error

The closing sentence of the interval part of Lemma 1.10 (printed p. 30) describes the inclusion as the identity on objects, although its construction has added H. Literally that is false: take the one-object dg category with endomorphisms R, and the displayed pushout has two object labels. The needed assertion is essential surjectivity on H^0, witnessed by s and its homotopy inverse. Step 8 explicitly proves that assertion and distinguishes the temporary cone object Z from the sole new object H of the pushout. The item's statement already gets this right; no statement dispute or weakening was needed.

## Not duplicates

The first dry run mistook the arXiv prefix 0710 in the source URL for Stacks Tag 0710. I opened all three flagged nodes and checked their statements, without changing the tool or hiding the source URL. The following comparisons satisfy that check and report the false-positive reason.

lem-coef-dgcat-formal-cone-enlargement vs lem-coef-dgcat-free-cell-calculus: the existing lemma gives dg-category presentations, colimits and free-arrow word filtrations; it does not give strict dg-module Yoneda, full cone enlargements, or the graded cone Hom matrices. Both cite the same Tabuada thesis; the apparent 0710 tag is its arXiv prefix.

lem-coef-dgcat-formal-cone-enlargement vs lem-weil-pbc-extension-by-zero-stalks: the existing statement computes geometric stalks of extension by zero for an open immersion. Its genuine Stacks Tag 0710 has no relation to the new lemma's strict dg modules and cone matrices; the new source's 0710 is part of arXiv:0710.4303.

lem-coef-dgcat-formal-cone-enlargement vs lem-amb-etale-sum-stalks: the existing statement computes the geometric stalk of etale direct-sum extension as a sum over points of the fibre. It is unrelated to strict dg Yoneda and formal cone enlargement; the apparent source-tag overlap is again the arXiv prefix.

lem-coef-dgcat-formal-cone-enlargement vs lem-coef-derived-enriched-yoneda: the existing node concerns derived/enhanced Yoneda over Z, quasi-equivalent models and coherent factorization; the new node concerns the strict complexes of all graded module maps over arbitrary R and a small explicit labelled cone enlargement with entrywise dg functor extension. Derived full faithfulness does not identify these strict complexes or give their cone matrices.

lem-coef-dgcat-formal-cone-enlargement vs lem-coef-dg-quotient-hom-cone: the existing node is a derived tensor/cofiber formula for dg quotients over Z, with derived localization universality. The new node supplies an unlocalized, fully faithful dg embedding with formal cone matrices over arbitrary R, before any contracting homotopy is adjoined. Neither statement is a specialization of the other.

lem-coef-dgcat-formal-cone-enlargement vs lem-cbc-enhanced-functor-cone-calculus: the existing node concerns cones of diagrams in quasicategories, their mapping spaces and terminal objects; the new node is about strict algebraic mapping cones of closed dg arrows and the full complexes of homogeneous maps.

Whole-DAG searches for formal cone, formal-cone, cone enlargement, strict dg Yoneda, finite twisted complexes, pretriangulated and matrix dg notions found no node stating the new construction. Whole-blueprint searches `formal cone`, `dg Yoneda`, `dg category`, `Yoneda`, and `twisted complex` also found no equivalent imported statement. `blueprint.same_as` is therefore empty. There is no Stacks-tag collision. The new node is not a clause of the item: it asserts no homotopy-inverse realization, no invariance after adjoining a contraction, and no lifting of inverse data. Those arguments stay in the item's steps.

## Unfinished work

The only new unsplit obligation is the generic strict dg Yoneda/cone enlargement theorem. Its construction is explicit in its statement: use the stated right modules and graded maps, evaluate at 1_x, and take the small category on the labelled representables and their displayed cones. For its eventual split, evaluation and the inverse m ↦ (a ↦ ma) are mutually inverse by the module action, commute with differentials, and preserve composition; graded biproduct decompositions give all matrix entries and the differential; applying a dg functor to those entries preserves their identities. This proof sketch is here, not in the unsplit node's statement. No other mathematical gap is left in the item. The second reader is to repair and deliver; this worker only runs the required dry run.

## Review by NW

I read Tabuada's actual PDF, not just the inherited source field: Proposition 1.7 on printed p. 27 for cone matrices, the entire interval construction and filtration in Lemma 1.10 on pp. 29–30, and the cone endomorphism lifting in Proposition 1.13 on p. 32 with its preceding argument in Lemma 1.12 on p. 31. The new node isolates the strict representable-module and cone construction used there; its statement gives the precise modules, grading, map differential, full embedding, cone Hom complexes and entrywise functor extension. The source does not prove a model theorem being assumed circularly here.

For step 1 I opened lem-coef-dgcat-free-cell-calculus and checked that it really defines the signed cochain convention and free adjoining construction used by the item. The inverse representative v and a,b exist by the definition of H^0 invertibility; they are not taken from an unquoted theorem. I checked dz=0, db'=uv−1 and d(za)=ua−b'u with b'=b+zv. This is an explicit algebraic step, not a new lemma renaming clause (a).

Step 2 uses the new cone node's actual Hom matrices and its differential, not derived full faithfulness. I multiplied out the four entries of D_u H+H D_u with H=[[-b,-w],[v,a]]. They are −db+uv, −dw+ua−bu, −dv and vu−da. This corrects the shift-sign ambiguity of informally reading the source's matrix without its convention; the displayed item equations are preserved.

Step 3 uses exactly the existing free-cell node's word description to compute the old Homs, Homs into H, and vanishing Homs out of H. Its additional-object operation is a coproduct with the one-object category before adding s. It then uses exactly the new node's small full cone enlargement. In particular s_* is an actual isomorphism, not merely a quasi-isomorphism requiring a flatness assumption. Step 4 uses these same two cited statements: the former permits adjoining h with dh=1, and the latter gives cone matrices, graded inclusions/projections and the entrywise extension needed for the inverse map. I wrote both maps and the matrix expansion proving they are inverse, instead of hiding that assertion under “identifies”. The identity on the cone is the sum of its two graded corner projections, so expansion and recombination work for arbitrary nonclosed words as well.

Step 5 cites the arbitrary-degree, prescribed-differential free-arrow filtration in the existing free-cell statement. Its tensor factors and degree of Rh match the statement exactly. Step 6 cites the new node's cone Hom formula and computes k(a,b)=(0,a), dk+kd=1. I checked the tensor sign (−1)^|q|: terms differentiating q cancel, so all the positive quotients are contractible without projectivity or flatness. Step 7 uses no external assertion: its finite-length induction explicitly reduces cycles by a lifted boundary in each contractible quotient, then proves surjectivity and injectivity on cohomology of the length-zero inclusion. There is no unbounded spectral-sequence convergence claim. Step 8 uses the free construction's unchanged objects under arrow attachments and the written equations for f,g to show essential surjectivity; it repairs the source's object-count slip.

Step 9 uses precisely the new node's finite matrix Hom modules and dg-functor extension. The hypothesis that p is surjective on every original Hom complex gives a surjection on each of the four shifted matrix entries, hence on the cone endomorphism algebra in every degree. The specified u is closed and H^0-invertible, so the already-proved (a) supplies h_0; the given bottom functor supplies h_D. Step 10 checks the correction e=dk−1 and h=k−h_0e: de=0, P(e)=0, dh=1, P(h)=h_D. This proves simultaneous lifting with the given u and the given images of all four remaining generators; it does not silently lift a different representative of f. The same cone and free-presentation statements cited there give the entry dictionary and the final functor. The proof does not require p to be a quasi-equivalence or surjective on objects.

I checked B–E point by point. The one new node is statement-only, introduces R, A and every module and cone notion, and has no proof or proof dependencies. Its TeX uses single mathematical backslashes (double only for genuine matrix row separators). All recorded Mathlib queries were actually run using msearch.py, with second semantic phrasings. I read the candidates in Mat.lean:20–105, HomotopyCategory/Pretriangulated.lean:25–70, Homotopy.lean:120–150 and the shape-extension context in Embedding/Extend.lean; they do not give dg Yoneda or a cone enlargement of arbitrary dg categories in one line. The focused dg vocabulary grep returned zero hits. The new node's inherited blueprint via list prepends the item, and its place names the ancestor's finite mapping-complex calculation. All proof citations are backed by verbatim statement quotes in citations.json, all uses equal the proof-dependency union, and no off-unit theorem is used.

For small cases I checked the zero coefficient ring, the empty dg category (the new cone category is empty and clauses with a selected object are vacuous), and a discrete R-linear category with an actual isomorphism u (take v=u⁻¹ and a=b=w=0). For u=1 the cone differential and k above give the identity explicitly. Over a ring with torsion or nonflat Hom modules the tensor contraction still works because it uses a contracting homotopy, not preservation of quasi-isomorphisms by tensor. In (c), even a surjective p with nonacyclic original kernel works: multiplication by h_0 contracts the relevant cone-endomorphism kernel, as the displayed correction shows. These checks found no missing hypotheses or statement defect.

## Second reading by NW

I independently read delivery-errors B–E, GOAL.md and coord/dag-sync.md; opened the item, both cited node statements and every citation quote; and read Tabuada, Chapter 1, Definition 1.4 and its preceding paragraph (printed p. 26), the interval definition and Proposition 1.7 (p. 27), Lemma 1.10 (pp. 29–30), and the contraction lifting in Lemma 1.12 and Proposition 1.13 (pp. 31–32). There is no Stacks tag for these constructions. I also read the current main-20261015 ancestor proof, the unit and chapter records: this is auxiliary algebra for the finite mapping-complex adjunction, with neither upper-level route nor maintainer metadata changed. The item's statement is unchanged and agrees with the source's intended realization, pushout and lifting assertions, including the specified arrow in (c); no statement dispute was found.

- Step 1: checked against the free-cell node's signed Leibniz rule and free presentation; checked each generator's squared differential and the explicit identities for z, b' and w. Valid over arbitrary R, including characteristic 2; no uncited cone-contractibility theorem is used.
- Step 2: checked against the new node's actual graded Hom matrices and differential; multiplication gives exactly the four displayed entries, including -dv. Valid; the upper-row minus signs correct the source's literal display (see below).
- Step 3: checked against the free-cell node's word formula and colimits, and the new node's strict Hom identification. A word into H contains s exactly once and there is no word from H to an old object. Valid; s_* is an actual complex isomorphism, so no flatness hypothesis is missing.
- Step 4: checked the two inverse functors against both cited statements and Tabuada's construction of L_0 through L_3. Clarified that the shifted cone coordinates are homogeneous arrows to and from c itself, with degrees -1 and 1; wrote all four generator formulas and the exact expansion of h. Valid: this uses graded arrows already in L_1 and introduces no unlisted shift object or relation.
- Step 5: checked every tensor factor against the existing free-cell node with s=t=Z, n=-1, d(h)=1_Z; for m=1 the middle tensor power is R and the formula is still correct. Valid; differentiating h lowers the exhaustive word filtration.
- Step 6: checked against the new node's cone-Hom statement and step 3; on (a,b), d k+k d=(a,b). With the sign (-1)^|q| the two dq terms in the tensor calculation cancel. Valid for torsion and nonflat modules, because the last factor is contractible rather than just acyclic.
- Step 7: checked directly from steps 5–6: the top filtration component of a quotient cycle bounds, degreewise lifts reduce length, and the same finite reduction proves both cohomology surjectivity and injectivity. Valid and elementary; no spectral sequence or convergence theorem is hidden.
- Step 8: checked against the free-cell node's unchanged objects under arrow attachment and the two written boundary equations. Valid: H is the only new pushout label, [f] and [g] are inverse, and Z has been omitted. The source's identity-on-objects sentence is correctly repaired already.
- Step 9: checked against the new node's four shifted Hom modules and entrywise dg-functor extension. Surjectivity on the original complexes gives every matrix entry, even when x=x'; one can choose entries independently. The degree-minus-one entries have original degrees -1,-2,0,-1. Valid; (a) supplies h_0 and the bottom functor supplies the prescribed h_D without requiring p to be a quasi-equivalence or surjective on objects.
- Step 10: checked directly using both cited statements: d e=0, P(e)=0, d(h_0e)=e and P(k-h_0e)=h_D. Valid and elementary; the four lifted entries have exactly the bottom values and the fixed u, so both functor triangles commute strictly.
- New node lem-coef-dgcat-formal-cone-enlargement: compared all hypotheses and conclusions with Definition 1.4, Proposition 1.7 and Lemma 1.10 and checked the Yoneda inverse a↦ma, its differential and composition, shift action, entry degrees and functoriality. Valid, statement-only, self-contained and B1–B7 compliant after making dgMod notation, the unchanged shift action and the graded coordinate maps explicit. This generic strict construction is neither a clause of the item nor a two-line specialization of a cited theorem: the Yoneda complex identification and the simultaneous cone/matrix/functor construction remain its distinct unsplit obligation.

Independently searched the whole DAG for cone-enlargement, strict dg Yoneda, pretriangulated and dg-module vocabulary, and opened the likely existing candidates lem-coef-derived-enriched-yoneda, lem-coef-dg-quotient-hom-cone, lem-coef-dg-module-projective-resolution, lem-coef-dg-module-base-change, lem-coef-dg-module-diagram-classification and lem-coef-dg-semi-free-homotopically-projective. None states the strict cone enlargement: the derived statements retain localization/model hypotheses and base change gives representables but not all cone matrix complexes. They would also create an inappropriate dependency back through the model theorem. The current blueprint searches for `dg category`, `Yoneda`, `twisted complex` and `formal cone` gave no equivalent node; the three Yoneda hits concern schemes and exceptional adjoints. The ancestor command confirms prop-coef-integral-exceptional-adjoint. Independent read-only searches in slopmaster2 and the upstream name map found no attachment.

Ran my own msearch queries using broader enriched-category vocabulary: LeanFinder `A category enriched in cochain complexes embeds in representable dg modules and admits a functorial category of mapping cones` (8 hits), Loogle `"EnrichedCategory", "yoneda"` (0 hits), and grep `DGModule|DgModule|dgYoneda|Enriched.*[Cc]one|[Cc]one.*Enriched` (5 hits). Read Mathlib/Algebra/Homology/DerivedCategory/Basic.lean:13–25,59–96 and Mathlib/CategoryTheory/Enriched/FunctorCategory.lean:333–342. The first is ordinary derived localization and the second an ordinary limit cone for enriched natural transformations; neither gives the new lemma. Appended these actual logged results to its search record. No Mathlib leaf was found.

Small cases: the empty A gives an empty labelled cone category; the assertions requiring a chosen object are then vacuous. Over the zero ring labelled objects remain distinct even though every Hom module is zero. For an actual isomorphism over a field, v=u⁻¹ and a=b=w=0 work. For u=1 the cone contraction k(a,b)=(0,a) works in every degree, including degrees 0 and 1. For u=0 between zero or contractible objects the same matrix dictionary applies. Thus no nonzero-ring, nonempty-category, flatness, boundedness or unequal-object hypothesis has been silently assumed.

Additional source-display error: Proposition 1.7 prints the contraction matrix with upper row (r_2,r_12), while its differential and the interval relations require (-r_2,-r_12) in the stated cochain convention. For an explicit counterexample to the unsigned display, work in dg complexes over Q, take x=0 and y=(Q→Q) in degrees 0 and 1 with identity differential, and let k:y→y have degree -1 and d k=1_y. Set f=g=0, r_0=t=0 and r_1=-k. These satisfy every interval relation, but the printed unsigned cone endomorphism has differential -1_y rather than 1_y. Step 2 already has the correct matrix; I recorded this as a source-display error, not a change to the correct item statement.

Changes made and reasons:

- Defined the previously implicit dgMod notation and shift action in the new node, and spelled out the degrees and biproduct identities of its graded coordinate arrows, so later readers need no convention from the proof.
- Expanded step 4's four entry formulas and h reconstruction, making explicit why the strict pushout calculation does not need a shift object in L_1.
- Corrected the item's source location from section 1.3.1 to section 1.3 for the definition of K, and added Definition 1.4 on printed p. 26 to the new node's source.
- Added the independent Mathlib search results and the explicit source-sign counterexample; regenerated all 12 citation quotes verbatim from the repaired statements. Kept all first-reader sections and all otherwise correct proof steps.

Validation: required `deliver.py NW lem-coef-dgcat-equivalence-cell-calculus --no-push` completed with `OK (not pushed)` at c8f2e24846; preflight passed. The final delivery uses the same node and citation contents, with this validation line added to the report.
