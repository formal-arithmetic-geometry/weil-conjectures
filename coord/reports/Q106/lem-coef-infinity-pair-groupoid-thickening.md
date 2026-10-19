# Worker report

## Files written

- dag/nodes/sec-six-functors/lem-coef-infinity-pair-groupoid-thickening.json — existing statement node, now split into six coordinate arguments; no full Mathlib match.
- citations.json — one verbatim statement quotation for the definition cited by each of the six steps.

No new nodes and no Mathlib leaves. The item's statement, source, original searches, creation record, unit, chapter and historical blueprint ancestry are retained. Sandbox-only write_split.py is the reproducible JSON-writing script; searches.jsonl is the search command's untouched log.

## Attachments

None. Searched /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact item id, pair-groupoid, indiscrete and codiscrete terminology. No matching project declaration was found. Ordinary homotopy equivalences of chain complexes do not state this quasicategorical result; the upstream master's sorry declarations are not attachments.

## WANTED

WANTED: an archived copy of Jacob Lurie, Higher Topos Theory, Proposition 5.3.1.16, opening proof paragraph, printed p.383 of the March 10, 2012 text, for lem-coef-infinity-pair-groupoid-thickening. Read online at https://www.math.ias.edu/~lurie/papers/highertopoi.pdf (PDF page index 400). The repository does not archive this document, so proof_origin.by is agent. No literature was downloaded or written.

## Audit findings and changes

The imported item already states the correct stronger, explicit version of the opening product construction: it specifies a section and an actual coherent natural equivalence over I. The source assumes filteredness later, to construct fresh-coordinate cones and a cofinal poset, but this isolated contraction needs only a specified element of X; it works for arbitrary I, including the empty quasicategory. No statement dispute or statement change is needed.

The proof was empty. It now supplies the missing all-horn argument for J_X, the coordinatewise inner-horn argument for K, the section, the exact homotopy formula, and both inverse triangles in Fun(K,K). In particular, a simplicial homotopy alone was not accepted as the proof of natural equivalence: the reverse edge and two triangles are displayed. There is no appeal to pointwise detection, contractibility implying equivalence, preservation of products by nerves, or a general nerve-of-groupoid theorem. The coordinate checks use only the definition node.

Read the chapter record sec-six-functors and unit record sk-prop-sf-biduality-general. The item is an auxiliary node with inherited unit binding, not the unit's key statement, so no unit record is changed. Read the current main-20261015 blueprint prop-coef-integral-exceptional-adjoint statement and proof (sk-thm-sf-package); its second paragraph is the integral mapping-complex adjunction. The item's historical ancestry through the cofinal-poset and spaces-calculus nodes remains exactly as recorded. This proof only fills the coordinate sublemma already assigned to that route. No SGA source is used.

## Search and duplicate review

The whole imported blueprint was searched using tools/blueprint_refs.py search with 'pair groupoid', 'indiscrete', 'contractible nerve' and 'product quasicategory'; all returned zero blueprint matches. The ancestor command identifies prop-coef-integral-exceptional-adjoint. Whole-DAG keyword search for pair.groupoid, indiscrete and codiscrete includes the item and its citer lem-coef-infinity-cofinal-kappa-poset, as well as other settings such as Segal completion and ordinary algebroids; none replaces this specified contraction of an arbitrary quasicategory. No new node is proposed, so there are no new/existing pairs requiring a Not duplicates section.

The original Q91 searches and results remain in the item. Q106 additionally ran leanfinder twice with distinct phrasings, loogle, leansearch, and two grep searches through the required msearch.py command. All returned successfully; queries and actual search-log summaries are appended verbatim to mathlib_searches. Read the hits and the sources of CategoryTheory.Codiscrete.equivFun (NerveCodiscrete.lean:33-35), CategoryTheory.Nerve.quasicategory (Quasicategory/Nerve.lean:32), CategoryTheory.Codiscrete.natIso (CodiscreteCategory.lean:107-109), and the walking-isomorphism construction (CoherentIso.lean:143 onward). They provide partial infrastructure, not the claimed arbitrary-quasicategory product equivalence with its exact coordinate witnesses. Consequently this is a split, not a Mathlib leaf.

## Unfinished work

None in the one-level split. The external HTT archive request remains recorded above. No Lean was written and no compiler, Lake or build command was run.

## Review by Q106

I read Scholze, Six-Functor Formalisms, Lecture II, Definition 2.2 and basic facts (1), (3), (4), printed pp.14-15, directly from literature/scholze-six-functor-formalisms.pdf. These give the internal-hom convention and inverse-triangle description of equivalence. I also read the opening paragraph of HTT Proposition 5.3.1.16 online: it takes the nerve of the category with one isomorphism between every pair of objects and uses its product to thicken a filtered category. The present item's formula is an agent expansion of that reduction, not a formula quoted from HTT. There are no new nodes with additional sources to verify.

For each of steps 1-6 I opened and read the statement of def-cbc-enhanced-diagrams-cones, the only cited node. Step 1 uses precisely its definition of an ordinary nerve as functors out of [n] with restriction as operators. Unique arrows make the vertex-list identification a direct construction, so no separate theorem about nerves is assumed. Finite powers and products stay in the chosen universe. Step 2 uses its definition of all Kan horns and explicitly extends them; n=1 is separate because that horn lacks one vertex. For n>=2 the retained faces contain every vertex and the uniqueness from step 1 makes the proposed tuple agree with every simplex of the horn, not merely its vertices. Thus outer horns are actually treated. Step 3 uses the same node's degreewise-product and inner-horn definitions, filling each factor, and checks the section and ps identity degreewise. It needs only I's stated inner-horn property.

Step 4 uses the exact definition Fun(K,K)_r=Hom(K times Delta^r,K) in that statement. Its word formula gives an explicit map, and for every beta it checks the equality on the first coordinate and the conditional kth coordinate, which proves all simplicial identities at once. It also computes every face by word restriction. Step 5 uses exactly the definition's inverse-edge/two-triangle criterion, not a pointwise-equivalence theorem: words 010 and 101 have the displayed edges and constant long edges, hence witness the two inverse equations for the same eta and theta. Step 6 uses the quoted quasi-inverse definition of functor equivalence. The first-coordinate identity proves the equality over I strictly; ps has the constant identity witness. All uses are quotations of the definition's actual statement, recorded in citations.json, rather than results appearing only in its proof.

These six steps are marked elementary because each is a direct coordinate construction or definition check with the argument written out; no general quasicategorical calculus theorem is invoked. In particular the inverse-triangle step computes the two witnesses rather than assuming that an arbitrary simplicial homotopy is invertible. No proof step exceeds 2,000 characters and none hides a comparison lemma. No clause is moved into a new node. The definition citation is a notion, so there is no off-unit theorem or tool-use declaration.

I checked the small cases X={x0}, where p and s identify with the identity and all word maps are constant in the interval direction, and I empty, where all products and transformations have unique empty-domain maps and no object of I is chosen. For a discrete I with two vertices the formula preserves the I coordinate, confirming there is no hidden filteredness assumption. For X with two distinct points, the n=1 outer-horn extension really requires choosing a missing coordinate; the word triangles still have constant long edges even when the original tuple is nonconstant. For a general higher simplex of I, every word map retains that very simplex, so none of the checks assumes I is an ordinary nerve.

Against delivery-errors B-E: the item introduces all objects and hypotheses already, and its statement is unchanged; every used notion is in its existing definition dependency or is constructed explicitly. There are no new unsplit nodes, hidden proof sketches, missing Mathlib leaf lines, or unrecorded searches. Each step's only cited statement says exactly what is taken, the proof dependency union is exactly that singleton definition, and that definition has no edge back to this item. No statement has been weakened and no source error was found. The correction from the empty proof is the full explicit inverse-triangle argument and the low-dimensional horn check described above.
