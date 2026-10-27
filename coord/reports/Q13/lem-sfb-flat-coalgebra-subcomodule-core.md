# Stage-1 delivery: lem-sfb-flat-coalgebra-subcomodule-core

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-flat-coalgebra-subcomodule-core.json: statement, split; no Mathlib match for the item. The statement and statement dependencies are unchanged. Five proof steps, 2383 characters in total; no step exceeds 2000 characters.
- citations.json: seven entries, one per step/dependency occurrence, checked as verbatim substrings of the cited statements.
- searches.jsonl: five searches actually run for this item through msearch.py, with the returned summaries retained in mathlib_searches. The earlier creator's searches remain untouched.
- report.md: this report. No new nodes and no new Mathlib leaves.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and the concepts flat coalgebra, subcomodule, coaction. The only subcomodule hit in GeneralLinear/Representation.lean concerns simple representations over an algebraically closed characteristic-zero field and does not state this arbitrary-ring construction. No attachment is claimed.

## WANTED

WANTED: J. S. Milne, Basic Theory of Affine Group Schemes (2012), VIII Aside 4.7, printed p.117, https://www.jmilne.org/math/CourseNotes/AGS.pdf, for lem-sfb-flat-coalgebra-subcomodule-core. The referenced local literature/milne-basic-affine-group-schemes.pdf is absent. I read the author's PDF online (PDF page index 116) without downloading into the repository. The proof is marked agent-written: it supplies the stability calculation omitted in the aside. The available local supporting source is literature/stacks-project/algebra.tex.

## Problems found and corrected

The input was unsplit with no proof. Its arbitrary-ring statement is correct; no STATEMENT-DISPUTED correction is needed. The Noetherian assumption belongs to the subsequent finite-generation argument, which is outside this item. I replaced no statement or route, and made no claim about finite generation or torsion-freeness.

The inherited blueprint ancestor lookup returns None: the creation chain terminates at an upstream Lean declaration name rather than a DAG node. Its existing detailed from.place and via chain already identify det-thm-sf-ctf-stability-direct-images proof (3) and the DVR-lattice prerequisite. These inherited fields are retained, with same_as confirmed empty after blueprint search. I read the current literature/blueprint/latest unit text, rather than its historical snapshot, as well as the unit and chapter records. No unit or chapter is edited.

## Not duplicates

No new nodes. Both required tensor facts already exist as Mathlib leaves: lem-weil-pbc-tensor-right-exact and lem-weil-pbc-flat-tensor-exact; the tensor definition is def-weil-pbc-module-tensor-product. I read all three complete statements and their Mathlib source excerpts. Searching DAG names and statements for tensor, exactness, kernels, and flatness found these reusable results; blueprint_refs searches for tensor exact and subcomodule returned no matching imported nodes. No clause of the item has been repackaged as a new lemma.

## Review by Q13

I read Milne VIII Aside 4.7 at printed p.117 and the preceding subcomodule convention on printed p.116. This gives the same inverse-image construction and maximality claimed here, but leaves the core-stability argument unstated. My proof writes that argument in terms of the quotient map and coassociativity. For its algebraic tools I read Stacks algebra.tex: lemma-tensor-product-exact (Tag 00DF), definition-flat (Tag 00HB), and lemma-flat (Tag 00HD), checking the tag/label table. The tensor definition and three local Mathlib modules were read to verify the interfaces recorded by the existing leaves. No SGA source is used, and there are no new nodes requiring further sources.

Step 1 uses def-weil-pbc-module-tensor-product for pure-tensor generation and linear tensor maps. An inverse image of an image of linear maps is a submodule; counitality applied to a finite tensor sum puts every element of the core back in W. No basis, finite-generation or Noetherian assumption appears.

Step 2 uses the statement of lem-weil-pbc-tensor-right-exact, specifically the kernel/image equality after tensoring a right exact sequence. Here the quotient map M to M/W is surjective and has kernel W, so all hypotheses hold. This identifies the core with ker((q tensor 1)rho); it is not a citation of the proof of that node.

Step 3 uses tensor functoriality from the tensor-definition statement and the kernel-sequence assertion of lem-weil-pbc-flat-tensor-exact. Its exact sequence begins 0 to K to M to (M/W) tensor C, with no surjectivity required at its last term. The flat module is C, exactly the input hypothesis. Coassociativity gives the displayed vanishing of (f tensor 1)rho on K. The cited flat-exactness statement supplies both the image/kernel identification and injectivity; unique preimages then give a linear map by checking sums and scalar multiples. Thus the proof does not infer preservation of a kernel merely from an uncited definition of flatness.

Step 4 uses the same two statements only for tensor functoriality and injections. Tensoring the injection j first once and then again with the flat module C makes j tensor 1 tensor 1 injective. The equations for the new coaction become the two equations for rho after postcomposition with these stated injections. The cancellations are elementary. In particular I do not assume that K, W or M is flat, and do not invoke flatness of C tensor C without proof.

Step 5 uses the tensor-definition statement's compatibility with composition to compare the images for U and W. The stipulated inclusion U in W gives the actual factorization of inclusions, so stability of U implies membership in the defined core. This proves precisely the maximality clause, independently of any finite-generation assertion. The citations file quotes the actual tensor functoriality sentence for steps 3--5; every quoted assertion is in the cited node statement.

For edge cases I checked W=0: counitality makes rho injective, so the core is 0; W=M: the core is all M; M=0 and the zero ring: all constructions are zero and the uniqueness argument still holds. For the unit coalgebra C=R with its canonical coaction, every W is its own core, including torsion modules and non-Noetherian base rings. As a nontrivial proper-core example over any nonzero ring, the regular comodule C=R e_0 direct-sum R e_1 with group-like basis and W=R(e_0+e_1) has zero core, as the quotient/coaction formula predicts. The proof uses no field coefficient extraction and works without a basis.

Against delivery-errors B--E: every object is bound by the unchanged complete statement; no new statement-only node or duplicate is needed; sources and actual searches are recorded; all non-elementary steps cite the existing statements that give the needed result; the three dependencies do not depend on the item, so no cycle is introduced. The assembly is a proof of the item rather than an application of a newly renamed clause. All five steps are below 2000 characters. No Lean was written and no compiler, Lake or build command was run.

## Unfinished work

None in this stage-1 split. The independent maintainer review remains part of the normal delivery process.
