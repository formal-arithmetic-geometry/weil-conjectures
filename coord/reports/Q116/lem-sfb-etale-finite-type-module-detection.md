# Stage-1 report: lem-sfb-etale-finite-type-module-detection

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-etale-finite-type-module-detection.json: item, statement, split into six steps; Mathlib has finite-type definitions and general module pullbacks, but no matching change-of-topology equivalence.
- citations.json: one verbatim statement quotation per cited node and proof step.
- report.md: this report. No new nodes; zero Mathlib leaves.

The sandbox was empty apart from dispatcher markers. I copied the current item, retained its statement, source, ancestry and Q125 search records, and appended only searches logged by msearch.py in this sandbox. No repository or launcher file was written. No compiler, Lake, build, git command or agent was run.

## Attachments

None. Project source searches by the exact blueprint tag, 08HD, finite-type/Zariski combinations and finite-type/etale concepts found no declaration giving the equivalence for arbitrary structure-module sheaves. IsFiniteTypeEtaleModuleSheaf.lean defines finite type for constant coefficient modules, not the structure-module comparison here. The generating-section and finite-presentation Mathlib hits likewise do not prove the equivalence.

## WANTED

None. All source material used is present locally.

## Corrections and source observations

The item statement is unchanged and agrees exactly with Stacks spaces-perfect.tex, Tag 08HD (lemma-descend-finite-type). Its initially empty proof is now complete. No quasi-coherence, Noetherian or quasi-compactness hypothesis was added.

The source's refinement paragraph says that x is in the image of X' after introducing X''. What is needed is x in the image of X''. Steps 2 and 3 explicitly retain a point over x at every refinement. The source also compresses the two different sheafifications in the local tensor representation; step 3 separates the tensor sheafification from the inverse-image sheafification, and takes a finite intersection of the resulting neighbourhoods.

The final faithful-flat check uses the existing geometric-stalk comparison and strict henselization rather than restating the ordinary-stalk comparison as a new lemma. This is the same local faithful-flat detection argument as the source, and changes no unit route. The generic ringed-topos adjunction, local lifting, scalar pullback, geometric stalk and faithful-flatness inputs are recorded as tool uses where off-unit and not already Mathlib/Lean-closed.

The latest blueprint is literature/blueprint/latest (COMMITS.txt records main-20261023-1620, 7284bb09daf97437d544c51882b325f9c52cd345). I read its sk-thm-sf-ctf-stability/_section.md and direct-images.proof.md. The imported unit record and this descendant retain historical ancestry, including a null blueprint ancestor. I preserved it. This node supplies the 08HD finite-type input to the recorded 08HE pseudo-coherence induction; it is not itself a key unit node. No chapter or unit record was changed.

## Unfinished work

None in the requested stage-1 split. Existing cited nodes retain their own stages; no new unsplit obligation was introduced.

## Not duplicates

No new nodes. Whole-DAG searches by 08HD, local-pullback, module pullback, finite type, faithful-flat local maps and the relevant stalk notions found the existing tools now cited. Blueprint searches by finite type, finite type module, finite generation, finite type of arbitrary, 08HD and local-pullback found no equivalent blueprint statement; the finite generation hit is a Rees algebra lemma. In particular I did not create duplicate nodes for local lifting, change-of-topology tensor sections, geometric stalks or faithful-flat reflection of surjectivity.

## Review by Q116

I read Stacks spaces-perfect.tex, lemma-descend-finite-type (08HD), including its proof, and compared the statement clause by clause: X is arbitrary, F is an arbitrary O_X-module, and finite type is local finite generation on the two respective sites. I also read sites-modules.tex lemma-local-pullback (03DO), the tensor/adjunction descriptions in the existing nodes, sheaves.tex lemma-stalk-pullback-modules (0098), algebra.tex lemma-local-flat-ff (00HR), and morphisms.tex lemma-etale-open (03WT). There are no new nodes whose independent source must be checked.

For step 1 I opened the ringed-topoi-module-adjunction statement: it really states the tensor-formula left adjunction for arbitrary modules. Thus its pullback preserves cokernels and finite sums. The free-rank comparison is explicitly multiplication of tensor factors. I opened etale-scheme-base-change: its statement applies to every base change, so it justifies the all-test-objects cover condition without requiring quasi-compactness.

For step 2 I opened zariski-etale-tensor-sections. It says exactly that the tensor pullback of any module is the sheafification of V -> Gamma(V,f^*F), naturally in the module map, without a quasi-coherence hypothesis. I do not claim that this presheaf is already a sheaf or that its sections equal the pullback sections globally. The presheaf-module-sheafification statement supplies the adjunction, so its unit becomes invertible on sheafifying. The cited site-sheafification-iso-locally-bijective statement is for abelian presheaves on any site and supplies local surjectivity of that unit. Successive covers lift finitely many generating sections on one refinement still meeting the chosen fibre.

For step 3 I opened module-pullback and sheaf-tensor-product: they specify respectively the sheafified neighbourhood-colimit inverse image and the sheafified sectionwise tensor. Those are precisely the two local lifts taken, both justified by the same locally-bijective criterion, not just by the universal-property definition alone. Once lifted, tensor elements are finite sums and elements of a filtered neighbourhood colimit have representatives. Finite intersections allow all coefficients from F to be represented on one common open. Shrinking retains z throughout, hence the resulting U contains x. This step does not claim that stalkwise finite generation alone implies local finite type.

For step 4 I opened the etale-morphism definition: it includes both flatness and local finite presentation. The flat-lfp-open statement therefore applies, and produces the open image W containing x. The chosen finite sections need not descend the coefficients a_ij: only their span must contain each s_i after pullback, which the written finite-sum equations prove. I opened site-abelian-sheaf-epi-locally-surjective: it applies to arbitrary sites and states exactly the local lifting criterion used. The module-category definition says cokernels are the sheafifications of sectionwise cokernels, so the underlying abelian test detects the module epimorphism too. Surjectivity of V'' -> W is by the definition of W as its image, not a finiteness assertion.

For step 5 I opened every cited statement. Geometric-stalks-exact gives exactness of the underlying abelian stalk functor. Etale-zariski-module-geometric-stalk gives both O_et,bar(y) = R^sh and the natural comparison (epsilon^*M)_bar(y) = M_y tensor_R R^sh for arbitrary modules, including naturality in q; no quasi-coherent-only comparison was substituted. Strict-henselization-faithfully-flat applies to each local ring R and the chosen separable closure of its residue field. The local-flat-faithful-flat-reflects-surjective node states reflection of surjectivity explicitly, rather than merely defining faithful flatness. Finally the abelian-sheaf-epi-iff-stalk-epi node is about ordinary topological stalks, which are exactly the stalks q_y now shown surjective. Together with the module cokernel description it proves q epi. No finite generation assumption on F_y was used to obtain this reflection.

Step 6 is only assembly of the neighbourhoods into an open cover and the definition of finite type. I checked the empty scheme, F=0, rank zero and a non-quasi-compact scheme (the ranks and chosen covers may vary with x). All steps work on arbitrary, possibly non-Noetherian stalk rings. I checked that the closure of each substantive reused node does not contain this item, avoiding a cycle. Every non-elementary input is cited, every quotation in citations.json is copied verbatim from the cited statement, and no step exceeds 2000 characters. I did not introduce a node restating either implication or a clause of the item. The source route is retained, with the local representation and faithfulness arguments made explicit.
