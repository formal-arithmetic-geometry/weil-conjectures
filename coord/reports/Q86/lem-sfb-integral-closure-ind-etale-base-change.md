# Q86 repair: lem-sfb-integral-closure-ind-etale-base-change

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-integral-closure-ind-etale-base-change.json: statement unchanged, four assembly steps, 2380 proof-text characters, status split. Existing Lean, review, blueprint, source and search metadata retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-directed-tensor-integral-embedding.json: new statement, status unsplit, no Mathlib match. Stagewise injective tensor maps with integral image induce an injective comparison into the limit integral closure, with all transition equations. No proof or proof dependencies.
- dag/nodes/sec-six-functors-basics/lem-sfb-directed-algebra-tail-base-change.json: new statement, status unsplit, no Mathlib match. Upper-tail algebra and ring colimit universal properties and compatible algebra tensor identifications, including the structure map and element equations used in descent. No proof or proof dependencies.
- citations.json: one verbatim statement quotation per cited node per item step.
- searches.jsonl: actual output records of the required msearch commands. The old item's searches remain in its JSON; the new nodes record only searches executed in this repair.

Two new unsplit nodes, zero new Mathlib leaves. No Lean source, repository file, launcher file, compiler, Lake or build operation was used for writing or validation.

## Attachments

None. I searched the project under WeilConjectures for the item tag and for integralClosure, tensor cancellation, injectivity and colimits. The item's declaration TensorProduct.toIntegralClosure_bijective_of_indEtale is in Sheaf/RingTheory/IntegralClosureIndEtaleBaseChange.lean and has sorry. It cannot justify an attachment. IntegralElementsColimitDescent.lean already provides the more general finite-family descent theorem and is reused through its existing node, not duplicated. The project uses of cancelBaseChange supply tensor comparisons in other constructions, not the complete new tail-colimit statement.

## WANTED

None. The required Stacks source and blueprint files are present.

## Repair of latest landing return 11a79b7e227

The current coord/returns/Q86.md identifies the returned head as 11a79b7e227, dated 2026-10-22 14:05 UTC. The earlier return sections below are retained history. On resuming after the provider interruption I checked that no delivery process for this item remained active, read the retained ready receipt and report, and ran the required dry run before editing. It exited successfully with OK (not pushed), head 922b1a35ac2, on the current server base. This is the delivery tool's supported rebasing operation; no git command was run in the shared repository. The read clone still contains the original five-step proof and released keep_plan re-split order, and neither extracted dependency exists there. Only proof, proof_deps and split_report differ between the retained item and current read-clone item; the statement and all other metadata remain identical.

I re-read the full current statements of every proof citation and every definition cited by the two new nodes. The seven citations.json entries are still verbatim statement substrings and cover exactly the seven step/node pairs. In step 1 the presentation uses the geometric etale interface of the existing finite-stage leaf; directed reindexing preserves the algebra colimit. In step 2 both assumptions of the new embedding node follow from the stage isomorphisms, with v the integral-closure inclusion. In step 3 the elementwise node provides a representative with N=B; the tail node provides the ring-colimit hypothesis and the lambda/theta equations required by singleton descent, with no finite-type assumption. I strengthened step 4 by displaying f(t)=(a_j tensor 1)f_j(t_j)=(a_j tensor 1)x_j=(a_i tensor 1)x_i=x, using a_j a_ij=a_i. The integral-closure inclusion then detects the required equality. This is an explicit adjustment of the split after the named return, not an unchanged re-push.

I re-read the Stacks 0CBF proof, the finite-stage 03GE statement and proof, and the monic-equation lifting argument of 07RG; the last is used through the existing finite-family descent node, whose statement explicitly has no finite-type hypothesis. I also re-read the current main-20261015 direct-images proof and chapter/unit records. The retained two jobs allocate the nontrivial directed embedding and tail/tensor-comparison arguments; neither supplies the parent's whole assertion or its surjectivity. The retained 16 actual search-log results were read, including the unavailable LeanSearch results and corrected Loogle pattern. The statements and search questions have not changed, so the searches are reused as instructed. I read the flat-injectivity and tensor-cancellation hits in Mathlib source: their hypotheses/conclusions still do not give either complete extracted statement in one line.

The existing B–E review remains applicable. In particular the new nodes are statement-only and self-contained, no new definitions or source routes were introduced, zero rings and constant systems satisfy the formulas, and noninjective transitions are handled by eventual zero rather than cancellation. The parent remains below 3000 proof-text characters and every step below 2000. The side-to-live promotion refusal is maintainer state, which this worker does not edit; this delivery supplies the rebased, checked split for that promotion.

## Repair of latest landing return 6ee65f6dca6

The current return is dated 2026-10-22 10:18 UTC, head 6ee65f6dca6; the 33b7c5946db section below describes the earlier attempt and is retained as history. I continued the retained sandbox rather than reconstructing it. Before editing, the required dry run successfully rebuilt its delivery on the current server base (f7bd7aaee47, OK, not pushed). The read clone still has the original five-step proof and the released stage-1 repair note with keep_plan and at least two new nodes; neither new node is present there. The retained item's only field differences from the read clone were proof, proof_deps and split_report. In particular its statement, statement dependencies, source, searches, Lean record, review records and blueprint metadata agree. Promotion of the side completion remains L's operation; this delivery supplies the requested current-base split and does not edit maintainer state.

I re-read every current cited statement, not only the finite-stage leaf: def-weil-pbc-ind-etale-algebra; lem-weil-pbc-filtered-category-directed-cofinal; lem-sfb-integral-closure-etale-base-change; lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise; lem-weil-pbc-integral-tensor-generators-colimit-descent; and both retained new nodes. The current statements agree with the retained citation quotations. I also re-read the category-colimit, tensor-product and integral-closure definitions used by the new nodes. No current cited interface forces a change of statement or route. The finite-stage leaf retains the maintainer's geometric-etale interface; the common-universe condition and the ring-colimit condition are still needed and retained.

This revision makes the descent application explicit: the upper tail is a nonempty directed preorder with initial index i; phi_i is the map s maps to s tensor 1; the lambda and theta isomorphisms identify both the source scalar map and the selected element; no finite-type hypothesis on D_i is needed. It also makes explicit that equality in C_S in the final step is detected by its injective subring inclusion into D. These details are in proof steps 3 and 4, not just in this report, so this is not an unchanged re-push. The two new statements, their sources, prior searches and the complete preserved original argument are retained. The new assembly has 2305 proof-text characters, below the 3000 limit, and no step exceeds 2000.

I read all 16 retained searches.jsonl results and the new nodes' recorded queries. There is no changed statement or search question, so no search was repeated. I read the relevant source hits for the integral-closure map and flat injectivity and for algebra tensor cancellation, including its two pure-tensor formulas; none gives either complete new assertion in one line. Fresh whole-blueprint searches for upper tail, tensor integral and integral closure and the ancestor query confirm the retained provenance. The current same-tag normalization and descent statements do not supply the two arbitrary-algebra assertions; the distinctions below remain applicable. citations.json has been regenerated from the current cited statements, with one exact statement quotation for every use.

## Repair of landing return 33b7c5946db

The return dated 2026-10-22 07:00 UTC reports that the reader approved the split but landing refused the side completion because it had not been promoted to the live DAG. I retained the sandbox's two new statements, four-step assembly, original argument, report and actual search log. The sandbox ready record names b6c98ce5ec1; the return identifies the subsequently reviewed delivery head as 33b7c5946db. I compared the retained node with the current shared DAG without running git there: before this repair the only different item fields were proof, proof_deps and split_report. Thus the statement, statement dependencies, Lean signature, reviewed records, blueprint, searches and source already agree with the current base. The current DAG still has the original five-step proof, and neither new node exists in it. The released stage-1 repair order remains applicable with keep_plan and at least two new nodes.

I re-read every cited current statement: ind-etale presentation, directed cofinal reindexing, etale integral-closure comparison, tensor-colimit representatives/eventual zero, finite-family integral-tensor descent, and both new statements. The finite-stage leaf now states etaleness through Spec and the scheme definition, as the prior maintainer fix requires. Its Mathlib match includes the scheme-to-ring equivalence; I adjusted assembly step 1 to say explicitly that the etale stages have exactly that geometric meaning. The ind-etale definition gives those same stages via scheme-conventions, so no extra lifting-property equivalence is assumed. The tensor-colimit node requires a common universe; step 1 retains it. The descent node still requires a ring colimit, arbitrary B_0,C_0 and a finite family; step 3 obtains the ring colimit from the tail lemma and uses B_0=S_i, C_0=D_i and the singleton. The remaining cited interfaces support every clause taken from them. citations.json was refreshed from those actual current statements, and every quote is verbatim.

The first resumed dry run exited with duplicate-check diagnostics for two recently added 0CBF nodes: active-root-tower-normalization-splitting and normalization-strict-local-etale-spreading. I opened both full statements and added all four required comparisons under Not duplicates. They are geometric/Noetherian normalization inputs and give neither of the arbitrary algebra statements here. No new search question or mathematical statement changed, so I reused and read searches.jsonl and the source hits rather than repeat queries. I re-read Stacks 0CBF and 03GE and the coefficient-lifting proof of 07RG, plus the current direct-images blueprint paragraph (3). The chapter/unit route is unchanged. The retained TeX contains a single backslash per command in parsed text; the doubled appearance in JSON is correct serialization, so no TeX repair was necessary.

I again checked small cases and B–E against the actual statements: the constant system and zero rings satisfy both new assertions; noninjective stage maps are handled by eventual zero; upper-tail cocones use common upper bounds and need no globally least original index. Both new nodes remain statement-only, with no proof or proof dependencies, and the parent proof remains below 3000 characters, with no step above 2000. This is a substantive rebased repair with an explicit current finite-stage interface and updated duplicate/citation review, not an unchanged re-push. The delivery tool prepares the commit on the current server base and runs all required checks there.

## Corrections and repair of the earlier re-split return

The initial sandbox contained only dispatcher brief markers: no earlier node, report or search log. I first ran deliver.py --no-push as instructed; it exited with 'no node files'. I then recovered the item from the current read-only DAG and the previous report from coord/reports/Q35. The current item has exactly the five returned proof steps (lengths 889, 889, 450, 1630, 584), so this is the argument the return requires us to redistribute. I preserved the full old proof below and the earlier report in a further appendix, and retained all item metadata and searches. No git command was run in the repository; its current source is the comparison base. There is no independently retained returned-head sandbox version to rebase.

The human's return requires two comparable new unsplit jobs, not shortening alone. The new tensor-integral-embedding job has a 1315-character statement and carries the transition/naturality, monic-polynomial image, and eventual-zero kernel arguments formerly in steps 2 and 3. It assumes stagewise injectivity and stagewise integral image, not etaleness and not that C is an integral closure. The upper-tail-base-change job has a 1718-character statement and carries the complete comparison formerly proved inside step 4: tail restriction, passage from an algebra colimit to a ring colimit, cancellation of the iterated algebra tensors, and compatibility with the structure maps and the chosen element. Neither states surjectivity of the item's integral-closure map. Their arguments are independent once the common presentation is supplied, so two workers can start them concurrently. Only the already-existing integral-tensor descent theorem, finite-stage comparison and short assembly remain in the item.

There is no statement dispute. The item is precisely Stacks 0CBF specialized to etale stages, with arbitrary rings and arbitrary R-to-B map. The finite-stage leaf is already live and is reused. The two new nodes keep the item's chapter, unit and inherited null blueprint ancestor; blueprint_refs.py ancestor confirmed that null ancestor. Their via lists prepend this item, and their places specify exactly the part of the inherited current main-20261015 direct-image argument being extracted. I read the chapter record, unit record and main-20261015 sk-thm-sf-ctf-stability-direct-images.proof.md, especially paragraph (3). No unit or chapter route or realization is changed.

## Argument allocation

1. Old step 1: new item step 1 retains the etale presentation, directed reindexing, common universe, tensor notation and finite-stage isomorphism; the stage maps are injective with integral image.
2. Old step 2: the new embedding node includes both commuting tensor squares and the limit comparison with its exact pure-tensor formula. Its proof task is to lift an element to a stage, transport a monic equation coefficientwise to S, and restrict the tensor map to the integral closure. The new item step 2 instantiates this task with C included in B.
3. Old step 3: the same new embedding node includes injectivity. Its proof task is to lift t to t_i, kill f_i(t_i) at a later stage by the existing tensor-colimit eventual-zero theorem, use the commuting square and injectivity of f_j, and pass back to the limit. Applying this to differences yields injectivity. No flatness hypothesis replaces this argument.
4. Old step 4: the new tail node includes all four tensor maps, their inverses and all compatibility equations, and the upper-tail universal property in both categories. To prove it, the old upper-bound extension of cocones and ring-cocone-to-R-algebra construction remain necessary; the exact old text is retained below. New item step 3 explicitly makes the singleton application of the existing descent node with B_0=S_i, C_0=D_i, phi_0 the structure map, and s={x_i}. Thus the new node does not duplicate or absorb the existing descent theorem. Its comparison equations identify that theorem's hypotheses and conclusions with integrality over S and S_j respectively.
5. Old step 5: new item step 4 retains the preimage under q_j, compatibility at the limit, surjectivity, and the algebra inverse argument. It keeps the zero-ring/noninjective-transition caveat. This is a short elementary assembly from earlier conclusions.

## Mathlib and blueprint searches

All Mathlib searches were executed through msearch.py Q86 with this item id, and their outputs were read. Each new node has LeanFinder in two distinct phrasings, Loogle, grep, and LeanSearch; unavailable LeanSearch requests are marked unavailable. One initial Loogle pattern contained the unknown identifier Algebra.TensorProduct; I did not treat that as evidence of absence, and ran the valid quoted-name query for CommAlgCat and colimit. The valid tensor/integrality pattern returned no matches. The log is retained exactly as generated.

For the embedding node the hits TensorProduct.toIntegralClosure_injective_of_flat and Algebra.IsIntegral.tensorProduct concern different hypotheses: the first assumes flatness and fixes C to an integral closure, and the second asserts only integrality of a base-changed integral algebra. Neither gives the displayed stagewise-to-limit theorem for arbitrary v and arbitrary coefficient stages. I read the map and flat-injectivity declaration in Mathlib/RingTheory/Smooth/IntegralClosure.lean:39-56. DirectLimit tensor hits identify tensor colimits and do not assert the combined injectivity and integral-image comparison.

For the tail node, I read commAlgCatEquivUnder and the colimit-existence instance at Algebra/Category/CommAlgCat/Basic.lean:203-214, CommRingCat.FilteredColimits.colimitCoconeIsColimit at Algebra/Category/Ring/FilteredColimits.lean:350, and Algebra.TensorProduct.cancelBaseChange with its two pure-tensor formulas at RingTheory/TensorProduct/Maps.lean:476-490. The tensor-isomorphism clause alone is available; these hits do not directly state the specified upper-tail cocone from an arbitrary algebra-colimit cocone or the complete compatibility package. This job is not a Mathlib leaf solely on the strength of a colimit-existence instance or a binary coproduct. It must assemble the functors and prove those compatibilities. The module-level scalar cancellation node also omits the ring-colimit and algebra-comparison clauses.

Whole-blueprint searches included integral closure, integral colimit, integral element, tensor integral, tensor injective, upper tail, algebra tail, tensor cancellation and the item id. No exact matching blueprint node was found. I searched the whole DAG by the source tags 0CBF, 03GE, 07RG and by the statement concepts, then opened the plausible statements. The normal-domain colimit result assumes domains and concerns absolute integral closedness, not these arbitrary relative algebra comparisons.

## Not duplicates

lem-sfb-directed-algebra-tail-base-change vs lem-sfb-active-root-tower-normalization-splitting: the existing node descends a finite tame splitting on a specific punctured root tower over a Noetherian F_p-algebra and compares its normalization; the new node states the upper-tail ring-colimit universal property and tensor identifications for arbitrary commutative R-algebra diagrams, without roots, covers, or normalization conclusions.

lem-sfb-directed-algebra-tail-base-change vs lem-sfb-normalization-strict-local-etale-spreading: the existing node proves finiteness and localization of normalization and spreads etaleness from a strict henselization under Noetherian, finite and normal hypotheses; it provides neither an arbitrary directed algebra ring-colimit universal property nor the displayed natural tensor comparisons.

lem-sfb-directed-tensor-integral-embedding vs lem-sfb-active-root-tower-normalization-splitting: the existing node concerns a specified finite tame cover, root tower and strict-local normalization splitting; the new node passes conditional stagewise injectivity and integral image to a directed colimit for arbitrary v:C→B, and asserts no splitting, finiteness or surjectivity.

lem-sfb-directed-tensor-integral-embedding vs lem-sfb-normalization-strict-local-etale-spreading: the existing node concerns finite normalization of a finite etale algebra over a normal localization and spreading etaleness; the new node is a conditional injectivity/integral-image theorem for arbitrary directed tensor maps, with no normality, Noetherian or localization hypotheses.

lem-sfb-directed-tensor-integral-embedding vs lem-sfb-integral-closure-ind-etale-base-change: the existing item assumes an ind-etale map and identifies the entire integral closure after base change. The new node assumes no etaleness; it is only the conditional injective integral-image passage for an arbitrary algebra map v, with no surjectivity conclusion.

lem-sfb-directed-algebra-tail-base-change vs lem-sfb-integral-closure-ind-etale-base-change: the existing item assumes an ind-etale map and identifies the entire integral closure after base change. The new node assumes no etaleness; it constructs ring-colimit and tensor-comparison data and makes no integral-closure assertion.

lem-sfb-directed-tensor-integral-embedding vs lem-sfb-snc-tame-root-etale-extension: the existing geometric node extends a finite etale torsor after tame roots on a strict normal-crossings pair; it does not state the general directed tensor embedding with conditional integral image.

lem-sfb-directed-algebra-tail-base-change vs lem-sfb-snc-tame-root-etale-extension: the existing node is a geometric tame torsor extension theorem, not a universal property of directed algebra cocones or compatible tensor cancellations.

lem-sfb-directed-algebra-tail-base-change vs lem-weil-pbc-integral-tensor-generators-colimit-descent: the existing node assumes a ring colimit and descends a finite family of integral elements; the new node establishes the required ring-colimit and tensor-comparison interface from an algebra colimit, with no integrality or descent assertion.

lem-sfb-directed-algebra-tail-base-change vs lem-weil-pbc-colimit-finite-ring-map: the existing node assumes a ring colimit and a finite-type algebra map and descends module finiteness; the new node has neither finite-type nor finiteness hypotheses or conclusions.

lem-sfb-directed-algebra-tail-base-change vs lem-weil-pbc-descend-finite-affine-open: the existing node descends finiteness of a scheme morphism on an affine open, assuming affineness at a stage; the new node is an arbitrary ring/algebra cocone comparison.

lem-sfb-directed-algebra-tail-base-change vs lem-weil-pbc-descend-finite: the existing node descends finiteness for qcqs schemes along affine transitions; the new node is a specified algebra-colimit-to-ring-colimit and tensor compatibility statement.

lem-sfb-directed-algebra-tail-base-change vs lem-weil-pbc-descend-finite-affine-base-piece: the existing node is a local geometric finiteness descent result for morphisms over an inverse scheme system; the new node assumes only a diagram of commutative algebras and supplies its ring-colimit interface.

lem-sfb-directed-algebra-tail-base-change vs lem-trf-scalar-tensor-cancel-base-change: the existing node gives one linear isomorphism of modules, not the upper-tail ring-colimit universal property, algebra isomorphisms and coherent structure-map/element equations.

lem-sfb-directed-algebra-tail-base-change vs lem-weil-pbc-directed-tensor-cocones-colimit-n3: that node starts with a ring-colimit diagram and supplied stage and limit comparison equivalences for two other diagrams and proves those cocones colimiting. It does not construct the ring-colimit structure from an R-algebra colimit or the new node's tensor comparison data.

lem-sfb-directed-algebra-tail-base-change vs lem-weil-pbc-directed-subalgebra-tensor-colimit: that node constructs a tensor colimit from a directed covering family of subalgebras of a fixed ring. It has inclusion transitions and different input data; this node allows arbitrary algebra transition maps and asserts the upper-tail forgetful-colimit property.

lem-sfb-directed-tensor-integral-embedding vs lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise: the existing node supplies stage representatives and eventual zero; it does not assert the injective comparison of two tensor systems or its integral image. It is a tool needed to prove the new node.

## Review by Q86

For returned head 11a79b7e227 I completed the fresh current-statement review recorded above. All seven citation quotations still match, and the only retained item/base differences are the proof fields and split report. I made the final surjectivity argument explicit using the coprojection equation a_j a_ij=a_i, checked it on the chosen representative x_i, and verified that its equality in D implies equality in C_S by the subring inclusion. I re-read both new statements and their sources; their assumptions remain valid without injective transitions, flatness or nonzero rings. The repaired assembly has 2380 proof-text characters. The prior searches and full original argument are preserved.

For the latest return 6ee65f6dca6 I re-read Stacks 0CBF (lemma-integral-closure-commutes-colim-smooth), 03GE (lemma-integral-closure-commutes-etale), and the coefficient-lifting proof of 07RG (lemma-colimit-finite), together with the current direct-images blueprint paragraph (3). These allow arbitrary ambient B; no domain, injective-map, Noetherian or nonzero-ring hypothesis was introduced. Step 1 uses the exact geometric-etale stage comparison; step 2 uses the new conditional tensor embedding with the inclusion C into B and the two stagewise conclusions. In step 3 the representatives theorem applies to N=B in the common universe, the new tail theorem supplies precisely the ring colimit and tensor identifications, and the finite-family descent statement applies to the singleton without finite-type assumptions. I clarified those hypotheses and identifications in the proof itself. Step 4 now explicitly uses the subring inclusion to detect equality; all its remaining work is elementary assembly from steps 1 and 2. I rechecked zero rings, constant diagrams and noninjective transitions; neither new node needs additional hypotheses. Both remain genuine independent statement-only jobs, with the original arguments preserved below.

For the current landing return I performed the fresh dependency/source review detailed above, including the changed geometric-etale leaf and the two new same-tag normalization statements. All four assembly steps still take only conclusions stated in their cited nodes. The only elementary assembly is the final choice of a stage preimage and inversion of the bijective algebra map.

I read Stacks algebra.tex Tag 0CBF, lemma-integral-closure-commutes-colim-smooth, and Tag 03GE, lemma-integral-closure-commutes-etale, in full at their statement/proof passages. The source 0CBF calls commutation with filtered colimits straightforward; this repair allocates that omitted reasoning rather than inventing a new route. For the embedding node I checked the tensor-colimit elementwise statement and the definition of integral closure. Lifting t and mapping its monic equation needs no nonzero ring, injective structure map, or flatness. For the tail node I checked the same source's colimit interface against the original step and against Tag 07RG, lemma-colimit-finite, whose proof lifts finitely many polynomial coefficients and later kills their evaluations. The new node is the comparison needed to use the already extracted finite-family version of that proof; it is not falsely attributed as a separately numbered Stacks lemma. Both new node files are statement-only; their proof obligations and the full original arguments remain in this report for the later workers.

For assembly step 1 I opened def-weil-pbc-ind-etale-algebra, lem-weil-pbc-filtered-category-directed-cofinal and lem-sfb-integral-closure-etale-base-change. The definition provides the etale stages, the reindexing theorem explicitly preserves every colimit cocone, and the finite-stage comparison's statement supplies its exact pure-tensor formula. Thus the composite into D_i is injective and has integral image. A common universe includes all ring carriers and the small index. I do not assume the transition maps are etale, injective or flat.

For step 2 I read the new embedding statement against that application, hypothesis by hypothesis: the arbitrary v is the inclusion of the actual integral-closure subalgebra C in B; the diagram and universe are those of step 1; both stagewise hypotheses are exactly the conclusions of that step. Its conclusion says injectivity of q, landing in C_S, the canonical formula and the two commuting squares. No part is taken from a proof instead of the cited statement.

For step 3 I opened lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise and lem-weil-pbc-integral-tensor-generators-colimit-descent, including the actual Lean signature of RingHom.exists_integral_tensor_generators_of_colimit. The first gives precisely an x_i in D_i, without requiring stage coprojections injective. The new tail statement supplies a colimit in commutative rings, not just algebras; J_i is nonempty and directed and has initial index i. Its lambda and theta identify id tensor phi_i with the T-structure map and identify 1 tensor x_i with the correct transition image. The descent node allows arbitrary B_0 and C_0, so B_0=S_i and C_0=D_i need no finite-type assumption. It applies to the finite singleton even when x_i=0 or a ring is zero. At the resulting j the same equations yield exactly integrality of x_j over S_j. This explicitly avoids the previous algebra-colimit/ring-colimit mismatch.

For step 4 the stagewise surjectivity comes from step 1 and the required compatibility from step 2. Equality in C_S follows from equality in D by the literal subring inclusion. The final inverse preserves the algebra operations because q is injective and preserves them; this is the only elementary step. citations.json contains actual verbatim parts (the full statements) of every node cited by every step.

For the B-E checklist I verified self-contained statements and actual definition dependencies, single TeX escaping, empty proof/proof_deps and null proof_origin for the two new jobs, source tags and labels in tags/tags and algebra.tex, real logged searches including unavailable service results, absence of duplicate statements, and no cycle back to the item in the new nodes. The long comparison formerly hidden in step 4 is now an explicit job with its own hypotheses, while the item has no step over 2000 characters and totals less than 3000. These are the two independent jobs the return requests, rather than a new theorem restating the entire item. The existing generic tool-use declarations remain in split_report; no new maintainer tool_uses entries were added.

Small cases checked: a one-stage constant system reduces to its given stage embedding and to the usual tensor cancellation; R=S and arbitrary B gives the expected original closure; S=0 or B=0 makes the comparison between zero rings; noninjective R-to-B and noninjective transitions remain permissible because eventual zero, not embedding stages in the limit, is the kernel argument. For the tail node an index below i is reached through a common upper bound, so it does not assume i is globally least; ring cocones acquire a consistent R-map by a common upper bound of any two tail indices. The tensor inverse identities use only balancing and the unit, and hold also for zero rings. I found no false statement or missing hypothesis and made no statement change.

## Unfinished work

Only the proofs of the two new unsplit dependency nodes, deliberately left as separate stage-1 jobs by the human's re-split instruction. Their statements and the short parent assembly are complete. No Lean proof was attempted.

## Validation

Initial empty-sandbox dry run failed before any commit because no node files existed. The server review_split check of the repaired sandbox reported PASS. The required full delivery dry run and push are recorded below when complete.

## Preserved original argument

The following is the full original five-step argument recovered from the current DAG, not a shortened replacement. Its obligations are allocated above.

### Original step 1

Choose a filtered presentation of $S$ by finitely presented etale $R$-algebras using [def-weil-pbc-ind-etale-algebra]. By [lem-weil-pbc-filtered-category-directed-cofinal], reindex it by a nonempty directed set $I$, retaining $S$ and its coprojections $a_i:S_i\to S$ as the colimit in commutative $R$-algebras. Choose a common ambient universe for the diagram and its algebra carriers. Put $D_i=S_i\otimes_R B$, $E_i=S_i\otimes_R C$, $D=S\otimes_R B$, and $E=S\otimes_R C$. For every transition $u:i\le j$ use $a_u\otimes1$ on these tensor products. By [lem-sfb-integral-closure-etale-base-change], $q_i:E_i\to\overline{S_i}^{\,D_i}$ is an isomorphism, with $q_i(s\otimes c)=s\otimes c$. Denote its composite with the subring inclusion by $f_i:E_i\to D_i$; in particular $f_i$ is injective. All the rings $R,B,S_i$ satisfy that leaf's hypotheses, without hypotheses on the transition maps.

Cited nodes: def-weil-pbc-ind-etale-algebra, lem-weil-pbc-filtered-category-directed-cofinal, lem-sfb-integral-closure-etale-base-change

### Original step 2

By [lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise], applied with $N=C$ and $N=B$, every element of $E$ or $D$ lifts to a stage; an element at a stage mapping to zero is zero after a later transition. The stage-to-limit and transition maps are ring maps. The tensor map $f:E\to D$ induced by $C\subseteq B$ commutes with them: on $s\otimes c$ both composites give $a_i(s)\otimes c$, and pure tensors generate [def-weil-pbc-module-tensor-product]. For $t\in E$, lift it to $t_i\in E_i$. The element $f_i(t_i)$ is integral over $S_i$ by step 1. Map its monic annihilating polynomial coefficientwise along $a_i$; the resulting monic polynomial over $S$ annihilates $f(t)$ because ring maps preserve sums and products [def-weil-pbc-integral-closure]. Thus $f$ lands in $C_S$ and defines the required $S$-algebra map $q:E\to C_S$. Its pure-tensor formula is the one in the statement.

Cited nodes: lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise, def-weil-pbc-module-tensor-product, def-weil-pbc-integral-closure

### Original step 3

If $q(t)=0$, lift $t$ to $t_i\in E_i$. Then $f_i(t_i)$ maps to zero in $D$. The eventual-zero clause of [lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise] for $N=B$ gives $u:i\le j$ with $(a_u\otimes1)f_i(t_i)=0$. By the pure-tensor compatibility this is $f_j((a_u\otimes1)t_i)=0$. The injectivity of $f_j$ from step 1 gives $(a_u\otimes1)t_i=0$; its image in $E$ is $t$, so $t=0$. Applying this to a difference proves that $q$ is injective.

Cited nodes: lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise

### Original step 4

Let $x\in C_S$ and lift its underlying element to $x_i\in D_i$ using [lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise] with $N=B$. For any $S_i$-algebra $T$ obtained from $S_j$ ($j\ge i$) or $S$, the maps $T\otimes_{S_i}(S_i\otimes_R B)\to T\otimes_R B$, $t\otimes(s\otimes b)\mapsto ts\otimes b$, and $t\otimes b\mapsto t\otimes(1\otimes b)$ are mutually inverse: balancing moves $s$ to the first factor, and the formulas preserve multiplication and units. Likewise $T\otimes_{S_i}S_i\cong T$ via $t\otimes s\mapsto ts$ [def-weil-pbc-module-tensor-product]. Under these identifications $1\otimes x_i$ over $S$ is $x$. Restrict the directed system to indices $j\ge i$; it still has colimit $S$, since every index has a common upper bound with $i$, and any compatible cocone on the tail extends uniquely by those upper bounds. The colimit is also one in commutative rings: a cocone of commutative rings $(T,(b_j)_{j\ge i})$ on the tail becomes a cocone of commutative $R$-algebras when $T$ is given the structure map $b_j\circ(R\to S_j)$, which is independent of $j$ because the transition maps are $R$-algebra maps and any two indices have a common upper bound; the induced $R$-algebra map $S\to T$ is the unique ring map compatible with the $b_j$, since such a map is automatically $R$-linear for this structure. Apply [lem-weil-pbc-integral-tensor-generators-colimit-descent] with initial index $i$, $B_0=S_i$, $C_0=D_i$, the structure map $S_i\to D_i$, and the singleton $\{x_i\}$. Its integrality hypothesis is exactly $x\in C_S$. It gives $j\ge i$ for which the image $x_j$ of $x_i$ in $D_j$ is integral over $S_j$.

Cited nodes: lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise, def-weil-pbc-module-tensor-product, lem-weil-pbc-integral-tensor-generators-colimit-descent

### Original step 5

By the finite-stage isomorphism $q_j$ in step 1, there exists $t_j\in E_j$ with $f_j(t_j)=x_j$. Its image $t$ in $E$ satisfies $q(t)=x$: their underlying elements in $D$ agree by the compatibility checked in step 2, and the inclusion $C_S\subseteq D$ is injective. This proves surjectivity. Together with step 3, $q$ is a bijective $S$-algebra homomorphism, hence an isomorphism (its inverse preserves operations by applying the injective map $q$). Zero rings cause no exception, and the nonempty index used above comes from filteredness, not from a hypothesis that a ring is nonzero.

Cited nodes: 

## Preserved previous report (Q35)

# Q35: lem-sfb-integral-closure-ind-etale-base-change

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-integral-closure-ind-etale-base-change.json: item, statement, split into five proof steps; original statement and source retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-integral-closure-etale-base-change.json: new statement, Mathlib leaf. TensorProduct.toIntegralClosure_bijective_of_smooth, Mathlib/RingTheory/Smooth/IntegralClosure.lean:380, specializes using Algebra.Etale.instSmooth, Mathlib/RingTheory/Etale/Basic.lean:223. The comparison map's definition is at IntegralClosure.lean:39–48.
- citations.json: verbatim statement quotations for every citation in every item step.
- searches.jsonl: unmodified output records written by the required search command; queries are copied exactly into the nodes. The single-file grep's output omits its filename, so the same query was repeated on its directory and that usable output is recorded.

One new node, one Mathlib leaf, zero new unsplit nodes. No Lean files or repository files were written, and no compiler, Lake or build tool was run.

## Attachments

None for the item. Searched WeilConjectures by the blueprint tag and by integralClosure, IntegralClosure, indEtale and tensor/colimit combinations. Existing integral-closure declarations cover finite products, normal rings, or integral-element descent, not this arbitrary ind-etale base change assertion. The existing RingHom.exists_integral_tensor_generators_of_colimit is already attached to lem-weil-pbc-integral-tensor-generators-colimit-descent; it is reused rather than duplicated.

## WANTED

None. All mathematical source passages used here are available in literature/stacks-project/.

## Corrections and route

The item was unsplit, with no earlier sandbox node or report. Its statement is correct: Stacks 0CBF allows arbitrary ring maps and a filtered colimit of smooth algebras, and the present etale specialization requires no additional ring hypotheses. No STATEMENT-DISPUTED correction is needed. The source says tensor products and integral closures commute with filtered colimits without expanding that assertion; the five steps supply that argument instead of moving the whole item into a new lemma.

Read the chapter and unit records and the current main-20261015 direct-images proof, paragraph (3). This is the finite tame normalization comparison input below the open-direct-image case. No chapter or unit statement, route, or realization is changed. The inherited nearest blueprint ancestor is null (confirmed with blueprint_refs.py ancestor); the inherited current-snapshot place and via chain are retained and extended for the new leaf. Whole-blueprint searches for integral closure, integral-closure-commutes and integral tensor found no equivalent blueprint node. The weakly-etale integrally-closed-domain result has extra domain hypotheses and does not give the arbitrary-algebra comparison here.

Generic tools from another unit are declared in split_report.tool_uses: directed reindexing, tensor-colimit element calculus, and integral-tensor-element descent. These supply algebraic tools under the existing normalization route, not a replacement of a unit step.

## Not duplicates

lem-sfb-integral-closure-etale-base-change vs lem-sbc-trait-generic-normalization-charts: both cite 03GE, but the existing node asserts existence of polynomial root charts for a finite normalization of a torsor on a smooth scheme over a trait. It neither states integral closure base change for arbitrary ring maps nor specializes to that assertion. The new node is exactly the finite etale algebra comparison, with no schemes, traits, torsors, or chart conclusions.

lem-sfb-integral-closure-etale-base-change vs lem-sfb-integral-closure-ind-etale-base-change: the new leaf assumes a single finitely presented etale algebra. The item allows any filtered colimit of such algebras; the new leaf cannot be applied directly to that colimit. The item's injectivity and surjectivity arguments supply the missing content.

lem-sfb-integral-closure-etale-base-change vs lem-exc-weakly-etale-normalization-tensor: the existing node assumes Noetherian local rings, a universally catenary domain, finite normalization, and compares normalization in total fractions. It does not cover arbitrary ambient B or arbitrary rings as required by this leaf.

## Review by Q35

I read Stacks algebra.tex, lemma-integral-closure-commutes-colim-smooth (0CBF), its cited smooth comparison lemma-integral-closure-commutes-smooth (03GG), and the etale version lemma-integral-closure-commutes-etale (03GE). The new leaf agrees with 03GE, and I read Mathlib's full declaration at line 380 and its map definition at lines 39–48. The smooth declaration has only commutative-ring and algebra assumptions; the Etale-to-Smooth instance at Etale/Basic.lean:223 supplies its extra typeclass. The new leaf writes finite presentation and formal etaleness inline so it does not rely on a convention-collector node for its meaning. The result is a direct Mathlib specialization, not an unproved comparison of different notions of normalization.

For step 1 I opened the statements of def-weil-pbc-ind-etale-algebra, lem-weil-pbc-filtered-category-directed-cofinal and the new leaf. The definition supplies the presentation, the reindexing node explicitly preserves the same colimit cocone for every target category, and the leaf supplies precisely the isomorphism at every stage. I also read categories.tex lemma-directed-category-system (0032). Reindexing stays in commutative R-algebras, so its transition maps are R-algebra maps. A common ambient universe avoids the oversized-diagram failure documented on the existing tensor-colimit node. No injectivity or etaleness of transition maps is assumed.

For step 2 I opened the tensor-colimit node's entire statement: it gives representatives, eventual zero, and ring-homomorphism structure when the tensor factor is an algebra. C is a commutative R-algebra by the integral-closure definition. The tensor definition explicitly says pure tensors generate and gives its universal property, which suffices to verify the displayed square. I opened the integral-closure definition: it gives an actual monic equation, so mapping that equation proves integrality at the limit without invoking an uncited flatness or integral-base-change theorem. The image being contained in C_S makes the map well-defined as an S-algebra homomorphism.

For step 3 the cited tensor-colimit statement supplies eventual vanishing of f_i(t_i) in D_j. The same transition on E_i commutes with f_i by the formulas already checked, and f_j is injective by step 1. Thus eventual zero holds before taking the limit. This does not incorrectly require S_i to embed in S, or require S itself to be flat by an uncited theorem.

For step 4 I opened lem-weil-pbc-integral-tensor-generators-colimit-descent and its Lean docstring in IntegralElementsColimitDescent.lean. Its arbitrary B_0,C_0 and finite s allow exactly B_0=S_i, C_0=S_i tensor_R B, s={x_i}. Its hypothesis refers to integrality through id tensor phi_0, not merely integrality over the wrong coefficient ring. I wrote both directions of the tensor cancellation identification: under them id tensor phi_0 is precisely the S-structure map, and 1 tensor x_i is precisely x. The upper tail is nonempty (contains i), directed, and has the same ring colimit, with the elementary extension-of-cocones argument written in the step. The cited descent lemma needs no module-finiteness or finite-type assumptions. This is a singleton use of an already existing general descent statement, not a new restatement of the item's surjectivity.

For step 5 the finite-stage preimage comes from step 1; compatibility from step 2 identifies its image with x. Only applying an inverse to a bijective homomorphism remains, so the step is elementary. All non-elementary external results used are cited, and citations.json quotes their actual statements, not their proofs. No step exceeds 2000 characters; the largest is the explicit tensor-identification and singleton-descent application, which hides no separate non-elementary comparison.

I checked the B–E checklist against the node files: the only new node has a self-contained statement and no proof; searches are real logged commands; the Mathlib file and lines were read; tags match tags/tags; no SGA source appears; dependencies introduce the notions actually used; no new clause merely restates the whole item. Small cases checked include R=S, S=0, B=0, noninjective R→B, and directed systems with noninjective transitions. In particular, zero rings do not obstruct monic equations or the tensor formulas, and filteredness supplies a nonempty index rather than a nonzero-ring hypothesis. The proof uses neither normality, domains, finiteness of B, nor cancellation inside a ring.

## Unfinished work

None in the requested stage-1 split. Existing dependency nodes keep their own states; the one new dependency is a Mathlib leaf.

## Validation

The first delivery dry run requested a separate numeric mathlib_match.line field; I added line 380, already read and documented above, without changing any mathematics.
