# Worker report: lem-sf-triple-compactification-normal-form

## Files written

- dag/nodes/sec-six-functors/lem-sf-triple-compactification-normal-form.json: item, statement, now split in twelve steps; Mathlib searches found no match. Statement and statement dependencies unchanged.
- citations.json: every step/node pair, with the cited statement copied verbatim. Full statements are retained where several clauses or normalization conditions are used.
- report.md: this report.
- searches.jsonl: the search command's actual log. write_split.py and finish_split.py are sandbox-only working scripts, not delivery files.

No new DAG nodes; no Mathlib leaves added. The existing binary identity and open normalization theorems are sufficient. This avoids creating a node for either triple identity or for the naturality calculation.

## Attachments

None. I searched lean/WeilConjectures for the item id, triple compactification and compactification normal forms, and read Kunneth/Relative.lean and the comparison interface. AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct at Relative.lean:132 has a sorry at line 142 and only asserts an isomorphism, not this item's identities for specified maps or its integral strict-diagram assertion. It cannot attach this item. No Lean was written or compiled.

## WANTED

None. coord/dag-sync.md mentioned by the inherited brief is absent; the current direct-delivery brief and read-only live clone determine this task's paths and protocol.

## Defects and corrections

The item was unsplit with an empty proof. Its statement is correct as a consequence of the already present binary normal-form and open-product statements, and I made no statement correction. In particular, I did not infer an integral map equality by comparing finite derived Hom classes, assume transitions on etale-origin witnesses, or use the parent Kunneth coherence theorem (which depends on this item). The two proper triple composites are kept separate: equality of those composites is outside the normal-form calculation.

The initial assembly needed explicit domain checks for nested realization. I added uniform Tor/cohomological bounds using finite dimension, the coefficient-independent direct-image vanishing bound, the direct-image Tor theorem, and the system etale-origin comparison. I also expanded the completion check from completeness of E to the inverse limit of its valuation-ring quotients. This prevents the more restrictive system-realization statement from being applied solely on the basis of object names.

## Unfinished work

None for stage 1. Existing cited nodes remain independent obligations of the DAG; this delivery introduces none. Server check results are recorded after the dry run below.

## Searches and route

I read AGENTS.md, GOAL.md, SETUP.md including all three blueprint levels, stages/1-dag.md, roles/worker.md, coord/brief-stage1.md, delivery-errors.md B--E (including the repeated imported copy), and the chapter/unit records. The unit's route is unchanged. Blueprint ancestor is lem-sf-kunneth-coherence; tools/blueprint_refs.py searches for compactification, compactification identity, external tensor and triple gave no other blueprint statement of this item. Relevant imported nodes only give the full Kunneth theorem, not this separate normal-form lemma. DAG and project-source searches located the existing binary and open-product statements used below; no candidate new node survived that search.

I ran msearch.py with two LeanFinder phrasings, a Loogle extensionByZero/tensor query, a grep compactification/open-tensor query, and LeanSearch. I read all returned hits. LeanFinder returned homological-complex tensor associators and ordinary sheaf pushforward compositors, LeanSearch returned compactly supported continuous-map constructions, and grep returned topological compactifications. Loogle returned no hits. None states the equality of specified geometric compact-support composites or its coefficient-diagram normalization. All actual queries are appended to the inherited item searches; no new node requires a search record. Services were available for these queries.

No SGA source is used. The proof is marked agent-written because it expands the blueprint reduction-to-proper paragraph using existing DAG theorems. I read the current main-20261015 lem-sf-kunneth-coherence.proof.md and sk-thm-sf-kunneth-relative/_section.md. I also read Stacks sites-cohomology.tex Tag 0GL1 (lemma-j-shriek-and-tensor), Tag 0E48 (remark-compatible-with-diagram), and Tag 0941 (lemma-derived-limit-is-ok). These explain the open-tensor and diagram background; they are not substituted for the stronger cited DAG statements. No new source-only claims are introduced.

## Not duplicates

No new nodes. The existing lem-sf-product-compactification-identity, lem-sf-open-external-tensor-normalization and lem-sf-integral-open-product-diagram-normalization are reused verbatim, not replicated. None is a triple normal-form lemma, and their binary identities plus naturality give the two triple identities by the displayed calculations.

## Review by NR

I checked every proof citation by opening its node and reading its statement, including its coefficient stage and domain. citations.json contains those exact statements. My check against delivery-errors B--E is the following mathematical review, not just the mechanical gates.

Step 1 uses proper base change/composition from lem-weil-pbc-proper-fp-permanence for a12, a23 and c. The product open is concretely the intersection of the inverse-image open subschemes. lem-trf-open-ctf preserves the input intervals; lem-sf-pullback-tor-amplitude preserves them under projection pullback; lem-sf-tensor-ctf adds them; lem-sf-proetale-constructible-origin supplies bounded witnesses. These statements all apply at A_E,n over the algebraic closure of the fixed finite field. No unrestricted pro-etale input is used.

Step 2 takes exactly the binary normal-form identity from lem-sf-product-compactification-identity. It is applied first to 12 and 23 and then to 12,3 and 1,23. Each product compactification has the proper/open properties just checked. The objects Qij and Hij differ, and the map eij between them is exactly the normalized map in lem-sf-open-external-tensor-normalization. I did not silently replace them by equality of objects.

Step 3 takes naturality of projection from prop-sf-pf-coherence, naturality of the exchange and canonical comparisons from def-exchange-projection, and the supplied compositor/proper identifications from def-sf-datum. Composing natural transformations proves the displayed naturality square for lambda. No special new theorem is needed for this three-line operation.

Steps 4 and 5 are the actual argument for the normal forms. For the left side the middle subcomposite is lambda(H12,P3)(Ra12_*e12 tensor 1), and step 3 changes it to Rc_*(e12 external 1)lambda(Q12,P3). For the right side it is lambda(P1,H23)(1 tensor Ra23_*e23), and step 3 changes it to Rc_*(1 external e23)lambda(P1,Q23). In each case functoriality combines this map with the outer e to give exactly eL or eR. The only remaining identifications are the supplied composition isomorphisms of A4, not a proof of triple Kunneth coherence. Thus these steps are elementary substitutions and are not newly named clauses of the item.

Step 6 uses the actual three-open associativity clause of lem-sf-open-external-tensor-normalization, including the restriction-to-identity and isomorphism assertions. lem-pur-derived-pullback-tensor-iso supplies monoidality with associativity compatibility so nested external products have the asserted triple source. It is used only as a tensor tool, not as a Kunneth result. There is no attempt to detect a proper direct-image map by its open restriction.

Step 7 uses refinement compatibility explicitly stated by the binary identity. fix-lem-exchanges supplies exchange refinement/composition compatibility; prop-sf-pf-coherence supplies projection independence of compactification. Pasting these binary squares is an explicit functorial composition, so the triple refinement comparison does not need a new lemma.

Step 8 reads the diagram statement, not merely the completed conclusion, of lem-sf-integral-open-product-diagram-normalization. It supplies actual e-bullet maps, binary identities and three-open associativity in the derived diagram category. Its quotient-ring tensor is used, not the tensor of forgotten O_E-module towers. The finite reductions have bounded etale witnesses without witness transitions.

Step 9 checks why the stronger lem-sf-integral-compactification-system-realization can be used for the nested expressions. Uniform Tor intervals come from def-weil-finite-tor-amplitude, and open/pullback/tensor bounds from step 1. lem-kun-dimension-finite-type and lem-sf-etale-direct-image-vanishing give uniform 2d bounds for the finite set of proper source schemes, independent of m. This is exactly the uniform vanishing hypothesis in thm-sf-direct-image-tor-amplitude, so the output intervals are common finite intervals. lem-fix-operation-reduction preserves normalized transitions. lem-pur-coefficient-system-derived-comparison constructs coherent origin presentations from the actual system through its counit, rather than adding transitions to arbitrarily chosen witnesses. The coefficient hypotheses follow from the DVR statement of lem-weil-l-adic-extension-integers-dvr and completeness of E in lem-weil-l-adic-extension-complete, with the Cauchy-sequence argument written in the step. All uses are the statements of these nodes, not details available only in their proofs. The substitutions are then naturality identities of actual system transformations.

Step 10 uses the contextual/whiskering clause of the system-realization theorem. I checked that it covers nested compact-support functors and their compactification-composition maps, explicitly in its statement. Functorial Rlim carries the diagram equations of step 9 to the specified completed equations; the binary identification comes from the open-product diagram theorem. This proves equality before evaluating reductions and needs no faithfulness of derived evaluation or reduction.

Step 11 checks refinements at the same level: lem-cbc-strict-tower-proper-open-calculus states horizontal/vertical/base-change pasting for actual strict-tower maps including noncartesian refinement squares. The system-realization statement gives those equations intrinsically before restriction/evaluation. fix-lem-exchanges and projection coherence give the generator refinement squares. Pasting followed by contextual realization yields the completed refinement squares.

Step 12 uses the rationalization and common-field clauses of the open-product diagram theorem and lem-fix-operation-reduction. def-exchange-projection fixes the scalar-extension cocycle and the specified canonical maps, so the transported equations are the required field-stage equations. A common field handles the finite list of objects and maps. There is no rational-to-finite reduction.

I tested the edge cases conceptually: with an empty Xi the external input and its extension are zero and both normal forms are the zero-object identities; identities for the opens give eij=1 and reduce the calculation to the chosen proper model; zero complexes give the same equations; coefficient n=1 is allowed and no step uses n>1. Odd shifted inputs require the signed symmetry already in Psi and in the normalized open maps, so no unsigned swap or rearrangement was inserted. The integral calculation uses the same ordered factors and associators. All twelve steps are below 2000 characters after expanding the realization checks, and none hides an independent comparison lemma: the non-elementary comparisons are already cited nodes. There is no cycle through the parent theorem. All off-unit generic tools are declared in split_report.tool_uses with their purpose.
