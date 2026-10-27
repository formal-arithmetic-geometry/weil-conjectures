## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-qcqs-permanence.json: statement split into four steps, original statement and statement dependencies retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-qc-cancellation.json: new statement-only general cancellation lemma, unsplit; not in Mathlib for algebraic spaces.
- citations.json: verbatim statements supporting every citation of all four steps.
- searches.jsonl: actual search-command records, read before recording verdicts.

## Attachments

None. Searched lean/WeilConjectures for the blueprint id, algebraic-space names, and quasi-compact cancellation. There is no project declaration of the algebraic-space statement. Scheme permanence instances do not prove this item for arbitrary algebraic spaces.

## WANTED

None. All sources used are in literature/stacks-project/.

## Findings and corrections

The unsplit item correctly states parts (1)-(2) of Tag 073B. No statement correction is needed. Its pre-existing search hits and the new searches all concern schemes. Read Mathlib/AlgebraicGeometry/Morphisms/QuasiSeparated.lean lines 245-257: QuasiCompact.of_comp and quasiCompact_of_compactSpace have Scheme parameters, so neither is a match for the item or the new algebraic-space cancellation lemma.

The new node is Tag 03KS (lemma-quasi-compact-permanence), not a clause of Tag 073B: it concerns arbitrary composable arrows, assumes quasi-compactness of the composite instead of compactness of the source, and permits noncompact source and target. It is the general intermediate theorem the source explicitly uses. The remaining work to apply it, including the quasi-compact structure map to Spec Z, is proved in the item rather than hidden in another node. The quasi-separated conclusion is established directly by the scheme-test identity in the proof of Tag 03KR, not by introducing a node for that clause.

Read the latest blueprint sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). This auxiliary finiteness input remains on its inherited alteration/moduli/finite-presentation branch. blueprint_refs.py ancestor returns None for this item's inherited chain; the null ancestor and inherited via chain are retained, with the exact new supporting place appended. Whole-DAG searches by tag 03KS, cancellation, and source label found no existing algebraic-space cancellation statement. Whole-blueprint searches for 03KS and quasi-compact cancellation returned zero; the broader quasi-compact/quasi-separated search found scheme results, not this statement.

No work remains for this one-level split. The new lemma deliberately remains unsplit for its next worker. No Lean or compiler/build tool was used.

## Not duplicates

lem-sfb-space-qc-cancellation vs lem-trf-space-qc-separated-etale-local: the latter characterizes simultaneous quasi-compactness and separatedness after etale target covers; it does not cancel a quasi-separated second arrow of an arbitrary composite.

lem-sfb-space-qc-cancellation vs lem-pc-quasi-compact-local-on-target: the latter is Zariski target-locality for morphisms of schemes; the new statement is cancellation for arbitrary algebraic-space morphisms.

lem-sfb-space-qc-cancellation vs lem-sfb-space-quasicompact-affine-tests: the latter gives affine-test characterization and base change, not cancellation from a quasi-compact composite and quasi-separated second arrow.

lem-sfb-space-qc-cancellation vs lem-sfb-space-affine-locality: the latter characterizes affine maps and their consequences; it does not give quasi-compact cancellation for non-affine maps. The overlap is Tag 03KG, cited only for the convention on affine tests in the new node.

lem-sfb-space-qc-cancellation vs lem-weil-pbc-qcqs-morphism-permanence: that node treats schemes and also products/base change; the new result treats arbitrary algebraic spaces and has the general composable-arrow cancellation hypotheses.

## Review by Q39

I read spaces-morphisms.tex Tag 073B, lemma-quasi-compact-quasi-separated-permanence, statement and proof of (1)-(2); Tag 03KS, lemma-quasi-compact-permanence, with its graph/section proof; and Tag 03KR, lemma-compose-after-separated, including its scheme-test identity. For the new node I also read the affine-test equivalence in Tag 03KG, lemma-quasi-compact-local, to ensure that the stated convention agrees with the source's quasi-compactness convention. The report's intended future proof of the unsplit cancellation lemma is precisely the source's factorization through the graph: quasi-separatedness controls the section, and base change of the composite controls the projection. I have not placed that proof inside the new statement.

I opened each cited node and used only its statement. In step 1, lem-sfb-qc-space-affine-etale-atlas supplies one affine atlas from point-space compactness, with no separation hypothesis. lem-trf-space-fibre-products-etale-covers supplies its surjective etale base change to the arbitrary affine test of the absolute structure map. In step 2, lem-weil-pbc-fibre-product-affine-spectra states the tensor-spectrum identification over Spec Z with precisely both affine factors required here; lem-weil-pbc-affine-scheme-qcqs gives compactness of that affine scheme. The independent final assertion of lem-a1-space-finite-affine-subatlas gives compactness of the target of a continuous surjection; applied to this surjective etale atlas it proves compactness of the test fibre product. No quasi-compactness of the atlas morphism is asserted or needed. This node is an off-unit generic topological tool and is declared in split_report.tool_uses. The other off-unit inputs in step 2 are Mathlib leaves.

In step 3 the newly stated general cancellation theorem is applied with g the absolute structure map of Y. Its quasi-separated hypothesis is exactly the given absolute quasi-separatedness of Y. Its composite is the map proved quasi-compact in steps 1-2. Thus no compactness of Y or of the original base S has been added. In step 4 the only cited theorem is existence of the sheaf fibre products. I wrote out their test-sections: both pullbacks consist of pairs (x,t) for which x=u(t)=v(t); the extra equality fu=fv is already part of the map to X times_Y X. Hence the comparison is an actual sheaf isomorphism, and the compactness used is exactly an affine test of the given absolute diagonal of X. This is the elementary proof of the needed specialized 03KR argument, not an unsupported appeal to a theorem. Every citation has a verbatim quote in citations.json.

I checked B1-B10: the new node is self-contained and statement-only, every geometric notion is defined inline or has its defining dependency, source tags and labels match tags/tags, and searches are copied only from searches.jsonl. Semantic results, Loogle, and the grep were inspected, including a second cancellation phrasing; no Mathlib leaf is claimed. I checked C1-C8 by comparing every step to the opened cited statements, ensuring that no source reference substitutes for a node and that the off-unit tool is declared. I checked D1-D5: the new composable-arrow lemma is an actual intermediate input, the absolute structure-map proof is retained, and the diagonal argument is explicit. No proof step exceeds 2000 characters. I checked E1-E7 against the following edge cases: X empty, Y empty (forcing X empty), zero-ring affine tests, noncompact Y, arbitrary non-quasi-separated S, and quasi-compact X that is not quasi-separated. The last case is allowed in the first clause only; step 4 is used solely when the extra hypothesis on X holds. No claim that affine intersections are affine, or that a contained image factors through an immersion, enters this proof. Reuse searches and citation records, rather than fabricated or unavailable results, support the delivery.
