# Stage-1 delivery: lem-trf-smooth-strict-local-base-model

## Files written

- dag/nodes/sec-trace-formula/lem-trf-smooth-strict-local-base-model.json: statement, split in six steps; no exact Mathlib match.
- citations.json: twenty verbatim statement quotations, one per citation and proof step.
- searches.jsonl: actual search-command results; five new searches, preserving the item's inherited search records.
- report.md: this report. write_split.py is a sandbox-only preparation script.

No new nodes and no Mathlib leaves were created. The item's statement, statement dependencies, ancestry and existing search history are retained. No Lean file, repository file or launcher file was written; no git or compiler command was run.

## Attachments

None. I searched WeilConjectures for the exact blueprint tag and the strictHenselizationMap, strict-local base-change, and smooth local-model concepts. Existing declarations cover related stalk/cohomology comparisons, not all clauses of this item. A partial result or sorry declaration was not treated as an attachment.

## Wanted literature

None. All sources used are present in literature/stacks-project. No SGA source is used.

## Defects and corrections

The incoming node had a complete, valid statement but no proof. In particular, Tag 08HV in its source is not by itself a proof of the geometric comparison with all specified arrows. I supplied an assembly proof through existing canonical ind-etale invariance and affine strict-local comparison statements, then identified the required local ring map by the uniqueness statement of functoriality. No statement correction or statement dispute is needed.

The latest blueprint is read at literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md and its proof, together with the current unit _section.md. The generic local-algebra input belongs to the recorded historical nearby-duality/alteration ancestry. This delivery does not change the current unit or chapter route or try to restore the invalid internal-Hom stalk argument that the latest blueprint rejects.

## Unfinished work

None within this stage-1 item. Existing dependency nodes remain responsible for their own proofs. There are no new unsplit obligations.

## Searches and reuse

I read the imported Mathlib searches and retained them. New searches were run only through batch2/msearch.py, using N7 and this item's exact id. Both semantic phrasings returned smooth-chart or localization-stability results. Loogle for the strictHenselization/Smooth pair and Mathlib AlgebraicGeometry grep for strictHenselization, strict_hensel and strictLocalization returned no hits. LeanSearch returned localization and general stability lemmas. I read Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean:62-102, RingTheory/Localization/BaseChange.lean:40-60 and the localization stability declaration at RingTheory/LocalProperties/Basic.lean:490. These concern affine smooth charts or ordinary localization, not the geometric strict henselization comparison; the item is not a Mathlib leaf. All five calls succeeded; no failed service is represented as a negative search result.

The DAG was searched by tags 04HX, 08HV, 01VB, 01VF, 06LJ, by strict-local base-change and Noetherian strict-henselization concepts, and by titles. blueprint_refs.py searches included strict henselization, strict localization, henselian functorial, smooth flat, smooth, and proper and smooth. The ancestor command confirms lem-trf-local-term-locality. This found the existing tools used below, so no new node was made.

## Not duplicates

There are no new-node/existing-node pairs. The nontrivial ingredients are all reused: lem-trf-strict-local-comparison-ind-etale, lem-trf-ind-etale-strict-local-invariance, lem-exc-affine-strict-local-ring-comparison, lem-pc-proper-base-change, lem-pc-smooth-flat, and lem-sc-strict-henselization-noetherian. Neither a smooth-only specialization of strict-local invariance nor a separate Noetherian-stalk node was created.

## Review by N7

I read the item against Stacks etale-cohomology.tex Tag 04HX (lemma-describe-etale-local-ring), including its affine-neighbourhood proof and the paragraph after Definition 03PS; algebra.tex Tag 08HV (lemma-strictly-henselian-functorial-improve) and Tag 0GIP (lemma-base-change-strict-henselization-quasi-finite); morphisms.tex Tags 01VB and 01VF; more-algebra.tex Tag 06LJ. I also read Schemes Tag 01HV's stalk formula and Properties' locally-Noetherian definition/characterization. There are no new nodes requiring additional source reviews.

Step 1 cites functoriality (1), which explicitly supplies locality, the closed geometric lift and the residue embedding. The map into Spec A therefore lies over its maximal ideal; the fibre-product point w lies over that same ideal. The existing ind-etale comparison lemma really does say that structural maps factor through the chosen affine charts and that their coordinate maps are ind-etale. Applying it to the identity of S is legitimate: the two charts are the same, and the identity ring algebra is etale, hence the one-term filtered colimit in the cited ind-etale definition. This gives the hypothesis for j at every point of its whole affine source, not just at the closed point.

Step 2 cites the invariant-localization lemma's canonical-map conclusion and its arbitrary-base-change clause. The checked morphism is j from step 1, not the smooth morphism f. Its base change is q:W→V. The geometric points use the same algebraically closed field Ω, as the lemma requires. The statement explicitly yields an isomorphism over V, so no unrecorded comparison theorem is used here.

Step 3 uses exactly the affine-open stalk localization statement, including its germ-map compatibility, and the affine strict-local comparison statement, including the local-ring structure, structural equality and evaluation equality. The point w admits an affine open without any separatedness assumption. Its ordinary local ring is D_P; transporting that actual ring isomorphism simply gives C and its residue embedding. Full faithfulness and contravariance of spectrum are explicitly in def-weil-affine-spectrum; taking the ring map of α and composing it with θ gives B≅C^sh. This is a composite of the cited comparisons, not a fresh comparison lemma hidden inline.

Step 4 reuses the same affine comparison at s,v for the evaluation kernels. Functoriality (1),(3) gives the residue inclusion for the canonical α and hence its compatibility with evaluation. Defining h=β⁻¹(A→C→C^sh), the structural equality comes from j p=f q and the cited affine comparison over W; equality of evaluation comes from p barw=a and the comparison's evaluation equality. Thus h is local (the maximal ideals are the evaluation kernels), is over S, and has the specified residue inclusion. All three hypotheses of functoriality (3)'s uniqueness statement are now verified; that statement says h=φ. This repairs the tempting but insufficient assertion that an abstract isomorphism automatically identifies the required map.

Step 5 cites the smooth clause (2) of lem-pc-proper-base-change for the actual arbitrary base change f,j. lem-pc-smooth-flat states smooth implies flat. The cited flat-morphism definition defines flatness on ordinary local stalk rings, so it really supplies the stalk flatness used here. At the maximal ideal of a local ring the stalk identification A_m=A follows by sending a fraction a/s to a times the inverse of s, since every s outside m is already a unit. The cited locally-ringed-space definition supplies locality of the scheme stalk map. This elementary identification is not made into a new node.

Step 6 uses the actual locally-Noetherian definition to select a Noetherian affine chart at each point. The affine-open stalk lemma gives its localization description; the existing Mathlib leaf for localization of a Noetherian ring supplies Noetherianity. The affine strict-local comparison gives A and B as algebraic strict henselizations for the selected separable residue closures. Only now is lem-sc-strict-henselization-noetherian applied, with its local and Noetherian hypotheses satisfied. No assertion of Noetherianity is made for arbitrary S,V, or used in earlier steps.

I checked the B–E checklist against the files. All citations refer to the statements opened, not to their internal proofs. citations.json copies actual statement text verbatim, and proof_deps is the union of the step citations. Every step is non-elementary because it applies a cited theorem; none relies on an uncited tag. All steps are below 2000 characters. No new lemma restates a clause or hides the item in a single new node. The off-unit generic tools are declared individually in split_report.tool_uses; the same-unit comparison and invariance tools are reused directly. The statement introduces all objects and its definition dependencies remain unchanged.

Edge cases checked: f=id_S gives W=Spec A and the expected localization-again comparison; an etale f and an open immersion give the usual invariance; a positive-dimensional smooth fibre uses an arbitrary geometric point, not a closed point of W itself; Ω may be much larger than the selected separable closures, and is never identified with the residue field of A or B. In positive characteristic those closures may be imperfect, which does not affect the evaluation argument. Non-Noetherian bases are allowed throughout steps 1–5. Non-separated bases are harmless because an affine open around each image suffices and no intersection of arbitrary affine opens is claimed affine. Empty schemes have no selected geometric point, so the hypotheses already exclude that vacuous case. All added edges point to existing generic tools; no dependency relies on this item.
