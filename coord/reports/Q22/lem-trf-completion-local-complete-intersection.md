# Q22: lem-trf-completion-local-complete-intersection

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-completion-local-complete-intersection.json`: statement, split into six proof steps; statement and statement dependencies unchanged; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-regular-quotient-completion-kernel-test.json`: one new statement-only, unsplit lemma; no Mathlib match.
- `citations.json`: one verbatim statement quotation for each of the 25 step/node citations.
- `searches.jsonl`: six actual new searches, retained as returned by msearch.py. The item's five inherited search records are preserved. `prepare_split.py` is sandbox-only preparation code, not a project delivery file.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item id and blueprint tag, complete-intersection terminology and declaration spellings, and regular/kernel/completion combinations. There is no project declaration stating the item or the new kernel comparison. The upstream master was consulted only as reference; no sorry declaration is treated as completed work.

## WANTED

None. All sources used are present in `literature/stacks-project/`.

## Corrections and scope

The item was an unsplit statement with no proof and no own Lean attachment. Its statement is true as written, including inseparable residue fields, because condition (2) asks for a ring isomorphism. A coefficient-field embedding of F into the completion need not extend the given embedding of k. I kept that distinction explicit in step 2 and did not add separability or require a k-algebra isomorphism.

The three imported references 09Q1/09Q3/09Q6 describe the intrinsic complete-intersection notion, not an already specified presentation over F. The split supplies that presentation by the existing coefficient-ring, power-series evaluation, regularity/completeness and complete-source surjectivity statements. The new node states the independent general kernel-comparison theorem used in both directions, without any finite-type field hypothesis, neighbourhood assertion, or depth conclusion. It is not a clause of the item restated under a new name. Spreading out the regular kernel is already in the DAG and is reused. The depth conclusion is proved through existing single-element Cohen-Macaulay quotient statements; I did not create an LCI-is-CM restatement.

No unit/chapter record or maintainer-owned metadata was changed. The node inherits the existing sk-i-curve-zero unit and historical ancestry through lem-trf-local-term-locality. The generic algebra facts from sk-thm-p1 are declared in split_report.tool_uses; they implement the existing nodal-completion algebra step and do not replace the unit's geometric route. No SGA source is used.

## Not duplicates

lem-trf-regular-quotient-completion-kernel-test vs lem-trf-completion-local-complete-intersection: the existing item mentions 09Q1 but concerns finite-type algebras over a field, principal LCI neighbourhoods, a residue-field power-series presentation and depth; the new lemma only compares the regular-sequence kernel in a regular local quotient R/I with the kernel of a regular-local surjection onto its completion. It supplies no field presentation, neighbourhood or depth statement.

lem-trf-regular-quotient-completion-kernel-test vs lem-trf-nodal-point-local-criterion: that node mentions 09Q1 in its audit/source context and uses the item, but states a criterion for nodal closed points of one-dimensional schemes using a first Fitting ideal. It gives no comparison for arbitrary regular local rings R,Q and ideal I.

lem-trf-regular-quotient-completion-kernel-test vs lem-weil-pbc-lci-regular-sequence-global-complete-intersection: the existing node spreads an already regular polynomial-local kernel to a principal global-CI neighbourhood. It does not compare completion kernels or arbitrary regular-local presentations. Step 5 cites it instead of creating a second spreading lemma.

lem-trf-regular-quotient-completion-kernel-test vs lem-weil-pbc-global-complete-intersection-local-regular-sequence: the existing node starts with an equation-count/dimension global-CI presentation and concludes regularity of its equations at a prime. It has no completion or independent regular-local presentation. Step 4 cites it instead of creating a second local-equation lemma.

lem-trf-regular-quotient-completion-kernel-test vs lem-weil-pbc-regular-local-quotient-independent-generators: that node assumes the quotient R/I is itself regular local and produces generators independent in the cotangent space. A complete-intersection quotient may be singular; the new statement compares regular kernels through completion and assumes neither quotient regularity nor cotangent independence.

The whole-DAG searches included 09PZ, 09Q1, the source labels ci-well-defined/quotient-regular-ring, and kernel/regular-sequence/completion/complete-intersection terminology. The blueprint searches were `completion local complete intersection`, `complete intersection`, `Cohen`, and `regular sequence`; only four unrelated regular-immersion/coefficient-convention blueprint nodes occurred, and none states either this item or the new kernel comparison. Both same_as lists are therefore empty. The ancestor command returned lem-trf-local-term-locality; the new via chain prepends this item to its inherited via chain.

## Mathlib search assessment

For the new node I ran leanfinder with the explicit equivalence for regular local R,Q, loogle `IsRegularLocalRing, RingTheory.Sequence.IsRegular`, grep `complete.intersection|ci_well_defined|regular.*kernel.*completion|completion.*regular.*sequence` in RingTheory, leansearch with independence/detection after completion, and a second leanfinder phrasing about regular presentations of the completed quotient. All services answered successfully. I read the results: regular-sequence definitions, regularity after localization, standard smoothness, completion objects and one-variable Weierstrass quotient equivalences do not compare arbitrary regular-local kernels after completion. The sole grep hit is the comment in Mathlib/RingTheory/Extension/Presentation/Basic.lean:103; I read lines 90–108. Its `Presentation.dimension` is a count of generators minus relations and assumes no complete-intersection theorem. No new node is a Mathlib leaf. The item's previous searches have the same negative outcome; I also ran the explicit finite-type/closed-point/completed-power-series phrasing for it.

## Review by Q22

I read the item against the complete Stacks dpa proofs and definitions at 09PZ (lemma-ci-well-defined), 09Q0 (lemma-quotient-regular-ring-by-regular-sequence), 09Q1 (lemma-quotient-regular-ring), 09Q3 (definition-lci), and 09Q6 (lemma-check-lci-agrees). I read Algebra 00SC (lemma-lci), 00SG (lemma-lci-at-prime), 00SB (lemma-lci-CM), the coefficient-ring definition and all of the Cohen structure proof 032A, the power-series regularity remark 032C, 02JN and the depth-bound statement/proof 00LK. These are also the sources for the sole new node: 09Q1 supplies the equivalence with a regular generating sequence before completion; 09PZ allows the arbitrary regular local source Q of the displayed surjection. Its statement makes those data explicit and leaves all proof work to its future split, rather than putting a sketch in an unsplit statement.

For step 1 I opened all six cited node statements. Finite type supplies a polynomial surjection; the polynomial regularity node says both Noetherianity and regularity at every prime; the surjective-image node gives Noetherianity of A; the completion-Noetherian node gives it for C; the local-completion node identifies precisely its maximal ideal and residue field; the completion-mod-ideal node states completeness for the extended maximal ideal. The quotient/localization identification is written as an explicit fraction map. No finite-type base-change or excellence assumption is used.

For step 2 the coefficient-ring node explicitly gives a complete local subring with residue isomorphism and maximal ideal p Lambda. I checked that equicharacteristic follows from the nonzero k-algebra structure on C, so p Lambda is zero also in positive characteristic. The field and residue-section conclusion is elementary from that statement. In particular, I did not cite the characteristic-zero-only coefficient-residue-section node for a positive-characteristic input.

For step 3 I opened the Noetherian definition, the power-series field/Cohen structural node, the power-series universal-property node and the complete-source-surjectivity node. The structural statement gives the maximal ideal, completeness and regularity for every field and r>=0. The universal-property statement applies because C is complete and each chosen y_i lies in its maximal ideal. The extended variable ideal is the entire maximal ideal by the choice of generators. Constants hit every residue class. These are exactly the precompleteness/Hausdorffness and surjective-residue hypotheses of the surjectivity node, so a plain definition is not being used for a lifting or surjectivity theorem.

For step 4 I read the entire global/local-CI definition, the polynomial regularity statement, the global-equations regular-sequence statement, and the new comparison statement. The cover supplies one global-CI neighbourhood of the indicated prime. It is nonzero, as required by the global-equations statement. Its presentation has exactly the required dimension m-t. All equations lie in the inverse-image prime. Localizing that presentation gives A, and only then does the comparison apply to psi from step 3. This proves the forward implication rather than citing a new node that asserts it.

For step 5 the structural power-series statement makes the source of the hypothesized quotient a regular local ring, including r=0. The given ring isomorphism composed with the quotient map has precisely the given regular-sequence kernel. The new comparison therefore gives the regular kernel in the fixed polynomial-local presentation from step 1. The existing regular-sequence-to-global-CI node has exactly this input and produces g outside p; a global CI is locally one by its one-open cover. Neither 09Q6's proof nor an off-statement construction is borrowed from any cited node.

For step 6 I opened all six cited statements. The finite-dimension theorem applies to the Noetherian regular local ambient ring; the regular-ring definition gives d maximal-ideal generators; the regular-generators theorem makes them a regular sequence and the depth definition gives the lower bound. I wrote the induction on successive quotients: the previous quotient is Noetherian local and has depth at least its dimension, and the next equation is a maximal-ideal nonzerodivisor by regularity of the original sequence. The single-element quotient-CM node then gives the next quotient's lower bound. Its hypotheses are verified at every index, not assumed from the final quotient. The depth-upper-bound node applies to A as a nonzero finite module over itself; its support is all Spec A, as the fraction argument in the step checks. This proves depth=dimension and the g=1 specialization.

Small-case tests: k itself has r=c=0 and depth=dimension=0; k[t] at (t) has r=1,c=0; k[t]/(t^2) at (t) has the regular hypersurface equation t^2 and depth=dimension=0; k[u,v]/(uv) at (u,v) gives depth=dimension=1. The non-CI square-zero ring k[u,v]/(u,v)^2 fails the regular-kernel test, so the split does not wrongly give it a CI neighbourhood. Over an imperfect field of characteristic p, k[t]/(t^p-a) with a not a p-th power is an inseparable field F: its completion is F (r=c=0), its hypersurface presentation is a global CI, and the proof never asks for an F-section that is k-linear. For the new general kernel statement, I=0 and the empty sequence work; R regular with I generated by one nonzerodivisor includes singular hypersurfaces; Q need not be complete, exactly as in 09PZ; unit ideals are excluded by I contained in the maximal ideal and the nonzero completed quotient.

I checked delivery-errors B through E individually: statement-only new node, self-contained objects and definition dependencies, single-escaped TeX, tag/label sources verified in tags/tags, no invented/unrun searches, no missed Mathlib leaf, filled blueprint references; every non-elementary step input is a cited statement and every quote is verbatim; no new node restates a clause and no dependency points upward into the item; no missing separability, excellence, nonzero quotient, or regularity hypothesis. All six proof-step texts are shorter than 2000 characters. The coefficient construction and the quotient induction are routine arguments from the cited statements, not hidden comparison lemmas; the genuinely nontrivial comparison is the new node. No compiler, Lake, Lean writer or other agent was used.

## Unfinished work

No part of the item's one-level split remains unfinished. The new kernel-comparison node is intentionally unsplit, as required by the stage-1 brief. Delivery validation follows below.
