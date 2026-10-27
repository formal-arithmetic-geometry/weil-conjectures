# Q26 stage-1 report: lem-sfb-space-single-complex-rhom-inheritance

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-single-complex-rhom-inheritance.json`: statement, split; five proof steps, eight distinct existing proof dependencies; no complete Mathlib match.
- `citations.json`: twelve entries, one for every use in every proof step, with literal statement excerpts.
- `report.md`: this report. `searches.jsonl` is the unmodified msearch output; `write_split.py` is a sandbox-only preparation script.

New nodes: 0. New Mathlib leaves: 0. Statement and statement dependencies retained unchanged. No unit record needs realization changes: this supporting node is not the unit's key statement.

## Attachments

None. Searches in `lean/WeilConjectures/` for the exact blueprint identifier and for single-complex/internal-Hom/inheritance notions found no declaration stating this algebraic-space result. The existing SingleComplexInheritedTensorCondition theorem concerns schemes and tensor inheritance, not this item. Neither that result nor ringed perfect-duality comparisons alone attach all clauses of the item.

## WANTED

None. All mathematical sources used are present in literature/stacks-project. The inherited brief references `coord/dag-sync.md`, which is absent in this read clone; the explicit live repository and direct delivery instructions in this task were followed.

## Imported material and changes

The node was unsplit, with empty proof, on first inspection; the sandbox had no item or earlier split/report/search log. I copied its node and preserved its statement, source, statement dependencies, import/provenance information and earlier Mathlib searches. There is no repair note for the item. I added real msearch queries in this sandbox and read every result, including a second semantic phrasing. The semantic hits concern ordinary dual module base change or scheme morphism properties; Loogle gives general derived-category localization, and the grep hits are substring collisions. I read the ordinary-module candidates in Mathlib/LinearAlgebra/Dual/BaseChange.lean (including IsBaseChange.toDualBaseChange) and Contraction.lean (dualTensorHomEquiv, line 281): they do not give the geometric-stalk condition or derived sheaf Hom.

The statement agrees with Stacks 0DKI(2), with the arbitrary target algebraic-space formulation supplied by 0DKG and quasi-coherence from 0A8A. There is no statement dispute. In particular, no quasi-compactness or quasi-separatedness is introduced: the direct-image conclusion of 0DKH is never used.

The source says "Some details omitted" for the perfect Hom calculation. I supplied those details by the equivalent perfect-dual tensor calculation: the already existing tensor-inheritance node handles the stalk argument, while a short uncurrying computation checks precisely the evaluation-defined coefficient morphism. The proof is honestly marked agent-written with its Stacks source; the omitted calculation has not been replaced by a new node restating this item.

## Blueprint and duplicate searches

Read the chapter record, the assigned unit record, and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and direct-images proof. The supporting-input route recorded on the item (direct-images proof (3), the chain through Hom representability and 08JQ, applying 0DKI(2) before 0DKH) is preserved. The unit record is historical and its source is an older blueprint path; I used latest when reading blueprint text and did not edit that record.

`tools/blueprint_refs.py ancestor` reports `from.node=None`; this is already inherited through the complete recorded via chain and is preserved, as in the accepted neighbouring pullback-comparison node. The inherited place is specific and was not unspecified. The split_report names it and the current proof's role. Searches of the whole DAG and blueprint for single complex, internal Hom, perfect duality, and source tags found no blueprint statement equivalent to this whole result; same_as remains empty. Existing tensor inheritance, ringed-site perfect duality, ringed-topos perfect internal-Hom pullback, and the algebraic-space quasi-coherence theorem were reused rather than duplicated. No new node means there are no same-tag pairs requiring a Not duplicates list.

## Review by Q26

I read spaces-perfect.tex at lemma-single-complex-base-change-condition-inherited (0DKI), including all three clauses and its entire proof, the definition and etale locality of equation-bc in 0DKG, and lemma-quasi-coherence-internal-hom (0A8A). I read sites-cohomology.tex at lemma-strictly-perfect-pullback (08H3), lemma-perfect-pullback (08H6), lemma-dual-perfect-complex (08JJ), remark-prepare-fancy-base-change (08JF), and lemma-pullback-tensor-product (07A4). The latter two specify the exact comparison, rather than merely an abstract existence of an isomorphism. I also checked the adjunction and symmetric monoidal statements as recorded in the cited DAG nodes.

For step 1 I opened the statements of lem-weil-pbc-strict-perfect-ringed-pullback-model, lem-sfb-ringed-site-perfect-duality and lem-sfb-space-pseudocoherent-rhom-quasicoherent. The first gives the K-flat representative comparison and preservation of the specified finite-free retracts, so its local application proves perfectness of LP without any flatness hypothesis on h. The second states that the dual E is perfect. The third has exactly the perfect-source/arbitrary-quasi-coherent-target case needed three times, including with target O_X; I never invoke its pseudo-coherent bounded-below alternative. This verifies E, J and J' are quasi-coherent with the bounds present in the item, namely none on K or K'.

For step 2 I reread the perfect-duality statement (natural canonical evaluation isomorphism for every N), the full evaluation-normalized ringed-perfect-internal-hom-pullback statement, and the monoidal comparison statement including its unit comparison. The perfectness just established licenses both instances of perfect duality. The pullback comparison at O_X gives the precise isomorphism r with its pairing e_L; it is not an arbitrary dual identification. This constructs actual derived isomorphisms a and b. No degreewise replacement of a derived statement is made.

For step 3 I opened the entire statement of lem-sfb-space-single-complex-tensor-inheritance. Its rings R,A,B,C and D, canonical coefficient and lack of boundedness/flatness assumptions are identical to this item's setup. Step 1 supplies its extra quasi-coherence input E. It proves exactly the stalk isomorphisms for lambda, not for psi; the next two steps are necessary to connect them.

For step 4 I checked each of the four cited statements: perfect duality specifies a by evaluation; the pullback-Hom comparison specifies alpha as the transpose of pulled-back evaluation; monoidal comparisons preserve associators, unitors and signed symmetry; the closed symmetric monoidal statement explicitly says the transpose is a bijection with the specified evaluation counit. I uncurried both composites. After substitution of e_L and the evaluation equation for a they are both e_L tensored with phi, with the same factor reordering. Thus the equality is a routine adjunction calculation from these statements, and elementary=true refers to that calculation, not to the non-elementary existence of the cited isomorphisms. The step is 1017 characters and hides no separate derived comparison theorem.

For step 5 I opened def-sfb-space-single-complex-stalk-condition. It defines beta by the canonical base-derived tensor cohomology map followed by the pullback-stalk identification and phi. Consequently applying those functors to the previous coefficient equality gives the explicitly displayed square; this is just naturality of the definition, not a theorem borrowed from the proof of a definition node. Functors carry the chosen inverses of a,b to inverses. The displayed equation then proves invertibility of beta_psi.

The three off-unit citations are declared in split_report.tool_uses: the generic strict-perfect ringed-pullback representative, symmetric monoidal derived comparisons, and the closed tensor-Hom adjunction. They serve only as general category/sheaf tools, not as a replacement for any geometric unit step. All other theorem citations are in the assigned unit. I independently traversed the statement/proof dependencies of these existing inputs to confirm none reaches this item, so the new proof introduces no cycle.

Edge cases checked: P=0 gives zero J,J' and their unique invertible zero-object comparison; P=O_X recovers the original condition; P a shift changes degrees through the signed evaluation constraints, which are respected by the monoidal comparison. A non-flat ring change, for example Z to Z/2, does not turn L into underived pullback: the strict-perfect source is K-flat, and all other tensors stay derived. Unbounded K and K' are explicitly permitted by both perfect-duality and the tensor-inheritance statement. The empty source space makes the stalk claim vacuous and causes no issue. Bounds and ranks can vary on the perfectness cover, and no finite subcover is chosen.

I checked delivery-errors B through E against the files: no new statements with missing notions or hidden proofs, no unrun searches, no source meaning defined by tag alone, no uncited non-elementary step, no use of a cited node's proof in place of its statement, no relabelled clauses, no added hypotheses, and no SGA source. Each cited statement excerpt in citations.json is literal and contains the part actually used. All five proof steps are shorter than 2000 characters; no long step conceals another lemma. Nothing remains mathematically unfinished in this split.

## Validation

The required deliver.py --no-push completed successfully and wrote the durable .stage1-ready.json receipt. Server preflight includes check_dag.py and review_split.py; no compiler or local check script was run. Direct delivery follows the final dry run on this report.
