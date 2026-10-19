# Q40 stage-1 report: lem-trf-scheme-etale-quasi-coherent-kernel

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-scheme-etale-quasi-coherent-kernel.json`: statement, split; no exact Mathlib match. Four proof steps, using existing DAG nodes only. The statement and its four statement dependencies are unchanged.
- `citations.json`: 11 entries, one per step/node citation; every excerpt was verified as a literal substring of the cited statement.
- `report.md`: this report. `searches.jsonl` is the search command's actual log; `prepare.py` is item-specific sandbox preparation code.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter file changed. No Lean was written and no compiler, Lake, or build tool was run.

## Attachments

No attachment for the item. The existing declaration `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_kernel` belongs to the existing node `lem-weil-pbc-quasi-coherent-module-kernel`, in `WeilConjectures/AlgebraicGeometry/Modules/QuasicoherentKernel.lean:165`. I read its signature and proof (lines 162–179). Its inputs are Zariski `X.Modules`, so it does not state the item on the small etale site. The existing node already records the declaration as transitively closed. The new split uses that existing node only for the Zariski kernel.

Searches for the exact blueprint tag and the notion in the project Lean source found no exact etale-kernel declaration. The upstream master is reference material only; it was not used as evidence of a finished proof.

## WANTED

None. All sources needed for this split are available in the repository.

## Corrections and findings

The item was statement-only, with no proof. It is true as imported. Stacks `descent.tex`, Tag 0GNB (`lemma-properties-quasi-coherent`), proof of (3), writes the etale morphism as the association of a Zariski morphism and transfers its kernel via Tag 06VE (`lemma-equivalence-quasi-coherent-limits`), (1) and (5). The split expands the kernel part of this transfer rather than treating the equivalence as automatically exact in the ambient sheaf category.

I replaced inherited search entries that explicitly said they were not run with searches actually executed through `msearch.py`. The item was searched in LeanFinder, LeanSearch, Loogle and Mathlib grep, including a second wording about exactness of the association. Two malformed Loogle queries reported unknown identifiers and are recorded as inconclusive; the qualified kernel query completed with zero hits. None of the returned category/module infrastructure states the etale quasi-coherent kernel assertion. In particular, the generic sectionwise finite-limit theorem is not quasi-coherent kernel closure. The actual search log is retained unchanged.

Whole-DAG searches included tags 0GNB, 06VE, 03M1, 03DX, 01IC, kernel/quasi-coherence wording, and the Zariski declaration name. Whole-blueprint searches through `blueprint_refs.py` for `quasi-coherent kernel`, `kernel quasi-coherent`, `0GNB`, and `Kernels` found no blueprint statement identifying the present assertion. The existing equivalence, Zariski kernel, tensor-pullback, stalkwise-flat kernel, global-sections and site-module-limit nodes suffice. No elementary specialization or clause of this item was made into a new node.

The blueprint's historical ancestry is retained. This item is the scheme kernel input at the end of Stacks 03M9's affine-target pushforward paragraph, introduced by the reviewed parent split. It is a foundational descendant of `lem-trf-local-term-locality`, not a replacement for its normal-cone/Varshavsky argument. No prohibited SGA source is used.

## Unfinished work

None for this one-level split. The reused nodes retain their own existing proof/Lean states. The independent maintainer review and the downstream proof tasks are outside this delivery.

## Review by Q40

I read `descent.tex` at Tag 03DX, proposition-equivalence-quasi-coherent (especially (2) and its fully faithful/essential-surjectivity proof), Tag 06VE, lemma-equivalence-quasi-coherent-limits (especially the proof of (5)), and the complete statement and kernel paragraph of Tag 0GNB, lemma-properties-quasi-coherent. I also read `schemes.tex` Tag 01IC, lemma-kernel-cokernel-quasi-coherent, `modules.tex` Tag 01AH, lemma-limits-colimits (1), and Tag 02N4, lemma-pullback-flat with its proof, `morphisms.tex` lemma-etale-flat, and `sites-modules.tex` Tag 03DB, lemma-limits-colimits with its limits proof. There are no new nodes requiring a separate source review.

Step 1 uses the equivalence node's actual statement: it is an equivalence between quasi-coherent Zariski modules and quasi-coherent module sheaves on the *small* etale site. Essential surjectivity supplies F and G and full faithfulness supplies psi after conjugating phi. I separately read `lem-trf-zariski-etale-tensor-sections`: its final sentence gives the action on morphisms as Gamma(U,u*psi), not just an object-level comparison. Its sheafification is already the associated sheaf in the equivalence. No pushforward clause, separatedness assumption, or invertible-module comparison of the larger equivalence statement is used here.

Step 2 uses precisely `lem-weil-pbc-quasi-coherent-module-kernel` for F,G, which are Zariski modules at this point. Its hypotheses are a scheme and two quasi-coherent modules; all hold by Step 1. This is where the Zariski result legitimately applies. Applying the equivalence to K gives quasi-coherence of K_et by the *forward* clause of its statement.

Step 3 is the essential exactness check. I opened both definition statements: `def-weil-etale-morphism` includes flatness, and `def-weil-flat-morphism` says this is flatness of every scheme stalk map. Thus every etale test u:U->T meets the stalkwise hypothesis of `lem-sc-stalk-flat-tensor-pullback-kernels`. I read that node's statement in full: it requires an additive functor with the tensor object and inverse-image/change-of-rings map formulas. The statement of `lem-pc-module-pullback-adjunction` supplies those exact formulas, and the proof step verifies additivity explicitly on local tensors, so it does not assume this extra functor condition. The kernel theorem applies to arbitrary module morphisms and supplies preservation of the diagram (psi,0). `lem-sc-global-sections-left-exact` says Gamma(U,-) preserves kernels for every scheme U; it has no affineness or quasi-coherence requirement. This gives the claimed component kernel without assuming exactness on the right. These are generic tools, declared with reasons in `split_report.tool_uses`, not changes of the unit route.

Step 4 again uses the tensor-sections node's map formula to match the inclusion with the component computed in Step 3. The statement of `lem-weil-pbc-module-sheaves-limits-sectionwise` supplies module-sheaf limits as sectionwise module limits, including evaluation preserving them. Its index category is finite here, so its smallness hypothesis is satisfied. The proof writes out how the factorization and its inverse commute with restrictions: the inclusion is natural and injective and each element has its unique kernel preimage. Thus the result is an isomorphism of module sheaves, with their specified scalar actions, not just an unrelated family of group bijections. Its target is exactly the kernel in the item, and Step 2's quasi-coherence passes across this isomorphism.

Against delivery-errors B: no new statements, definitions, unproved-data constructions, proof-carrying unsplit nodes, or unverified Mathlib leaves were introduced. The item introduces its objects and has the required existing definition dependencies; the source tags and labels were checked in the source and tag table. TeX uses single backslashes after JSON decoding. Its blueprint place and same_as field are complete, and the report explains the ancestry. No candidate Lean declaration was falsely attached across coefficient sites.

Against C: I read the statement of every node cited in all four steps and generated a verbatim quote for every use, rather than quoting a node's proof or a nearby theorem. Every substantive transfer fact has a cited node; the only inline arguments are functor additivity on tensors, transport along chosen isomorphisms, and the uniqueness calculation for restrictions. The generic off-unit tools are explicitly declared. The server `review_split` check passed with zero new nodes; the full dry run also checks the delivered dependency graph for cycles.

Against D: this is the argument of 0GNB(3), expanded through the existing tools for 06VE(5). No new node restates a clause or moves the whole theorem elsewhere. Every non-elementary proof step is under 1000 characters, hence below the 2000-character long-step review threshold; none hides a separate comparison theorem, since the two map/comparison inputs are cited explicitly.

Against E: the argument allows arbitrary T and arbitrary etale U, with no quasi-compactness, separation, Noetherianity, finite presentation of F or G, or affineness hypothesis. Only the flatness of the site object u is used. I checked the zero morphism (kernel F), the identity (zero kernel), the empty scheme (all components zero), and arbitrary modules on an affine scheme (flat etale base change of the ordinary kernel). Non-affine U is covered by the cited global-sections kernel result, not an exactness-on-affines assertion. The small etale restriction is essential: replacing it by the big site would allow Spec(F_2)->Spec(Z), and pulling back multiplication by 2 would destroy injectivity. The proof does not make that invalid generalization. No statement dispute or source error arose, and no statement was weakened.
