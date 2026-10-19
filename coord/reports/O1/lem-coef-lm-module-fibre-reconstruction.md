# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-lm-module-fibre-reconstruction.json`: statement item, now split into six elementary finite-list calculations; no Mathlib match.
- No new nodes and no Mathlib leaves. The statement, statement dependency, historical blueprint ancestry, chapter and unit are unchanged. Existing search records are retained; the five searches of this attempt are appended.
- `citations.json`: one verbatim statement excerpt for each of the three step/node citations.
- `check_small_cases.py`: sandbox-only exhaustive finite combinatorial check; `write_split.py`: sandbox-only JSON-writing script; `searches.jsonl`: required search tool log. No Lean was written or compiled.

## Attachments

None. Searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item id and its blueprint tag, module/fibre reconstruction, LMPrism, LMArrow, LMObject, LeftModuleOperadic, left-module operads and ordered fibres found no declaration giving this statement. In particular the stage-2 Lean record on the parent prism item is not evidence of this item's completed proof. The read-only upstream master is not used as completion evidence.

## Sources wanted

WANTED: Jacob Lurie, Higher Algebra, September 18, 2017, Notation 4.2.1.6 (printed p. 506), Proposition 4.1.2.11 (pp. 463–464), Construction 4.2.2.6 and Remark 4.2.2.8 (pp. 514–515), for lem-coef-lm-module-fibre-reconstruction; archive in literature/.

I read these passages in the [online 2017 PDF](https://people.math.harvard.edu/~lurie/papers/HA.pdf). The operator formula and module-input convention agree with the DAG definition. The cartesian calculation is abbreviated in the source; the six-step expansion here is an agent proof, and proof_origin.by is agent. No download or literature change was made. No Stacks tag states this finite LM-operator calculation. No SGA source is used.

## Errors and corrections

No statement dispute: every clause is true as written. The item previously had no proof. Its parent lem-coef-lm-prism-approximation step 10 already cites exactly this module-target reconstruction. I supplied the missing calculation without changing the parent's route or unit metadata. The significant distinction from the neighbouring algebra-target lemma is that alpha(n)=s is NOT required: all later algebra fibres concatenate into the module-output fibre. The module input guarantees a nonempty tail, which bounds lambda(s) by r rather than r+1.

The specified main-20261015 ancestor text was read at `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.md`; its historical master location is different. I preserved the existing blueprint ancestry and maintainer-owned unit binding. This item is not a unit key statement and requires no unit realized-field change.

## Unfinished work

None for the requested one-level split. The source archive remains wanted. There are no new unsplit nodes.

## Mathlib and duplicate search

The required msearch command ran LeanFinder with two distinct phrasings, Loogle, Mathlib grep, and LeanSearch. All five services returned successfully; every query is recorded exactly as run in searches.jsonl and mathlib_searches. I read all hits. The plausible candidates inspected in source were SimplexCategory.Hom.mk/toOrderHom/ext' (Defs.lean:77–96), OrderedFinpartition (FaaDiBruno.lean, structure and its surrounding explanation), and SimplexCategory.II.map' (SimplicialObject/II.lean). Bundling a supplied monotone map is not this reconstruction; the Faa di Bruno partitions have nonempty parts ordered by maxima and permit nonconsecutive parts, unlike this conclusion. No hit gives the LM equation or final module tail. No Mathlib leaf was asserted.

DAG searches included the item tag and fibre/reconstruction keywords, ordered fibre, interval fibre, and HA references 4.1.2.11/4.2.2.8. Blueprint_refs ancestor returned prop-coef-integral-exceptional-adjoint; searches for ordered fibre and interval fibre returned no blueprint match. The broader module fibre search returned only a finite-etale trivialization statement, on different objects. I read the neighbouring algebra reconstruction statement and the parent's proof steps 9–13; the former has an algebra target and a terminal endpoint hypothesis, and is not a duplicate of this module-target lemma. No new node was created, so no new/existing duplicate pairs arise.

## Not duplicates

No new nodes; no pairs requiring justification.

## Review by N1

I read coord/delivery-errors.md sections B–E in full and checked the split against the actual statement of def-coef-left-module-operadic-encoding, not its proof. I read the item, the chapter and unit records, the current blueprint ancestor text, and the parent prism's factorization argument. In the online Higher Algebra source, I checked the LM morphism conditions in Notation 4.2.1.6, the increasing block/tail formula in Construction 4.2.2.6, the approximation comparison in Remark 4.2.2.8, and the abbreviated prefix-cardinality cartesian-lift calculation at the end of Proposition 4.1.2.11. These give the context, while the argument written here supplies its omitted finite calculation. There are no new nodes needing separate literature checks.

Step 1 cites the definition's explicit rule that composition substitutes and concatenates ordered fibres. I checked arrow types X_0(r) to X_0(s) to X_0(n), the algebra index ranges, and the final module-output range. The unique module input is p+1 in B_beta and beta(q)<=p ensures that its module fibre is nonempty. Equality of ordinary arrows gives equality of ordered lists, not only equality of underlying sets.

Step 2 uses step 1 and alpha(0)=0 to concatenate ALL C_j in order. I checked that the ranges continue through s+1 even when alpha(n)<s; no fibre is discarded by B_alpha. Matching the complete suffix list identifies exactly the discarded inputs, so the proof does not infer a pointed map from cardinalities alone. This is a direct finite-list calculation and needs no further theorem node.

Step 3 reads each C_j from its actual positions in the complete list. Its start position is one more than the sum of preceding lengths; its end is that sum plus its own length. This proves increasing interval fibres even for initially unordered fibres of h, and allows empty C_j. The module fibre is the remaining suffix. No separate comparison or identification lemma is hidden here: the entry at position k is explicitly delta(0)+k.

Step 4 cites the same definition's module-fibre condition, quoted verbatim in citations.json: there is exactly one module input, last. Because the source has precisely r+1 as its module input, the final fibre has length at least one. Counting step 2 gives lambda(s)=r+1-|C_{s+1}|<=r. Nonnegative lengths give monotonicity and all lower/upper bounds; I did not assume surjectivity or a terminal endpoint for alpha.

Step 5 concatenates the first i composite algebra fibres, counts them, and obtains lambda(alpha(i))=delta(i). For i=0, alpha(0)=0 makes both prefix lists empty, so the initial identity is included rather than inferred from a nonexistent algebra output. This uses previous steps and only the elementary length of an integer interval. The case alpha(n)<s is included because the leftover outputs belong to the module composite.

Step 6 cites the definition's description of an arrow as a pointed map with ordered fibres. All non-basepoint fibres and discarded inputs were already identified, so this gives equality with B_lambda. I separately checked s=0, n=0 and empty algebra fibres in the text. The hypotheses were neither strengthened nor weakened.

For the small-case check I enumerated every ordinary LM arrow for 0<=r,s<=3, including all assignments of algebra inputs to outputs or the basepoint, every order of each algebra fibre, and every order of the algebra entries before the unique final module input. For every monotone alpha with alpha(0)=0 and every monotone delta, with 0<=n<=2, I retained exactly the arrows satisfying the composite equation. All 1340 satisfying cases passed every stated conclusion. They include 30 cases s=0, 121 cases n=0, 34 cases r=0, 1185 cases with an empty algebra fibre and 830 cases alpha(n)!=s. The finite enumeration supports the hypothesis audit; the general proof is the explicit list calculation above.

Against B: the statement is self-contained using the existing definition, TeX is singly escaped in JSON, source places are precise, no new leaf or node is fabricated, existing fields are retained. Against C: each external fact is precisely in the cited definition and each citation has a verified substring quote; other steps calculate from earlier steps. There are no new edges to downstream statements and no off-unit tools. Against D: the proof is expanded here rather than moved to a restatement child; no circular inference occurs, and no induction is asserted without a base or step. Against E: the tail bound uses the module input, the alpha endpoint is exactly the one assumed, ordered equality is retained throughout, and no unspecified transport or compatibility argument remains. Every proof step is below 814 characters, so none triggers the long-step review threshold. The six steps are routine substitutions, positions and finite sums within this lemma, not concealed non-elementary results.
