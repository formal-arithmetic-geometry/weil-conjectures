# Stage-1 report: lem-sfb-projective-coordinate-koszul-sequence

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-projective-coordinate-koszul-sequence.json: existing statement node, split; no full Mathlib match.
- citations.json: verbatim statement quotations for every citation of all four proof steps.
- report.md and searches.jsonl: report and six actual logged Mathlib searches.

New nodes: 0. New Mathlib leaves: 0. The actual proof consists of coordinate-map gluing, the square-zero computation, a signed chart contraction, and the existing local-lifting exactness criterion.

## Attachments

None. I searched the project source by the blueprint tag and coordinate/Koszul concepts and read WeilConjectures/AlgebraicGeometry/ProjectiveSpace/Koszul.lean. AlgebraicGeometry.ProjectiveLine.koszul_shortExact proves only n=1, with a different ordered signed presentation; it does not give every dimension of this item. AlgebraicGeometry.ProjectiveSpace.twistMulX and its local invertibility are useful related results, but do not prove the whole complex exact in arbitrary dimension. No Lean file was written or compiled.

## WANTED

None. The sources used are present locally.

## Findings and corrections

The item's statement is correct and was retained byte for byte. I read Stacks Tag 0BQS, perfect-lemma-construct-the-next-one, including its graded Koszul and sheafification proof. Its intermediate graded display has a binomial with n rather than n+1; the actual lemma and the final display have the required n+1. Our basis-indexed construction supplies exactly that rank, so this typographical problem in the intermediate proof does not require a statement dispute.

Below the unit level I use a direct chart proof of the same sequence rather than importing the graded regular-sequence resolution and its sheafification machinery. This is an agent-written proof and is marked as such. It does not change the direct-image unit route: it is an algebraic prerequisite for the existing projective-twist generator argument. I read the chapter/unit records and the latest blueprint's section, unit and direct-images proof. The imported unit record refers to sec-six-functors, whereas the current blueprint locates this unit under sec-six-functors-basics; this is inherited metadata, not changed here.

The blueprint ancestor script returns None for this item's inherited creation chain. The item's existing from.node is already null, with a long explicit from.place and via chain giving its direct-images ancestry. I preserved it rather than inventing a blueprint identity; from.place already specifies Tag 0BQS. The split_report records the precise prerequisite and the current blueprint reading. Blueprint searches for coordinate Koszul, exact sequence twists, Koszul contraction, ringed space exactness and twists found no other blueprint statement of the complete item; same_as stays empty. Whole-DAG keyword/tag searches found the item and its generator parent for 0BQS, and found the existing generic local-lifting theorem, which is cited rather than recreated.

## Not duplicates

No new nodes. The existing lem-weil-pbc-ringed-space-module-exactness-local-lifting is exactly the generic theorem needed for the last step. No algebraic contraction node is created: its entire finite signed-matrix verification is written in the proof.

## Review by N5

I read delivery-errors B through E in full and checked the split against their substantive failure cases. There is no unsplit new node, no hidden proof in a statement-only node, no new definition, and no relabelled clause. The item uses its actual signed differentials, not merely an abstract existence of some exact complex. Sources are local and Stacks places use tag and label. No SGA source is used.

For step 1 I opened def-pc-proj, def-pc-projective-space-twist and def-weil-sheaf-of-modules-category. The first gives homogeneous-prime points and standard opens; missing a coordinate is exactly the definition of a Proj point for this polynomial ring. The second gives all integer twist bases and their transition factors. I checked the displayed overlap identity by cancelling the unit x_k/x_l, so the local coordinate maps glue with the stated degree shift. The module-sheaf node defines precisely the sectionwise linear maps commuting with restrictions used here. Finite direct sums of the local bases give the displayed binomial ranks. citations.json quotes these actual statements.

For step 2 I independently checked the two insertion orders for j<l. Their exponents differ by one, their scalar factors commute, and every off-diagonal term is paired. This proves square zero for the stated maps and uses no unstated Koszul exactness theorem.

For step 3 I used only the same twist trivializations, quoted again in citations.json. I checked both cases k outside I and k inside I. In the latter the exponents of the two off-diagonal contributions differ by [j<k]+[k<j]=1, while the diagonal contribution is t_k=1. This proves the complete contraction formula in every degree. The contraction is local to a chart; the proof never asks it to glue globally. This is a basis computation of 1189 characters, not an invocation of a general homotopy lemma; it hides neither an identification of derived objects nor a separate comparison lemma. Every step is shorter than 2000 characters.

For step 4 I opened lem-weil-pbc-ringed-space-module-exactness-local-lifting and read its full statement, its Stacks source in modules.tex (01AF, modules-section-kernels; 01AG, modules-lemma-abelian), and its project-source theorem. Its clause (2) states exactly that cycles locally lifted under the preceding differential imply exactness at the middle module sheaf. I apply it to the ringed space underlying X, using the cover W intersect U_k and the explicit lifts h(s). Square zero was proved in step 2. No affine/global-sections exactness or stalk-forgetful comparison is smuggled in. The final degree uses the outgoing zero map, and at degree zero the contraction and sheaf separation show the kernel is zero. This closed generic tool is declared in split_report.tool_uses for transparency even though its closed status already exempts it from unit-route restrictions.

Small-case checks: n=0 is 0 -> O(a) -> O(a+1) -> 0, with coordinate map the identity in the sole standard chart. For n=1 the chart identity gives the ordinary three-term Koszul sequence, and for arbitrary n both endpoint identities are included. The zero ring gives the empty scheme, whose sheaves make the conclusion vacuous. The formulas use additive inverses and are valid in characteristic two, with nilpotents or zero divisors, for negative a, and without Noetherian hypotheses. In addition to the symbolic argument, I evaluated the formal polynomial-coefficient matrices over integers, leaving all t_j other than t_k indeterminate, and checked delta squared is zero and delta h+h delta is the identity for all 1538 basis/chart cases in ranks 1 through 7. This was Python arithmetic in the sandbox workflow, not Lean or a compiler test.

I read the results of all six msearch invocations and retained their actual queries and digests. The second wording asked for the more general unit-coefficient contraction. Semantic hits concern cotangent exactness, projective resolutions, Clifford algebra contraction and alternating constant complexes. I read the relevant Mathlib projective-resolution/exactness definitions and the grep hits: LocalCohomology lists Koszul homology as future work, RegularSequence lists Koszul regularity as TODO, and the remaining hit is a differential-geometric Koszul connection. None is a one-line specialization giving this complex. The original creator's searches remain untouched and six freshly logged searches are appended; no unrun search has been added.

## Unfinished work

None in the stage-1 split. The required server dry run exited 0 and printed OK at 4216a6dcdd0: preflight passed (including the DAG and split checks). This final report update is checked again before the authorized direct push.
