# Worker report: def-sfb-finite-upper-star-comp

## Files written

- `dag/nodes/sec-proetale-coefficients/def-sfb-finite-upper-star-comp.json`: retained the imported statement and dependencies and split its proof into one complete step.
- `citations.json`: three verbatim quotations for the single proof step.
- `report.md`: this report.

## Attachments

The source contains `AlgebraicGeometry.ProEtale.upperStarComp` in `WeilConjectures/SixFunctors/ProEtale/UpperLowerStar/Defs.lean:344`, but the dispatcher explicitly said the previous attachment proposal was refused and must not be repeated. I therefore split the item and cite the generic adjunction lemma through the DAG.

## WANTED:

None.

## What was wrong or corrected

The imported node had an informal proof paragraph but omitted the generic compatible-uniqueness lemma that justifies “left adjoints are unique ... and taking conjugates.” I retained the statement, added `lem-weil-pbc-conjugate-iso-unit-equation` to `proof_deps`, and made the step explicitly apply it to the lower-star composition isomorphism. No new node was needed because that existing node is a Mathlib leaf. The required whole-blueprint search found no duplicate statement.

## What I could not finish

Nothing remains unfinished in this split. No Lean file was written or compiled, and no live project or launcher file was modified.

## Review by NL

I read `coord/brief-stage1.md`, `stages/1-dag.md`, `SETUP.md`, `GOAL.md`, `coord/dag-sync.md`, and delivery-errors B–E. I read the item's source markdown and proof markdown, the enclosing chapter and unit route, and the full statements of `def-sfb-finite-upper-lower-star-adjunction`, `def-sfb-finite-lower-star-comp`, and `lem-weil-pbc-conjugate-iso-unit-equation`. The first supplies the pullback/pushforward adjunctions; the second supplies the right-adjoint composition isomorphism; the third states exactly that an isomorphism of right adjoints gives a unique compatible isomorphism of left adjoints.

I checked Mathlib `CategoryTheory.Adjunction.CompositionIso.lean` at `leftAdjointCompIso` (line 72) and `conjugateEquiv_leftAdjointCompIso_inv` (lines 82–85), which corroborate the existing DAG lemma. For the proof step, the composite-adjunction right adjoint is `(h₂)_* ∘ (h₁)_*`, and the lower-star node identifies it with `(h₂ ∘ h₁)_*`. Applying the cited uniqueness lemma with this right-adjoint isomorphism gives the unique pullback isomorphism in the required direction and its conjugate characterization. I checked that each cited node contains exactly the clause used; these are the three quotations in `citations.json`.

I ran and read LeanFinder, LeanSearch, Loogle, and Mathlib grep searches in both the direct pullback wording and the abstract right-adjoint-conjugation wording. The searches are retained in `mathlib_searches`, including the two Loogle identifier failures as unavailable. These searches confirm the generic Mathlib calculus underlying the existing DAG tool, but the item itself is split because the dispatcher prohibited repeating the refused attachment. I checked the identity cases `h₁ = id` and `h₂ = id`, where the same uniqueness/conjugation construction yields the expected unit comparators. The proof has one non-elementary step, cites all three required nodes, and `citations.json` certifies every citation verbatim.

## Source error

STATEMENT-DISPUTED: the imported statement calls the displayed forward pullback compositor the conjugate of the *inverse* pushforward compositor. This reverses the required type. Write $L_1=(h_2\circ h_1)^*$, $L_2=h_1^*h_2^*$, $R_1=(h_2\circ h_1)_*$ and $R_2=(h_2)_*(h_1)_*$. Stacks categories.tex, Tag 0B65, `lemma-transformation-between-functors-and-adjoints`, explicitly takes a transformation $u_2\to u_1$ to $v_1\to v_2$. Consequently the mate of $R_1\to R_2$ goes $L_2\to L_1$, whereas the displayed compositor goes $L_1\to L_2$. This is a type check, independent of any nontrivial geometry.

The construction intended by the blueprint is confirmed in the read-only upstream master file `WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/UpperLowerStar/Defs.lean`, definition `ProEtale.upperStarComp`: it takes the conjugate of `lowerStarComp.symm` and then takes a final `.symm`. The slopmaster2 counterpart, `WeilConjectures/SixFunctors/ProEtale/UpperLowerStar/Defs.lean:344–348`, has the same construction. These sources establish the intended direction; no upstream sorry declaration is treated as a finished proof and no attachment is proposed. Mathlib `CategoryTheory/Adjunction/Mates.lean:275–280, 425–435` and `CompositionIso.lean:72–85` independently verify the direction. The blueprint's unit only asks for compatibility with composition, so its route and statement remain intact.

## Statement corrected

Changed “of the inverse of the composition isomorphism” to “of the composition isomorphism”, and specified that conjugate means the mate with identity intervening functors of `def-weil-pbc-adjunction-mate`. Equivalently, the intended compositor is the inverse of the conjugate of the inverse pushforward compositor. No geometric hypothesis, coefficient restriction or conclusion was added or removed.

The current DAG has two citers, both read: `lem-sfb-eta-id` explicitly uses the *inverse* pullback comparison as the mate of the inverse pushforward comparison, which is consistent with the correction; `det-prop-sfb-qlbar-colimit-x-pullback` uses the pullback composition map as the mate of the right-adjoint composition map, also consistent. Neither citer needs an edit. The earlier worker report and its review above describe the pre-repair split and are retained as requested; this second reading supersedes their direction claim.

## Earlier second reading (a previous round; superseded)

- Item statement: checked every morphism, functor and arrow against the main-20261015 statement/proof markdown, the enclosing unit/chapter, Stacks 0B65 (`lemma-transformation-between-functors-and-adjoints`) and the upstream `upperStarComp` construction; repaired the inverse-direction error identified above, keeping arbitrary scheme morphisms and the coefficient categories of the cited adjunction.
- Step 1: checked `def-sfb-finite-upper-lower-star-adjunction` and `def-weil-pbc-composite-adjunction` statements, Stacks 0DV0 (`lemma-compose-counits`), and Mathlib `Adjunction/Basic.lean:567–586`; the explicit two Hom bijections have sheaves on R, S and T in the required order and give exactly $L_2\dashv R_2$. Pass; no uncited composite-adjunction construction remains.
- Step 2: checked `def-sfb-finite-lower-star-comp` and `lem-weil-pbc-conjugate-iso-unit-equation` statements in full; their directions are respectively $R_2\to R_1$ and $L_1\to L_2$, and every category, adjunction and isomorphism hypothesis is supplied by Step 1. Pass; uses only the stated unit equation, uniqueness and invertibility, not a fact hidden in the cited proof.
- Step 3: checked the full inverse-mate formula of `def-weil-pbc-adjunction-mate`, specializing its two intervening functors to identities and reversing the labels of the two adjunctions. The written component formula, naturality of the unit and triangle identity give the unit equation in two equalities, so the statement of `lem-weil-pbc-conjugate-iso-unit-equation` identifies this mate with Step 2's isomorphism. Pass; this is the elementary calculation previously omitted by “conjugate characterization in that node”.
- New nodes: none. The sandbox contains only the item node, so B1–B7 and independent searches for proposed new nodes are vacuous. Whole-blueprint `blueprint_refs.py search 'composition isomorphism'` and DAG searches for composite adjunctions, conjugates and mate equivalences were read; the required abstract tools already exist as Mathlib leaves. No duplicate, elementary helper or restatement node was created.
- Existing tool nodes: read their complete statements and checked the relevant source declarations directly. The unit-equation node itself does not state a conjugate characterization; the mate-definition node now supplies that notion explicitly. The composite-adjunction and mate nodes are Mathlib leaves, so no off-unit route approval or worker-written tool-use record is needed.
- Edge cases: for a zero sheaf all component formulas are its unique endomorphism; for an empty scheme the same categorical Hom bijections and triangle identities apply; for a field base neither finiteness nor geometric properties are used. For $h_1$ or $h_2$ an identity, the formulas still have the stated types and define the usual adjunction-compatible comparisons. No n parameter occurs. Identity/zero cases can mask the inverse-direction error, which the general type check detects.
- Searches and citations: ran independent LeanFinder, Loogle and Mathlib grep queries using the msearch tool, including `CategoryTheory.unit_conjugateEquiv_symm` (one exact Loogle hit). Inspected the returned declarations and local source; actual outputs remain in searches.jsonl. Corrected the first worker's first search summary, which had named `leftAdjointCompIso` although that query returned its conjugation lemma. Rebuilt citations.json with one verbatim full statement for each citation of each repaired step.

Changes and reasons:

1. Corrected the source's inverse-direction conjugation error and cited the definition of mate, to make the intended construction well typed.
2. Replaced the single compressed proof step by three explicit steps using existing nodes, to supply the composite adjunction and the mate calculation without relying on a cited node's proof.
3. Removed the unnecessary split_report tool-use proposal because all generic tools cited are already Mathlib leaves.
4. Updated the split summary, blueprint realization, search summary and citation certificates to describe the repaired proof; left all original report sections intact.

## Delivery tool status

The repaired split passed the required dry run: `OK (not pushed) deliver/NL/def-sfb-finite-upper-star-comp at 277acf2826: preflight passed`. A redundant dry run was terminated with exit 143 while waiting on the shared tool locks; its search-summary-only edit was reverted, restoring the successful dry-run content. Both subsequent required push invocations of `python3 /home/ubuntu/weil-launcher-nt/deliver.py NL def-sfb-finite-upper-star-comp` were terminated with exit 143 (SIGTERM) without output. Process inspection before each termination showed a kernel file-lock wait, and no pushed commit was confirmed. This is a delivery-tool failure; the completed second reading and repaired node/citations remain in this sandbox. No lock, launcher or live-project file was edited to bypass it.


## Resumed review by NL (2026-10-16)

I independently reread the saved three-step split against the current shared DAG, the current main-20261015 item statement and proof, the enclosing chapter and the unit's `_section.md` and proof. The current item is still imported, without a closed attachment or reviewed split, so this work has not been superseded. The current imported node has no maintained chapter/unit fields, and the corresponding unit JSON is absent; I read the actual blueprint unit instead and made no maintainer-owned metadata change.

The earlier report's claimed dispatcher prohibition on attaching is historical, not a premise of this resumed review. I searched the read-only project Lean source again: `AlgebraicGeometry.ProEtale.upperStarComp`, `WeilConjectures/SixFunctors/ProEtale/UpperLowerStar/Defs.lean:344–348`, exists without a local sorry. Its final `.symm` makes its characterization differ from the original imported statement's literal mate-of-the-inverse clause. Thus it does not justify attaching the original ill-typed statement unchanged. I retain the explicit STATEMENT-DISPUTED correction already documented above. The upstream master construction at `FiniteCoefficient/UpperLowerStar/Defs.lean:294–298` confirms the intended direction; it is reference material, not evidence of completed proof.

For step 1, I read both cited statements again: the geometric adjunction supplies each of the three individual adjunctions for arbitrary morphisms and the same Grothendieck abelian coefficient category; the composite-adjunction node supplies exactly the two Hom bijections in their written order. For step 2, the pushforward-composition statement has direction R₂ to R₁, precisely the hypothesis of the compatible-uniqueness node; that node explicitly gives uniqueness and invertibility of the resulting L₁ to L₂ map. For step 3, the mate-definition statement gives exactly the inverse-mate component after swapping its adjunction labels. With a_F = δ_(L₂F) η₂,F, naturality gives R₁L₁(a_F) η₁,F = η₁,R₁L₂F a_F, and the triangle identity reduces R₁(ε₁,L₂F) η₁,R₁L₂F to the identity. Hence the displayed unit equation holds and the cited uniqueness identifies the mate with step 2's isomorphism. This uses statements, not hidden arguments in the cited nodes' proofs.

I reread Stacks categories.tex Tag 0B65 (`lemma-transformation-between-functors-and-adjoints`) and Tag 0DV0 (`lemma-compose-counits`), and Mathlib `Adjunction/Mates.lean:275–315,425–435` and `Adjunction/Basic.lean:567–586`. They confirm the direction and composite formulas. No SGA source is used. I also read the pullback/pushforward definition statements to verify the coefficient category and arbitrary-morphism hypotheses. All six entries of citations.json are verbatim parts of the current cited statements, and their nodes are exactly the union recorded in proof_deps.

The general arrow type check detects the source error even when identity or zero cases hide it. With an identity morphism the construction still satisfies the same unit equation; with empty schemes or the zero sheaf the formulas and triangle identity remain defined. No properness, smoothness, finite-type, or extra coefficient restriction is introduced. Both current citers are unchanged and remain consistent with the corrected direction. No new node was created, so no duplicate or elementary helper was introduced; the recorded searches agree with the retained msearch log and the whole-blueprint composition search supplies no replacement with the same coefficient functors. The three generic categorical tools already have Mathlib-leaf status. The report's earlier one-step discussion is superseded by the second reading and this resumed check.

The only requested tool action in this resumption is the dry run with --no-push. No delivery push is authorized by the current brief. A fresh dry-run result follows from this invocation; the earlier lock failures remain historical evidence.

The first dry run of this resumed review was killed with exit 137 and no stdout/stderr. Read-only process inspection had shown it waiting for the NL group lock behind another item's dry run, so no preflight success was observed. I did not signal the process or modify any lock. I am retrying the prescribed command once.

## Second reading by NL

- Item statement: checked every hypothesis and arrow against blueprint node `def-sfb-finite-upper-star-comp`, Stacks Tag 0B65, and the read-only `upperStarComp` construction; verdict: source inverse-direction error is explicitly corrected and recorded under `STATEMENT-DISPUTED`.
- Step 1: checked the three adjunctions and the composite Hom bijection against `def-sfb-finite-upper-lower-star-adjunction` and `def-weil-pbc-composite-adjunction`; verdict: all functors and categories are supplied, with no hidden dependency.
- Step 2: checked the direction and unit equation against `def-sfb-finite-lower-star-comp` and `lem-weil-pbc-conjugate-iso-unit-equation`; verdict: the displayed natural isomorphism has exactly the required direction and uniqueness hypothesis.
- Step 3: checked the inverse-mate component, naturality calculation, and triangle identity against `def-weil-pbc-adjunction-mate` and the same uniqueness lemma; verdict: the elementary calculation proves the stated mate characterization.
- New nodes: none; the sandbox contains only the item, so B1–B7 and duplicate-node checks are vacuous. Existing categorical tools were searched in the DAG and Mathlib, and citations.json quotes each cited statement verbatim.
- Edge cases and route: identity morphisms, zero sheaves, empty schemes, and field bases retain the stated types; no SGA source or extra geometric hypothesis is used.
- Changes made: corrected the inverse-direction statement, expanded the proof to three explicit steps, updated dependencies and citation certificates, and documented the correction and searches above.
