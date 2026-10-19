1. Files written

- `dag/nodes/sec-six-functors/lem-coef-acyclic-cycle-orthogonal-splitting.json`: the item, a statement with eight complete proof steps; no Mathlib match for the whole assertion.
- `citations.json`: ten entries, one verbatim statement quote for every cited node in every step.
- `searches.jsonl`: actual searches appended by the required msearch.py command.
- `report.md`: this handoff.

There are zero new nodes and zero new Mathlib leaves. I removed the uncommitted `lem-coef-acyclic-cycle-hom-nullhomotopy.json` from the earlier sandbox attempt. The copied chapter/unit JSON files at the sandbox root are reference copies, not delivery changes; no chapter or unit is changed.

2. Attachments

None. Searching the item id, its literal blueprint tag, cycle orthogonality, acyclic/cotorsion, and the relevant Hom-complex notions throughout `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` found no project declaration stating the item. Generic InternalHom and resolution declarations do not establish this splitting assertion. No upstream master sorry declaration is treated as a proof.

3. WANTED

No missing document is needed by this delivery's proof. The item's inherited source field mentions WANTED: Gillespie (2004), Lemma 3.10. This is historical provenance, not a source that I read or a theorem that this proof assumes. The proof below is explicitly agent-written, using an existing, reviewed splitting-calculus statement and archived Stacks kernel/exactness conventions. No new request is made and no missing-source claim is disguised as a literature proof.

4. Faults in the earlier attempt and repairs

The target statement is unchanged and is not disputed. The earlier null-homotopy child, in the presence of the already cited degreewise-split extension identification, moved essentially the entire remaining argument into an equivalent new statement (delivery-errors D1/D2). I deleted that never-delivered child and wrote the two-pass correction in steps 4--7 of the item.

The earlier proof also used six-term derived Ext statements whose statements require small Ext groups, whereas the item defines Ext-one vanishing directly as splitting of short exact extensions. Rather than leave an implicit derived/Yoneda comparison and universe convention, I use `lem-coef-cotorsion-orthogonality-calculus`, whose statement uses exactly the item's splitting interpretation and assumes only an abelian category. This avoids adding any hypotheses to the item. The degreewise-split/Hom cohomology classification is also unnecessary: step 8 constructs the actual section and checks its differential equation.

I read the inherited master blueprint paragraph and its current counterpart in `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`, the associated statement, the recorded chapter and unit, and the created.item ancestry. These paragraphs motivate derived coefficient adjunction but do not contain the extension-splitting proof. `proof_origin.by` is therefore `agent`. The inherited ancestry, chapter and unit are retained; this is an abstract tool below the unit's route, not a replacement of that route. No SGA source is used.

5. Unfinished work

None in this one-level split. There are no new statement-only children. The second reader must review and deliver; I run only the required --no-push dry run.

## Not duplicates

No new node is proposed. Whole-DAG searches for cycle orthogonality, orthogonal cycles, the earlier child id, Hom null-homotopy, and Gillespie, and `tools/blueprint_refs.py search` for cycle, cycle orthogonality, null-homotopy and cotorsion were read. The existing `lem-coef-cotorsion-orthogonality-calculus` supplies both extension closure and diagonal fillers, so it is reused. The hereditary-cotorsion-complex-lift node is the parent that uses this item and is not cited back. The generic disk/sphere extension node is not needed by this proof.

## Review by NE

I read coord/delivery-errors.md B--E in full, then checked the delivered item with the supporting statements and sources open. The sources read were the original master and current main-20261015 exceptional-adjoint paragraphs, Stacks `homology.tex` Tag 0109 (`definition-abelian-category`), Tag 010E (`definition-exact`), Tag 010I (`section-extensions`) and Tag 010J (`definition-extension`), as well as the complete statement of `lem-coef-cotorsion-orthogonality-calculus`. The Stacks tags supply the exactness/extension conventions, not the whole cycle-splitting assertion. I also read the cokernel node's complete statement, the exact-sequence definition and the abelian-category definition. There are no new-node sources to validate.

Step 1 uses `def-sp-abelian` for kernels, cokernels and preadditive identities, `def-weil-pbc-exact-sequence` for image=kernel, and clause (a) of `lem-weil-pbc-abelian-exact-epi-cokernel` for the cokernel of a monic cycle inclusion. The required exactness and epic quotient follow from acyclicity. The termwise construction of kernels and cokernels of cochain maps explains why the extension is degreewise short exact; induced differentials exist by their universal properties and square to zero by monic/epic cancellation. There is no assumed exactness of an unrelated functor.

Step 2 uses exactly the two extension-closure assertions of `lem-coef-cotorsion-orthogonality-calculus`. First fix the class of X cycles to obtain orthogonality of X cycles to all Y terms by the Y cycle rows; then fix the class of Y terms to obtain orthogonality of all X terms to those terms by the X cycle rows. The statement allows any class of objects. It needs neither a cotorsion pair nor enough projectives/injectives. In particular we obtain the cycle-to-term orthogonality later needed by step 5.

Step 3 uses splitting in its stated meaning to choose term sections and the abelian kernel universal property to factor the defect through Y. The explicit expansion proves the plus sign in the degree-one cocycle equation; it is a calculation, not an uncited Hom-complex classification theorem. The `def-sp-abelian` quote covers the preadditive and kernel operations used here.

Step 4 uses the diagonal-filler sentence of the calculus with (monomorphism, epimorphism) equal to (0 -> Z^nX, Y^n -> Z^{n+1}Y). The top arrow is zero, so its square commutes. Its obstruction pair is (Z^nX,Z^nY), exactly an original hypothesis. Kernel factorization of a^n on X cycles is justified by the cocycle identity.

Step 5 uses the same filler sentence with (Z^nX -> X^n, Y^n -> 0). Its obstruction pair is (Z^{n+1}X,Y^n), proved orthogonal in step 2. The square again commutes because its codomain is zero. Thus the cited statement really extends c^n, with no injectivity assertion. The displayed equality shows the residual vanishes on cycles.

Step 6 uses only the cited abelian-category definition and the explicit cokernel-factorization clause (a). Substituting r proves its cocycle equation; since r vanishes on cycles, its composite with the previous differential is zero. Therefore r has cycle-valued image and factors through the next X cycle. Epic cancellation and the kernel universal property give the displayed w^n. This calculation was previously hidden inside the proposed child.

Step 7 uses the filler with (0 -> Z^{n+1}X, Y^n -> Z^{n+1}Y), whose obstruction pair (Z^{n+1}X,Z^nY) is again an original hypothesis. It produces u^n with the exact quotient equality used. The equations k^{n+1}d_X^n=0 and d_Y^nk^n=r^n are written out. Hence h=b+k has differential a, with the cochain sign checked. This is done independently at every integer degree, so unboundedness requires no nonexistent starting degree and no infinite product in the abelian category.

Step 8 is the displayed preadditive calculation for s=t-iota h. It proves both ps=1 and the cochain-map equation directly. No additional Ext/derived category comparison or splitting classification is used. Every external node cited by any step has its own verbatim quote in citations.json; all non-elementary facts are exactly the closure or filler clauses of the calculus. Its node is in the same unit and its dependency closure does not use this item.

Small cases: zero X gives the unique zero section; zero Y makes the component epimorphisms isomorphisms and the construction reduces to their inverse cochain map. For a concrete unbounded case I checked all 81 degree-one cocycles over F_3 between the 2-periodic exact complexes F_3^2 with differential [[0,1],[0,0]]. The check executes both correction passes and verifies that (-h,1) is a section and cochain map in every corresponding block extension E with differential [[d,a],[0,d]]. Odd characteristic tests the minus sign, and periodicity checks that no endpoint induction is hidden. As a check on the scope of the hypotheses, over a field the extension 0 -> S^1(k) -> D^0(k) -> S^0(k) -> 0 has orthogonal cycle objects but is not split as complexes; its endpoints are not acyclic, so it is correctly outside the statement. No small-case check identified a statement error.

For Mathlib, I ran and read two distinct LeanFinder phrasings, Loogle, LeanSearch, and two greps through msearch.py; only these actual searches are recorded in the refreshed item record. I opened `DegreewiseSplit.lean:43-64` and `ShortComplex/Exact.lean:1003-1010`, and the projective-resolution Ext interface. A defect-cocycle constructor and a splitting constructor that already takes a section do not state the item. The generic resolution Ext computations do not apply to arbitrary X,Y here. None is an exact match or one-line specialization. The new statement-only-node, source-tag, duplicate, Mathlib-leaf and blueprint-field checks of B are vacuous for children because no child remains; the existing item's blueprint place and same_as were filled. C was checked against each statement as above; D was repaired by writing the argument; E was checked by the obstruction pairs and the small examples.

## Second reading by NE

- Statement: checked the item against the agent-formulated extension paragraph in `prop-coef-integral-exceptional-adjoint.md`, the inherited abelian/exactness conventions (Stacks Tags 0109, 010E, 010I, 010J), and the current `main-20261015` paragraph; every hypothesis (abelian category, two-sided integer complexes, acyclicity, pairwise cycle splitting) and the section conclusion is present and unchanged. Verdict: sound and not disputed.
- Step 1: checked the cycle rows, cokernel factorization, and degreewise exactness against `def-sp-abelian`, `def-weil-pbc-exact-sequence`, and `lem-weil-pbc-abelian-exact-epi-cokernel`; the kernel/cokernel construction for complexes is the marked elementary categorical calculation. Verdict: cited statements suffice.
- Step 2: checked both applications of extension closure in `lem-coef-cotorsion-orthogonality-calculus`; the first gives cycle-to-term orthogonality and the second term-to-term orthogonality, with no extra cotorsion-pair hypotheses. Verdict: correct.
- Step 3: checked the component sections, kernel factorization, and signed cocycle expansion against `def-sp-abelian`; the displayed expansion proves the plus sign. Verdict: correct and elementary.
- Step 4: checked the first diagonal filler with $0\to Z^nX$ and $q_Y^n$, including cokernel/kernel identification and the original cycle orthogonality obstruction. Verdict: correct.
- Step 5: checked the second diagonal filler with $j_X^n$ and $Y^n\to0$, including the required $Z^{n+1}X\perp_1Y^n$ consequence of step 2 and the residual restriction calculation. Verdict: correct.
- Step 6: checked the residual cocycle calculation, cancellation, and factorization through $q_X^n$ against the abelian and cokernel statements; no hidden Hom-complex theorem is used. Verdict: correct.
- Step 7: checked the final filler with $0\to Z^{n+1}X$ and $q_Y^n$, the equations $k^{n+1}d_X^n=0$ and $d_Y^nk^n=r^n$, and the resulting signed differential identity. Verdict: correct for every integer degree, with no boundedness assumption.
- Step 8: checked the section formula and cochain-map computation directly; it uses only the preceding identity and monicity of the kernel inclusion. Verdict: correct and elementary.
- New nodes: none remain after the earlier equivalent null-homotopy child was removed; therefore B1--B7 and per-node source/Mathlib/duplicate checks are vacuous. The existing calculus node was searched and cited instead.
- Edge cases and searches: zero complexes, zero subcomplex or quotient, and a periodic field example were checked; the recorded LeanFinder, Loogle, LeanSearch, and grep searches found no exact Mathlib declaration.

Changes made during this second reading: none to the item or citations; the proof already contains the missing two-pass construction and all cited statements match their uses. I added this section to record the step-by-step second reading required by the delivery contract.
