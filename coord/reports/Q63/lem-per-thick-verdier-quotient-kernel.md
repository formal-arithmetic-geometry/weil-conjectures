# Worker report: lem-per-thick-verdier-quotient-kernel

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-thick-verdier-quotient-kernel.json`: statement; split into five steps using existing Mathlib leaves. The statement is unchanged, and the existing localization definition is added to `stmt_deps`. Mathlib covers the localization machinery, but no declaration found states the complete kernel assertion.
- `citations.json`: one exact statement quotation for each node cited in each numbered proof step.
- `report.md`: this report. Existing `searches.jsonl` retained and extended by two searches through the required command.

New DAG nodes: 0. New Mathlib leaves: 0. No unit record is changed: this item is a generic tool several levels below its blueprint ancestor, not the unit key node.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact item tag and the thick/Verdier/kernel notions found no declaration stating this item. The additional declaration-name index search found no attachment. Upstream master was read as reference only and was not treated as completed proof evidence.

## WANTED

None. The proof uses the locally available Stacks sources and existing DAG interfaces.

## Findings and corrections

The item had an empty proof. Its source statement is correct: strict fullness and retract closure are essential for identifying the kernel with the given subcategory rather than its thick closure. The proposition is not replaced by a statement-only child restating its kernel clause.

The original searches and blueprint ancestry are retained. The earlier Q63 sandbox contained only search results; there was no split or report to recover. I read those search results and the candidate source APIs, retained them, and ran a second item phrasing plus a targeted grep. The new semantic search again returned homological-kernel and t-structure results rather than the full item. The grep found `CategoryTheory.MorphismProperty.map_eq_iff_precomp` at `Mathlib/CategoryTheory/Localization/CalculusOfFractions.lean:984`, a short specialization already covered by the existing right-fraction-common-refinement node, so it creates no new node. Earlier candidate names from newer search indexes (`Triangulated.Subcategory.W`) are compared against the pinned source's `ObjectProperty.trW` implementation, not blindly adopted.

I read the entire statements of all six dependencies used in the proof. The proof does not assume that the multiplicative system is saturated and does not use the statement of Stacks 05RK as an unproved black box. Instead it writes out the identity-fraction argument and uses the precise representable-exactness clause to exhibit a retraction. All non-elementary tools are existing Mathlib leaves; the localization-definition node is a notion. No cross-unit route exemption is needed.

An inherited source-label typo was found in `lem-pc-right-fraction-common-refinement`: its source says `categories-lemma-right-localization-equal-morphisms`. The correct local label for its Tag 04VJ is `lemma-equality-morphisms-right-localization` in `categories.tex:4642`. Its actual statement and Mathlib match are correct, and the delivered proof cites the correct label. The dependency is read-only and has not been edited.

## Unfinished work

None for this one-level split. No Lean file was written and no compiler or build tool was run. Delivery and checks use only the authorized launcher commands.

## Review by Q63

I read Stacks `derived.tex`, Tag 05RG (`lemma-construct-multiplicative-system`), Tag 05RI (`definition-quotient-category` and its following exactness note), and Tag 05RK (`lemma-kernel-quotient`). Tag 05RK describes the general kernel as objects whose direct sum with another object lies in the subcategory; the item's retract-closed, strictly full case therefore has precisely the asserted kernel. For the expanded argument I also read `lemma-kernel-localization`, the representable-Hom theorem Tag 0149 (`lemma-representable-homological`), and `categories.tex`, the right-fraction equivalence relation preceding Tag 04VJ (`lemma-equality-morphisms-right-localization`). The proof origin is recorded as agent-written because the particular explicit fraction/retraction expansion is supplied here, following that source route.

Step 1 uses `def-weil-triangulated-category` for the ambient triangulated structure, `def-pur-saturated-triangulated-localization` for the definition of localization and multiplicative systems, and `lem-trf-triangulated-subcategory-cone-system` for identities, both fraction calculi and compatibility. I checked that the latter expressly does not require closure under summands or saturation; our subcategory satisfies its full, replete, shift and triangle hypotheses. The localization definition includes the unsaturated universal property before its separate saturated situation. In the pinned Mathlib source the cone class is `ObjectProperty.trW` at `Subcategory.lean:462`, and the relevant instances are at lines 520, 546, 551, 603, 623 and 644. Step 1 defines the Verdier quotient at that class; it does not claim that localization inverts no additional arrows.

Step 2 uses `lem-pur-localization-triangles-05r6` for the triangulated structure and exactness of the quotient, not for its kernel. Its statement requires a compatible multiplicative system, not a saturated one, so Step 1 supplies every hypothesis. Its source is Stacks Proposition 05R6 (`proposition-construct-localization`). I read `Localization/Triangulated.lean:199,208,218` for the three parts of its recorded match. The second citation, `def-weil-triangulated-category`, explicitly makes exact functors additive; hence zero preservation here is definitional.

Step 3 uses only TR1/TR2 from `def-weil-triangulated-category` and inversion from the localization definition, as supplied by `def-pur-saturated-triangulated-localization`. Inverse rotation of the identity triangle has first arrow zero and third object A, so its first arrow belongs to W when A belongs to the subcategory. The inverse of its zero image gives the zero identity on Q(A), and composing with that identity proves uniqueness of all incoming and outgoing morphisms. This is the short elementary containment, with its algebra written explicitly; no theorem about quotient kernels is hidden in it.

Step 4 uses `lem-pc-right-fraction-common-refinement`, whose complete statement explicitly handles arbitrary right calculus localizations, with common refinements satisfying equality of numerators and denominators. It is not limited to quasi-isomorphisms despite the historical name of one of its own definition dependencies. `lem-trf-triangulated-subcategory-cone-system` supplies that right calculus. I checked the specialization: both denominators are identities of A, the numerators are identity and zero, so equality of denominators says a1=a2 while equality of numerators says a1=0. Their common denominator s therefore belongs to W and is literally zero. Exactness in Step 2 supplies Q(0)=0. The Mathlib relation and `RightFraction.map_eq_iff` were read at `CalculusOfFractions.lean:895-898,973-979`. This establishes a zero denominator without using a saturation criterion or a kernel theorem.

Step 5 uses clause (iii) of `lem-weil-pbc-hom-into-triangle-exact` exactly: with its X=R, Y=A, Z=C, W=R[1], u=0 and c=id, the shifted-zero hypothesis holds. The conclusion is an actual k with h k=id, so R[1] is a retract of C. This is the existing node's stated factorization, not merely its proof or a definition of homological functor. I read its pinned match `Triangle.coyoneda_exact₁` at `Pretriangulated.lean:267`. The other citation supplies additive shifts and the triangle framework. The remaining closure steps use the item's own hypotheses: retract closure, closure under inverse shift, and two-out-of-three in a distinguished triangle. No idempotent-completeness assumption is added: the particular retract is explicitly exhibited.

For B1-B10 and C1-C8, there is no new-node statement, duplicate, orphan, self-dependency, relabelled kernel clause, or new unsplit lemma. The DAG and whole-blueprint searches included Verdier, quotient, multiplicative system, split triangle and kernel localization; the general cone-system and localization/fraction/Hom nodes above were reused. I read every cited statement and generated `citations.json` directly from those statements. Every non-elementary application is a cited statement; elementary steps have their short arguments written. All five steps are shorter than 2000 characters.

For D and E, I checked the zero subcategory: a zero denominator has zero cone, and the retraction plus triangle argument forces A=0, as expected. For the whole category every zero arrow 0 to A has cone A, so every quotient object is zero. For a subcategory without retract closure Step 5 would stop at an actual retract of C, matching the thick-closure conclusion of Stacks 05RK; this shows exactly where the item's additional hypothesis is used. The argument also applies in a triangulated category not assumed idempotent complete, since it splits only a particular already exhibited retraction. The shift sign in TR2 cannot affect the zero map used in Step 3 or Step 5. No finiteness, smallness beyond the ambient localization universe, or geometry/coefficient hypothesis is introduced. The statement and all blueprint/import fields were retained. The repair made during self-review was to use the already existing representable-Hom clause and common-refinement node instead of creating redundant zero-localization or split-triangle nodes.
