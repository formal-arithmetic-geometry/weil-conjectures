# Stage-1 worker report

## Files written

- dag/nodes/sec-smooth-base-change/lem-sbc-finite-stage-rational-exchange-coherence.json: statement item, now split into 11 proof steps; no exact Mathlib match. The statement and all maintainer-owned fields are retained.
- citations.json: 17 step/node entries with verbatim excerpts from the cited statements.
- report.md: this report.
- searches.jsonl: five new actual msearch records, read and recorded in the item in addition to its inherited searches.

There are 0 new nodes and 0 new Mathlib leaves.

## Attachments

None. I searched the blueprint tag and rational exchange, Karoubi exchange, and scalar/exchange terminology in lean/WeilConjectures. The StageSystem/Functor.lean declarations descend already-coherent functor data; they do not supply the actual completed operations, finite-coefficient comparisons, or their rational and Karoubi coherence. No project declaration found states the entire item.

## WANTED

None. The item's source and the generic coefficient constructions used for the split are available locally.

## Corrections and source issues

No statement correction or statement dispute. The initial item had no proof. Its own ambient hypotheses are retained, including all four noetherian finite-dimensional schemes and invertible ell; no smoothness, constructible landing, exchange invertibility, or identification of a raw category with its Karoubi envelope has been introduced.

The generic prop-weil-pbc-rational-transport is restricted to integral constructible categories. It therefore cannot justify this ambient argument. Instead, I cite the already existing lem-pur-semilinear-scalar-localization, whose statement is for arbitrary linear categories and permits different coefficient rings. The canonical ambient scalar-comparison package is already in prop-weil-pbc-scalar-extension, so no second scalar-comparison node was created.

The current parent's proof now uses this item in step 1. The item's inherited source-place refers to earlier parent steps 1 and 3. The split_report records both the current parent placement and the sketch32 source locations; the original source and blueprint provenance are retained.

## Unfinished work

None within this one-level split. Existing dependency nodes remain the responsibility of their owners. No Lean file was written and no compiler, Lake or build command was run.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. I checked the existing rational transport, semilinear localization, ambient scalar extension, Karoubi-envelope definition and coherent-pair descent nodes. Reusing these avoids elementary Karoubi-extension nodes and any restatement of this item's clauses. Whole-blueprint searches for Karoubi, semilinear and rational exchange found no blueprint node stating this entire item in another form; same_as remains empty.

## Review by Q16

I read the standing brief, the stage-1 contract, the three-level route restrictions in SETUP.md, GOAL.md, the worker role, the unit sk-rem-rest and chapter sec-smooth-base-change, and both copies of delivery-errors.md sections B through E. For the mathematical source I read sketch32 lines 1191-1228, 1262-1279 and 1291-1321 in literature/blueprint/slopmaster2/src/version/sketch/32_smooth_base_change.tex. The first range defines the ambient raw and Karoubi categories and extends linear operations; the second keeps the ambient-versus-constructible distinction; the third specifies actual integral tensor, its localized action, and coherent tensor-unit/associator comparisons. I also read the current parent proof. The unit's continuation explicitly includes pro-etale, adic, rational and Qbar coefficients and has no separate proof steps to rewrite. No chapter or unit file is changed. There are no new nodes requiring additional source checks.

For step 1 I opened the full statement of lem-sbc-completed-operations-linear-natural-exchange. It supplies additive integral linear operations on the full complete categories, naturality of the specified unit-counit mate and its agreement with completed exchange. Thus I use its theorem, not an unstated construction in its proof. In step 2, lem-pur-semilinear-scalar-localization supplies additive extensions, extension of transformations, and preservation of composites; lem-weil-l-adic-integers-localization-uniformizer identifies the localized coefficient ring with E. I deliberately use only the additive portion and need no triangulated/exactness hypothesis.

For step 3 I read prop-weil-pbc-scalar-extension through its final paragraph. It expressly supplies comparisons on ambient derived-complete integral categories, and says they respect identities and successive coefficient extensions. I spell that compatibility as the operation tower equation, with the target/source tensor associators, and apply the identity normalization fixed in def-sbc-ambient-complete-coefficient-categories. In step 4 I verified that integral tensor is semilinear by its balancing relation, and the source uniformizer is a nonzero element of M. The localization-of-integers lemma therefore verifies the inversion hypothesis for the existing semilinear extension lemma. That lemma explicitly preserves natural isomorphisms, whiskering, and equations; the ambient definition prescribes precisely this raw transition. This checks the comparison endpoints even though the coefficient rings differ.

For step 5 the last paragraph of prop-weil-pbc-scalar-extension explicitly identifies scalar extension of the canonical completed-and-rationalized exchange with that at the new field under the specified comparisons. I use that rationalized ambient clause, not an unstated integral exchange-square assertion. The two comparison composites are written out in the order matching F=P^fD^g and G=D^hP^e. The inverse-image maps go from the base to X and from T to Y respectively, so both composites have source category at T and target category at X. All four schemes meet the scalar-extension node's noetherian, finite-dimensional and invertible-ell hypotheses, including on Y by its map to S.

Steps 6-9 use the full statement of def-weil-karoubi-envelope, which gives the supported-arrow relation, identity p and underlying composition. The ambient definition in step 6 fixes the same transition on these objects. The steps actually check idempotency, the support condition, functor identities and composition, naturality, both inverse products, vertical composition and both whiskerings. In the naturality calculation, v=qvp implies both vp=v and qv=v; naturality at p lets the extra projectors be removed. In the inverse calculation I checked that the products are H(p) and J(p), rather than incorrectly requiring identity arrows of the underlying raw objects. At p=1 this gives exactly the identity-idempotent inclusion, not an unspecified isomorphism.

In step 10 I opened lem-sbc-coherent-pair-functor-descent and checked the displayed unit and tower equation. The proof does not invoke its descent conclusion to obtain coherence: it expands the composite comparison, substitutes the two individual tower equations from steps 3-4, and writes the naturality identity interchanging the middle factors. This gives precisely that node's prescribed tower equation. The scalar associators used are those fixed in the ambient definition. Step 11 then applies the explicit preservation-of-composites and whiskering calculation of step 9 to the raw square already obtained in step 5. This proves the equality at every idempotent object while retaining the specified comparisons.

For the B-E checks: there are no new unsplit statements, no hidden proof in a statement, no unintroduced object in a new node, and no new-tag source ambiguity. The item's statement is byte-for-byte unchanged. Every node in every uses list was opened; citations.json selects literal substrings of those statements, rather than a paraphrase or a claim from their proofs. Every non-elementary theorem used is an existing cited node, and proof_deps is the exact union of uses. All other steps are the displayed elementary identity/support/composition calculations. No elementary fact or clause of the item is moved into a new node. No proof step exceeds 2000 characters; I still checked all steps for hidden comparisons and wrote the only potentially compressed composite tower calculation out explicitly.

I tested E=M (identity comparisons), E=M=P (tower becomes the identity equation), p=1 (raw inclusion), p=0 (zero supported arrow and zero Karoubi identity), and nontrivial p (inverse products return the projector, not the raw identity). Noninvertible exchange is allowed throughout the naturality and coherence calculations. Different-field scalar localization inverts the image of the original uniformizer in M, not an incorrectly identified new uniformizer. No faithful localization or constructible bound is assumed.

The msearch commands were actually executed for this item with two natural-language phrasings, Loogle, grep and LeanSearch, and I read all hits. The generic Mathlib functorExtension constructions and the localization linearity hits cover parts of the elementary/generic machinery but not this completed ambient operation and specified comparison package. I read Mathlib/CategoryTheory/Idempotents/FunctorExtension.lean through functorExtension2 (Unicode subscript in the source), including the supported transformation formula, and the relevant Karoubi definition and identity/support declarations. Those checks support the elementary calculations; there is no claimed unrecorded Mathlib leaf.

The off-unit generic tools are declared in split_report.tool_uses for maintainer review: the existing ambient scalar-comparison package, generic semilinear scalar localization, and the localization-of-integers coefficient lemma. They supply coefficient algebra and compatibility, without replacing any smooth-base-change argument.
