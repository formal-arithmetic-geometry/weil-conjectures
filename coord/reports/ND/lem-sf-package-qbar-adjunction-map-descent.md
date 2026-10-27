# Stage-1 report: lem-sf-package-qbar-adjunction-map-descent

## Files written

- `dag/nodes/sec-six-functors/lem-sf-package-qbar-adjunction-map-descent.json`: item, statement, split. Its conditional statement is unchanged. Six proof steps use the actual comparison conjugations and the existing Mathlib Hom-colimit leaf.
- `citations.json`: one verbatim statement quotation for every step/node citation.
- `report.md`: this report.

There are zero new nodes and zero new Mathlib leaves. `searches.jsonl` is the search command's original log; `make_split.py` is sandbox-only preparation code. No Lean was written and no compiler, Lake, build tool, or local DAG checker was run.

## Attachments

None. Searches for the exact blueprint tag and for `qbar`, adjunction, and common-stage terminology in `lean/WeilConjectures/` found no declaration giving this statement. The VerdierDual and LocalDuality files mention the broader blueprint theorem in documentation; those mentions are not declarations proving this item.

## WANTED

None. The proof is an agent expansion of available blueprint material and is marked `proof_origin.by = agent`.

## Audit of the item and sources

The live item was unsplit and the sandbox had no previous item, report, split, or search log at launch. There is no repair-note file. I read the chapter and unit records, the current `main-20261015` package statement and proof, and the older `thm-coef-qbar-verdier.md` statement and proof. The latter explicitly describes representative conjugation and passing the finite adjunction through the Hom colimit; the package's exceptional-adjunction sentence supplies this item's place in its route. The chapter and unit are unchanged, and the item is not their key statement node.

The item assumes the finite-field adjunctions, their compatible units and counits, and coherent internal Hom/tensor comparisons preserving evaluation. The proof uses these as hypotheses. It does not prove them from the finite-quotient or integral constructions. This distinction permits a direct representative calculation rather than creating nodes that simply restate the unit, counit, and evaluation clauses.

I searched the whole DAG and blueprint for common-stage, filtered-colimit, and adjunction statements, and opened the candidate statements. `lem-coef-qbar-adjunction-hom-descent` already gives exactly the generic additive-colimit equivalence needed here. I read its Mathlib match, `AddCommGroup.DirectLimit.congr`, and the two representative formulas in `Mathlib/Algebra/Colimit/Module.lean:417,429,437`. It applies to the directed tail of finite fields containing the two object fields. `prop-weil-pbc-common-stage-calculus` provides related general calculus, but it is unnecessary: the pair-category definition already states the representative/equality rule and composition used in the elementary calculations. The smooth-purity counit lemma has smoothness and condensed-category hypotheses and is not the same statement or an input to this proof. No off-unit theorem requiring a tool-use declaration is cited; the only theorem citation is an existing Mathlib leaf.

Mathlib searches were run exclusively with the prescribed `msearch.py` command. The six new recorded searches match `searches.jsonl`, with exactly its tool/query pairs and results. Both semantic phrasings were read. Results concern fixed-category adjunctions, parametrized adjunctions, evaluation adjunctions, condensed modules, or colimit preservation, rather than adjunctions between varying coefficient categories. I inspected the generic adjunction data in `Adjunction/Basic.lean`, the closed-category definitions in `Monoidal/Closed/Basic.lean`, and `Category/Cat/Colimit.lean`, which constructs colimits of small categories rather than this descent theorem. The existing search records on the item are preserved; their results are consistent with these new searches. None of the queried services was unavailable.

## Not duplicates

No new node was created, so there are no new/existing same-tag pairs. The existing additive-colimit Mathlib leaf was reused instead of creating another descent ingredient.

## Review by ND

I checked delivery-errors B–E against the completed item and its cited statements. There are no new statement-only nodes, unmatched notions, unverified Mathlib-leaf claims, or new-node source tags to audit. The statement and all maintainer-owned fields remain unchanged; only split-owned fields have been updated. Every cited identifier is an existing node and every entry of `citations.json` was checked as a literal substring of its statement. All six proof steps are shorter than 2000 characters. There is no forbidden SGA citation.

Step 1 uses `def-weil-algebraically-closed-coefficients` for the actual pair objects, eventual equality, and common-field composition. The compact-support definition gives the object formula for $F$; the morphism action is constructed here from the assumed comparisons. The exceptional inverse-image and tensor/internal-Hom definitions also explicitly give their common-stage arrow actions. The proof states the comparison conjugations explicitly. The item supplies coherence as a hypothesis, so the proof only checks that extension preserves the conjugation formula, that equal representatives give equal images, and that intermediate comparisons cancel in a composite. These calculations also cover the reversed first variable of internal Hom. No exactness, constructibility-preservation, or scalar-extension comparison theorem is being inferred from a definition citation.

Step 2 uses the same pair-category Hom description, the rational morphism action of `def-weil-exceptional-inverse-image`, and `lem-coef-qbar-adjunction-hom-descent`. I checked the leaf's hypotheses: the index is a nonempty directed partially ordered set of finite fields, the Hom sets are abelian groups, and the maps are additive equivalences. Additivity follows here from the additive rational operation action and the explicit formula `G(u) eta`; the inverse is `epsilon F(v)`. Compatibility is not hidden behind the word transport: the step writes the two equalities obtained by substituting the comparison conjugations and the hypothesized unit/counit preservation equations. The existing leaf then supplies both colimit maps with exactly these representative formulas. Its statement, rather than its proof, is all that is used.

Step 3 uses the pair-category composition/equality rule and the finite-stage adjunction already assumed in the item. I checked the types of `b u F(a)` and `G(b) phi(u) a`; their equality at a common field proves naturality for arbitrary common-stage arrows. Applying the two Hom maps to the appropriate identity arrows recovers the unit and counit at their original field. Changing an object's field is comparison by the identity-represented canonical isomorphism, rather than an assertion that two distinct pair objects are literally equal.

Step 4 uses the internal-Hom/tensor definition for the actual source object over the compositum and the pair-category rule for equality of classes. The evaluation comparison is an explicit hypothesis of the item. Its equation identifies the extension of the proposed evaluation with the proposed evaluation at the next field; passing two choices to their compositum proves independence. This retains the actual finite-stage normalized map.

Step 5 uses the same two definitions only to interpret arrow actions and classes. I checked evaluation's variance carefully: the proof writes naturality in the second variable and dinaturality in the first, with common source `H(P',Q) tensor P` in the second displayed equation. These are the finite-stage evaluation laws, followed by taking their classes. They prove the intended naturality for internal Hom rather than an ill-typed assertion of covariance in its first variable. Identity-represented field-change isomorphisms give presentation independence. No statement change was needed.

Step 6 uses the pair-category rule for composites and identity classes. I checked each triangle separately, at the field of its own object, with `epsilon_(F K) F(eta_K)` and `G(epsilon_M) eta_(G M)` in the correct order. The general finite-diagram clause is verified by induction on the expressions, using only the operations and maps already identified in steps 1–5 and the specified associators. It assumes the stated equality at one common finite field, exactly as the item does; it does not infer equality at an initial field from equality of colimit classes.

For small cases I checked coincident fields (the comparisons become identities), distinct object fields (use their finite compositum), repeated field enlargements (use the tower equation), identity arrows, zero objects/zero maps, and empty schemes (the operation formulas are still typed and the Hom calculations are trivial). No faithful or injective transition functor is assumed: representatives are compared only after a further extension, so noninjective transition maps do not invalidate any step. No finite-quotient reduction on the algebraically closed category is used. The proof does not introduce an ambient exceptional adjoint or change the rationalized common-stage coefficient category.

## Corrections and unfinished work

The old item had no proof; the new proof fills it without changing its statement or deleting its inherited provenance/searches. There was no source error or statement dispute. No mathematical part remains unfinished. The server `review_split` passed, and the initial full `deliver.py --no-push` preflight passed at `37eccf53fff`. A final citation check then sharpened step 1 to distinguish the compact-support object definition from the induced morphism action constructed under this item's assumptions; full preflight is rerun on this final version before direct push.
