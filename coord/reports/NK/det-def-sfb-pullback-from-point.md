## Files written

- `dag/nodes/sec-proetale-coefficients/det-def-sfb-pullback-from-point.json`: definition with six assembly steps, existing construction/property dependencies, and recorded Mathlib searches; not a Mathlib leaf as a whole.
- `citations.json`: all 20 step/node citations, quoted verbatim from the current repository statements.
- No new nodes and no new Mathlib leaves.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and for `profiniteToProEt`, `pointUpperStar`, and `upperStarFromPoint`, then read `SixFunctors/ProEtale/ModuleObject/Basic.lean` at lines 150–474. The construction and many property declarations are present, but the inverse-limit identities occur in their docstrings rather than in declarations stating those identities. I therefore do not assert an attachment covering all clauses. Upstream Lean is reference material only; no compiler or build was run.

## WANTED

None. This is an assembly of existing DAG statements following the current blueprint; its proof is marked agent-written, not attributed to an unread external text.

## Problems found and corrections

The imported first proof paragraph omitted the displayed absolute inverse-limit identity. Step 2 now obtains it from the existing relative test-object statement at X = Spec Z, with the canonical base-change identification and its compatibility with finite quotients. The imported last paragraph named a left-adjoint lemma without giving the composition argument. Step 5 instead writes the two natural adjunction bijections explicitly; step 6 checks the section formula also on maps of profinite sets and maps of sheaves. No statement or hypothesis was changed.

The whole blueprint search (`blueprint_refs.py search 'Pulling back'`), the keyword search over all DAG nodes, and direct reading of `sk-def-sfb-pullback-from-point` found an existing parallel blueprint formulation. It is recorded in `blueprint.same_as`, not recreated as a new node. Its coefficient tensor is the same sheafified objectwise tensor over Z; the detail node uses `lem-weil-pbc-sheaf-tensor-closed` for that structure. No new lemma restates a clause of this item.

## Unfinished work

None at this level. The delivery deliberately reuses existing nodes without splitting those dependencies. There is no new statement-only lemma awaiting a proof in this delivery.

## Review by NK

I read the current `literature/blueprint/latest/blueprint/sec-proetale-coefficients/sk-prop-pe-condensed-point/det-def-sfb-pullback-from-point.md` and its complete `.proof.md`, the chapter record and the `sk-prop-pe-condensed-point` unit record. I kept all four constructions and all their assertions. I read each cited node's current statement, and `citations.json` retains the exact text consulted. No new node needs a separate source review. The source of these assembly steps is the agent-written blueprint; no SGA route is used.

Step 1 takes the actual action on morphisms from `def-sfb-profinite-to-proetale`, weak étaleness from `lem-sfb-lc-weakly-etale`, preservation of finite limits from `lem-sfb-profinite-to-proetale-finite-limits`, finite-cover preservation from `lem-sfb-profinite-to-proetale-cover-preserving`, and preservation of sheaves by restriction from `lem-sfb-profinite-to-proetale-continuous`. These statements concern precisely profinite S and the same LC(S,Z) functor. Precomposition proves functoriality directly. The opening equality of structure morphisms is uniqueness of maps to the terminal scheme already stipulated in the item.

Step 2 uses the statement, not the proof, of `def-sfb-profinite-test-objects`: it explicitly includes both the composite-with-base-change construction and the full inverse-limit identity for arbitrary X. Setting X = Spec Z is allowed with no additional hypothesis; the base change by the identity is canonically the original scheme, naturally in S. This supplies the missing absolute identity as well as part 2. It is an elementary specialization of an existing node, not a new theorem disguised as a definition.

Step 3 uses `def-sfb-point-lower-star` for restriction on sheaves, `lem-sfb-point-lan-exists` for the left Kan extension of every abelian presheaf, `def-sfb-point-upper-star` for the construction after sheafification, and `def-sfb-point-adjunction` for its adjunction. Continuity was established in step 1. I retained the source's size convention: small sites relative to the enlarged coefficient universe, as in the profinite-functor definition and the Kan-extension existence statement. No arbitrary large comma-category colimit is assumed instead of that existence result.

Step 4 uses `lem-sfb-point-upper-star-unit` for the actual adjoint oplax structure and its invertible unit, `lem-sfb-point-upper-star-tensor` for all tensor comparisons, and `lem-sfb-point-upper-star-braided` for the resulting strong monoidal symmetry compatibility. The latter's statement explicitly supplies strong monoidality, so no unquoted mate/coherence theorem is smuggled into this assembly. `lem-weil-pbc-sheaf-tensor-closed` states the sheafified objectwise tensor and its sheafified constant unit. These are exactly the abelian tensor and unit used in the three comparison nodes, as seen also from `sk-def-sfb-sheaf-tensor`. The tensor is over Z, not a cartesian product.

Step 5 takes both the definition and monoidal braided assertion directly from the existing statement `def-sfb-upper-star-from-point`. For the adjunction I read `def-sfb-finite-upper-lower-star-adjunction`: it is for every scheme morphism, despite the historical 'finite' in its id. It applies at g = pi_X with abelian coefficients. Combining its Hom bijection with `def-sfb-point-adjunction` gives the displayed bijection. The composite argument is elementary from those two bijections and adds no hypothesis on X. It avoids using a new node equivalent to the clause being proved.

Step 6 reads exactly the section formula of `def-sfb-finite-lower-star`, that of `def-sfb-point-lower-star`, and the definition of X[S] in `def-sfb-profinite-test-objects`. The same base-changed morphism acts in both restriction formulas. A sheaf morphism acts by the same component at X[S]. Thus the comparison is natural, not just an equality of objectwise values. The identified functor takes values in sheaves because it is the already defined composite of sheaf-valued right adjoints. The preceding Hom bijection is consequently the asserted inverse-image adjunction.

I checked S empty (LC(empty,Z) is the zero ring and X[empty] is empty), S a singleton (LC(S,Z) = Z and X[S] = X), finite S (the finite disjoint union), X empty, and X = Spec Z. In particular I did not use faithfulness or an equivalence for arbitrary X; neither is asserted. In the empty case the inverse-image target is the trivial abelian sheaf category, consistently with the adjunction. All six steps are under 2000 characters; none hides a separate subclaim needing a new node. New-node checks B1–B9 are vacuous except for the recorded duplicate and Mathlib searches; C1–C8 are addressed by the statement-by-statement readings and the verbatim citations; D1–D5 by the genuine assembly using existing nodes and explicit final adjunction; E1–E7 by the hypothesis, coefficient, naturality and edge-case checks just described.

Mathlib searches were run through the required msearch command and their actual logs are retained. The first Loogle query failed to resolve the unqualified identifier Sheaf; I recorded that diagnostic and ran a qualified second query. LeanFinder was tried with two different phrasings, and LeanSearch returned general tensor/sheaf facts. The qualified Loogle and second grep found the general Kan-extension pullback and adjunction in `Mathlib/CategoryTheory/Sites/Pullback.lean`; I read lines 45–75. These cover existing dependencies, not the whole scheme-specific item with its LC construction and inverse-limit assertions. Accordingly this item remains a split node and no speculative Mathlib match is claimed.
