# Stage-1 report: lem-trf-compact-support-exchange-counit

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-compact-support-exchange-counit.json`: the existing item, split in six steps; statement, statement dependencies, inherited searches, and blueprint ancestry retained. No new nodes or Mathlib leaves.
- `citations.json`: verbatim quotations from every statement cited in every proof step.
- `report.md`: retained delivery report, revised to describe the repaired proof and checks below.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact item tag and for compact-support/exchange/counit terminology. The two lexical hits concern braided categories and geometric-stalk exchange; neither states this geometric compact-support counit identity. The upstream master sorry declarations are not treated as proofs.

## WANTED

None. The current blueprint and the Stacks source needed for the geometric normalization are present locally.

## What was wrong or corrected

The retained three-step proof said that exceptional composition mates and triangle identities make the right-hand ordinary transpose equal to Theta. This inference was not supplied by the cited `lem-sf-mate`: that node concerns exceptional adjunctions and does not identify the ordinary mate of the compact-support exchange. I replaced this unsupported inference by the actual proper/open compactification computation. The existing node `lem-trf-compact-composition-proper-square-normalization` already states both normalizations the computation needs, so no new lemma is introduced. In particular I did not create a node restating this item's conclusion.

I retained all previous Mathlib searches and read `searches.jsonl`, including the later NX searches. Their hits are general over-category adjunction identities, locally constant functions, chosen-pullback formulas, or ordinary compact-support predicates on functions. None identifies the geometric derived exchange and its specified compact-support composition, so this item is not a Mathlib leaf. The preserved inherited queries and results are not represented as newly run searches. No new node requires new searches.

The initial required dry run, run before editing the retained split, exited successfully with `OK (not pushed)` at `ed757383b6`. This established that the saved work was mechanically intact; it did not resolve the mathematical inference above.

## Source error

The first paragraph of `literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-p-proper/lem-trf-trace-map-exchange.proof.md` says that since alpha and alpha-prime are proper, Ex_! equals Ex_*. This is the wrong orientation for the exchange in this item: its direct-image arrows are beta and beta-prime, which need not be proper. For example take alpha to be the identity of the affine line and beta the open immersion of the punctured affine line. Both vertical maps are proper identities, but beta_! of the constant finite coefficient sheaf has zero stalk at the omitted origin whereas beta_* has a nonzero degree-zero stalk there. The two exchange transformations consequently have different functors as endpoints and cannot simply be identified. This is an error in that proof sentence, not in the item statement. The repair keeps compact support, factors beta as an open immersion followed by a proper map, and proves the claimed normalization on those factors. It changes no chapter route, unit step, statement, coefficient datum, or properness hypothesis.

## What I could not finish

No part of the item's stage-1 argument remains unwritten. The pre-existing normalization node is reused as a statement-level dependency; this delivery does not claim to prove that node or the whole dependency closure.

## Review by NX

I read the worker rules, delivery-errors B through E, the `sec-trace-formula` chapter and `sk-p-proper` unit, the current item and retained sandbox, the current main-20261015 blueprint proof of `lem-trf-trace-map-exchange`, and the cited statement nodes. I also read Stacks `more-etale.tex`, Tag 0F7B (`lemma-shriek-proper-and-open`, beginning at line 2460) and Tag 0F7J (`lemma-shriek-composition`, beginning at line 3159). Their proper/open interchange and compactification construction explain the geometric normalization. I use the existing pro-etale normalization statement for its exact named maps; I do not silently transport an etale theorem to arbitrary pro-etale inputs. There are no new nodes whose sources or duplicate pairs need separate review.

Step 1 uses `lem-weil-pbc-proper-base-change` exactly for stability of properness, `thm-sf-ctf-stability` (i), (iii), (iv) for the intermediate operation domains, `lem-sf-proetale-constructible-origin` (ii) for bounded finite-coefficient etale-origin witnesses, and `thm-sf-comp-composition` on its explicitly witnessed domain. All of these statements were opened. Boundedness and constructibility come from the item, the coefficient ring is finite, and every intermediate map is separated of finite type over the stated field. Thus composition's witness hypothesis is checked rather than assumed from the notation D^b_ctf.

Step 2 uses `thm-nagata-compactification` for a compactification of the separated finite-type beta and the two base-change statements for proper and open maps to type its pullback. The target is a separated finite-type field scheme, hence quasi-compact and quasi-separated as required by Nagata. `def-exchange-projection` explicitly defines T by the proper-exchange/open-exchange composite for this compactification; `fix-lem-exchanges` (2), (4) supplies normalization, pasting, and choice independence. `thm-sf-comp-composition` supplies associativity. The definition and both clauses of `lem-trf-compact-composition-proper-square-normalization` give the exact chi and Theta_p that factor Theta. That node is not a duplicate of this item: it identifies specified compositions in the proper/proper and proper/open squares, whereas this item proves the counit identity for arbitrary beta. Its dependency graph does not reach this item, so it introduces no circular proof.

Step 3 checks the proper factor with the actual ordinary exchange formula of `def-exchange-projection`. The two successive mates are the composite mate of `lem-weil-pbc-mate-pasting` (2); `fix-prop-adjunctions` (3) specifies that ordinary direct-image composition is the conjugate of pullback composition. Clause (1) of the existing normalization node identifies this conjugate with Theta_p. This is precisely what the discarded exceptional mate citation did not supply. All four maps in this smaller square are proper, so the proper comparisons used in that clause apply.

Step 4 checks the open factor. `prop-weil-open-closed-recollement-adjunctions` gives both open adjunctions and their invertible units. `lem-sf-open-tensor-normalization` supplies the inverse of b as the stated open-adjunction transpose, with the exact constant finite-coefficient specialization to the map in `def-exchange-projection`. This explicit inverse, `lem-weil-pbc-mate-pasting` (2), and the inverse rule in `def-weil-pbc-adjunction-conjugate` identify its right conjugate with the restriction exchange M. Clause (2) of the normalization node then gives lambda and lambda-inverse. No unproved assertion that a general square mate of an isomorphism is invertible is made: this use is conjugation between two composite adjunctions.

Step 5 opens the formulas of `def-weil-pbc-adjunction-mate` and `def-weil-pbc-adjunction-conjugate`, computes the ordinary mate C, and computes its open adjunct. I checked the source and target of the unit u-prime at Z, counit naturality at u-prime, and the open triangle epsilon at J-prime Z composed with J-prime u-prime. The open Hom bijection supplied by the recollement adjunction is injective. Clause (2) of the normalization node says exactly that chi has the same adjunct lambda-inverse, so C equals chi. Undoing the ordinary a adjunction uses `fix-prop-adjunctions` (1), not an exceptional adjunction.

Step 6 displays all five equalities of the final calculation: substitute the chosen-compactification formulas, insert the open-factor identity, use naturality of T_p at chi, insert the proper-factor identity, and reassociate Theta. The cited defining formula, choice-independence/pasting statement, composition theorem, and ordinary adjunction statement justify these operations. This proves the item for arbitrary Z on its stated finite-coefficient domain, without imposing properness on beta or beta-prime.

I checked the elementary identity/empty-square cases: identity alpha reduces to the identity comparison and identity counit; a proper beta reduces to the ordinary square-conjugate computation; an open beta reduces to the computed open adjunct; empty inputs give the unique morphism. The conjugation directions and the open unit inverses agree in all these cases. Every non-elementary input is a cited statement; the categorical cancellations are written in the steps and use the stated mate formulas. All six steps are shorter than 2000 characters, and none hides a separate geometric sublemma. The proof is agent-written, from the available geometric sources and existing DAG statements, and is labelled accordingly. No SGA source is used. The statement and statement dependencies are unchanged; all writes are confined to this sandbox, with no Lean or build command.

The cross-unit normalization node is declared as a generic tool use in the item split report; its statement is quoted in citations.json and the reason is that the proper/open compactification comparison is established in the additivity unit, not by this unit's own route.
