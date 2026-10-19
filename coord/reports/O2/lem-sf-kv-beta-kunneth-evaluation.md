# Worker report — N2

## Files written

- `dag/nodes/sec-six-functors/lem-sf-kv-beta-kunneth-evaluation.json`: split in eight proof steps; the original statement is unchanged. No Mathlib match for this equality of specified geometric maps.
- `dag/nodes/sec-six-functors/lem-sf-exterior-projection-kunneth.json`: one new statement-only lemma, status unsplit. The specified compact-support projection maps commute with the specified exterior Ku_! maps. The Mathlib searches found no match.
- `citations.json`: a verbatim statement quotation for every step/node citation.

## Attachments

None. Searched the item id, externalHom, evaluation/Kunneth and projection/external product in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`. `AlgebraicGeometry.Etale.HasKunnethComparisons.externalHom` in `SixFunctors/Etale/Derived/Kunneth/Comparisons.lean:121` is a structure field asserting existence of an isomorphism, not equality with a specified morphism. `hasKunnethComparisons` ends in sorry at line 175. Neither states this item. The ordinary-cohomology Kunneth and proper projection declarations in `Finiteness/Kunneth.lean:72–97` also have sorry and state different assertions. No new-node attachment was found by projection/product searches of the same project sources. Upstream master is reference material, not proof evidence.

## WANTED

None. The source is the available current blueprint. Its final beta sentence is agent-written and omits the map calculation, so the expanded argument is explicitly marked `proof_origin.by = agent`. No forbidden SGA source is used and no claim is attributed to a Stacks tag that does not state it.

## Findings and corrections

The item is a map-normalization lemma, not the theorem that beta is invertible. Its original statement correctly restricts to finite coefficients and actual constructible exceptional adjoints and explicitly asks only for equality. I retained it, its immutable ancestry and its unit. The current `main-20261015` proof and unit were read; this realizes only the last beta paragraph, without changing the chapter or unit route. No unit-record edit is needed because this is not the unit's key statement node.

The formerly empty proof needed to specify three things that the source suppresses: evaluation of tensor–Hom through ordinary and exceptional counits; the transpose of the two successive ordinary product maps; and the projection/exterior-product square. The first is already the statement of `lem-pod-hom-chain-counit-formula`. I reused it instead of adding a differently named normalization lemma. Its hypothesis supplies the specified exceptional adjunction of the operation datum; in this application that very constructible adjunction is supplied by `thm-sf-ambient-adjoint-class` and `sk-def-sf-operations` (vi). I do not apply the conditional existence assertion of `fix-prop-adjunctions` (2), nor assert unrestricted ambient admissibility. Clauses (1) and (3) of that node supply only the ordinary adjunction and ordinary composition counit.

The new lemma isolates the geometric projection/exterior-product square, before internal Hom or exceptional alpha is involved. It does not restate any clause of the item: it has arbitrary pairs of morphisms and arbitrary coefficients and asserts a compatibility solely of compact support, ordinary pullback and tensor. Even with that square supplied, the item's steps 3–6 and 8 must still compute the Hom-chain representative, ordinary transpose, exceptional counit and final evaluation transpose.

## Not duplicates

Whole-DAG statement searches for projection/external/exterior/Kunneth, and blueprint_refs searches for `projection formula`, `tensor–Hom`, `evaluation`, `exterior projection`, `Künneth projection`, and `projection Künneth` were read. The new id was absent. No Stacks tag is assigned to the new lemma, so there are no same-tag pairs. The closest statements were opened:

- lem-sf-exterior-projection-kunneth vs lem-sf-kunneth-coherence: that node assumes an axiomatized datum and states relative symmetry, triple associativity, base change and one identity-factor projection comparison. The new node states the two-coefficient exterior projection square for the actual finite operations; it is not one of those displayed formulas or a one-line specialization.
- lem-sf-exterior-projection-kunneth vs sk-thm-sf-kunneth-relative: the relative theorem constructs Ku_! and gives coherence and its one-identity-factor specialization. It does not explicitly state compatibility with tensoring both arbitrary source factors by pullbacks of independent target coefficients; proving that square requires pasting those coherences.
- lem-sf-exterior-projection-kunneth vs prop-sf-pf-coherence: this states the composition and base-change laws for PF in a supplied datum, not compatibility with the exterior Ku_! map.
- lem-sf-exterior-projection-kunneth vs lem-sf-product-compactification-identity: that compares a relative product map with its proper/open compactification construction, with no two independent target coefficients.
- lem-sf-exterior-projection-kunneth vs lem-trf-product-projection-comparison: the trace lemma assumes one proper f, repeats f on two factors, includes structure-morphism integration and additional coefficient data; it does not state this general square.
- lem-sf-exterior-projection-kunneth vs lem-trf-relative-kunneth-counit: the latter gives the ordinary counit transpose of the inverse relative product for two proper maps to one base, with no arbitrary external projection coefficients.

The existing Hom-chain counit lemma was reused directly; no new version of it was created. The other opened candidates (`lem-sf-open-external-tensor-normalization`, `lem-sf-finite-exchange-projection-commshift`, `lem-trf-cohomological-evaluation-calculus`) state respectively open normalization, shift compatibility and correspondence-comparison calculus, not the new square.

## Mathlib searches

The interrupted sandbox contained searches.jsonl but no split or report; there was no running delivery. I read the recorded hits and retained that log. The item inherits earlier searches and records its own logged concept searches. The new node records only exact msearch queries that actually ran: grep, Loogle, LeanSearch and two LeanFinder phrasings. The services returned hits, not unavailable errors. I read the relevant candidate sources: Mathlib `Monoidal/Closed/Functor.lean:45–116`, `Monoidal/Functor.lean:947–985`, `Monoidal/ExternalProduct/Basic.lean`, and the counit and closed-evaluation formulas in `Adjunction/Basic.lean` and `Monoidal/Closed/Basic.lean`. Cartesian Frobenius/exponential comparisons, lax monoidality of a right adjoint, and exterior products of functor diagrams do not supply the actual geometric compact-support square. No leaf is claimed merely from an analogous generic name.

## Review by N2

I checked the current blueprint `sec-six-functors/sk-thm-sf-kunneth-verdier/_section.md` and its proof, particularly the beta paragraph beginning with finite-projective generators and ending with the ordinary/exceptional adjoint calculation. I also read `sk-thm-sf-tensor-hom`'s displayed Hom chain and `sk-thm-sf-package/fix-lem-tensor-adjunction.proof.md` step 1 for the existing counit representative. The new lemma makes precise the projection-formula square used by that same beta sentence; its source is an expanded blueprint argument, not an invented quotation from human literature. It leaves the genuinely geometric compatibility as a new unsplit task.

For step 1 I opened the statements of `sk-def-sf-operations`, `sk-thm-sf-tensor-hom`, `thm-sf-ctf-stability` and `thm-sf-ambient-adjoint-class`. These give respectively the actual operations, the tensor–Hom identification, preservation under (i)–(v), and the finite comparison-class exceptional adjunction. Here all schemes are separated finite type, all h_i are locally closed and hence separated finite type, and all complexes are bounded constructible finite Tor. In particular B_i is a legitimate coefficient for PF; no preservation on arbitrary unbounded pro-etale objects is assumed. The finite-projective identifications themselves are part of the item's prescribed setup. Step 2 is the written local scalar-contraction calculation under those identifications; finite-projective retracts of finite-free modules obey the same formula. I checked that no sheaf is treated as globally constant, and the derived interchanges retain Koszul symmetry.

For step 3 I read `lem-pod-hom-chain-counit-formula`, including its actual p_N formula, not just its title. With M=F_i, N=L_i, and t the identity of B_i it gives exactly the displayed e_i. `lem-pod-closed-uncurry-laws` supplies the evaluation representative. I checked the ordinary counit comes from `fix-prop-adjunctions` (1), and PF is exactly the transformation defined in `def-exchange-projection`. The constructible exceptional adjunction required as data in the Hom-chain statement is already present from step 1; optional ambient admissibility is not being deduced.

For step 4 I opened `sk-lem-sf-kunneth-star` and `def-exchange-projection`. The former is the canonical ordinary identity-factor product map, and the latter supplies the exact exchange and projection mate formulas used in calculating its transpose. The factorization is h=b a through S_1 times Y_2, matching the requested first-factor-then-second-factor order. I read clause (3) of `fix-prop-adjunctions`: its ordinary composite counit is precisely the formula that combines the two transposes. This is not an assertion that a square mate preserves invertibility.

Step 5 uses the existing Hom-chain statement for the product h and a specified t, rather than quoting its proof. Naturality of the counit then substitutes the transpose computed in step 4. The resulting u is typed from F tensor h^*B to W, and alpha is only applied after that. `lem-pod-closed-uncurry-laws` identifies the uncurried representative; no inverse alpha appears.

For step 6 I read clause (ii) of `sk-def-sf-kv-maps` and the entire generic adjunct–counit statement `lem-weil-pbc-adjunct-counit-identity`. They give mu P(alpha)=(mu_1 external mu_2) K_W, exactly the formula needed, with the correct direction of Ku_!. The naturality asserted by `sk-thm-sf-kunneth-relative` gives the second identity, since u is the external product u_1,u_2 after delta. In step 7 the new lemma is applied only after all its finite-coefficient, separatedness and ctf hypotheses have been checked in step 1. Its entire displayed square is quoted verbatim in citations.json. Step 8 precomposes by K_F inverse in the contravariant Hom argument; I checked this direction rather than cancelling a map on the wrong side. Clause (iii) of the KV definition is exactly the two-evaluation transpose, and uniqueness of curry gives equality.

I tested the new statement with identity morphisms (both sides are the same signed interchange), zero inputs and empty schemes (both maps are zero), the unit coefficient (the unit projection normalization), finite-projective ranks zero and one, and shifted coefficients (both paths use the same tensor permutation and hence the same Koszul sign). No smoothness, properness, global triviality of a lisse sheaf, or inverse of alpha or beta has entered. The item is unchanged, so no statement dispute is needed.

I checked delivery-errors B–E with the actual node statements open: the sole new node is self-contained, not elementary relabelling of the item, is not an existing statement, and is not a Mathlib specialization. Every proof citation now has a quotation from its statement. Off-unit generic tools are declared in split_report.tool_uses, not in maintainer-owned tool_uses. I shortened no hidden argument merely to pass the long-step check: all eight steps are below 1,100 characters; the one substantive extra square is a node of its own. I corrected the initial quotation selection so step 6 quotes alpha's defining transpose rather than beta's definition, and step 3 quotes the ordinary adjunction rather than only its composition law.

## Unfinished work

The new node is intentionally statement-only, as required for a one-level stage-1 split; its proof remains a downstream task. No Lean was written or compiled. Required server checks and delivery follow this report.
