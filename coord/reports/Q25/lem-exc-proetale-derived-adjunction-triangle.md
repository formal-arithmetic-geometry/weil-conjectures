# Stage-1 delivery: lem-exc-proetale-derived-adjunction-triangle

## Files written

- `dag/nodes/sec-smooth-purity/lem-exc-proetale-derived-adjunction-triangle.json`: existing statement split into eight proof steps; no statement change; no new nodes and no new Mathlib leaves.
- `citations.json`: nineteen verbatim statement quotations, one for each citation in the eight steps.
- `searches.jsonl`: the five actual Q25 Mathlib searches; their results were read, and their exact tool/query texts are appended to the item's inherited search records.
- `report.md`: this report. `write_split.py` is a sandbox-only construction script, not a delivery file.

## Attachments

None. I searched the blueprint tag and the closed-support/derived-adjunction notions under the read-only slopmaster2 `WeilConjectures/`. The tag is absent. `AlgebraicGeometry.ProEtale.lowerStarClosedUpperShriekAdjunction` and `AlgebraicGeometry.ProEtale.derivedLowerStarClosedUpperShriekAdjunction` in `SixFunctors/ProEtale/Derived/ClosedImmersion.lean` construct related adjunctions, but are not declarations stating every clause of this conditional lemma, including the explicit kernel-normalized derived counit. I therefore do not claim an attachment from their docstrings. The exact master source was checked for this helper's tag as reference material only, with no match.

## WANTED

None. The current blueprint proof and the Stacks sources used below are present locally.

## Findings and corrections

The item was statement-only; there was no earlier Q25 split, report, or search log to resume. Its hypotheses are sufficient. I kept the statement, coefficient category, and all clauses unchanged. In particular, the closed unit on supported sheaves, exactness and full faithfulness of closed pushforward, and annihilation by open restriction are assumptions here. This proof does not import a theorem establishing them only for commutative coefficients.

I read the current `main-20261015` proof of `lem-exc-proetale-support-triangle`, also compared its older master proof, and read the item's chapter and supported-localization unit. This helper makes precise the parent's first sentence about computing the ambient right adjoint and its final sentence identifying the associated triangle's first map. It does not prove or assume that triangle. No unit record or route is changed. The older unit text mentions an excluded SGA route; that reference is not used in this proof. The sources actually used are the blueprint and the specified Stacks lemmas.

The derived-functor equalities in the unchanged statement are interpreted as its explicitly specified canonical comparisons. The proof displays both comparison arrows and the exact formula for the counit. A generic derived-adjunction theorem requires absoluteness hypotheses; instead of silently assuming them, this proof constructs the Hom bijection directly from K-injective targets, checks naturality after localization, and evaluates that bijection on the identity.

The Q25 Mathlib searches returned the generic `CategoryTheory.Adjunction.derived`/`derived_counit` infrastructure, scheme module restriction adjunctions, a scheme ideal-kernel adjunction, and generic abelian-category transfer/Serre-class results. I read `Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean:40–150`, including `derivedε_fac_app` at line 125. These supply infrastructure under already-established adjunction/derived hypotheses; none constructs this supported-kernel adjunction and proves the full explicit assertion in one specialization. The results of the second semantic phrasing were also read. I preserved the searches inherited in the repository item rather than representing them as newly run Q25 searches.

## Not duplicates

No new nodes. I searched the whole DAG and `tools/blueprint_refs.py` for derived adjunctions, closed support, termwise adjunctions and the relevant tags. The generic existing nodes are reused. `lem-exc-proetale-closed-support` and `lem-exc-proetale-closed-essential-image` restrict their module coefficients to commutative rings, and `det-lem-formal-closed-support-sheaves`/`derived` use the condensed admissible coefficient setting. None is silently identified with this conditional finite, possibly noncommutative left-module assertion. No blueprint node found states all of this helper's clauses under these hypotheses, so `same_as` remains empty.

## Tool uses

The split report declares five off-unit generic tools: `lem-weil-pbc-termwise-adjunction-homotopy`, `lem-weil-pbc-right-adjoint-preserves-kinjective`, `lem-weil-pbc-ring-sheaves-grothendieck`, `lem-weil-pbc-kinjective-functorial-existence`, and `lem-weil-pbc-kinjective-total-derived`. They provide general homological algebra needed by the supported-localization route, not a replacement geometric route. The other generic infrastructure citations are definitions or existing Mathlib leaves.

## Review by Q25

I checked the split against delivery-errors B–E with the item, every cited statement, and the sources open. There are no new unsplit nodes to carry hidden proofs, duplicate clauses, or unsearched Mathlib facts. I read Stacks `derived.tex` Tags 070I (`lemma-K-injective`), 070K (`lemma-enough-K-injectives-implies`), 070Y (`lemma-K-injective-defined`), 08BJ (`lemma-adjoint-preserve-K-injectives`), 09T5 (`lemma-derived-adjoint-functors`), and 015F (`lemma-right-derived-exact-functor`), and `injectives.tex` Tags 079P (`theorem-K-injective-embedding-grothendieck`) and 079Q (`remark-existence-D`). The blueprint itself is agent-written, and the kernel calculation and naturality/counit calculations are supplied explicitly here, so the item's proof origin is honestly marked agent.

Step 1 uses the statement of `def-weil-sheaf-of-modules-category` for sectionwise kernels, `def-weil-proetale-inverse-image` for the actual direct-image formula, and `prop-weil-pbc-proetale-constant-exact` for the additive exact inverse image with transported left action. The last statement explicitly permits a finite noncommutative ring. On an object over the open, the restriction unit is the identity, so its kernel vanishes there; the supported-unit hypothesis then applies to exactly this kernel. The kernel maps, their additivity, and naturality of the supported-unit isomorphism are written out. Step 2 uses the same kernel universal property and the item's full faithfulness assumption to give inverse Hom maps. I checked both composites and both naturality variables. Its identity transpose is precisely the sheaf counit claimed in the item. No extra closed-image theorem or unproved geometric assumption enters either step.

Step 3 cites `lem-weil-pbc-termwise-adjunction-homotopy`, whose statement includes actual chain-map units/counits and the adjunction on homotopy classes, not merely an objectwise correspondence. It also cites `lem-weil-pbc-right-adjoint-preserves-kinjective`, which applies to additive adjoints between abelian categories when the left adjoint is exact. The constructed adjunction has exactly that orientation: closed pushforward is left adjoint and is exact by hypothesis. Both functors are additive, so both cited statements apply to the unbounded complexes in the item.

Step 4 cites `lem-weil-pbc-ring-sheaves-grothendieck`, whose statement concerns sheaves of left modules over an arbitrary, not necessarily commutative ring sheaf on a small site, and `lem-weil-pbc-kinjective-functorial-existence`, whose hypothesis is precisely Grothendieck abelianness. These statements provide K-injective resolutions on both pro-etale sites with the chosen size convention. I did not use `prop-weil-pbc-kinjective-resolutions-exist`, which by itself states only an etale-module version.

Step 5 explicitly checks the exact-functor hypothesis of `lem-weil-pbc-kinjective-total-derived`: the cone block matrix, minus-projection and shifted differential are preserved by an additive termwise functor. `def-weil-abstract-derived-category` supplies those formulas; `lem-pur-homotopy-category-triangulated` supplies the triangulation of the homotopy category and exactness of localization; `def-weil-triangulated-category` specifies exactness. This verifies the input condition instead of claiming that the nonexact sheaf right adjoint is exact on abelian categories. The total-derived theorem's actual statement supplies both existence and the comparison isomorphism on every K-injective complex.

Step 6 uses `lem-sf-exact-functor-derived-triangulated` solely for exact closed pushforward descending termwise. The statement of `lem-weil-pbc-kinjective-hom-derived` permits any source complex and a K-injective target, so its two applications have targets respectively I and H(I), already proved K-injective. The middle bijection is exactly that stated by `lem-weil-pbc-termwise-adjunction-homotopy`. The final postcomposition is the natural invertible comparison from step 5. Step 7 uses the same K-injective Hom statement for all target morphisms and the localization definition for the source variable. Its inverse-quasi-isomorphism argument is written explicitly; it does not assume a new comparison lemma. Changing a K-injective representative is among the target isomorphisms already checked, so the bijection extends to the full derived categories.

Step 8 evaluates the preceding bijection on the termwise counit, whose transpose is the identity by the cited homotopy-adjunction statement. I checked the domains and order of all three factors: first apply the inverse RH comparison by derived closed pushforward, then the exact-pushforward comparison, then the localized kernel counit. The displayed isomorphism of objects is the inverse change of source. Thus the result identifies the specified arrow as well as the object, with no appeal to uniqueness of right adjoints without a normalization.

I tested the empty closed and empty open cases: for Z empty, F and H are zero and the counit is the unique zero map; for U empty, F is the identity, the supported unit is an isomorphism, and the construction gives the expected equivalence adjunction and its derived version. For the zero coefficient ring all module categories are zero and every displayed bijection and comparison remains valid. A noncommutative example such as matrices over a finite field changes none of the factorizations: all arrows are left-linear and no tensor symmetry is used. The construction imposes neither boundedness nor injectivity of the individual terms of the given K-injective I. Every non-elementary input is an existing cited statement, not a tag used in place of a DAG citation. All eight steps are shorter than 2000 characters; no long step hides a new lemma. All nineteen quotations were checked against the exact current statement text.

## Unfinished work

None within this split. Dependencies remain separate DAG items as required by stage 1. No Lean file was written and no compiler, Lake command, local preflight, local check_dag, or local review_split was run.

## Validation

The first server dry run rejected the phrase “the item’s hypothesis” in step 3 under the self-contained-statement wording check. I replaced it with “by hypothesis”; the exactness assumption already appears explicitly in the unchanged statement. The revised required server dry run exited successfully: `OK (not pushed)` at `6d2f183912`, with server preflight passed. Delivery uses the same checked split and citations.
