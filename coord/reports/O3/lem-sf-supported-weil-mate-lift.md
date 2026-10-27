## Files written

dag/nodes/sec-smooth-purity/lem-sf-supported-weil-mate-lift.json: statement, split using existing nodes; not a Mathlib leaf.
citations.json: verbatim statement quotations for every step citation.
No new nodes; zero new Mathlib leaves. All current searches were run through msearch.py; inherited searches remain intact.

## Attachments

None. I searched the project for the exact blueprint tag and for supported Weil/mate notions. WeilConjectures/WeilSheaf/Localization.lean has a supported localization construction, but its WeilComplex is a derived category of Weil sheaves, whereas this item uses fixed pairs in the geometric derived category. Its assertions therefore do not state this item. The general IsoAlgebraAdjunction.lean construction supplies existing lem-sf-fixed-pair-adjunction-lift, which I reuse without claiming an attachment of this item.

## WANTED

None. The blueprint, project categorical source, Mathlib mate source, Stacks derived.tex and BBD are available.

## Statement corrected

STATEMENT-DISPUTED: exactness of the functors alone does not make an arbitrary adjunction's unit and counit compatible with their specified shift structures. The original conclusion asserted shift compatibility for the counit-normalized mate without imposing that compatibility on the given adjunction.

Explicit test: take X_0=Spec(F_{q^2}), i_0=id and U_0 empty. Its geometric fibre has two points exchanged by geometric Frobenius P. On the bounded constructible E-derived category, use i_*=J=id with their usual exact shift structures. Modify the identity adjunction by a natural automorphism t of id: on the first point in cohomological degree n use 2^n, and on the second point use 1. In this semisimple derived category this is a natural automorphism. Let eta=t and e=t^{-1}. This is an adjunction, and e_K:K->K followed by K->0 is a supported distinguished triangle, unique on morphisms with prescribed middle component. All prescribed pullback and direct-image Frobenius comparisons are the canonical ones. The normalized mate is P(e_K)t_{PK}. On its first point in degree n it is 2^n; on the second it is 2^{-n}. It does not commute with the usual shift comparison. Thus the assertion as written is false for arbitrary adjunction data.

The corrected statement specifies exact adjunctions (units and counits commute with the chosen shifts). It also spells out what the given coefficient comparisons must preserve: the supported triangles and adjunction maps, Frobenius comparisons and tower coherences. Without normalization, arbitrary scalar comparisons for J need not commute with a Frobenius comparison either. No coefficients or geometric hypotheses are weakened.

This is faithful to the blueprint's final Weil-structures paragraph, which concerns the actual derived adjunctions and their specified coefficient comparisons, not arbitrary renormalizations. The sole current citer, prop-sf-localization-all-stages, still applies: its supported adjunction is built from the counit triangle and its exact coefficient transports, not from the modified identity adjunction in the counterexample. Its final Weil clause is preserved. The item is not a unit key node; no unit record changes.

## Proof and source audit

The item's source is literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sf-localization/prop-sf-localization-all-stages.proof.md, final paragraph. I read the whole proof, including its finite, integral, rational and common-stage construction, and the chapter/unit records. The split concerns only the final Weil argument; it assumes the supported adjunction and triangle already constructed there.

I read the statements of all cited nodes, checked their dependency closures do not reach this item, and read the categorical implementation in lean/WeilConjectures/CategoryTheory/Endofunctor/IsoAlgebraAdjunction.lean, especially mapOfNatIsoAdjunction and its carrier formulas. I also read Mathlib/CategoryTheory/Adjunction/Mates.lean (mateEquiv, its counit and unit identities, and pasting), the TR3 and third-isomorphism passages of literature/stacks-project/derived.tex, and BBD Proposition 1.1.9 and Corollary 1.1.10 on PDF pages 24-25. No prohibited SGA route is used.

The current Mathlib searches include two different semantic phrasings, Loogle, LeanSearch, and source grep, with results retained in the item and searches.jsonl. The Loogle NatIso query was rejected as an unknown identifier and is recorded as an invalid query, not evidence of absence; the subsequent mateEquiv query ran and returned the expected general mate declarations. The leanfinder Frobenius hits concern monoidal Frobenius reciprocity, not geometric Frobenius. Mathlib contains generic mate facts but not this full supported fixed-pair assertion.

## Not duplicates

No new node is created. Whole-DAG and blueprint searches for mates, supported triangles and fixed pairs found the reusable mate and fixed-pair nodes. The proof does not move a clause into a new node.

## Review by O3

Step 1 uses exactly the stagewise equivalence assertion of lem-sf-automorphism-constructible-stage-equivalence and the actual closed exchange formula in lem-sf-open-closed-weil-mate-structures. The automorphism lemma explicitly allows non-k-linear scheme automorphisms, so it applies to geometric Frobenius. I did not substitute the finite/integral-only isomorphism-pullback lemma at rational coefficients.

Step 2 instantiates def-weil-pbc-adjunction-mate with L=i_*, R=J, G=Q and H=P, and square a^{-1}. I checked all source/target orders. The invertibility lemma requires Q to be an equivalence and P fully faithful, both supplied in step 1. Uniqueness follows from the mate's actual transpose bijection, not from a claim that an arbitrary invertible square always has invertible mate.

Step 3 cites the existing fixed-pair adjunction theorem for the actual unit and counit, after verifying its inverse-mate hypothesis. Its second application uses the closed exchange formula in the cited open-closed Weil node. This also verifies the equivariant counit used to recover JK from i^*i_*JK. This is a generic category-theoretic tool from another unit, declared in split_report.tool_uses.

Step 4 invokes TR3 from the cited triangulated-category definition. I wrote out why its third component is the prescribed open comparison: adjunction with Rj_* and the invertible open counit make precomposition with the open unit injective after j^*. Thus the connecting-arrow equation is obtained from a triangle morphism, not assumed from a vague claim about functorial cones. Every triangle is in the underlying category. The prescribed middle and outer components are isomorphisms, so no unsupported detection-of-isomorphisms argument is needed.

Step 5 computes the actual fixed-pair morphism equation by naturality of b and uses the cited definition, rather than identifying the derived category of Weil sheaves with pairs. The recovery under i^* uses the equivariant closed counit already proved in step 3.

Step 6 explicitly computes Frobenius-equivariance on all Hom groups, not only on their invariant subsets. The computation uses naturality and the previously established counit equation; no extra non-elementary lemma is hidden.

Step 7 uses the actual identity and pasting assertions of lem-weil-pbc-mate-pasting and the bijection in def-weil-pbc-adjunction-mate. I checked that the corrected hypotheses preserve the units/counits required to identify both pasted squares. This is precisely where arbitrary unnormalized adjunction or coefficient data would fail.

I checked the checklist B-E against the files: there are no statement-only new nodes, no duplicate or elementary nodes, no source tags passed off as missing dependencies, and no step takes an assertion only from another node's proof. All step uses have verbatim quotations in citations.json. No step exceeds 2000 characters. Small cases i=id, Z empty, U empty, the zero complex and identity Frobenius give the expected identity or zero lifts. The two-point example above isolates the genuine missing shift hypothesis and explains its correction. I checked rational E and common-stage coefficients separately; neither requires triangulating the fixed-pair category.

## Unfinished

No mathematical subclaim of this one-level split is left unaccounted for. The cited unsplit or split nodes retain their own independent proof obligations. Server validation and delivery follow this report.
