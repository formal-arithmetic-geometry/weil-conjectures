# Worker report: lem-sfb-injective-standard-resolution-quotients

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-injective-standard-resolution-quotients.json`: item, statement unchanged, now split into five steps. Polynomiality and augmentation surjectivity are proved explicitly; acyclicity uses the generic simplicial-module input below.
- `dag/nodes/sec-six-functors-basics/lem-sfb-simplicial-flat-base-change-quasi-iso.json`: one new statement-only lemma, unsplit, no Mathlib match. It concerns an arbitrary quasi-isomorphism of simplicial rings and an arbitrary degreewise flat simplicial module, without standard resolutions, injective ring maps or polynomial algebras.
- `citations.json`: six exact statement quotations, one for every citation in the five steps.
- `searches.jsonl`: genuine search-command log. `write_split.py` is the sandbox-only construction script, not a delivered library file.

## Attachments

None. Searched all of `lean/WeilConjectures/` for the exact blueprint tag and standard/polynomial-resolution terminology, and the ring and algebraic-topology sources for simplicial rings and base change. The standard resolutions returned there are abelian/injective/representation resolutions, not this ring-algebra construction. Further checks of `lean/Sheaf/RingTheory/` found the cotangent coherence interface, not an exact finished proof of the item or the new lemma. A sorry-bearing cotangent interface is not an attachment.

## WANTED

None. Every source used is available in the read-only literature tree.

## Problems found and corrections

The item had an empty proof and no proof dependencies. Its hypotheses and conclusion agree with the diagram and argument of Stacks 08SD, so its statement is retained. I expanded the complementary-variable calculation instead of creating nodes for elementary polynomial manipulations, and reused the existing free-implies-flat Mathlib leaf rather than creating another one. I separated the genuinely homological input, Stacks 08RX interpreted by 08QD, from these calculations. No distinguished triangle or comparison of cotangent complexes is asserted by this split.

### Source error

There is a harmless wording typo in the opening paragraph of Stacks 08SD (`cotangent.tex`, line 1413): it calls Q the standard resolution of C over B, but the displayed terms are A[C], A[A[C]], etc. and the later paragraph and 08SE introduce the B-based resolution separately as R. The item correctly uses Q = Pstd(C/A), exactly as that diagram requires. No correction of the item is needed, and no conclusion is drawn using the erroneous prose version.

The existing blueprint ancestry is broken upstream: `blueprint_refs.py ancestor` returns null, and the item's inherited `blueprint.from.node` is null. I preserved that result, supplied the precise Stacks calculation in the provenance, and prepended the item to the inherited `via` chain for the new node. I did not fabricate a blueprint ancestor or edit other nodes. The chapter and unit records were read; this item is only a supporting cotangent-transitivity lemma, not the unit's key theorem. The route and realization fields are unchanged.

## Unfinished work

Only the intended next-stage item, `lem-sfb-simplicial-flat-base-change-quasi-iso`, remains unsplit. The present item's natural-language proof is complete relative to its cited statements. No Lean was written, no compiler/build tool was run, no agent was started, and no repository or launcher file was edited.

## Sources and searches

For the item I read `cotangent.tex`, Tag 08SD (`remark-triangle`, lines 1407–1484), including the explicit diagram and its application of the general homology lemma, and 08SE (`remark-explicit-map`, lines 1487–1527), which distinguishes Q from the B-based R. For the new lemma I read `sites-cohomology.tex`, Tag 08QD (`remark-simplicial-modules`, lines 10393–10418) and the entire statement and proof of Tag 08RX (`lemma-O-homology-qis`, lines 10422–10483). Tag 08QD identifies L pi_! with the alternating-face complex. In the identity-cover site on Delta, module sheaves are simplicial modules and exactness and tensor are objectwise; the stated degreewise flatness therefore makes ordinary tensor compute the derived tensor in 08RX. This is precisely the canonical unit map used in the item, not an arbitrary derived isomorphism. I also checked the simplex/simplicial-object definition in `simplicial.tex`, Tag 016A.

The whole DAG was searched for 08RX, 08QD, 08SD, 08SE, O-homology-qis, flat simplicial modules, and related tensor/quasi-isomorphism statements. I read all the dependency statements cited by the proof and the four definition statements needed by the new lemma. The blueprint searches included `standard resolution`, `standard simplicial`, `flat simplicial`, `08RX`, `08QD`, `base change simplicial`, `homology equivalence`, and `tensor product homology`; no exact blueprint statement was found.

All new searches were run through msearch.py and are recorded from its actual JSON log. For the new lemma the two semantic phrasings were “A quasi-isomorphism of simplicial commutative rings induces a quasi-isomorphism from any degreewise flat simplicial module to its degreewise base change” and “For simplicial rings, extension of scalars along a homology equivalence preserves the homology of any termwise flat simplicial module”. LeanSearch and the Loogle pattern for SimplicialObject and Flat also ran. Greps searched simplicial/tensor/base-change/quasi-isomorphism terminology globally, RingTheory/Flat, and AlgebraicTopology/DoldKan. None is an exact match or one-line specialization. Returned fixed-ring tensor-exactness candidates were read at `Mathlib/RingTheory/Flat/CategoryTheory.lean:43–68` and `Mathlib/Algebra/Category/ModuleCat/Descent.lean:36–46`; they do not handle a varying simplicial ring. Dold–Kan search hits give equivalences for a fixed abelian category, not this tensor comparison. Representation standard resolutions resolve group/monoid representations and do not state this algebra result.

For the item I retained all five historical search records and added the actual new standard-simplicial-resolution semantic, Loogle and grep queries. Presentation base-change and standard-smoothness hits do not imply the homology assertion. All services used in this run responded successfully; no absence claim rests on an unavailable service. The existing free/projective-flat leaf was read, together with `Mathlib/RingTheory/Flat/Basic.lean:227–230`; its statement explicitly includes every free module, with no finite-rank assumption.

## Not duplicates

lem-sfb-simplicial-flat-base-change-quasi-iso vs lem-sfb-injective-standard-resolution-quotients: the new lemma gives the general homology invariance mechanism for arbitrary simplicial rings R to S and a degreewise flat module M; the item constructs the needed polynomial structure, establishes flatness and surjectivity for its particular standard resolutions, and obtains the B-module augmentation quasi-isomorphism by composition. The new lemma does not state a polynomial-resolution clause, and the item is not simply its conclusion under renamed letters.

lem-sfb-simplicial-flat-base-change-quasi-iso vs lem-trf-simplicial-derived-colimit-computation: the latter compares a simplicial categorical resolution with a derived colimit under representable contractibility, and has no extension-of-scalars theorem for a varying simplicial ring.

lem-sfb-simplicial-flat-base-change-quasi-iso vs lem-trf-cotangent-resolution-coherence: the latter constructs standard resolutions and compares differential complexes of already supplied polynomial resolutions; it does not establish that base change of a degreewise flat simplicial module along a quasi-isomorphic simplicial ring preserves homology. In particular its statement cannot justify the quotient resolution without the new generic input.

No existing nonmerged node's source carries 08RX or 08QD. No new polynomial-ring, tensor-product, free-implies-flat, or resolution-coherence node was created.

## Review by Q17

I checked delivery-errors B–E against the actual files and source statements. The new node introduces its rings, simplicial module, semilinear operators, degreewise tensor and canonical map; it states a theorem only, with no proof hidden in its statement. Its four statement dependencies supply exactly simplicial objects, flat modules, quasi-isomorphisms and tensor products. Its Stacks tags were checked in `tags/tags`. The new lemma is non-elementary and is a general independent input to the argument, not a relabelled polynomiality or resolution clause. Elementary calculations remain inside the item.

For Step 1 I opened `lem-trf-cotangent-resolution-coherence` and checked the literal clauses: the standard augmentation is a resolution; each degree surjects; s(P) maps quasi-isomorphically to B[0]; and the standard ring-square map commutes with augmentation. These statements apply to both B/A and C/A without extra hypotheses. The conversion to the constant simplicial ring is written out: its alternating differential is 1 in positive even simplicial degree and 0 in odd degree, giving exactly B in cohomological degree zero. This avoids confusing s(const B) with B[0] as complexes.

For Step 2 I checked the stated polynomial universal property in `def-weil-pbc-mv-polynomial-ring`. The induction starts at j:B→C, not at A→B. At its nth step, injectivity in the previous degree makes the preimage label p unique. The two explicit maps fix all coefficients and generators, hence are inverse; evaluating complementary variables at zero retracts the source inclusion and proves the next injectivity assertion. This is an elementary generator calculation, not an uncited polynomiality theorem.

For Step 3 I opened `lem-weil-pbc-projective-module-flat`. Its sentence “In particular every free R-module is flat” is exactly the assertion used after the monomial-basis description from Step 2. No claim about flatness of C/B occurs, and arbitrary basis cardinalities are allowed. The basis itself is the finite-monomial-expression definition of the polynomial ring already used in Step 2.

For Step 4 I opened both tensor and polynomial definition nodes. Tensor balancing makes the displayed coefficient map well-defined; the inverse on b times a monomial is explicit. Multiplication also agrees on pure polynomial monomials, so the isomorphism is one of B-algebras. The augmentation formula is balanced by the square established in Step 1, and its image contains every c because Q_n→C is surjective. No unproved flat-base-change assertion enters this elementary step.

For Step 5 I read the entire new statement again and matched all its hypotheses: e:P→const B is a simplicial ring map and a quasi-isomorphism by Step 1; Q is its P-module through the functorial j; and every Q_n is flat over P_n by Step 3. Its literal conclusion supplies the canonical q↦q⊗1 quasi-isomorphism as abelian-group complexes. The composite with the B-linear quotient augmentation is the original Q→C map, so inversion of the first cohomology isomorphism proves the second is an isomorphism. Kernels, images and quotients for B-modules have the same underlying groups, and the inverse of a bijective B-linear map is B-linear. Thus the final conclusion really holds in B-module complexes even though Q itself need not be a B-module. This checks the potentially misleading change of coefficient category explicitly.

I tested the boundary situations in each new statement and step. When B=C and j is the identity, every E_n is empty and the quotient is the constant simplicial B-algebra, whose alternating complex was calculated in Step 1. If B=C=0 (including A=0), the same polynomial maps and module arguments are valid over the zero ring; no nonzero coefficient is cancelled. Taking A=Z→B=F_p and j the identity verifies that injectivity of A→B is unused. Taking A=B=Z and j:Z→Z×F_2, n↦(n,n mod 2), gives an injective map with nonflat target; the argument only requires Q_n/P_n to be polynomial and remains valid. Infinite variable sets require no finite generation because every polynomial uses finite support. For the generic lemma, M=0 and f=id give respectively zero complexes and a genuine degreewise isomorphism; for constant R and S the quasi-isomorphism hypothesis forces the underlying ring map to be an isomorphism, as expected.

I checked every uses entry against a verbatim quote in citations.json, the union against proof_deps, and that the new node's dependencies cannot lead back to the item. All non-elementary steps are below 2000 characters; there is no long step hiding another lemma. No SGA source is used. The off-unit standard-resolution result is explicitly declared as a generic tool use in split_report. No geometric unit step is replaced. The preliminary server review_split check passed; the full dry run and push follow this report.
