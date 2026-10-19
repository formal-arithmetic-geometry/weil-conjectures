# Stage-1 delivery: lem-trf-localization-cotangent-vanishing

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-localization-cotangent-vanishing.json`: statement, now split in five steps; no whole-item Mathlib match.
- No new nodes and no new Mathlib leaves. `citations.json` provides the verbatim cited statements; `searches.jsonl` preserves the five searches made in this sandbox.

## Attachments

None. Searched the project under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the exact blueprint tag, localization/cotangent names, full cotangent complex, and simplicial cotangent. There is no project declaration giving this item, with or without a sorry. The upstream-name index offers only naive cotangent, conormal and tangent-space declarations. The master checkout is reference material only; no purported attachment is inferred from it.

## WANTED

None. All mathematical sources used are available in `literature/stacks-project/`.

## Findings and changes

The imported statement is correct and is unchanged, including no finite-generation or finite-presentation assumptions and the permission that zero belongs to the multiplicative set. It matches cotangent.tex Tag 08R2, case (3). The imported proof was empty. I supplied the bottom-localization proof directly at the level of polynomial resolutions rather than adding another node that merely restates the vanishing.

I read the chapter sec-trace-formula, unit sk-i-curve-zero, the current main-20261015 ancestor statement/proof lem-trf-local-term-locality, the item's historical ancestry through lem-trf-affine-cotangent-comparison, and the four cited nodes. The current ancestor proof discusses contracting correspondences rather than explicitly mentioning cotangent complexes of ring localizations. The long ancestry text in the item records the historical semistable-modification support branch; it is preserved, not claimed to be a verbatim sentence of the current blueprint. This item supplies precisely the full ring-localization vanishing used by the existing affine comparison. No unit or chapter statement, binding, or route is changed.

Mathlib searches were made with msearch.py: LeanFinder for the full cotangent-complex localization statement and a second phrasing in terms of André–Quillen homology of flat epimorphisms, Loogle for H1Cotangent with IsLocalization, grep for cotangent/H1Cotangent in RingTheory/Etale, and LeanSearch for acyclicity in every degree. All services responded. I read the returned types and the relevant pinned Mathlib sources: Extension/Cotangent/Basic.lean lines 53–65 defines a single presentation differential; Etale/Kaehler.lean lines 279–284 localizes H1Cotangent. Formal etaleness and vanishing of H1 are insufficient for this item's full standard simplicial complex. The inherited search records are retained; the new records reproduce the actual search log and its digests.

## Not duplicates

There are no new nodes. The entire DAG was searched by tag 08R2 and localization/cotangent wording, and blueprint_refs.py was run on cotangent and localization-cotangent wording. The nearby etale-cotangent-vanishing node assumes finite presentation and cannot be applied to an arbitrary localization. The smooth-cotangent-identification node concerns the cotangent complex of a polynomial algebra over its original base, including localization of its target; its proof already uses the affine comparison, so using that localization clause here would create a cycle. Neither is used. The resolution-coherence node supplies a genuinely general polynomial-resolution comparison, and module-localization-exact is the already existing Mathlib tool. The new proof creates no duplicate or clause-restatement nodes.

## Unfinished work

No part of this split is left unfinished. The existing resolution-coherence theorem remains an unsplit dependency, as permitted for a one-level split; it is not asserted to be a proved Lean declaration. No Lean was written and no compiler, Lake or build tool was run.

## Review by Q41

I checked the statement against Stacks cotangent.tex, lemma-when-zero (08R2), case (3), and read the surrounding proofs lemma-localize-at-bottom (08QZ) and lemma-derived-diagonal (08R0). I also read remark-resolution (08QI), the proof of lemma-flat-base-change (08QP), the empty-variable instance of lemma-cotangent-complex-polynomial-algebra (08QH), and algebra.tex proposition-localization-exact (00CS). The proof is the resolution-level implementation of bottom localization and the identity-ring calculation in those sources.

Step 1 uses the fraction equivalence explicitly stated in lem-weil-pbc-localization-module-exact. The tensor/fraction maps and their inverses are written out. Equality after multiplying by a denominator is valid because that denominator acts invertibly on the tensor product. The inverse to localizing B again is given explicitly. This is elementary tensor balancing and fraction arithmetic, not an extra flatness theorem.

Step 2 uses exactly the existence and resolution criterion of lem-trf-cotangent-resolution-coherence and the exact-pair assertion of lem-weil-pbc-localization-module-exact. I checked that every term after tensoring is polynomial over B, the augmentation is surjective, and all the augmented exact pairs remain exact. The fraction calculation of Step 1 identifies the augmented target with B. Polynomial terms may have an arbitrary set of variables: each individual polynomial still has finitely many coefficients, which is all the common-denominator argument uses. Thus none of the finite-presentation assumptions excluded by the item are introduced.

Step 3 uses the universal-property clause, not an unrecorded base-change theorem, of def-weil-pbc-kahler-differentials. The reverse map is induced by the displayed B-derivation on P_n tensor_R B. I checked additivity, base balancing, the augmentation action in Leibniz, annihilation of the base B, both inverse equations, and the equality on dp for each face and degeneracy. This supplies a chain isomorphism, not merely degreewise isomorphic modules or an unsupported naturality assertion. It is a short universal-property calculation, so a new comparison node would be an elementary-node error.

Step 4 uses the polynomial-resolution criterion and comparison of lem-trf-cotangent-resolution-coherence. I checked the constant resolution directly: its differentials alternate between zero and the identity in the stated parity; it is augmented by the identity in degree zero. The universal property in def-weil-pbc-kahler-differentials implies Omega_{B/B}=0 since every base derivation is zero. The differential complex is consequently termwise zero. The source 08QH includes the polynomial algebra on the empty set, and no finite-type smoothness statement is needed.

Step 5 uses the comparison clause of lem-trf-cotangent-resolution-coherence and exactly the cohomology and quasi-isomorphism-localization clauses of def-weil-abstract-derived-category. The two resolutions from Step 2 have the same differential complex by Step 3, so the identity-ring calculation applies. Vanishing in all degrees is obtained from an isomorphism with the zero complex, and the converse is the quasi-isomorphism to zero. Every proof citation has a verbatim statement quotation in citations.json, including the existence/criterion clauses of the resolution theorem used in Steps 2 and 4.

I checked B1–B10, C1–C8, D1–D5 and E1–E7 against the actual node files: no new statements, missing notion nodes, mistaken cited hypotheses, unsupported non-elementary facts, source substitution, circular dependency, or moved conclusion was found. The only cross-unit proof tool is exact module localization, already a Mathlib leaf, so no additional route exception is needed. The derived-category and differential nodes are notions, not alternate route theorems. No proof step is longer than 2000 characters (the longest is 1023), and no long hidden standard comparison remains.

Small cases checked explicitly: S={1} gives the identity map and the constant-resolution calculation; 0 in S and R=0 give only zero B-modules and the same formulas; localization of Z at powers of 2 needs no new assumption; inverting all nonzero integers gives Q without finite presentation; and an infinitely generated denominator monoid is handled coefficient by coefficient. I also checked localizing the ring Z/6 at powers of 2: injectivity of R into B is not needed anywhere. The resolution theorem is cited only for its actual statement, not for internal constructions in its proof. No SGA source is used.
