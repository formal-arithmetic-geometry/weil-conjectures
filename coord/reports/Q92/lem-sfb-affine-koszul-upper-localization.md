# Stage-1 report: lem-sfb-affine-koszul-upper-localization

Group Q92. Direct delivery. Statement unchanged.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-affine-koszul-upper-localization.json`: statement node, now split in seven steps; no Mathlib match.
- `citations.json`: twenty entries, one per step/node citation, copied verbatim from the current cited statements.
- `report.md`: this report. Local preparation scripts and the authentic `searches.jsonl` are sandbox support files.

No new nodes, and no new Mathlib leaves. No unit, chapter, Lean source or repository file was edited. No compiler was run.

## Attachments

None. I searched the item id and tag, Koszul terminology, 0GEJ and upper-truncation/localization terminology in the project's `lean/WeilConjectures`. The project contains `AlgebraicGeometry.koszul_open_orthogonality` and `AlgebraicGeometry.koszul_powers_orthogonal_of_orthogonal`, but their hypotheses require every shift. They do not prove this item's bounded-range assertion. I read their declarations rather than treating their names as a match. The existing Koszul affine detection likewise detects zero from all shifts, so it is not substituted for high-degree detection.

## WANTED

None. All literature needed for the item's proof was available locally.

## Findings and changes

The imported statement agrees with Stacks 0GEJ, implication (2) to (1), including its threshold a and its nonpositive placement of the Koszul chain complex. There is no statement dispute. I retained its statement dependencies and all inherited metadata and searches. I appended the actual new Q92 queries from `searches.jsonl`; the earlier queries are inherited provenance and were not claimed as my own executions.

The new proof gives the missing argument. It does not introduce nodes for powers orthogonality restricted to a range, supported detection in a range, or the final truncation consequence: the actual induction, factorization and degree calculation are written in the steps. Every non-elementary input already has a node. I corrected my initial final step during self-review: choosing a roof is not supplied by the definition alone, so Step 7 now cites the existing quasi-isomorphism calculus and right-fraction representation statements explicitly.

The item's `blueprint.from.node` is null in the live repository. `tools/blueprint_refs.py ancestor lem-sfb-affine-koszul-upper-localization` confirms the broken inherited ancestry; I did not invent an ancestor or edit maintainer metadata. Its nonempty inherited `from.place` locates the supporting-tool chain and remains intact. The current `literature/blueprint/latest` direct-images proof and unit were read; the generic Zariski module-sheaf input here serves the inherited 0GEN supporting tool. Searches of the whole blueprint for Koszul, orthogonal and 0GEJ found no statement of this result. `same_as` remains empty.

## Not duplicates

No nodes were created. In particular, the existing all-shifts nodes `lem-pc-koszul-powers-orthogonality`, `lem-pc-koszul-affine-detection` and `lem-pc-perfect-generation-koszul-orthogonal` are reused as source context, not recreated. Their stronger vanishing hypotheses do not cover the item's bounded range. The existing coordinate multiplication triangle, supported augmentation and affine cohomology comparison provide the needed smaller inputs.

## Review by Q92

I read the complete statement and proof of 0GEJ (`perfect.tex`, lemma-orthogonal-koszul-first-variant), the affine comparison 06Z0, and the supported-class argument 08E3. I also read the tail comparison and representing proposition 08DC/08DD in `perfect.tex`, the multiplication triangle input 062C and Koszul null homotopy 0663 in `more-algebra.tex`, ringed-space adjunction 079W in `cohomology.tex`, representable exactness 0149 in `derived.tex`, and 00E4/00E8 in `algebra.tex`. No new-node source check is needed because no new node was made.

For Step 1 I read both spectrum-topology statements: one gives the homeomorphism onto D(f), the other explicitly gives quasi-compactness of Spec of any ring, so applying it to A_f proves the required compactness. The finite-union argument is written out. The open-unit-cone statement requires an affine ambient scheme, a quasi-compact open and a quasi-coherent E, all now established; it asserts both quasi-coherence and restriction-zero for the cone. Backward rotation produces the fibre N=C[-1], not the cone itself. Shifting its cohomology preserves both properties. The cited triangulated-category definition supplies completion and rotation. I did not import a noetherian or regularity assumption.

For Step 2 I checked that the restriction-zero node concerns the actual sheafified cochain Koszul object and every integer shift. The unbounded ringed-space adjunction statement gives exactly the Hom bijection into Rj_*; for an open inclusion the derived pullback is exact restriction. Hence Hom into B and B[-1] is zero in all shifts. The Hom-into-triangle statement applied to B[-1] -> N -> E factors a map to N whose composite to E vanishes. This proves the needed n >= a assertion using the item's own hypothesis, without a one-degree error.

For Step 3 the multiplication-triangle statement allows arbitrary scalars and all other coordinates fixed; its first and third objects have precisely the two exponent tuples used. I verified that each has smaller sum(e_i-1). Hom-out-of-triangle clause (i) gives the factorization of any middle-object map through the third. This uses only the induction hypotheses at the same n, so it preserves the threshold a. I deliberately did not apply the existing all-shifts powers theorem. This step is under 2000 characters and contains the complete induction, not a hidden standard comparison.

For Step 4 the supported-augmentation theorem states the needed eventual zero composite for every shifted structure-sheaf morphism, with no orthogonality assumption. Its indexing e means exponent e+1; I reconciled it explicitly with the represent-cohomology statement's positive exponent convention. The latter really states the augmentation triangle, not merely perfection or a colimit formula. Hom-out exactness factors phi through the shifted powered Koszul object. Step 3 then kills the factor. The two indexing conventions do not introduce exponent zero.

For Step 5 I read the natural structure-sheaf Hom/hypercohomology bijection, the triangulated affine derived equivalence with quasi-inverse RΓ, and the separate natural tilde/homology comparison. The latter applies to the same functor induced by termwise tilde. Thus high hypercohomology vanishing gives vanishing of the actual cohomology sheaves. Bare conservativity of the affine equivalence would not have given this degreewise assertion; the comparison is cited explicitly. All these statements concern unbounded Zariski O-module derived categories, so there is no finite/pro-etale coefficient switch.

For Step 6 the heart/triangle theorem's clause (5) explicitly supplies the long exact sequence for any t-structure, without a boundedness requirement. Both H^n(N) and H^(n+1)(N) vanish for n >= a. Thus the map induced by the actual unit is bijective in that degree. Standard truncation kills lower degrees and retains those degrees. For Step 7 I checked that quasi-isomorphisms admit right fractions in the homotopy category, and that the fraction node gives the roof used. The three-line inversion argument then follows from the definition of quasi-isomorphism and derived localization. This final step is marked elementary only with those substantive inputs cited.

I tested r=0: W is empty, C_f=O, the positive-tuple induction is the empty base case, and the supported augmentation has zero tail, so the proof forces tau_ge_a E=0, as required. If some f_i is a unit, W=Y, the Koszul object is zero and the unit is the identity; the fibre N is zero. If every f_i=0, W is empty and the Koszul complex has O as a degree-zero summand, so the Hom hypothesis entails high cohomology vanishing; the proof's powers argument remains valid. The zero ring gives empty spectra and zero sheaf categories throughout. No positivity, nonzero-ring, boundedness, regular-sequence or noetherian hypothesis was smuggled in.

Against delivery-errors B-E: there are no new nodes or restated clauses, no unsupported tag-only step, and no cyclic use of the parent item. Each dependency's actual statement was read before its quote was placed in citations.json. The split_report declares the off-unit statements as generic tools; their role is described separately, and none replaces a step of the current unit's six-functor route. There are no proof steps over 2000 characters and no source-route substitution.

## Unfinished work

None in the mathematical split. Dry-run and push are performed after this report; their terminal results determine the delivery disposition.
