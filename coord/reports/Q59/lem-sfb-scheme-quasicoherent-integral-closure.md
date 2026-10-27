# Stage-1 report: lem-sfb-scheme-quasicoherent-integral-closure

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-quasicoherent-integral-closure.json: item, statement, split; no exact Mathlib or project attachment found.
- dag/nodes/sec-six-functors-basics/lem-sfb-integral-element-prime-local-criterion.json: new statement-only node, unsplit; no exact Mathlib match after all four search methods and a second semantic phrasing.
- citations.json: one literal statement excerpt for each citation in each of the four proof steps.
- report.md: this report.

## Attachments

None. Searched lean/WeilConjectures for the item tag and for quasi-coherent integral-closure statements. Existing normalization results and special-case finite-normalization results do not state this result for an arbitrary quasi-coherent algebra. The ring criterion has no project declaration under its tag or concept either.

## Literature wanted

None. All sources used are available in literature/stacks-project/.

## Findings and changes

The imported item is a faithful restatement of Morphisms Tag 035F (lemma-integral-closure), not a statement dispute. I retained it and its four statement dependencies. Its previous proof was empty. I followed the source's construction and isolated only its genuine missing algebra input, Algebra Tag 034K (lemma-integral-closure-stalks). The other invoked algebra lemma, Tag 0307, already has the exact general node lem-weil-pbc-integral-closure-commutes-localization and is reused. Tag 00GO is already included in the Mathlib leaf def-weil-pbc-integral-closure, whose statement explicitly asserts that the integral elements form a subring containing the base image.

I read the chapter and unit records, and the current latest blueprint sk-thm-sf-ctf-stability/_section.md and direct-images proof. This item is a low-level scheme-chart input in the inherited alteration/algebraic-space normalization support chain, not a new route for a unit-level step. The current blueprint proof (3) remains the ancestor context. blueprint_refs.py ancestor prints None for this inherited chain; I retained the item's null ancestor and used the same ancestor with this item prepended to via for its child. Whole-blueprint searches for integral closure, locally integral, and 034K found no equivalent node; same_as is [].

The new node is strictly ring-theoretic: it has no scheme, sheaf, quasi-coherence, affine-sections, or sheaf-stalk conclusion. It is neither a clause of the item nor an elementary restatement of localization preservation: its reverse implication globalizes prime-local monic equations. Its statement contains all objects, the definition of prime ideal, and references for integrality and localization. Its proof and proof dependencies are empty as required.

## Mathlib searches read

All new searches were run through the prescribed msearch.py command, and the actual logged records are copied into mathlib_searches with their original query texts. The existing item searches by Q43 are retained. I inspected the source of Mathlib/RingTheory/RingHom/Integral.lean:44ff and Mathlib/RingTheory/Localization/Integral.lean:255ff and 439ff. RingHom.isIntegral_ofLocalizationSpan concerns integral ring maps on a principal-open spanning cover, rather than a single element tested at prime localizations; obtaining its hypotheses requires spreading equations out and using the monogenic subalgebra, so this is not a one-line specialization. IsIntegral.exists_multiple_integral_of_isLocalization and the localization instance preserve/clear integrality locally, not the full prime-local detection statement. The almost-integral hits require other hypotheses and state another property. Mathlib/AlgebraicGeometry/Normalization.lean:46ff is the integral-closure presheaf for a scheme morphism; its localization theorem assumes a qcqs source morphism. Passing from an arbitrary quasi-coherent algebra to this setting requires a separate relative-spectrum realization, so it is no exact attachment or one-line Mathlib match for the item.

## Not duplicates

lem-sfb-integral-element-prime-local-criterion vs lem-weil-pbc-integral-closure-commutes-localization: the existing Tag 0307 node computes the integral closure after one localization, whereas the new Tag 034K node detects membership in the original closure from integrality at every base prime. Neither statement supplies the other's global detection implication by one specialization.

Whole-DAG tag/label searches for 034K and lemma-integral-closure-stalks returned no existing node. Whole-DAG statement searches for locally integral and integral elements at every prime found no matching statement. The affine module, associated-sheaf, and stalk statements are all reused instead of being recreated. There is no other existing node with the new node's source tag.

## Review by Q59

I read Morphisms Tag 035F in morphisms.tex:13844-13875, including every invocation in its proof. I also read Algebra Tags 0307 and 034K in algebra.tex:7596-7663, and checked their labels against tags/tags. For the new node I compared every quantifier with 034K: the localization is at a prime of the base R, the algebra is localized at its image, and no assumption that R injects into A is introduced.

Step 1 uses def-weil-pbc-module-stalk for restriction and equality of germs, and def-weil-pbc-integral-closure for the subring and base-image assertion. I checked that the latter really states the closure property rather than merely naming the set. The sheaf assertion is proved by gluing in B and checking each germ on a member of the covering. This is elementary and creates no extra lemma.

Step 2 uses lem-weil-pbc-affine-tilde-gamma-adjunction specifically for its counit isomorphism for every quasi-coherent module, not just full faithfulness. I opened and read its full statement. lem-weil-pbc-spec-module-tilde-sections gives sections and restrictions on principal opens, while lem-weil-pbc-spec-tilde-stalk-localization gives the particular germ map M to M_p over the localized base stalk. I checked both statements; the stalk conclusion is not being attributed to the sections-only node. The elementary fraction multiplication calculation makes these identifications compatible with the existing algebra structure. The newly stated 034K criterion now proves the affine integral-closure assertion under exactly those hypotheses.

Step 3 reuses the injectivity and image clauses of lem-weil-pbc-integral-closure-commutes-localization on arbitrary R to A and the powers of f. Step 2 applies also to the affine open D(f). Thus D(D(f)) equals C_f as a submodule of A_f, with the actual restriction map c to c/1. I wrote both denominator-extension and power-torsion conditions explicitly, using the equality-of-fractions relation in def-weil-pbc-module-localization. I opened pqf-lem-qcoh-principal-open-criterion: these are precisely its two hypotheses on every affine open. It needs no quasi-separatedness or nontriviality assumption. Its use is declared as a generic tool from another unit in split_report.tool_uses; no node in this unit supplies this criterion. The cited definition of a quasi-coherent algebra then supplies only the meaning of the final adjective, not an unproved theorem.

Step 4 proves injectivity directly from equality of germs, avoiding an uncited exactness-of-stalks assertion. For surjectivity it uses the existing affine module/stalk identifications and the full image clause of Tag 0307 with the complement of p as multiplicative set. Writing an integral germ as c/s gives a section of D on D(s) by step 1, since s is invertible there and c belongs to D(V) by step 2. This proves the actual inclusion image, rather than an unrelated abstract isomorphism.

I checked edge cases: on the empty scheme every sheaf assertion is vacuous and affine sections are zero rings. If R is zero, its unital algebra A is zero; the prime-local criterion has a vacuous right side and a true left side. The cases f=0 and f=1 in step 3 give respectively the empty open/zero localization and the identity restriction. No cancellation by a possible zero divisor occurs. For example a nonreduced algebra k[e]/(e^2) is allowed, and the integral nilpotent e is retained. None of the proofs imposes Noetherianity, finite type, reducedness, or affine intersections. Every step is shorter than 2000 characters. Every entry in citations.json is a literal substring of the cited statement, checked while writing the file. The source's algebraic ring lemma is separated into a new statement-only node; no other hidden non-elementary subclaim is moved inline or recreated.

## Unfinished work

None for this one-level split. The new unsplit ring criterion joins the DAG queue. No Lean was written and no compiler, Lake, or build tool was run.
