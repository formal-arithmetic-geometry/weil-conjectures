## Worker report

Files written:
- dag/nodes/sec-smooth-purity/lem-pur-generic-finite-module-presentation.json: item split into seven steps; no Mathlib match.
- dag/nodes/sec-smooth-purity/lem-pur-fp-algebra-module-generic-freeness.json: statement, unsplit; no Mathlib match. This is Stacks 051S, not the finite-type conclusion being split.
- citations.json: complete verbatim statements for each of the four citations.

Attachments: none. Searched the item tag and generic finite/free/flat vocabulary in the project declarations of the read-only slopmaster2 source. FreeLocus.lean:123 proves generic freeness for a module finite over the domain itself; :575 assumes flatness. Neither covers a module finite only over a finite type algebra. The upstream master is reference material, not completion evidence. No compiler was run.

WANTED: none.

The imported item is correct as stated in 051T(b). Its module fractions are sufficient to state the result; the proof explicitly introduces localization at all nonzero scalars for its intermediate generic fibre. The unit is sk-prop-sf-cbc; this item is a below-unit algebraic tool for the generic preparation route of lem-fin-generic-radicial-smoothing, not the unit's key node. No unit record needs editing. The proof retains the 051T route indicated by the ancestor's preparation paragraphs. I avoid unnecessarily proving finite presentation of B_a itself: a finite P_a-module presentation descends to the quotient B_a by the explicit last-step argument.

Nothing remains unfinished in the split. The new 051S statement is intentionally unsplit for a later worker.

## Not duplicates

lem-pur-fp-algebra-module-generic-freeness vs lem-sbc-finite-type-algebra-generic-flatness: the existing node cites 051S in its source but states only flatness of a finite type algebra after localization. The new node concerns a separately specified finitely presented module over a finitely presented algebra and gives freeness over the base; its module is generally not finite over the base. The existing statement does not provide this result.

Whole-DAG tag and concept searches also returned lem-sbc-generic-flatness (scheme flatness), lem-sc-deg-pullback-finite (degree of line bundles), and the generic finite-presentation scheme nodes. None states 051S. Whole-blueprint searches for generic freeness, 051S, finitely presented module, 051T, generic finite and submodule found no same statement. The Noetherian algebra and finite-submodule facts were reused rather than duplicated. The new id was checked across the DAG and the project source.

## Review by NS

I read algebra.tex:28565-28637, Tag 051T (algebra-lemma-generic-flatness), including both the polynomial and general-case paragraphs. Its hypotheses are exactly domain base, finite type algebra, and finite module. I also read algebra.tex:28527-28562, Tag 051S (algebra-lemma-generic-flatness-finitely-presented), for the new statement: both algebra and module are finitely presented, the base is a domain, and the conclusion is freeness over a principal localization of the base, with possibly infinite basis. No Noetherian or injectivity assumption was imported. The finite algebra presentation and free module meanings are written inline; finite module presentation uses the existing definition node read in full.

Step 1 uses precisely the surjection from a finite polynomial algebra in def-weil-pbc-finite-type-algebra. Lifting coefficients shows the same generators generate M as a P-module, without assuming M finite over R. Step 2 spells out the fraction model, the finite-coefficient common-denominator polynomial isomorphism and kernel calculation: q(v)/s=0 gives hv in N, and v/s=(hv)/(hs). This proves the needed localization exactness directly rather than using a flatness definition as an exactness theorem.

Step 3 uses the exact statements of lem-weil-pbc-finite-type-algebra-noetherian and lem-weil-pbc-noetherian-submodule-finite, read from their JSON files, and their Stacks sources 00FN (algebra-lemma-Noetherian-permanence, algebra.tex:5991) and 00IK (algebra-lemma-Noetherian-basic, algebra.tex:12154). The hypotheses hold for the field K, its finite polynomial algebra P_K and finite free module P_K^t. K is Noetherian since every ideal is zero or the unit ideal; thus no assumption of Noetherianity on R or B enters. A generator of N_K has a numerator in N by step 2; dividing by s_i or multiplying by s_i does not change its span over P_K.

Step 4 constructs L by finitely many actual relation columns. It proves elementwise that ker(L to M) is R-torsion. The extra factor h in hs v in H is retained: equality in a localization may require an annihilating multiplier. Step 5 uses exactly the new node's 051S statement with A=P, the finite polynomial algebra with an empty list of algebra relations, and this finitely presented L. For the localized kernel it first multiplies by a power of a to obtain a genuine element of the original kernel. A further nonzero scalar kills it by step 4. The free R_a-module has no such torsion because R_a is a domain embedded in K, checked on fractions, and a free module is a direct sum of copies of R_a. This proves injectivity with no unsupported flat-tensor-exactness inference.

Step 6 gives both surjectivity and the kernel computation for localizing the finite presentation, by explicit a^k multiplication. Step 7 lifts every kernel vector from B_a^t to P_a^t and reduces its finite relation expression, so the same finite columns generate the B_a kernel. It does not require a finitely generated ideal ker(P to B). Both steps are elementary from the preceding construction and the stated fraction equality, with no additional black-box facts. Each citation has its entire verbatim statement in citations.json; the cited statements, not their proofs, supply the facts.

For the new node I checked B1-B8: it has a standalone statement, introduced objects, inline finite algebra presentation/free/localized-module definitions, empty proof and proof_deps, 051S with its exact label, and no claimed Mathlib match. Searches actually ran via msearch.py and are recorded from searches.jsonl. I read Mathlib Localization/Free.lean:78-91: its generic free-locus theorem assumes finite presentation over R itself, a missing hypothesis here; one cannot apply it to an arbitrary finite type R-algebra module (R[x] is not finite over R). I also read Finiteness/ModuleFinitePresentation.lean:36-85: the returned conversions require algebra finiteness as a base module, and do not provide generic freeness. A second semantic phrasing returned the same unrelated results. LeanSearch returned Internal Server Error and is recorded unavailable, not no match. The grep records are exact actual query strings. Existing project generic freeness for finite R-modules likewise does not establish this node. Thus the one new node is a genuine smaller input theorem on finite presentations, not the original finite-generation clause renamed.

Small cases checked: M=0 allows t=u=0 and L=0; n=0 gives P=R. B=0 and noninjective R to B are allowed; generic-zero M is handled because the torsion kernel is killed inside the free localized cover, so M_a=0. The new 051S statement allows A=0, L=0, the empty basis, and the infinite-rank base module A=R[x]. No case requires a finite rank over R. Non-Noetherian domain bases still enter only 051S, and finite generation of a generic kernel is used only over the Noetherian field-polynomial ring.

Corrections during review: made the extra annihilator h in clearing generic relations explicit, kept the a^k multiplier before applying the original torsion-kernel statement, and gave the quotient-ring kernel lifting argument rather than asserting descent of finite presentation without proof. No statement dispute or source error was found.

## Second reading by NS

- Item statement: checked against algebra.tex Tag 051T, label `lemma-generic-flatness`; the domain, finite-type algebra, finite-generation, localization, and finite-presentation clauses all match, including empty and zero cases. Verdict: correct.
- Step 1: checked against the finite-type algebra definition node and the polynomial-case construction in Tag 051T; lifting coefficients gives the stated surjection. Verdict: supported and elementary.
- Step 2: checked against the fraction definitions and Tag 051T's passage to the fraction field; common denominators and the annihilator multiplier establish the kernel equality. Verdict: supported and elementary.
- Step 3: checked against the Noetherian polynomial-algebra and Noetherian-submodule nodes, with the field and finite free module hypotheses verified. Verdict: supported.
- Step 4: checked against the finite relation construction in Tag 051T; the extra annihilator and torsion-kernel conclusion are explicit. Verdict: supported and elementary.
- Step 5: checked against the new Tag 051S node statement; its polynomial algebra has an empty relation list, and localization injectivity follows from the domain/free-module hypotheses. Verdict: supported.
- Step 6: checked directly from localized fraction equality and the finite relation presentation; numerator lifting and kernel generation are explicit. Verdict: supported and elementary.
- Step 7: checked the quotient map and relation-column reduction from (P_a) to (B_a); this yields the required finite presentation over (B_a). Verdict: supported and elementary.
- New node `lem-pur-fp-algebra-module-generic-freeness`: checked against Tag 051S and its self-contained definitions; statement only, with source and recorded searches. Verdict: appropriate unsplit dependency.

Changes made: corrected the item node's `created.item` metadata to the delivered item; no mathematical statement or proof step required repair.
