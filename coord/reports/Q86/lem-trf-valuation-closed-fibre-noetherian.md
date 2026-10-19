## Files written

- `dag/nodes/sec-trace-formula/lem-trf-valuation-closed-fibre-noetherian.json`: statement, split into five steps; reuse existing Mathlib leaves, with no new nodes.
- `citations.json`: ten step/node entries containing the exact statements read.
- `searches.jsonl`: the actual Mathlib queries and returned candidate names, written by msearch.py.

## Attachments

None. Searched all of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item id and the notions closed fibre, valuation, Noetherianity, EssFiniteType and finitePresentation_of_finite. No declaration states both clauses under these hypotheses. The existing fibre results in scheme modules and the generic-irreducibility field extensions do not state this ring-and-module assertion. Upstream master was used only as reference material, not as evidence of finished proofs.

## WANTED

None: all sources used are present locally.

## Corrections and scope

The item was statement-only; its implicit proof is now written out. The statement and its four statement dependencies are unchanged. In particular, A is allowed to be a non-Noetherian valuation ring, and N need not be finitely presented over B. A local essentially finite type map is not replaced by a finite type map: a finite type algebra C is chosen before localization, and it is its quotient D that is finite type over the residue field. The valuation and local-map hypotheses are retained even though the proof only needs a local base and essential finite type.

The source is More on Morphisms Tag 0GSG, `lemma-mod-injective-valuation-ring`, the finite-module approximation paragraph (following the polynomial-localization reduction). Its sentence asserting that N/m_A N is finitely presented over the Noetherian ring B/m_A B is exactly the two-clause statement being split. Algebra Tag 00CT, `proposition-localize-quotient`, supplies the fraction calculation expanded in step 2; Tag 00FN, `lemma-Noetherian-permanence`, supplies finite type and localization permanence; Tag 00FP, `lemma-Noetherian-finite-type-is-finite-presentation`, part (1), supplies finite-module finite presentation. Tags were checked in stacks-project/tags/tags. The existing finite-presentation leaf cites the broader finite-modules section (0517); its statement and recorded Mathlib theorem are nevertheless precisely the fact needed. No existing node was changed to improve its source metadata.

Mathlib searches found Algebra.EssFiniteType.isNoetherianRing, Algebra.EssFiniteType.quotient_map, Module.Finite.quotient, Module.Finite.of_restrictScalars_finite and Module.finitePresentation_of_finite. Their source statements were read. The first theorem is applicable after passing to the residue-field algebra, not with base A. The last theorem needs finiteness over the quotient ring, not merely finiteness over B. Rather than introduce duplicate helper nodes, the split gives the quotient localization conditions and quotient-module generating argument, and cites the three existing matching permanence/presentation leaves. No new Mathlib leaf is claimed for the entire conjunction.

The chapter and unit records were read; this remains a commutative-algebra tool below the recorded Tag 0GSG ancestry, without changing the unit route or realization records. Blueprint searches for Noetherianity, closed fibre, finite modules and finite presentation, together with whole-DAG title/statement searches, found no blueprint node with the same two-clause assertion. The existing blueprint ancestry and precise from.place are retained, with same_as empty.

## Not duplicates

No new nodes. Reused `lem-weil-pbc-finite-type-algebra-noetherian`, `lem-weil-pbc-localization-noetherian`, and `lem-sc-noetherian-finite-module-finite-presentation`. The existing prime-quotient localization node assumes the quotient ideal is prime and therefore cannot be applied to m_A B, which need not be prime. The principal-localization quotient node does not cover an arbitrary multiplicative set W. The needed localization criteria are instead checked directly from the already-cited definition of fractions.

## Unfinished work

None in this stage-1 item. No Lean source, compilation, Lake, global build, live project file, or launcher file was changed.

## Review by Q86

I read Tag 0GSG at the exact finite-module approximation sentence and then opened the cited Algebra source proofs 00CT, 00FN and 00FP(1). The item preserves precisely the valuation-ring, local-map, essential-finite-type, and finite-module hypotheses. It has no flatness requirement and no hidden finite-presentation requirement on N. Those extra hypotheses occur elsewhere in 0GSG and are unnecessary for the sentence isolated here.

In step 1, the statement of `def-weil-pbc-essentially-finite-type-algebra` gives C, W and the A-algebra isomorphism B = W^-1 C, including equality of fractions. The statement of `def-weil-pbc-finite-type-algebra` gives finite algebra generators. Reducing those polynomial expressions proves finite type for D over k. The statements of `def-weil-field` and `def-weil-pbc-noetherian-ring` are used literally: maximality gives an inverse modulo m_A, and ideals of a field have the stated finite generating sets. All of these are explicit definition-level arguments.

In step 2, I checked the statement of `lem-weil-pbc-localization-noetherian`: it lists exactly units, fraction representatives, and the zero-kernel annihilator criterion. This step verifies those hypotheses without yet applying the theorem. Its other citation, the essential-finite-type definition, states the exact fraction equality used. The finite sum c/1 = sum a_i d_i/w_i exists by the meaning of the extended ideal m_A B. I wrote the common denominator w, its numerator e and the additional multiplier u explicitly; this avoids treating m_A as finitely generated and does not cancel a possibly zero denominator. Thus (uw)c lies in m_A C and proves the required annihilator condition. This is a routine calculation from the cited fraction definition, not a new comparison theorem left implicit.

In step 3, I opened the full statements of both Noetherian permanence leaves. `lem-weil-pbc-finite-type-algebra-noetherian` accepts the finite type k-algebra D, with the Noetherian base established in step 1. `lem-weil-pbc-localization-noetherian` accepts the arbitrary multiplicative set W-bar and all three verified conditions. Neither requires the base valuation ring to be Noetherian, the localized ideal to be prime, or W to be finitely generated. Both are recorded Mathlib leaves, so no off-route unsplit tool is introduced.

In step 4, `def-weil-finitely-generated-module` explicitly states finite linear-combination generation. The action of B on N/m_A N kills m_A B by the displayed finite sum, so it descends to the required quotient-ring action. Reducing a generating expression proves finite generation for that action. In step 5, the statement of `lem-sc-noetherian-finite-module-finite-presentation` says exactly that a finite module over a Noetherian ring is finitely presented; both hypotheses now hold for R and Q. I did not use a definition of finite presentation as if it asserted this theorem. Each cited statement has been copied verbatim to citations.json.

I checked the field case m_A=0, the identity algebra B=A, a nondiscrete non-Noetherian valuation ring, zero N, and a local finite type algebra with nonreduced closed fibre (for example B=A[x]_(m_A,x)/(x^2)). The last example confirms why a prime-quotient lemma is insufficient; the proof uses no primeness. Empty algebra/module generating sets and empty sums/products in the kernel calculation work with the usual 0 and 1 conventions. If a quotient were zero the localization criterion still works. In the actual local situation m_A B is contained in m_B and hence proper. No new statements require separate small-case tests. All five proof steps are shorter than 2000 characters, and none hides a separately assumed auxiliary result. Checks B through E found no source error or statement dispute and no circular dependency; the only changes were the formerly absent proof, its dependency union, the fresh search records, and the split metadata.
