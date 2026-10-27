# Stage-1 report: lem-dl-a1-ind-etale-residue-action-rigidity

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-dl-a1-ind-etale-residue-action-rigidity.json`: statement item, split in six proof steps; no complete Mathlib match. Statement and original statement dependencies retained.
- `citations.json`: six verbatim extracts covering every node used by a proof step.
- `searches.jsonl`: required search command's six actual searches (two LeanFinder phrasings, Loogle, LeanSearch, two grep queries).
- `report.md`: this report.

There are **0 new nodes and 0 new Mathlib leaves**. Existing `lem-weil-pbc-separable-first-purely-inseparable` is already a Mathlib leaf and supplies the separable/purely inseparable decomposition.

## Attachments

None. Searched `lean/WeilConjectures/` by the exact blueprint tag and by residue action, rigidity, ind-etale and henselian map concepts. The exact tag has no declaration. `Algebra.map_into_henselian_colimit` in `WeilConjectures/RingTheory/MapIntoHenselianColimit.lean:355` is only a supporting uniqueness theorem; neither it nor the compatible strict-henselization residue lift gives the field decomposition, restriction homomorphism and three-way equivalence together. No proof of the whole item was found.

## WANTED

None. All mathematical sources used are in the read-only repository. The inherited reference to `coord/dag-sync.md` names a file absent from this clone; the direct-delivery brief supplies the current read-only and live-state rules.

## Audit and changes

The imported item was unsplit and correct. No STATEMENT-DISPUTED correction was necessary. I retained its statement, source, ancestry, original search records and creation metadata. I filled its proof, exact proof dependencies, proof origin, split report and blueprint comparison. The source proof is a generalized assembly by this worker, marked `proof_origin.by = agent`; it does not pretend that Stacks 0BSW states the arbitrary-group version verbatim.

I read the fixed chapter record, the inherited `sk-d-dl-a1-setup` unit record (no proof steps), and the current `literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/` chapter and `sk-lem-wft-curve-heart/rem-dl-a1-conventions.md`. The latest convention retains the extension/trivial-inertia equivalence. Its relocation to the curve-heart unit does not change this local algebra item; the original DAG unit and ancestry remain recorded. The split realizes the same residue comparison below `lem-dl-a1-henselian-global-inertia-comparison` and `lem-dl-a1-weil-kernel-inertia`.

The generic tool `lem-weil-pbc-map-into-henselian-colimit` belongs to another unit. It is declared in `split_report.tool_uses`: it supplies uniqueness with a fixed prime and residue map; the conventions unit has no local algebra lifting theorem. This replaces no unit proof step. No top-level `tool_uses` approval was written.

## Searches and existing-node reuse

Whole-DAG searches for 08HR, 030K and 0BSW found the existing lifting and separable-first statements. I opened and read them, together with `def-pd-separable-closure`, `def-weil-pbc-ind-etale-algebra`, `def-weil-pbc-henselian-terminology`, `def-weil-pbc-separable-algebraic-extension`, `def-kun-separably-closed`, `def-pc-separably-closed`, and the pure-inseparability definition. Blueprint-wide `blueprint_refs.py search` queries included `henselian`, `henselian colimit`, `purely inseparable`, `residue action`, and `ind-etale`; `ancestor` confirms `rem-dl-a1-conventions`. The searches found no imported node stating the entire rigidity item. In particular, finite-field subfield uniqueness and normal extensions with finite automorphism groups have different hypotheses and cannot replace the residue argument.

All six new Mathlib search records are copied from actual `msearch.py` log entries, retaining each exact tool/query and the actual hit names/count. Every service answered successfully. The two ind-etale grep queries returned zero hits. LeanFinder's residue `mapAut` is just the quotient action; its unramified and integral-closure hits do not compare fixing an ind-etale algebra with a residue kernel. LeanSearch's residue-field extensionality goes from equality on a ring to equality on its residue field; it does not lift equality in the opposite direction. Loogle's `AlgEquiv.isPurelyInseparable` and its iff transfer a property across an equivalence; they do not establish the item.

I inspected `Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean:96` and lines 135–172 for `map`, `mapEquiv`, `mapAut` and the induced action, `Mathlib/FieldTheory/IsSepClosed.lean:66` and lines 80–96 for splitting and roots, and `Mathlib/FieldTheory/PurelyInseparable/Basic.lean:148` and 481 for the supporting algebraic field results. None states the whole item. The already-recorded separable-first Mathlib leaf is used directly; no replacement node is created.

## Not duplicates

No new node is created, so there are no new/existing node pairs to justify.

## Review by Q96

I read Stacks `algebra.tex`, Tag **08HR**, label `lemma-map-into-henselian-colimit`, its statement and proof; `fields.tex`, Tag **030K**, label `lemma-separable-first`, statement and proof; `fields.tex`, Tag **09HE**, label `definition-purely-inseparable`; and `pione.tex`, Tag **0BSW**, label `lemma-identify-inertia`, statement and proof. I checked their tags against `literature/stacks-project/tags/tags`. Only the uniqueness and residue-action portion of 0BSW is used, without importing its normal-domain or fraction-field hypotheses into this general local-algebra statement. The explicit general uniqueness statement is supplied by 08HR. No SGA source is used.

Step 1 constructs the action on the actual quotient E, rather than assuming a separate compatible action. Automorphisms preserve nonunits, hence the maximal ideal; evaluation on quotient representatives proves both the induced action and its group law. This is elementary and needs no theorem node. Locality of H → T is what identifies the fixed base residue field with kappa.

Step 2 uses the **statement** of `lem-weil-pbc-separable-first-purely-inseparable`: its hypotheses require only that E/kappa is algebraic, exactly an assumption here, with no finite-degree or perfectness condition. Its conclusion supplies the separable subfield and the power condition/characteristic-zero equality. The chosen kappa_s is separable algebraic and separably closed by the quoted statement of `def-pd-separable-closure`. `def-weil-pbc-separable-algebraic-extension` identifies separability with coprimality of the minimal polynomial and its derivative; its Bezout identity persists after extension of scalars. `def-kun-separably-closed` explicitly states that every separable polynomial splits, so factor evaluation proves the reverse inclusion E_s ⊆ j(kappa_s). Thus the proof does not confuse an abstract chosen closure with the relative separable closure. All four cited statements say exactly what the step uses, and each has a verbatim extract in citations.json.

Step 3 proves preservation by applying each residue automorphism to a polynomial equation with coefficients in kappa and then applying its inverse. This proves equality of the preserved subfields, not merely inclusion. Conjugation by j then defines r, and cancelling the inverse identifications proves the group law. This is elementary from step 2 and the meaning of a separable algebraic element; it does not assume that the original ring action stabilizes i(R).

Step 4 proves injectivity of restriction on residue automorphisms by the displayed p-power identity and the absence of nilpotents in a field; in characteristic zero the preceding equality of fields is used. It does not assert that an automorphism of T itself is trivial. The reverse direction is simply restriction.

Step 5 uses the **statement**, not the construction, of `lem-weil-pbc-map-into-henselian-colimit`. I checked its complete hypotheses with H in place of the source's base R, our R in place of its A, and T in place of S. The definition of ind-etale gives its filtered etale presentation. The local hypotheses give p = m_H and q = m_R and both inverse-image equalities; automorphisms preserve m_T. The two candidate maps are H-algebra maps, T is henselian, and their prescribed residue maps are j and bar(gamma) composed with j, equal when r(gamma)=1. The source theorem states uniqueness for that prime and residue map, exactly what is required. Both citations have literal quotes. Injectivity of i is allowed and retained, although uniqueness only needs locality.

Step 6 uses the surjection R → R/m_R = kappa_s. Choosing a representative of each residue class proves that fixing i(R) pointwise forces bar(gamma) composed with j to equal j. This supplies the remaining implication without assuming that every element of E lifts from R. It is an elementary quotient calculation.

I checked B1–B10: no unsplit new statement hides a proof, no new notion is introduced without a definition or explicit construction, TeX is written once, Stacks labels/tags were verified, actual searches were recorded, and no partial project or Mathlib result was treated as an attachment of the whole item. C1–C8: every non-elementary input is a cited statement, citations are literal, the only off-unit proof theorem is declared as a generic tool, and no dependency leads back through the parent inertia comparison. D1–D5: the steps carry the assembly argument and no clause was moved to a new lemma. E1–E7: the hypotheses above were checked individually, including infinite algebraic residue extensions, inseparability and the characteristic-zero case. All six proof steps are shorter than 2000 characters; none hides a separate comparison theorem.

Small cases checked: (i) H = F_p, R = T = algebraic closure of F_p with Frobenius acting: the residue restriction and fixing R are both nontrivial; (ii) H = F_p(t), R a separable closure and T = R(t^(1/p)), a henselian field: the nontrivial purely inseparable extension has no nonidentity R-automorphism, as the power argument requires; (iii) H = R = a separably closed field and T = R[epsilon]/(epsilon^2), with an automorphism scaling epsilon: the entire group may lie in the residue kernel while acting nontrivially on T, correctly fixing i(R); (iv) characteristic zero, where an algebraic extension containing the chosen separable closure equals that closure; (v) the trivial group and R = H when the residue field is already separably closed. The zero ring is excluded by having a residue field. No Noetherian, normal, reduced, finite-extension, or continuity hypothesis is used.

I corrected no mathematical statement. During self-review I made the separable-subfield identification and the quotient representative argument explicit, and ensured step 5 records both the prime and the residue map needed by 08HR. Mechanical validation and delivery results are recorded below after execution.

## Unfinished work

No mathematical work remains for this split. Validation and direct delivery follow.
