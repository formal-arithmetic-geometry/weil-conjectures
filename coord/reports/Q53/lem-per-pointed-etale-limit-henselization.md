# Q53: lem-per-pointed-etale-limit-henselization

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-pointed-etale-limit-henselization.json`: statement, split; all original hypotheses and all three conclusions retained verbatim. Nine proof steps, using existing DAG nodes only. Mathlib searches: no exact match.
- `citations.json`: one verbatim statement excerpt for each of the twelve step/node citations.
- `searches.jsonl`: five actual searches run through the required msearch command, including two semantic phrasings. Their results were read and recorded in the item's mathlib_searches.
- `report.md`: this report. `write_split.py` is a sandbox-only writing helper, not a project tool or a delivered node.

## New nodes

None. No new Mathlib leaves. Existing elementwise filtered-algebra-colimit, henselian residue lifting, nil-maximal-ideal henselianity, and local quotient statements suffice. In particular I did not introduce a node restating any of the item's clauses.

## Attachments

None. Searched the read-only `WeilConjectures/` tree for the full blueprint tag and for henselization/henselisation, pointed etale, and limit/henselian variants. There is no project declaration covering the entire item. Mathlib's HenselianLocalRing and its root-lifting TFAE do not state the item, and StandardEtalePair's square-zero lifting theorem covers neither its hypotheses nor its conclusions.

## WANTED

None. The Stacks source needed for the argument is available locally.

## What changed and what was wrong

The imported item was statement-only. Its statement is correct; it needed an actual proof that the chosen henselian colimit has the henselization universal property, and a proof of the quotient/completion clauses without silently adding Noetherianity. I retained the source, ancestry, original creation record, statement and statement dependencies. I replaced the inherited search records by the five actual msearch queries from this worker's log. Inherited unavailability records did not describe these successful searches.

The proof now identifies the residue field of H using stage representatives and the specified trivial residue extensions. It proves the universal property over A_p by the existing ind-etale residue-lifting theorem. For each localized stage B it verifies the B-algebra extension condition by the single-etale uniqueness clause of that same theorem, instead of asserting that an arbitrary subdiagram is cofinal. Finally it constructs inverse maps H/m_H^n -> C/m_C^n for C=A_p and for each B by the two proved universal properties. Henselianity of both nilpotent local quotients is explicitly cited. Uniqueness proves the two inverse identities. The first map in the chain of quotients is then a composite of isomorphisms, and the completion maps are defined componentwise on compatible sequences. No flatness or Noetherian completion theorem is used.

The blueprint ancestry is unchanged. I read the chapter and unit records, the current main-20261015 ancestor proof, and the marked-cylinder parent's Steps 12--13. This is an algebraic tool for that existing branch (ILO V 2.2.7 and 3.2.4), not a new proof route for the perverse unit. The parent actually uses clause (1) in Step 12 and clause (3) in Step 13; these clauses remain exactly as delivered by Q95.

## Tool uses

The split_report declares the following generic off-unit tools for the maintainer's independent decision:

- `lem-weil-pbc-map-into-henselian-colimit`: existence and uniqueness of maps from a filtered etale algebra, including the single-etale case, with prescribed prime and residue map.
- `lem-weil-pbc-henselian-of-nil-maximal-ideal`: henselianity of local nilpotent quotients.
- `lem-weil-pbc-quotient-local-structure`: the actual quotient maximal ideals and locality of quotient maps.

The perverse unit has no substitute for these general ring facts. Definitions and the existing Mathlib element-representation leaf are used as notions/tools in their ordinary scope.

## Not duplicates

No new nodes were created. The existing general lifting lemma was reused rather than duplicating 08HQ/08HR; the nil-maximal-ideal lemma was reused rather than creating a henselianity theorem for each truncated quotient. Existing strict-henselization and Noetherian pair-completion nodes have different hypotheses and conclusions and are not used as substitutes for this item's ordinary, arbitrary-ring assertion.

## Review by Q53

I read algebra.tex at lemma-map-into-henselian (08HQ), lemma-map-into-henselian-colimit (08HR), lemma-uniqueness-henselian (08HT), lemma-henselization (04GN), lemma-henselization-different (04GV), and the definition-henselization paragraph (04GQ). I also read lemma-local-dimension-zero-henselian (06RS), the source and complete statement of the existing nil-maximal-ideal node, and the Newton correction theorem at Mathlib/Dynamics/Newton.lean:105 together with the Henselian definitions/TFAE in RingTheory/Henselian.lean:94--153. Those support the nilpotent-quotient input; there are no newly created nodes whose sources need separate checking. I read every cited DAG statement, not merely its proof or title.

Step 1 uses the localization definition's local structure and the existing elementwise algebra-colimit lemma's explicit assertion that every element has a stage representative. I checked that the prescribed field isomorphisms are the structural ones, so the residue map k -> H/m_H really is surjective and injective; no assumption that A -> k itself is surjective is made. All inversions occur in A_p or in the residue fields. The contraction of m_H to A is p at every stage and hence for the structural map.

Step 2 uses the full existence/uniqueness conclusion of the map-into-henselian-colimit statement with base A, source H, prime m_H, and henselian target T. Its hypotheses are exactly checked in the step: nonempty directed indexing, etale stages, the prime over p, and the compatible residue map obtained from Step 1. Any local extension of g has that same residue map because k -> H/m_H is an isomorphism. Thus the cited henselization definition is satisfied, not merely residue-preserving uniqueness for an arbitrarily chosen map.

Step 3 uses the localization statement and the given prime contractions to construct the maps A_p -> (A_a)_{p_a} -> H and check locality. The equality p_a H=m_H is proved by both ideal containments, using the hypothesis pH=m_H. Step 4 applies the same lifting theorem only to the etale A-algebra A_a, where its statement explicitly allows a single etale algebra. The two maps compared have the same prime preimage p_a and the same residue map, since k -> kappa(p_a) is an isomorphism. This proves the B-linearity missing from a bare application of part (1). Localization then extends equality from A_a to B, and part (1) gives uniqueness. No relative ind-etale presentation is asserted without proof.

Step 5 cites the exact local-quotient statement for C/m_C^n and H/m_H^n. Since n>=1, the ideal being divided out is contained in the maximal ideal, so both quotients are nonzero local rings. Every element in their maximal ideals has zero nth power; the nil-maximal-ideal lemma therefore applies with no finite-generation or Noetherian hypothesis. I checked that the induced u_n is local by its isomorphic residue map.

Steps 6--7 use the universal properties established in Steps 2 and 4, with the definition node recording precisely their quantifiers. The target C_n is henselian by Step 5, so the local lift v exists. Its locality kills m_H^n and makes its quotient factor local. One inverse identity holds on representatives of C_n. For the other, u_n v and q_H are both local maps to the henselian ring H_n and agree on C; uniqueness is therefore applicable, and quotient surjectivity gives the second identity. These are written arguments, not an appeal to a completion comparison theorem. Step 8 writes the original first quotient map as beta_n inverse composed with eta_n, and verifies the powers-of-extended-ideals notation. Step 9 uses only the cited definition of completion as compatible sequences; the reduction squares are checked on representatives and the inverse sequence map is explicit. It also verifies compatibility with each original structural map.

I checked B1--B10: no new nodes, complete original statement, sources by tag and label, actual logged Mathlib searches, correct blueprint provenance, and no eligible attachment. I checked C1--C8: every external non-elementary input has a node citation whose statement was read; all twelve quotations are literal statement substrings; no node's internal proof is used as an interface; no new reverse dependency is introduced; the three off-unit tools are declared for review. I checked D1--D5: the steps carry the universal-property and quotient arguments themselves, with no clause moved to a helper, no unproved cofinality assertion and no circular use of the item. I checked E1--E7 against the sources and the hypotheses in each application. In particular I corrected the tempting but insufficient shortcut 'same residue fields implies same completions' by writing out the nilpotent-quotient inverse construction.

Edge cases checked: n=1 gives exactly the structural residue isomorphisms; n=0, if included in the inverse limit convention, adds the zero quotient and no condition. A can be nonlocal and p nonmaximal; all local assertions are after the specified localizations. Stages can have additional points or factors, since only p_a is localized. An eventually constant system at a henselian local pointed etale algebra satisfies the same argument. For a field base the hypotheses force the local etale colimit's residue field to be that field, and the proof gives the expected identity isomorphisms. Nilpotent maximal-ideal quotients are henselian without an Artinian assumption, so even infinitely generated non-Noetherian maximal ideals cause no gap. No proof step exceeds 2000 characters or hides a separate unproved lemma.

## What remains unfinished

No requested mathematical split work remains. The existing input nodes retain their own prior proof/audit status; this delivery changes only the assigned item. Server preflight/dry-run and final push are the remaining delivery operations.
