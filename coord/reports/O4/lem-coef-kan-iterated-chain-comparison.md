# Worker report: lem-coef-kan-iterated-chain-comparison

## Files written

- dag/nodes/sec-six-functors/lem-coef-kan-iterated-chain-comparison.json: statement node, now split into five proof steps; no exact Mathlib match. The statement, original citations/searches, ancestry and maintainer fields are preserved.
- citations.json: verbatim statement excerpts for every cited node in each proof step.
- searches.jsonl: actual additional Mathlib searches through the prescribed msearch.py command, all read before recording verdicts.
- report.md: this report.

No new nodes and no new Mathlib leaves. Only the sandbox was written; no Lean file, compiler, Lake invocation, live repository mutation or manual git command was used.

## Attachments

None. Searches in /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact blueprint docstring tag, the item id, Kan/chain, iterated pullback/path, constant path, and homotopy-pullback spellings found no project declaration giving the item. The unrelated iterated blow-up and ordinary descent pullback hits do not state this theorem.

## Literature wanted

WANTED: archived Kerodon Construction 3.4.0.3 (010B), Proposition 3.4.0.7 (0329) and Proposition 3.4.0.9 (032B), for lem-coef-kan-iterated-chain-comparison. The two propositions and their proofs were read online at https://kerodon.net/tag/0329 and https://kerodon.net/tag/032B. These identifiers are Kerodon tags, not Stacks tags. No Stacks result states this simplicial comparison, and no SGA source is used. No literature was downloaded or written. The finite induction is marked proof_origin.by = agent.

## Problems found and changes

The interrupted attempt left only dispatcher marker files, with no item copy, proof, report, citation file, search log or active delivery process. There was consequently no earlier completed split to invalidate or repeat. The repository node was unsplit, with no proof steps. Its existing Mathlib searches were retained and actual new searches appended. The last attempt's prospective proof was available in the parent Q42 report and was checked against the current cited statements rather than accepted as a proof on its own.

The statement is mathematically sound and unchanged. The endpoint identity is needed before applying invariance; it is established by a separate elementary recursive coordinate check, rather than inferred after the weak-equivalence induction. Every path is an n-simplex of the internal functor simplicial set, not merely an edge assigned to a vertex. Kan fibrancy of the homotopy tower uses the unconditional Kan clause of the binary comparison; no fibration property of the homotopy-tower endpoint is assumed.

The chapter and unit records were read. The existing unit is sk-prop-sf-biduality-general, and its realized statement is not this auxiliary node, so no unit record is changed. The nearest blueprint ancestor is prop-coef-integral-exceptional-adjoint. Its main-20261015 proof paragraph 2 contains the derived coefficient adjunction calculation whose mapping-space foundation this chain supports. The classification-diagram Segal step reaches this item through the preserved ancestry. There is no route replacement or statement dispute.

## Not duplicates

No new nodes are proposed. Whole-DAG keyword/source searches and blueprint_refs searches for homotopy pullback, iterated pullback, constant path and Kan fibration were used to locate existing ingredients. The only blueprint match for iterated pullback was the unrelated descended-model node. The binary comparison, invariance and finite strict-tower fibrancy nodes already state all non-elementary inputs needed here. Their unit bindings agree with the item's unit.

Mathlib searches through leanfinder, leansearch, loogle and grep returned path-object gluing, ordinary iterated pullback associativity, and stability of binary trivial-fibration pullbacks. A second semantic phrasing was run, and the alternate grep spelling query returned no hits. I read PathObject.lean:275-285 (trans), Instances.lean:227-242 (binary pullback instances), and RightHomotopy.lean:77-82. A path object of one object has a specified weak-equivalence diagonal; the general E in this item has only two endpoint fibrations and need not be a path object of B. Consequently PathObject.trans is not a one-line specialization of this item. The other hits do not identify the prescribed finite comparison. No unavailable service or rejected query was silently treated as evidence of absence; retained historical parser rejections keep their original verdicts.

## Unfinished work

None within this one-level split. Existing dependency nodes may still need their own work; they are reused without modification. Remote validation and delivery are performed using the prescribed delivery command after this report is written.

## Review by N4

I read the node, the two online Kerodon propositions and proofs, the current statements of all four cited nodes, the parent classification-diagram node/report, and the blueprint ancestor's displayed derived-adjunction proof. The item is the positive-length induction of the binary comparison and invariance statements. There is no change in universes or simplicial-set conventions: def-cbc-enhanced-diagrams-cones gives degreewise pullbacks and the internal functor model, and defines weak equivalences by realization, components and all based homotopy groups. Both s and t remain Kan fibrations as originally stated, and no zero-length tower or nonemptiness assumption has been added.

Step 1 uses def-cbc-enhanced-diagrams-cones for the degreewise simplicial constructions. For an n-simplex b, the constant path is explicitly projection from Delta^1 times Delta^n followed by b. Its two restrictions agree with b and it commutes with all simplex operators. Thus both pullback equations hold, and taking t of the unchanged last E coordinate gives the strict endpoint identity. This is a direct check of the definition, marked elementary; no homotopy-extension assertion is hidden in it.

Step 2 uses exactly the statement of lem-coef-kan-iterated-pullback-fibrancy: every strict tower P_j is Kan, and its last endpoint is a fibration. Its hypotheses are exactly the item's Kan B,E and its two horn-lifting maps s,t. Its P_j and endpoint are the same recursive objects used here. This avoids proving the finite strict-tower lemma a second time or reaching into its proof.

Step 3 sets up simultaneous induction on H_j being Kan and c_j being a weak equivalence, with base j=1. The identity comparison induces identity maps on all the groups and components, so this is elementary and uses no theorem by implication.

Step 4 uses lem-coef-kan-pullback-path-comparison twice. First P_j,E,B are Kan, and s is the required fibration, giving the precise map a into the auxiliary binary path pullback J. Second H_j,E,B are Kan by the induction hypothesis, so the unconditional Kan clause gives H_{j+1}. I checked that the cited node explicitly states that Kan clause and both choices of the fibration hypothesis. Nothing here asserts that h_j is a fibration or that invariance creates Kan fillers.

Step 5 uses lem-coef-kan-homotopy-pullback-invariance with U=P_j, U'=H_j, V=V'=E, W=W'=B and maps c_j, identity_E, identity_B. The induction hypothesis supplies the only non-identity weak equivalence; step 1 supplies h_j c_j = r_j, and the other square is literally s=s. All six objects are Kan. The induced map leaves the B-path and final E coordinate unchanged, exactly as the cited statement says. Its composite with a is written on simplices and is c_{j+1}, so there is no unspecified identification. Composition preserves weak equivalences directly because the induced bijections on components and isomorphisms on groups compose, with the intermediate image basepoint. The definition node is cited for precisely that weak-equivalence convention. This completes the induction, retaining the endpoint equality from step 1.

For B empty, existence of E to B forces E empty, and all positive-length strict and path towers are empty; every comparison is the identity of the empty simplicial set and the Kan conditions are vacuous. For E empty and B nonempty all towers are again empty. At j=1 the comparison is identity; at j=2 it is exactly the existing binary map. For discrete Kan complexes all paths are constant and the comparison is an isomorphism. For E=B and s=t=identity, the path tower is finite composable paths and the formula inserts constant ones, consistent with the binary theorem. No choice of a base vertex is needed; the homotopy-group criterion is applied to each existing source basepoint. There are no new statements needing separate small-case tests.

I checked delivery-errors B through E against these files: every notion is defined inline or through the existing definition node; no new unsplit node hides a proof; each non-elementary fact is a cited statement; no clause is relocated into a fresh node; the induction base, hypothesis and successor are explicit; the exact strict endpoint and coordinate formula are preserved. citations.json quotes are literal parts of the cited statements. The step lengths are 871, 364, 317, 639 and 1222 characters, so no non-elementary step exceeds 2000 characters. No reference uses SGA 4 or SGA 4½. No maintainer-owned field or another item's node has been changed. The independent maintainer review remains separate from this author's check.
