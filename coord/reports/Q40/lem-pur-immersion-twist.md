## Files written

- dag/nodes/sec-smooth-purity/lem-pur-immersion-twist.json — statement, split; no Mathlib match. The proof has three steps and reuses the existing DAG.
- citations.json — one literal statement excerpt for each dependency of each proof step.
- report.md — this report.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. I read WeilConjectures/EtaleCohomology/Purity/Smooth/Coprojection.lean in /home/ubuntu/weil-src-slopmaster2, including the complete theorem at lines 255–267 and its parameters. AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_derivedTensor_shiftTateObject has a proof without sorry and gives the analogous formula for etale ModuleCat coefficients and a HasTateTwist datum. The DAG uses the pro-etale finite-coefficient construction fixed in def-pur-conventions. There is no exact attachment: the change of site and actual coefficient-object comparison is not part of this declaration. I make no claim about its transitive axiom closure.

## WANTED

None. The proof follows the current blueprint's one-line specialization, with the shifted inverse calculation written out by the worker. All non-elementary inputs already have DAG nodes. No SGA source was used.

## Findings and corrections

The assertion is unchanged. Its explanatory parenthesis attributed restriction compatibility to def-coefficient-twists-detailed, but the current statement of that definition does not assert restriction compatibility. I replaced this attribution by det-prop-sfb-cartesian-coefficients-twists and named det-def-sp-tate-twist-locally-free for invertibility. The definition def-weil-derived-tensor defines the K-flat derived tensor product; it does not itself prove invertibility. The proof now supplies an actual inverse and the signed shifted-complex calculation.

The current coefficient conventions explicitly make the finite-coefficient purity statements at Lambda=A; higher-coefficient versions are supplied by the transport section. Step 1 makes this scope explicit, without adding or changing any hypothesis. I did not replace the pro-etale coefficient category by the source's etale category, nor replace the unit's co-projection proof route by another purity theorem. The item is a consequence within sk-lem-coprojection, not that unit's key node; its unit realization fields are therefore untouched.

## Not duplicates

No new node was created. I searched the whole imported blueprint using blueprint_refs.py search with “twist”, “Tate twist”, and “co-projection”, and searched the DAG for twist/invertibility/pullback/restriction/shift statements. The general lem-pur-coprojection and sk-lem-coprojection contain a more general co-projection statement; they are not additional exact formulations of this item's sole specialization. Other twist nodes concern inverse images, local freeness, or internal Hom, rather than exceptional inverse image. blueprint.same_as is accordingly empty.

## Review by Q40

I read the full current main-20261015 statement and proof of lem-pur-immersion-twist, the current lem-pur-coprojection statement, pur9-cs-def-invertible, the chapter record, and the unit sk-lem-coprojection. The argument keeps the unit's invertible-factor specialization. I also read the actual current statements of all eight cited nodes, rather than treating the imported dependency lists as proofs. No new-node source review is needed because there are no new nodes.

Step 1 uses def-pur-conventions only for the finite coefficient domain and det-def-sp-tate-twist-locally-free for the twist equivalence and its inverse. That theorem states both the sheaf evaluation isomorphism and the derived-category autoequivalence, so no claim of derived invertibility is taken merely from a definition. The two shifts cancel in the total tensor differential of def-pc-tensor-complex-sheaves: 2m is even for every integer m, so moving the indices changes neither the differential signs nor total degree. Applying the same reindexing to an acyclic second factor verifies the K-flat condition in def-weil-derived-tensor. This short shift calculation turns the cited twist inverse into an inverse for the shifted object. The step as a whole is marked non-elementary because it invokes the twist autoequivalence theorem. pur9-cs-def-invertible specifies precisely the required inverse datum. I created no node for this short calculation.

Step 2 uses det-prop-sfb-cartesian-coefficients-twists for the isomorphism of inverse-image twist sheaves with their module structures; its statement explicitly includes all integer d. The prime ell is invertible on both schemes because they are over the fixed characteristic-p field and ell differs from p. The finite-level clause of def-weil-derived-pullback-tensor-hom explicitly represents derived pullback by termwise inverse image. Termwise application commutes with a cochain shift, including its sign, so the displayed rho has exactly the required source and target. This corrects the original C4 defect: restriction compatibility is now taken from a theorem that actually says it.

Step 3 applies the exact displayed statement of lem-pur-coprojection with W=X. The morphism is a closed immersion as required, K is the given bounded constructible finite-Tor object, and the shifted twist has the inverse constructed in Step 1. Composing with derived tensor of rho gives precisely the target formula. The inverse of the second arrow is tensor of rho inverse, so no unproved preservation-of-isomorphisms assertion is hidden. Its natural/canonical normalization is the general co-projection followed by the stated coefficient restriction, as required by the item.

I checked the edge cases m=0, m negative, K=0, Z empty, and i the identity. The shift computation uses evenness, not positivity; the inverse for a negative m is the opposite twist with opposite shift. For m=0 it reduces to the unit factor, for the identity it reduces to restriction along the identity, and for zero/empty input all maps have the required zero objects. No smoothness, regular-immersion condition, divisibility of n by the ramification index, or purity theorem is used. A traversal of the available prerequisite statements and proofs found no path back to this item. Ten pre-existing references are absent from the local deeper closure; server preflight must compare these with its baseline.

Against delivery-errors B–E: no new statement-only leaves or duplicate nodes are needed; the TeX and introduced data remain those of the source; every step's non-elementary input has a cited node and every quote in citations.json is literally in its current statement. Off-unit uses of the two coefficient theorems and the generic total tensor/pullback descriptions are declared in split_report.tool_uses for maintainer review. They verify hypotheses and identify the factor in our unit's co-projection specialization, and do not replace that route. There are no unsupported Stacks tags, SGA references, or fresh mathematical statement disputes.

## Continuation audit, 2026-10-17

I re-read the current main-20261015 statement and separate proof, both supporting coefficient-theorem source files, the invertible-object definition, the chapter and unit records, and all eight cited DAG statements. The finite-coefficient convention is explicit in def-pur-conventions. For negative m the inverse autoequivalence exchanges m and -m; for all m the shifts cancel with even signs. The theorem used in Step 3 states the co-projection for arbitrary objects with an invertible factor, so it supplies exactly the map used here. All eight quotation records remain literal excerpts of their current statements, and proof_deps is exactly the union of the uses lists.

I repeated the item's four required searches through msearch.py, then the second LeanFinder phrasing, the quoted upperShriek Loogle query, and the whole-Mathlib grep. The first repeated semantic query returned different ordinary-pullback hits, now recorded in the node; neither semantic phrasing returned exceptional co-projection. The quoted Loogle query and focused whole-Mathlib grep returned zero hits. I checked the existing project theorem again: it is over the small etale site with an abstract HasTateTwist datum; the current item is over the pro-etale site with its concrete finite-coefficient twists. It remains an analogy, without an exact attachment.

The first complete preflight returned a stale-base error and unrelated NG report/node changes which are absent from this sandbox. I am retrying the authorized delivery command without editing the launcher, its worktrees or the shared repository. No push is authorized for this worker; the required final accepted sandbox goes to the second reader.

## Unfinished work

None in the one-level split. The existing input lem-pur-coprojection remains an independently queued item; splitting it is outside this assignment. The sandbox is left for the required independent second reader, with no push.

## Second reading by Q40

- Item statement: compared hypothesis by hypothesis with main-20261015 `sk-lem-coprojection/lem-pur-immersion-twist.md` (order 2351), its separate proof, the fixed finite-coefficient scope in the current `def-pur-conventions`, and `pur9-cs-def-invertible`; PASS. The mathematical assertion and canonical map are unchanged. The worker's correction of the explanatory restriction citation is justified by the actual coefficient-theorem statement.
- Step 1: opened all six cited node statements; compared the coefficient hypotheses with `def-weil-l-adic-coefficient-extension`, the inverse equivalence with clause 3 of `det-def-sp-tate-twist-locally-free` and its main-20261015 source, the inverse datum with `pur9-cs-def-invertible.md`, and the tensor differential with Stacks 012Z (`homology.tex`, `definition-associated-simple-complex`) and 06YM (`sites-cohomology.tex`, `lemma-derived-tor-exact`, in section 06YL); REPAIRED the unstated finite-ring/ell-torsion checks, the negative-m specialization, and the K-flat shift shorthand. The reindexings now give the terms and the differential signs explicitly. Only these calculations are elementary; the twist autoequivalence is cited as a theorem.
- Step 2: opened `det-prop-sfb-cartesian-coefficients-twists` and its main-20261015 source, and the complete finite-level clause of `def-weil-derived-pullback-tensor-hom`; PASS. The theorem includes all integer twists, coefficient-module compatibility, and arbitrary scheme morphisms with ell invertible. The displayed rho is obtained by termwise inverse image, with precisely the shift of the pulled-back differential.
- Step 3: opened the current `lem-pur-coprojection` statement and the unit/chapter records and main-20261015 section texts; PASS. Its closed immersion, K, and invertible L are exactly the data in force. Tensoring rho and its inverse yields inverse maps, and the composite has exactly the target's source, target, and canonical normalization. This specializes the unit route; no smooth or regular immersion hypothesis is used.
- New nodes: none; PASS B1–B7 and C5 without introducing any leaf. Independent whole-DAG/current-blueprint searches for the twist co-projection, shifted Tate object and exceptional-twist formula found the item and other, differently scoped results; the existing generic co-projection is correctly reused.

Small cases checked independently: m=0 gives the coefficient unit and no shift; m=-1 uses the inverse of the m=1 twist equivalence and shifts -2 and 2; all integer shifts are even. For K=0 both sides vanish; for Z empty both objects lie in the zero sheaf category; for i the identity the map is the canonical tensor identification. On Spec k with E=Q_ell and n=1 the coefficient ring is F_ell and the twists are lines, so no zero-ring or characteristic exception is hidden. n=0 is excluded by the explicit coefficient conventions, rather than silently by this split. For a ramified E and n=1, ell still lies in (varpi_E), so the finite-ring theorem's ell-primary hypothesis holds.

Independent searches through msearch.py used a rank-one-local-system/extraordinary-pullback phrasing, the quoted rightDerivedUpperShriek Loogle query, and a whole-Mathlib search for coprojection, invertibility with shift, TateObject and UpperShriek. The actual outputs are in searches.jsonl and are now summarized in mathlib_searches; none states this result. I read the full parameter context and lines 255–267 of the analogous slopmaster2 theorem in EtaleCohomology/Purity/Smooth/Coprojection.lean: it is over the small etale site and an abstract HasTateTwist datum, so it is not an exact attachment for this concrete pro-etale statement. No Lean or compiler was run.

Changes made and why:

- Step 1 now cites the existing coefficient-extension definition and verifies finite ell-primary coefficients and ell invertibility before applying the twist theorem (C4/E1).
- Step 1 spells out the m<0 equivalence and both chain reindexings, including K-flatness, instead of “the same reindexing” (E5).
- Updated proof_deps and citations.json for the additional existing definition, and enlarged the invertibility and inverse-autoequivalence quotes so their complete relevant data are visible (C3).
- Appended three independently executed search records; no nodes were added or removed.

The proposed off-unit uses of the two coefficient theorems remain explicitly described in split_report.tool_uses for the maintainer to judge. I checked review_split.py lines 103–108: it expressly permits this proposal field and reserves promotion into the top-level maintainer-owned tool_uses for the merge. The two generic operation definitions do not replace the unit route. No top-level tool_uses, unit/chapter binding, live project, or launcher file was changed. The first worker's report and its Review by Q40 section are retained. There is no statement dispute and no SGA citation in the delivered nodes.
