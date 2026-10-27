# Q126: lem-sfb-space-compose-admissible-blowups

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-compose-admissible-blowups.json`: item, split into four steps; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-blowup-finite-degree-ideal-descent.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-blowup-product-ideal-comparison.json`: statement, unsplit; no Mathlib match.
- `citations.json`: literal statement excerpts for every step/node citation.
- `searches.jsonl`: search-command log; `prepare.py`: sandbox-only preparation script.

## Attachments

None. Searches in `lean/WeilConjectures/` for the item tag, blowups, composition, and algebraic spaces found no declaration covering algebraic spaces. `AlgebraicGeometry.Scheme.IdealSheafData.exists_blowup_comp` (`WeilConjectures/Blowup/AdmissibleBlowup.lean:518`) and `AlgebraicGeometry.IsAdmissible.exists_comp` in the same module have scheme objects, so neither attaches to this item or its new space lemmas. The finite-degree construction discussed there is also for schemes.

## WANTED

None. All mathematical sources used are present in `literature/stacks-project/`.

## What changed and what was wrong

The item had no proof. Its mathematical statement is correct, and is unchanged: its inherited doubled TeX backslashes have been normalized to single TeX commands. The ideal form of admissibility agrees with 086B, and 086C is precisely the required composition result. I followed the more precise construction in 0860, rather than creating a node that simply restates its conclusion.

The two new facts separate the substantive finite-degree descent from the independent product-ideal comparison. The first produces an ideal and an equality on the first blowup; it asserts no composition theorem. The second applies only when the second ideal is extended from the base, so it cannot by itself prove the item for an arbitrary ideal upstairs. Both new nodes carry statements only.

There are two literal source slips worth recording. In 085N (`lemma-closed-subscheme-proj-finite-type`) the closed immersion is printed as Z into X, although the composition with pi and the Proj quotient require Z into P. The proof itself constructs Z as a closed subspace of P. In 0860 (`lemma-composition-finite-type-blowups`) the equality of extended ideals is printed as being on X'', although both sides are defined on X', and the subsequent affine charts are charts of X'. The new descent statement explicitly locates this equality on the first blowup. Neither slip requires a change to the item's statement.

The recorded unit is `sk-thm-sf-ctf-stability`; its record still has the older chapter name `sec-six-functors`, while the item and the latest blueprint locate it in `sec-six-functors-basics`. I retained the existing ownership fields. The latest blueprint proof's proper-direct-image paragraph uses compactification f=pj; this work stays within the inherited lower-level representability/Chow-modification prerequisite chain. This item is not the unit's statement and changes no unit realization.

## Not duplicates

lem-sfb-space-blowup-finite-degree-ideal-descent vs lemma-nagata-proj-closed-center-finite-degree-exists: the existing statement is for schemes and gives a homogeneous quotient presentation and support condition; the new statement is for algebraic spaces and gives an equality of extended ideal subsheaves on the first blowup.
lem-sfb-space-blowup-finite-degree-ideal-descent vs lemma-nagata-composition-extended-ideal-equality: the existing statement is a scheme comparison under its named composition-center setup; the new self-contained existential statement descends any finite-type ideal from an algebraic-space blowup.
lem-sfb-space-blowup-finite-degree-ideal-descent vs lemma-nagata-composition-center-ideal: the existing scheme node asserts finiteness and a support equality for a previously constructed center, not this ideal-descent statement on algebraic spaces.
lem-sfb-space-blowup-product-ideal-comparison vs thm-nagata-blowup-product-ideal: the existing comparison is for schemes and their previously defined maps; the new statement concerns arbitrary algebraic spaces and introduces all ideals, extended ideals, and maps.
lem-sfb-space-blowup-product-ideal-comparison vs def-nagata-blowup-product-comparison: the existing node defines scheme comparison maps and is not a theorem identifying blowups of algebraic spaces.
lem-sfb-space-blowup-product-ideal-comparison vs lem-sfb-space-common-admissible-blowups: the existing statement glues blowups of two spaces along an open into a common ambient space, and does not identify a product-ideal blowup with successive blowups.

The whole DAG was searched by tags 085N/085Y/0860, source labels, finite-degree and product/composition terms, and the imported blueprint by `blueprint_refs.py search` for blowup, finite degree, two ideals, composition finite type blowups, composition of blowups, and product blowup. The latest blueprint was also searched directly by Stacks tags. No algebraic-space duplicate was found. Some bare digit strings occur inside unrelated search digests; these are not source-tag citations.

## Mathlib searches

For the item and each new node I ran LeanFinder, Loogle, grep, and LeanSearch using msearch.py, and read their actual returned signatures. LeanFinder and LeanSearch used different natural-language formulations for each fact. All services answered. Loogle and source grep returned zero hits. The descent query returned `reesAlgebra.fg`, ideal powers and ring-level Zariski Main statements: none produces a descended ideal from a sheaf upstairs. The product query returned zero loci of products and functoriality of subscheme ideals: none identifies blowups. The composition queries returned composition of proper/finite-type/quasi-compact scheme morphisms: these do not construct a blowup center. Therefore there are zero Mathlib leaves. Original item searches are retained, with the Q126 searches appended; every new-node query and its actual digest is copied from the command log.

## Review by Q126

I read Stacks `spaces-divisors.tex` Tags 086B and 086C for the item, then the complete construction in 0860 and the inputs 085N, 085Y, 085T, and 085V. I read the chapter and unit records and the current blueprint unit statement and proof. I also opened the statements of every cited existing node and of the scheme results listed above; I did not take any assertion from an existing node's proof.

For step 1, the new finite-degree lemma states exactly the existence of d and H and the equality H O = E^d J used here. Its hypotheses are just qcqs of T and finite type of I and J, all in the item. Its source is the finite-degree presentation of the second closed center in 085N, used in 0860: on a chart A[I/a] the ideal of that center is generated by h/a^d, and multiplication by a^d gives the asserted equality. This construction is the content intentionally left in the new unsplit lemma. The remaining formation of I H is elementary: locally products of finite generators generate the product, and the product image of quasi-coherent ideals is quasi-coherent by their local module presentations. The cited definition node gives these local presentations; it is not being used as a black-box flatness or exactness theorem.

For step 2, `lem-sfb-space-blowup-chart-properties` explicitly says that the first structure map is an isomorphism off its center. U lies there because I restricts to the unit ideal. Restriction of the equality obtained in step 1 along this isomorphism gives H unit on U because both E and J are unit there. This is equality of ideal subsheaves, not merely equality of vanishing sets. Hence I H is also unit. No density or reducedness is used.

For step 3, the new product-ideal comparison explicitly states the required isomorphism over the original base with commuting structure maps, for the ideals I and H. Both are finite-type quasi-coherent ideals by construction. I checked the statement is about extension as an image ideal, not tensor pullback regarded incorrectly as an embedded ideal. The step then substitutes the actual equality from step 1.

For step 4, the existing chart-properties statement explicitly gives a local non-zero-divisor generating E. Thus E^d is a Cartier ideal. I supplied the elementary identity case of 085V: multiplication by a^(dn) identifies degree n of its Rees algebra with A, and Proj A[t] has the one chart Spec A. The inverses glue because they invert the same structure map. Applying the cited product comparison on T_1 with first ideal E^d and second J therefore removes the Cartier factor. These ideals remain finite type, and the new product comparison imposes no qcqs hypothesis on this new base. Finally the two structural identifications over U are isomorphisms by the existing chart node; the constructed map commutes with them, so its expression as a map U to U is the identity. This checks the exact last clause of the item, not just existence of an abstract isomorphism.

I tested the new statements when I is the unit ideal (the first blowup is the identity and H can be J), when J is the unit ideal (H can be I^d), when either center ideal is zero (the corresponding blowup is empty, and empty-space statements remain valid), and over nonreduced affine charts. Non-zero-divisors are used only for the exceptional ideal on the blowup, not for the original generators; nilpotents or zero-divisors on T are allowed. U may be empty or all of T. No base is assumed noetherian, separated, reduced, or affine. None of the four proof steps exceeds 2000 characters, and no non-elementary subclaim is concealed in a long step. Every cited statement has a literal excerpt in citations.json. I checked B1--B10, C1--C8, D1--D5, and E1--E7 against these files and sources; the two source slips above were repaired at the level where they enter the construction.

## Unfinished work

None for this one-level split. The two new statement-only nodes intentionally remain unsplit for later workers. Server dry-run validation and direct delivery are recorded by the delivery tool.
