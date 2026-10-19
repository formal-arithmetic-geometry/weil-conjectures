## Worker report

Files written: `dag/nodes/sec-deligne-laumon-a1/lem-per-admissible-finite-quotient-separated.json`: statement item, now split in three steps. Its statement is unchanged. The statement dependency on surjectivity is now explicit.

## New nodes

None: 0 new nodes and 0 new Mathlib leaves. Existing Mathlib leaf `lem-weil-pbc-finite-proper` and existing split `lem-weil-pbc-surjective-universally-closed-separated` already state all non-elementary inputs.

Attachments: none. Searching slopmaster2 WeilConjectures for the exact blueprint tag, admissible quotients, separated quotients, and finite groups found no declaration proving the item. I read the affine quotient discussion in `WeilConjectures/Mathlib/AlgebraicGeometry/ColimitsOver.lean`: it supplies affine colimits and flat base change, not the separated-target assertion for an arbitrary admissible action. The master source was searched as reference only, not as evidence of a closed proof.

WANTED: none.

No error in the statement or blueprint was found. The original item was unsplit; the quotient hypothesis is sufficient without any use of freeness, invertibility, or regularity. No part remains unfinished.

## Searches and existing nodes

I searched the whole DAG for quotient separatedness, surjective universally closed separated images, finite/proper morphisms, and the relevant Stacks tags, then opened the matching nodes. Whole-blueprint searches were `quotient separated`, `separated quotient`, `admissible finite`, `finite proper`, and `universally closed separated`. The first, second, third and fifth found no imported equivalent to this item; the fourth included the already existing finite-proper leaf. Blueprint ancestry was checked with `ancestor`. No new node was warranted and no duplicate pair was created.

Fresh Mathlib searches were run through msearch.py (LeanFinder twice, LeanSearch, Loogle, and grep twice). The exact queries and returned names are preserved in searches.jsonl and appended to the item's inherited search history. In particular `IsSeparated.of_comp` concludes separatedness of the first factor, whereas this item requires the second factor. `IsFinite.of_comp` similarly concludes finiteness of the first factor. `UniversallyClosed.of_comp_surjective` concludes universal closedness, not separatedness. No returned declaration states the item or the general separated-image theorem. No search was recorded as run without being executed.

## Review by Q89

I read ILO, Expose IX 1.4, printed pp.132--133 (PDF pages 138--139), including the admissibility remark for projective X' and Y', the successive finite group quotients and situation (*). This is the quotient construction the item needs; the separatedness property is justified by the independent general scheme lemma, not by a free-action quotient theorem. I read Stacks `morphisms.tex`, Tag 01WN (`lemma-finite-proper`) and Tag 09MQ (`lemma-image-universally-closed-separated`), especially part (4) and its final paragraph. I also read the diagonal discussion following Schemes Tag 01KK, with 01KJ and 01IQ, to verify the mechanism of the cited general result. There are no new nodes requiring additional sources. No SGA route is used.

Step 1 cites the definition of an admissible finite scheme quotient. Its actual statement explicitly includes finiteness and a topological quotient map. The surjectivity definition says every point has a preimage, exactly the consequence of being a topological quotient map used here. The structural equality h q = p is the meaning of the induced S-morphism in the item. This step is elementary unpacking; it does not use a theorem about invariant rings or free actions.

Step 2 cites `lem-weil-pbc-finite-proper`, whose full statement is “A finite [def-weil-pbc-scheme-conventions] morphism is proper.” It applies to q itself, not to p or h. I opened its convention definition and the separate finite/integral morphism definition to check that finite has the same affine-local module-finiteness meaning. I read `def-weil-proper-morphism`, whose statement explicitly includes universally closed in proper. Thus no bare definition is being cited for the nontrivial finite-implies-proper theorem. Step 2 is marked non-elementary and cites that theorem.

Step 3 cites the full statement of `lem-weil-pbc-surjective-universally-closed-separated`: it has schemes over the same S, a surjective universally closed f with commuting structure maps, and a separated source structure map. Every hypothesis is supplied above or is present in the item. Its conclusion is precisely separatedness of the target structure map. The cited node assumes neither flatness, finite presentation, Noetherianity nor freeness; none was silently inserted. This is an existing general lemma, not a new node restating the item's conclusion. Its underlying argument is the closed image of the source diagonal under f times f; no assertion about points of fibre products being pairs of ordinary points is needed.

I checked B--E against the actual files: no new unsplit statement or implicit notion, no duplicate, no new lemma containing the item itself, no uncited non-elementary inference, and no use of a cited node's proof in place of its statement. All citations.json quotes are the exact complete statements read, so each includes verbatim the part used. Every proof step is shorter than 2000 characters. The general 09MQ lemma is an off-unit generic tool, declared in split_report.tool_uses for maintainer review; the unit's Fourier/perverse route and the ancestor's uniformization branch are unchanged.

Small cases checked: the empty scheme (surjectivity forces an empty Q), the trivial group (the quotient can be the identity), a nonfree trivial action on a nonreduced scheme, and a group whose order equals the residue characteristic. The argument in all cases only uses that q is finite surjective and that M is separated over S. It does not require q to be flat or an etale torsor. No statement correction was necessary; the changes were the explicit proof and dependencies and the fresh, honestly recorded searches.
