# Worker report: lem-per-open-separated-etale-pushout

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-open-separated-etale-pushout.json`: statement item, split into seven explicit proof steps; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-space-etale-relation-quotient.json`: one new statement-only node, unsplit; no Mathlib match. Effective etale equivalence-relation quotients for algebraic spaces, including kernel pair, etale-local lifting and quotient universal property.
- `citations.json`: verbatim statement quotations for every citation in every item proof step.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for elementary distinguished squares, algebraic-space quotients and open/separated-etale pushouts. No project declaration states this item or the new general quotient assertion. The unrelated pushout declarations concern categories of complexes or schemes. No Lean was written or compiled.

## WANTED

None. All sources used are available in `literature/stacks-project/`.

## Audit findings and changes

The imported item was an unsplit statement with no proof. Its statement correctly expands Stacks Tag 0DVJ, including the reduced closed complement in the elementary distinguished square. I left it unchanged. In the source's notation its $V',V,U,W$ are this item's $W,Z,V,Y$.

I followed the five-summand relation of 0DVJ, rather than replace the construction by a pushout-existence citation. The source omits the checks that the square is elementary distinguished; Steps 5 and 6 now prove them using its actual kernel relation. Step 7 gives the pushout directly by the quotient's universal property. The same construction is the supporting geometric input to Tag 0ALT in the existing nilpotent-neighbourhood lift route; no chapter/unit route or target was changed.

A significant convention check is that chartwise etale does not imply scheme-representable for arbitrary algebraic-space sources. The existing `lem-trf-etale-relation-quotient` explicitly assumes schemes for both its object and relation. I therefore did not cite it on $V\amalg Z$. The one new input is the general effective etale-relation quotient theorem, not an open-pushout clause. It will be split independently; its intended source route chooses a scheme atlas of the object space, restricts the relation, and applies the scheme-relation presentation theorem. The bootstrap proof's reduction (1) to (2) at 04S6 explicitly addresses this passage. Its kernel-pair assertion is 046O plus monomorphy, and its universal property is that of the stated sheafification of the presheaf quotient. No proof is embedded in the new node's statement.

I also expanded the finite-union etaleness verification in Step 3: a scheme chart splits into five clopen schemes, and on a target scheme test the morphism is the finite coproduct of etale scheme maps. This uses the existing finite-coproduct lemma with precisely its scheme hypotheses, not with algebraic spaces substituted for schemes.

## Searches

The exact commands, actual hits, and full returned output of the new searches are in `searches.jsonl` and `search-results.json`. Both item and new node received two differently phrased LeanFinder searches, a Loogle name/pattern search, LeanSearch and Mathlib grep, all through the mandated msearch command. All services answered. I read every returned hit. The quotient queries find scheme etaleness, scheme etale sites, ordinary set quotients and rational maps. The pushout queries find scheme pullbacks and scheme open-gluing data. I inspected the scheme-only `Etale` definition in `Mathlib/AlgebraicGeometry/Morphisms/Etale.lean` and the open-immersion gluing-data signature in `Mathlib/AlgebraicGeometry/Gluing.lean`. Neither constructs algebraic-space etale quotients or the present pushout. No new Mathlib leaf results.

Before creating the node I searched the whole DAG by quotient/equivalence-relation titles and statements and by tags 04S6, 046O and 0DVJ. Blueprint searches were `etale equivalence`, `equivalence relation`, `etale groupoid`, `04S6`, `quotient`, and `pushout`; none of the blueprint hits states the new theorem. The ancestor tool gives `lem-per-artin-gabber-affine-curve`. I read that ancestor's latest proof and the unit/chapter records; the new node retains the existing ancestor/via chain and identifies its supporting 0DVJ subargument.

## Not duplicates

lem-per-space-etale-relation-quotient vs lem-sfb-fppf-space-atlas-bootstrap: the latter assumes all scheme pullbacks of an already supplied cover are algebraic spaces, flat and locally finitely presented; it does not construct effective quotients, identify their kernel pairs or prove etale-local lifting. The new node starts with an arbitrary etale equivalence relation and asserts those conclusions.

lem-per-space-etale-relation-quotient vs lem-sfb-fppf-relation-etale-replacement: the latter starts with an affine scheme relation with flat locally finitely presented locally quasi-finite projections and produces finite affine etale-local replacement relations. The new statement concerns arbitrary algebraic spaces with etale projections and their quotient, without affineness or the replacement construction.

lem-per-space-etale-relation-quotient vs lem-trf-etale-relation-quotient: the existing theorem requires both object and relation to be schemes. Our $V\amalg Z$ and $R$ are arbitrary algebraic spaces, so its theorem is not applicable by a one-line specialization.

lem-per-space-etale-relation-quotient vs lem-sfb-flat-groupoid-algebraic-quotient: that theorem constructs an algebraic stack from a general flat groupoid, with algebraic-space representability of its presentation. It does not assert a sheaf quotient or etaleness of its presentation. The new theorem concerns monic etale relations and an algebraic-space quotient, not a stack.

lem-per-space-etale-relation-quotient vs lem-sfb-algebraic-setoid-space: that theorem starts with an algebraic stack without automorphisms. It does not construct an algebraic space from a relation or provide its etale quotient map and effective kernel pair.

lem-per-space-etale-relation-quotient vs lem-per-open-separated-etale-pushout: the general quotient input has no open subspace or separated-etale gluing data, and gives no cartesian open square or complement isomorphism. The item's main work is to construct its particular etale relation and extract these properties, rather than apply a relabelled existence theorem.

## Review by Q70

I read the complete proof and statement of `spaces-pushouts.tex`, 0DVJ (lemma-construct-elementary-distinguished-square), and the preceding elementary-square pushout lemma. For the one new node I read `bootstrap.tex`, 04S6 (theorem-final-bootstrap), statement and reduction from space to scheme relations; `spaces-groupoids.tex`, 046O (lemma-quotient-pre-equivalence), including its test-scheme local-equality criterion; and the scheme presentation statement 02WW. I checked the etale convention against `spaces-properties.tex`, definition-etale and lemma-etale-local. The new statement permits nonrepresentable etale maps, as required, and makes no separation assumption on the object or relation.

For Step 1 I opened all cited statements. Fibre products and chartwise permanence give the projections of $P$. The etale-monomorphism lemma, not a definition of unramifiedness, gives the open diagonal; closedness is exactly the assumed separatedness. The algebraic-space coproduct theorem applies to the finite atlas coproducts within the size bound, and the sheaf-coproduct partition theorem supplies the clopen structure used here. The closed-immersion and open-subspace definitions are used only as definitions.

For Step 2 the coproduct-partition statement reduces arbitrary test sections to fixed labels. I checked each label pair, injectivity, reflexivity, symmetry and transitivity as written. Membership in the diagonal is not treated as a single global yes/no choice on a disconnected test scheme: the diagonal is clopen and the proof respects its clopen partition. The only cited additional assertion is that algebraic spaces are sheaves, to glue the unique relation sections. This is a direct relation calculation, so the step is marked elementary.

For Step 3 I verified that the open-chart test explicitly asserts chartwise etaleness of an open inclusion, and permanence explicitly gives composition and base change. The finite-coproduct etale lemma applies only after pulling back to schemes. The scheme-coproduct lemma and clopen-partition theorem say exactly how that test coproduct is represented. There is no hidden representability assumption on $q$ or on $s,t$.

Step 4 cites the newly stated theorem, whose complete hypotheses were established in Steps 2 and 3, and uses its algebraicity, quotient map, kernel pair and local lifting conclusions. In Step 5 I checked that restricting the kernel pair gives respectively the diagonal $V$ and the specific graph copy of $W$, with their actual projections; the etale-monomorphism statement therefore proves the open-embedding clause and no extra separation is needed.

For Step 6 the reduced-closed-support theorem supplies the closed space and does not claim reducedness survives base change. The point-open-calculus statement provides precisely the pullback image formula needed to show the intersections are empty. The quotient theorem supplies local lifts and its effective kernel pair. The only arrows left over the complement are the diagonal, and the ordinary sheaf gluing axiom constructs the inverse globally; this is why the proof also controls nilpotent test schemes, rather than only geometric fibres.

In Step 7 I checked equality of the compatible pair on all five relation summands, including the off-diagonal one. The new theorem's universal property concerns every fppf sheaf, so it applies to the target algebraic space by its definition. The coproduct theorem concerns the sheaf coproduct, which has exactly the required maps out. All construction maps are over $S$.

I checked small cases: $W=\varnothing$ gives $Y=V\amalg Z$; $W=Z$ gives $Y=V$ even when $q$ is not surjective; an isomorphism $q$ gives $Y=Z$; empty object spaces and empty relation summands are allowed. In the noninjective etale case the off-diagonal $E$ is essential, and the proof includes it. Neither base, atlas, diagonal complement nor closed support was assumed affine, quasi-compact, Noetherian or finite type. I checked B1-B10, C1-C8, D1-D5 and E1-E7 against these files: definitions and lemmas are distinguished, every non-elementary assertion is cited, quotations are verbatim, and the one new node is a genuine general supporting input. Every non-elementary step is under 2000 characters. No imported-statement correction or source error was found.

## Unfinished work

None for this stage-1 item. The one new statement-only quotient node is deliberately queued for its own future split, as the one-level splitting rule requires.
