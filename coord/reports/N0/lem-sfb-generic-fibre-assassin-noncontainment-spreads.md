## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-generic-fibre-assassin-noncontainment-spreads.json`: statement, split in four steps; statement and statement dependencies unchanged; not a Mathlib leaf.
- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-assassin-neighbourhood.json`: new statement-only unsplit node for Stacks 05F1; no Mathlib match.
- `citations.json`: verbatim statement quotations for every step/node citation.

## Attachments

None. I searched the project `lean/WeilConjectures/` for the item id, 05KN, assassin, noncontainment, and generic-fibre/associated-point terminology. No project declaration states this item or 05F1. The ring-theory associated-prime declarations do not state either scheme result. No Lean was written and no compiler or build was run.

## WANTED

None. All mathematical sources used are present locally.

## Source error

The statement of 05KN is correct and is retained. Its proof at `literature/stacks-project/more-morphisms.tex:6923` is not a proof of it. The implication from noncontainment of the generic assassin to disjointness of the support and the given open fails. Take Y=Spec k, X=Spec(k × k), F=O_X and U one of the two points. Ass(F) consists of both points and is not contained in U, but Supp(F) intersects U. Even when U is empty, the assertion that T=Z minus U has empty generic fibre goes in the wrong direction. Hence the proposed empty-fibre shrinking cannot prove noncontainment. This is an error in the supporting source proof, not a dispute about the item's statement, and is already mentioned by the parent item's reviewed record.

The replacement chooses a single associated point outside U. Its entire closure avoids U. Stacks 05F1 gives associated generic points of fibres on a nonempty open of that closure; generic nonemptiness (05F5, through the existing stronger closed-subset theorem) ensures such fibres occur over a base open. Nothing changes in the unit or chapter route.

## Sources and searches

I read 05KN and the preceding 05F1 in `more-morphisms.tex`, including 05F1's proof by affine reduction, two generic-flatness shrinkings, a universally injective inclusion B/q into the finite module, and associated primes of the fibre quotient. I read the generic-fibre nonemptiness assertion 05F5 at lines 6510 ff. and the existing nonemptiness node's proof. The new node is exactly 05F1 with the reduced structure on the closure made explicit (the source uses B/q). I checked tags against `literature/stacks-project/tags/tags`.

I read the current latest blueprint unit and `sk-thm-sf-ctf-stability.proof.md`, the chapter and unit records, GOAL.md, SETUP.md's three levels, the stage-1 brief and stage document, and delivery-errors B–E. The inherited auxiliary chain has no blueprint-id ancestor: `blueprint_refs.py ancestor` returns None. The new node records that null ancestor and prepends the item to the inherited via list. Whole-blueprint searches for `assassin`, `relative assassin`, and `05F1` found no equivalent blueprint statement. Whole-DAG tag and key-word searches found no node stating 05F1.

The existing item's Mathlib searches are preserved as prior work. The new node records the actual item-log entries for two LeanFinder phrasings, the Loogle name query, the AlgebraicGeometry grep, and LeanSearch. Hits concern generic-point topology, stalks and localization, or purely algebraic associated primes; none gives 05F1 in one line. The associated-prime Basic.lean source was read to confirm the distinction. Preliminary searches for other possible decompositions were not turned into delivered nodes. The final decomposition has one new node.

## Not duplicates

lem-sfb-relative-assassin-neighbourhood vs lem-sfb-scheme-assassin-open-constructible: 05F1 concerns a neighbourhood in the closure of one relative associated point for an arbitrary locally finite type morphism; the existing 05KR node is a constructibility statement for the base locus of containment, with finite-presentation and quasi-compact-open hypotheses. Its mention of 05F1 is a reviewer note, not its statement.

lem-sfb-relative-assassin-neighbourhood vs lem-sfb-generic-fibre-assassin-noncontainment-spreads: the new node has no irreducible-base or open-complement hypothesis and no base-open conclusion; it supplies relative associated generic points within a point closure. The item's proof constructs the bad closure, a finite-type principal open and the nonempty base open.

lem-sfb-relative-assassin-neighbourhood vs lem-trf-relative-assassin-base-change: 05DC identifies associated points under a specified base change; it says nothing about neighbourhood persistence as the base point varies.

lem-sfb-relative-assassin-neighbourhood vs lem-sbc-generic-closed-subset-fibre-nonempty: the latter guarantees points on nearby fibres of a closed set, without an associated-point conclusion. It is reused, not copied.

## Review by N0

Step 1 uses the definition of relative assassin, which explicitly gives its union over fibres and equivalent canonical-point test, and the finite-type definition, which explicitly supplies an affine cover over each affine base with finite type coordinate algebras. I checked both node statements. Open restriction leaves the fibre local ring and the module stalk literally the same; therefore associatedness passes both ways here without a field extension or base-change theorem. The bad point stays outside U. A base open in Y_0 is a base open in Y.

Step 2 uses the reduced-induced-closed-subscheme theorem, whose affine clause gives the quotient by the radical ideal and whose range clause is precisely the chosen closed closure. The nonempty open from 05F1 contains xi because xi is the generic point of its own closure. All assumptions of 05F1 hold after the chart restriction: local finite type of the morphism, finite type and quasi-coherence of the sheaf, and relative associatedness of xi. Its statement expressly gives the images in the original fibre of all component generic points of W_y. It is stronger than a bare support statement and has the correct module F, rather than just O_Z. The whole closure is outside U because that complement is closed, irrespective of quasi-compactness of U.

Step 3 explicitly checks that the selected principal open is finite type over A: quotienting finite algebra generators and adjoining one reciprocal suffices. The existing generic-closed-subset-fibre-nonempty node assumes exactly finite type and a generic point of the entire base; it expressly needs no Noetherian, reducedness or separatedness hypothesis. I use C equal to its whole source, a closed subset, not a possibly non-quasi-compact open subset of X. The point xi ensures its generic fibre is nonempty. Its conclusion is an open containing eta, stronger than the nonempty open needed here.

Step 4 uses the component-cover theorem and scheme sobriety, whose statements respectively give a component through a point and a generic point of that component. These are general topology/scheme tools, not definitions used for theorems they do not state. The generic point belongs to W_y; applying 05F1 yields an associated point of the original F_y, and the closed-complement argument puts it outside U_y. I checked all citation quotes against the actual statement strings, and every use has a corresponding quotation. The proof dependency list is exactly the union of the uses. All four steps are under 2000 characters, and none hides another non-elementary subclaim: persistence itself is the single new node; nonemptiness, components, and sobriety are existing cited nodes.

For the new statement I checked empty F or empty X (no xi can satisfy the hypothesis); Y a field; an embedded associated point (the closure need not be a component of X, so the argument correctly uses its own closure); arbitrary nonreduced irreducible base; and non-quasi-compact opens. The theorem imposes no flatness: its proof obtains the required flatness after shrinking in the algebra argument, rather than assuming it. The two-point example tests the source error and the corrected proof: choose the bad point, its singleton closure and the whole base. No new elementary fact, duplicate, or clause of the item has been relabelled as a new node. I declared the off-unit generic tools in split_report.tool_uses and did not alter the maintainer-owned tool_uses field.

## Unfinished work

None for this one-level split. The new node is intentionally unsplit and statement-only, as required for a new dependency.
