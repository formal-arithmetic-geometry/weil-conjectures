# N9 stage-1 delivery: lem-trf-labelled-coordinate-boundary-globalization

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-labelled-coordinate-boundary-globalization.json`: item, split into nine proof steps; statement unchanged; no Mathlib match.
- No new nodes; no Mathlib leaves. `citations.json` contains one verbatim statement quotation per step/node citation.
- `searches.jsonl` records this worker's actual searches. `ilo.txt` is a sandbox-only PDF text extraction; `write_split.py` is the sandbox-only preparation script.

## Attachments

None. Searched `lean/WeilConjectures/` by the exact blueprint tag and by coordinate-hyperplane/normal-crossing notions; no declaration states the item. No project proof was treated as finished merely because its statement exists.

## WANTED

None. The ILO volume and Stacks source files used below are present locally.

## Findings and changes

The live item had a statement and inherited searches but no proof. No earlier item copy, split, report or search log existed in this sandbox. The item is still unsplit and there is no matching released repair note. I retained its statement, source, creation record, blueprint provenance and inherited searches. The new searches test the complete item with two semantic phrasings, Loogle and two source regexes. Returned signatures concern etale/smooth definitions, standard charts and etale loci; none states the labelled boundary result. Both normal-crossing source regexes and Loogle gave no hits. No search was fabricated, and no inherited search was represented as my own.

Read the chapter and unit records, SETUP's three levels and the latest `lem-trf-local-term-locality.proof.md`. The nearest ancestor's current proof uses Varshavsky's contracting-correspondence theorem and no longer narrates the historical nearby-duality alteration branch recorded in this item's provenance. This assigned item remains a valid local boundary lemma on that existing DAG branch; the split does not change the unit route or assert that the new ancestor proof requires this old branch.

The inherited statement is mathematically consistent. It requires an actual pointed etale chart at every point, and injective assignment of indices among nonempty labelled members. Reduced pullback is not automatically actual pullback; this is explicitly justified before using the equations as ideal equations. The strict-boundary definition also requires a local dimension equality, beyond the component codimension written in the informal criterion; step 4 proves that extra equality from the same hypotheses, without changing the statement.

## Not duplicates

No new node was created. Before settling the split I searched the whole DAG by the source tags, regular-etale descent, Cartier descent, normal components, parameter products, local dimension and component keywords; I read candidate statements rather than relying on filenames. Blueprint searches for `coordinate boundary`, `regular`, `Cartier`, and `irreducible components`, and the ancestor query were run. In particular existing `lem-trf-etale-regular-intersection-descent`, `lem-trf-finite-intersection-etale-stalk-model`, `lem-trf-etale-reduced-cartier-descent`, `lem-trf-fpqc-cartier-ideal-reflection`, `lem-sfb-transverse-prime-ideal-parameters`, `rem-pc-regular-normal`, and the stalk Cartier-spreading node cover the needed tools. Reusing them avoids creating nodes for either clauses of this item or short assembly arguments.

## Review by N9

I read ILO Expose VIII 4.1.2--4.1.4(i) on printed p.117, Remark 4.2.2(i)--(ii) on pp.118--119, and Lemma 4.2.9 with its coordinate calculation on p.121. The volume supplies the geometric chart route and the regular-intersection criterion; the detailed globalization argument is marked agent-written. I also opened the Stacks proofs at algebra.tex `lemma-flat-under-regular` (00OF), etale.tex `proposition-etale-regular` (025N) and `lemma-etale-dimension` (039S), more-algebra.tex `lemma-dimension-etale-extension` (07QP), properties.tex `lemma-normal-locally-finite-nr-irreducibles` and `lemma-normal-Noetherian` (0357 and 033M), spaces-divisors.tex `lemma-characterize-effective-Cartier-divisor` (083C), and divisors.tex `lemma-effective-Cartier-in-points` (0AG8). I checked the latest blueprint regular-normal statement too. No SGA route is used. There are no new-node sources to review.

For step 1 I read the complete finite-intersection stalk-model statement: it supplies local Noetherianity, the quotient stalks and flat local comparison maps, including its empty-subset case. The flat-under-regular statement has exactly the Noetherian local and flat hypotheses supplied by that model. Part (b) of transverse-prime-ideal-parameters supplies the regular parameter quotient. The regular-scheme definition then converts these stalk facts to scheme regularity. I did not cite the misleadingly named etale-local-ring descent nodes, whose actual statements assume field extensions and do not apply here.

For step 2 regular-normal supplies both regularity implies normality and the finite clopen integral decomposition under Noetherianity. The closed subset E is quasi-compact by the explicit finite-subcover argument, and its local Noetherianity was proved in step 1, so no absent finite-type hypothesis is being inserted. The integral-scheme definition is used only for reduced irreducible F_a. Removing the other finitely many clopen components in the local scheme is an elementary ideal/unit argument. This proves the refined labels are still actual single hyperplanes, not a claim that a possibly disconnected E is globally irreducible.

For step 3 the cited etale-intersection descent node really states regularity AND component codimension for every finite intersection, allows n=0, and takes the empty subset to the ambient scheme. Its hypotheses are verified using precisely the refined labels of step 2 and the item's regular-intersection hypothesis. Empty selected members give empty local intersections. There is no appeal to an unproved cover by global regular open subsets.

For step 4 the stalk-model statement identifies the base-changed intersection ring. Part (b) of the parameter lemma gives its dimension drop by |J|. The etale local dimension statement says equality for localizations of actual etale ring maps; I apply it on affine neighbourhoods of actual scheme morphisms, both V to Y and the intersection base change. The base-change node explicitly says this projection is etale. I do not claim that a stalk-to-stalk map is itself a finitely presented etale algebra. This verifies the stronger local dimension equality the strict-boundary definition needs.

For step 5 reduced Cartier descent's first sentence explicitly identifies the actual pullback of a reduced induced closed subscheme with the reduced induced structure on the inverse-image support. Uniqueness of reduced induced closed structures justifies applying it to the given C and D. The parameter lemma states the intersection-of-prime-ideals equals the product, radicalness, nonzerodivisors, and the empty-product convention. Those are exactly the facts used, rather than merely citing the definition of Cartier or of a parameter system.

For step 6 flat-local faithful flatness really supplies surjectivity of Spec. The affine faithfully flat morphism gives the fpqc covering appearing in the definition; no quasi-compactness of the original V to Y is assumed. The fpqc Cartier-reflection statement includes the ideal inclusion and yields an effective Cartier ideal, rather than only an abstract rank-one module. Finally the stalk Cartier-spreading node applies to a locally Noetherian scheme and an arbitrary closed subscheme with nonzerodivisor ideal generators at all points. This is why working only on Spec of the stalk suffices and no openness of the regular locus is used.

For step 7 the normal-crossings definition requires exactly an effective Cartier ideal and the pointed actual-etale product-of-parameters description; steps 5--6 provide these. This is a direct definition check and is the only step marked elementary.

For step 8 the parameter lemma supplies incomparability, excluding containment between different original labels. Components of E are already disjoint. The finite irreducible-union argument is written out; no new lemma merely restates the component clause. The reduced-induced uniqueness statement identifies the component structures, and the strict-boundary definition is checked against the finite integral regular list and the equalities established in steps 3--4.

For step 9 the closed-subset finiteness node explicitly covers the closed subset |C| of Noetherian Y, not merely the ambient components. The Cartier-nowhere-dense statement says C contains no nonempty open subset. Step 2 makes the ambient irreducible components open, so C cannot contain an ambient component. A strict containment between G and a component of C would create a length-two chain inside an ambient component, contradicting the singleton codimension-one conclusion of step 3. The union-of-components definition is support-based and permits D empty, exactly as used.

All cross-unit statement citations are declared as generic tools in split_report.tool_uses with their individual reasons. They concern descent, local commutative algebra, or Noetherian component geometry; none substitutes another route for a unit proof. Every cited statement was opened and its actual usable clause checked. `citations.json` quotes those statements verbatim, including complete statements when several clauses are used. This checks C1 and C4 together rather than attaching an irrelevant short quotation.

I checked the B--E return checklist against the completed JSON: no new unsplit nodes or hidden proof sketches, no duplicate statement nodes, no clause moved out merely to apply it, no dependency on this item's parent, and no tag substituted for a needed node. Every non-elementary input is in the step's uses and their union is proof_deps. All nine steps are below 2000 characters, so there is no long-step hidden-lemma exception.

Small cases checked: empty Y; C or D empty (unit ideal); m=0; E empty; disconnected regular E with disjoint components; a regular local field (dimension zero, forcing all local boundaries empty); two transverse axes and their scheme-theoretic intersection; and a three-line weakly normal-crossing configuration xy(x+y)=0, which correctly fails the distinct-parameter and codimension hypotheses as ILO warns. A putative duplicate or contained label would violate the local parameter-prime incomparability. No excellence, equidimensionality or global regular-locus openness is assumed.

## What remains

No mathematical subtask left for this item's stage-1 split. Required server dry run and direct delivery follow; their outcomes are recorded below.
