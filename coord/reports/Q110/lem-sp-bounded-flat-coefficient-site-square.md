# Stage-1 report: lem-sp-bounded-flat-coefficient-site-square

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-bounded-flat-coefficient-site-square.json: statement, split into seven proof steps; no Mathlib match for the combined assertion.
- citations.json: one verbatim statement excerpt for each node used by each step.
- report.md: this report. No new nodes, no new Mathlib leaves. prepare.py is sandbox-only preparation code, not a delivery file.

## Attachments

None. I searched WeilConjectures for the exact blueprint tag, bounded-flat names and the K-flat/scalar comparison notions. The existing bounded-flat ringed-space theorem is about a different site. Etale.reductionModIdeal_flatModel handles an ideal quotient and has a bounded-constructible input; it does not state the general finite-ring-map etale/proetale square. The item's complete assertion is not attached to any such declaration. I wrote no Lean and ran no compiler or Lake command.

## WANTED

None. All source inputs used here are available in literature/stacks-project. The combined statement is an agent deduction, not a single Stacks theorem.

## Issues and changes

The live item had no proof. Its statement, stmt_deps, source, created provenance and blueprint ancestry are preserved. Its prior Mathlib searches are retained; actual searches run for this item are appended from searches.jsonl. The returned Mathlib material concerns ordinary modules, general exact functors and mapping complexes; none states the simultaneous five-complex square. In particular the grep hit in Localization/DerivabilityStructure/Basic.lean:48 is a TODO about constructing flat derivability structures, not a theorem. The second semantic phrasing also found no match. No statement dispute was necessary.

The generalization from the etale site to the pro-etale site does not follow merely by citing an etale K-flat criterion. I used the existing general ringed-site bounded-above-flat lemma instead. The target-ring flatness of a scalar extension does not assert that B is flat over A. The normalization of the actual derived map is stated explicitly, using the existing scalar-adjunction normalization and a coefficient-resolution square; it is not inferred from an arbitrary object isomorphism.

## Not duplicates

No new nodes were created. Whole-DAG source-tag and statement searches found the existing generic inputs. Blueprint searches for K-flat, bounded flat and scalar comparison found no blueprint node stating this entire combined assertion. lem-sfb-kflat-scalar-comparison-normalization supplies the scalar/site comparison clause but not the bounded support, five flat/K-flat complexes and universal Tor interval. lem-weil-pbc-independent-bounded-flat-kflat supplies only the generic bounded-flat criterion. Both are reused, rather than recreated.

## Review by Q110

I read the worker brief, stage-1 rules, GOAL, SETUP's three-level route rule, the chapter and sk-thm-sf-compatibility unit, and both copies of delivery-errors B through E. The item is a technical input beneath the coefficient clause of the existing chart route; it is not the unit key node, so there is no unit record to update. Its nearest blueprint ancestor is det-sp-reduction-exceptional. I read that ancestor's current node and the ordinary scalar-pullback blueprint proof supporting the normalization tool. This split stays in the finite-coefficient chart input and does not invoke a purity theorem or change the unit route.

For the item I read Stacks sites-cohomology.tex, lemma-bounded-flat-K-flat (06YQ), lemma-pullback-K-flat (0G7E), lemma-derived-base-change (06YY), lemma-pullback-tensor-product (07A4), the construction preceding definition-derived-tor (06YU), and lemma-tor-amplitude (08G1), including its forward computation. I also read sites-modules.tex, lemma-tensor-product-pullback (03EL) and lemma-pullback-flat (05VD). I use the Stacks statements and arguments, not the literature reference listed inside the flat-pullback lemma. No SGA source is used. There are no new nodes requiring additional source review.

Step 1 uses the full statement of lem-sf-comparison-pullback-exact: it provides the constant-ring identifications and exactness, not just a definition of nu. The exact-functor-derived-factorization statement explicitly says every termwise complex represents the derived image, so it gives the claimed Q(N_AP) identification. Both finite-ring hypotheses hold. Compatibility of constant ring maps is their construction on constant values.

Step 2 uses lem-weil-pbc-ringed-topos-flat-module-pullback, whose statement allows an arbitrary structural ring map and expressly assumes no flatness of that map. I apply it separately for the etale coefficient map, the two comparison inverse images and the pro-etale coefficient map. These are actual morphisms of ringed topoi by Step 1 and by the identity-topos scalar construction. The sheaf tensor definition gives 0 tensor B = 0, and additivity gives preservation of zero by N. Thus support remains [a,b], even for a nonflat quotient of rings. No stronger cohomology-support claim is substituted for termwise support.

Step 3 uses lem-weil-pbc-independent-bounded-flat-kflat. Its statement is for arbitrary ringed sites relatively small in the coefficient universe and for every acyclic test complex, not only bounded tests. Each of the five complexes is bounded above by b by Step 2 and flat over its own ring; the small-representative convention supplies the size condition. The etale-only lem-kun-kflat-criteria would not have sufficed on the pro-etale side.

Step 4 uses the actual natural computation morphism in lem-weil-pbc-ringed-topoi-derived-pullback on the two coefficient-extension ringed morphisms. The hypotheses are flat terms and K-flatness, established already. The definition of constant-coefficient-scalar-extension identifies its functor as exactly this left-derived extension. Inverting these computation isomorphisms has the orientation in the item's displayed formulas; Step 1 identifies the intermediate N_A image. Naturality follows from the cited natural morphisms, with no arbitrary choice of isomorphism.

Step 5 uses the ordinary B-linear coequalizer comparison explicitly stated by lem-sfb-kflat-scalar-comparison-normalization. Its inverse-image coefficient hypotheses are exactly those verified in Step 1. I convert its B tensor P convention to P tensor B by the explicit balanced flip. The equation against each differential is the naturality square of that ordinary comparison, and gives the chain isomorphism without a new theorem. The same square for an arbitrary chain-map component verifies naturality. There is no sign on this flip because the coefficient factor is in degree zero.

Step 6 uses that same node's derived clause: inverse Q(chi) is the specified scalar-adjunction mate on every flat-term K-flat representative, with no flat coefficient-map hypothesis. I also read the complete statement of lem-weil-pbc-ringed-topoi-derived-tensor-pullback; it gives the canonical bifunctorial derived monoidal comparison, and its source construction uses the ordinary tensor map on two K-flat representatives. lem-pc-kflat-resolution supplies a flat-term K-flat V resolving B[0], with no boundedness or projective-dimension restriction. lem-trf-site-one-sided-tensor-normalization explicitly gives natural comparison isomorphisms when only one factor is flat-term K-flat. Hence P tensor V -> P tensor B and N_AP tensor N_AV -> N_AP tensor B are the canonical computation maps. Naturality of the ordinary comparison in V -> B makes the square commute and pins down the map, not just the objects; exactness from Step 1 handles inverse image of the quasi-isomorphism. The scalar-normalization clause retains B-linearity in this comparison. These are generic tool uses recorded in split_report.tool_uses, not a substitution of a different chart route.

Step 7 again uses the one-sided normalization theorem, now on each complex C and every module sheaf M on C's own site and over C's own ring. Its statement allows an arbitrary second complex; M need not be flat. The definition of the total tensor gives exactly C^q tensor M in degree q. Those terms are zero outside the interval, so the kernel and image defining cohomology there vanish. The two Tor-amplitude definitions quantify over exactly these module sheaves. I did not test only constant or constructible M. This directly realizes 08G1's short (2) implies (1) argument and requires no new Tor-amplitude node.

I checked small cases: P=0; a=b (one flat module); negative or shifted intervals; X empty; A=B and the identity coefficient map; and A=Z/4 -> B=F_2 with P=A[0]. In the last case the result is B[0], flat over B, although B has infinite projective dimension over A; none of the proof steps incorrectly requires B to be A-flat. Zero rings cause no obstruction. The proof makes no perfection, constructibility, Noetherianity or geometric invertibility assumption. Every proof step has fewer than 2000 characters, and the normalization step is a resolution/naturality square using existing lemmas, not a hidden new comparison theorem. I checked dependency reachability locally from the cited files: none reaches the item, so the added proof edges create no cycle. All cited node statements were opened and the citation records are literal substrings of them.

## Unfinished work

No mathematical portion of the requested split remains. Independent maintainer review is pending after delivery; the required dry run and push are recorded by deliver.py.
