# Stage-1 delivery: lem-per-nilpotent-etale-neighbourhood-pushout-lift

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-nilpotent-etale-neighbourhood-pushout-lift.json: item, seven-step split of Stacks 0ALT; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-open-separated-etale-pushout.json: new statement-only lemma, Stacks 0DVJ; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-elementary-distinguished-universal-pushout.json: new statement-only lemma, Stacks 0DVI and 08GN; no Mathlib match.
- citations.json: verbatim statements for all 22 step/node citations.
- searches.jsonl and new-node-search-results.json: actual search log and complete returned hits; prepare.py is sandbox-only preparation code.

Two new nodes, zero Mathlib leaves. The new nodes intentionally remain unsplit, with empty proof and proof_deps, as required for a one-level split.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag and for nilpotent pushouts, lifting/approximation and elementary distinguished squares. No declaration states this item or either new geometric theorem. EtaleCoverThickeningLift concerns lifting a cover and comparison maps, not the prescribed affine pushout model.

## WANTED

None. All proof sources are locally available Stacks tex files.

## Corrections and scope

The item is precisely Tag 0ALT (restricted.tex, lemma-lift-approximation): the nilpotent ideal J is in the base ring A, not merely in C. Its hypotheses and all conclusions are retained. I removed doubled TeX backslashes in the statement; this is a rendering repair only. No mathematical statement dispute arose.

The imported item had no proof. The source's last sentence, saying that the properties are clear, needed an explicit finite-type argument and an explicit identification over the complement of V(I). These are Steps 6 and 7. I lift V0 over U rather than assume that either punctured open is affine. The affine reduction is identified with the specified Y0, including its Z0 leg, before descending affineness. I use the finite closed-immersion case 07VS of the source's 07VT affine-descent theorem, already present in the DAG.

I read GOAL.md, the three levels in SETUP.md, the chapter and unit records, and the newest blueprint under literature/blueprint/latest (main-20261024). The item is a supporting algebraization input below the Artin--Gabber ancestor, through the existing compatible-model-tower chain. No chapter or unit record is changed. The current ancestor proof and unit text were read; no unit step is replaced. The generic off-unit tools are declared in split_report.tool_uses for the maintainer's review. No SGA route or source is used.

## Not duplicates

lem-per-elementary-distinguished-universal-pushout vs lem-sfb-space-elementary-shriek-exact: the existing node states a short exact sequence of module-sheaf endofunctors and its base-changed version; it does not assert the categorical pushout property of algebraic spaces. The new node is a geometric universal-pushout statement with no sheaf modules.

lem-per-elementary-distinguished-universal-pushout vs lem-sfb-space-distinguished-derived-gluing: the existing node glues derived module objects and compatible morphisms on an elementary distinguished square and states its base-change conditions. It does not give the universal property for maps of algebraic spaces. The new node supplies that geometric property, not derived gluing.

I also opened lem-sfb-space-qcqs-distinguished-square-induction: it defines the square inline and gives induction for qcqs etale spaces, not a pushout construction or universal property. lem-sfb-space-pushout-etale-base-change concerns a thickening/affine pushout and only etale scheme base changes; neither the input square nor the arbitrary base change here is covered by it. lem-sfb-space-affine-thickening-pushout has a closed thickening leg, whereas the new construction has an open leg and a separated etale leg. The new 0DVJ node does not repeat the item: it has no nilpotent base, no prescribed affine reduction, and no finite-type or etaleness-away-from-an-ideal conclusion. The assembly of those properties remains in the item.

Before creating nodes I searched the whole DAG for 0DVJ, 0DVI, 08GN, 039R, 06AG, 07VT and their labels, and for elementary distinguished squares, pushout, thickening and etale equivalence. I searched tools/blueprint_refs.py for nilpotent etale, pushout, distinguished square, 0DVJ, 0DVI, open etale pushout, and elementary distinguished, and ran ancestor on the item. No blueprint statement supplies either new theorem; same_as is empty. The item already had the correct ancestor and via chain; the new nodes prepend the item to that chain.

## Mathlib searches and candidate reading

For each new node I ran msearch.py with LeanFinder twice using different phrasings, Loogle, LeanSearch and grep, and read the returned hits. All services answered. The exact query strings and their returned results are in each node and the sandbox log. For the item I also ran all four kinds, including two LeanFinder phrasings, and preserved its inherited search records.

The construction searches return Scheme.GlueData and etale pullback facts. I read Mathlib/AlgebraicGeometry/Gluing.lean: its gluing data require open immersion identifications and do not construct the open/separated-etale algebraic-space pushout. For the universal-pushout node I read Mathlib/CategoryTheory/Sites/MayerVietorisSquare.lean, especially the structure and its constructors: the structure assumes the sheaf pushout property. mk_of_isPullback assumes both covering maps monic, whereas our etale leg need not be monic. Thus these are not exact matches or one-line specializations. The other hits concern universally open maps, base-change closure of general morphism properties, or ring pushouts sent by Spec to scheme pullbacks; those do not state either geometric theorem. The item's ordinary formally smooth lifting hits do not construct the prescribed model B.

## Review by NL

I read restricted.tex Tag 0ALT (lemma-lift-approximation), from the full ring diagram through the whole pushout proof. I compared A, I, J, both finite-type hypotheses, both etale-away hypotheses, h0 and its quotient isomorphism against the item. The conclusion keeps the specified reduction isomorphism and its commutation with h0, as well as h being etale and B being finite type and etale away from I.

For the first new node I read spaces-pushouts.tex Tag 0DVJ, lemma-construct-elementary-distinguished-square, including its hypotheses and conclusion. For the second I read Tag 0DVI, lemma-elementary-distinguished-square-pushout, and spaces-perfect.tex Tag 08GN, lemma-make-more-elementary-distinguished-squares, parts (2) and (3). I also read the definition in Tag 08GM. The new statements spell out the cartesian square and the isomorphism over the reduced closed complement. The first needs separatedness on the input etale map; the second requires none on its etale leg or on its base-change map. Neither statement contains a proof sketch or borrows objects from the item's setting.

Step 1 uses the statement of def-weil-affine-spectrum for affine contravariance and prime points; lem-weil-pbc-quotient-base-change-closed-immersion-ideal gives Z0 and the closed immersion from the base quotient; lem-sfb-space-thickening-base-change gives the thickening on U. Nilpotence implies containment in every prime by the definition of a prime ideal. The quotient isomorphism over the entire closed subscheme cut out by I restricts to the reduced complement; it is stronger than the needed pointwise assertion. All square identifications are the displayed fibre products, not just equality of point images. This step is elementary relative to those statements and the hypotheses.

Step 2 uses exactly the essential surjectivity and Hom-set bijectivity asserted in lem-sfb-space-thickening-etale-scheme-equivalence. I read its statement, not just its proof, and checked it supplies scheme objects, so V is a scheme. The base is U, not X: the etale-away hypotheses give W/U and V0/U0. Etale cancellation from lem-weil-pbc-etale-composition-cancellation proves q etale. I read spaces-more-morphisms.tex Tag 05ZS, lemma-thickening-equivalence, and etale.tex Tag 039R, theorem-remarkable-equivalence, for this use.

Step 3 uses lem-weil-pbc-affine-source-morphism-separated only for Z0 -> Y0, whose source is affine. lem-weil-pbc-separated-base-change applies because W0 -> V0 is its actual cartesian restriction. Thickening base change applies to both W and V. I read lem-sfb-space-thickening-topological-properties, whose statement explicitly reflects separatedness for morphisms of arbitrary thickenings without requiring a flat source; spaces-more-morphisms.tex Tag 09ZY, lemma-thicken-property-morphisms (6), says exactly this. This avoids incorrectly applying a flat-deformation lemma to Z/X.

Step 4 checks all hypotheses of the new construction: W is an open in Z, q is etale by Step 2 and separated by Step 3. The new universal-pushout statement gives pushouts for both the reduced square and the original square with vertex Y0. The two maps between fourth vertices and their inverse property are obtained by their universal properties; their equality on the Z0 leg is written out and is what later ensures h reduces to h0. This does not assume that arbitrary pushouts commute with base change.

Step 5 applies lem-sfb-space-thickening-base-change with X0 -> X and Y -> X, giving a representable surjective closed immersion from the specified affine Y0. On every scheme test, lem-weil-pbc-closed-immersion-finite gives precisely the finiteness needed in lem-sfb-finite-surjective-affine-space-target. I read that node's full statement and spaces-limits.tex Tag 07VS, lemma-affine; it allows an algebraic-space target and needs no Noetherian or finite-presentation hypothesis. def-weil-affine-spectrum then supplies B, not merely an unknown ring of functions on a non-affine space.

Step 6 uses affine-spectrum contravariance, the quotient base-change statement and the specified isomorphism from Step 4 to get beta and the exact reduction formula. lem-trf-space-chartwise-etale-permanence explicitly identifies chartwise etaleness with representable etaleness for scheme sources, and def-weil-etale-morphism gives the affine scheme/ring etale interpretation. I checked def-weil-pbc-finite-type-algebra and def-weil-pbc-algebra-hom-quotient: they supply the exact generator and quotient notions used. The finite-generation calculation is elementary: B = D + JB implies B = D + J^n B by substitution because J comes from A, which is inside D; nilpotence then gives B = D. No unproved Nakayama assertion is cited and no flatness is used.

Step 7 uses the arbitrary-base-change clause of the new universal-pushout node. Since U is an open base and the structure maps of W and V factor through it, restriction turns the top leg into the identity of W. The universal property then identifies the fourth vertex with V, preserving its U-structure. This proves the exact etale-away conclusion using the already selected etale lift. It does not merely claim that the comparison transports or is clear.

I checked delivery-errors B--E point by point. Every non-elementary input is a cited statement; citations.json copies verbatim text from those statements, including the two sandbox nodes. No step uses a node's proof or a definition as an unnamed theorem. All seven steps are under 1000 characters, so there is no long inline lemma hidden in a step. The new statements introduce every object and cite the notions they use. The new nodes have no proof dependencies, so no circular lemma was introduced.

Small cases: for the construction W empty gives the disjoint union; W = Z gives V; q the identity gives Z; all-empty spaces are allowed. Taking a target V and W = Z = V disjoint-union V, with q the fold onto V (a separated etale map), shows why q must not be required to be an open immersion, and distinguishes this construction from ordinary open gluing. For the universal-pushout assertion V = Y gives an identity-leg pushout; a nonflat quotient base change is explicitly allowed by 08GN; the reduced complement is taken anew, never assumed to be the literal reduced base change. For the item, J = 0 recovers the original diagram; I = A reduces to etale infinitesimal lifting; I = 0 forces h0 to be an isomorphism and the construction recovers C; the zero ring and an empty generator list cause no failure. I made no stronger separation or flatness assumption to handle these cases.

## Unfinished work

None in the authorized one-level split. The two new general geometric lemmas are statement-only future items. No Lean file was written and no compiler, Lake or build tool was run. The required dry run and direct delivery follow this self-review.

## Validation

The first required deliver.py --no-push exited successfully: preflight passed at 9e05863c687. After a minor wording repair to the edge-case paragraph, the final dry run is run again before the push.
