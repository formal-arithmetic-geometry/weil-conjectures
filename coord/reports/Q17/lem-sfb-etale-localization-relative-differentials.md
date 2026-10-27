# Q17: lem-sfb-etale-localization-relative-differentials

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-etale-localization-relative-differentials.json: item split in four steps; statement unchanged; not a Mathlib leaf.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-differential-transitivity-short-exact.json: new statement-only lemma, unsplit; no Mathlib match for the scheme-sheaf statement.
- citations.json: a verbatim statement quote for every node used in each proof step.

## Attachments

None. Searched WeilConjectures for the exact blueprint tag and for relativeDifferentials with etale/Etale and inspected AlgebraicGeometry/Modules/Differentials.lean. Its relativeDifferentialsCompIso (line 271) assumes the base map is an open immersion; that does not cover a general etale base map, and the affine-section declarations do not give the requested arbitrary square. No exact completed project declaration was found.

## WANTED

None. All sources needed here are available in literature/stacks-project/.

## What was wrong or incomplete

The item had no proof. Its assertion agrees with Tag 04BX, including the fact that the square need not be Cartesian. There is no statement dispute and no change of hypotheses. The derivation and restriction clauses are the canonical-map characterization in Tag 01UV, which must be checked rather than inferred merely from existence of an abstract isomorphism.

The inherited blueprint ancestry has from.node = null. tools/blueprint_refs.py ancestor reports that same null ancestor. I preserve this inherited ancestry and its full supporting-input place/via chain; the new node prepends this item to that chain. I read the current latest blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its direct-images proof (3), and the recorded chapter/unit. This is a below-unit prerequisite in its existing alteration/moduli/deformation chain, not a replacement of the unit route.

## What remains unfinished

Nothing in this item's assembly proof. The new general smooth transitivity lemma is intentionally statement-only and remains a future stage-1 item. No Lean file was written, no compiler invoked, and no repository or launcher file modified.

## Searches and candidates read

searches.jsonl records every search actually performed. The item was searched by LeanFinder, LeanSearch, Loogle and Mathlib grep; the new node has both natural-language phrasings, Loogle exact-sequence searches and successful directory greps. I read Mathlib/RingTheory/Etale/Kaehler.lean:38-52 and Algebra/Category/ModuleCat/Differentials/Presheaf.lean:193-239. The first is the formally-etale ring tensor equivalence and the second constructs presheaf differentials. Neither is the scheme-sheaf theorem. Smoothness instances and the ring Jacobi-Zariski exactness results likewise do not furnish a one-line specialization to a short exact sequence of scheme differential sheaves. The remote semantic index uses some older IsEtale/IsSmooth names; the read clone's Mathlib uses Etale/Smooth, as checked in its Morphisms/Etale.lean and Smooth.lean. No semantic hit was accepted without reading its relevant source.

Exploratory searches for an etale-smooth-zero-differentials node were superseded when I found existing lem-weil-pbc-etale-smooth-zero-dimensional-fibres and lem-sc-smooth-omega-finite-locally-free. No redundant etale-vanishing node is created. A preliminary grep used a nonexisting Smooth directory; its empty answer was not used as evidence of absence. Corrected whole AlgebraicGeometry and RingTheory/Smooth directory searches are the recorded evidence for the new node.

## Not duplicates

lem-sfb-smooth-differential-transitivity-short-exact vs lem-a1-differential-sheaf-transitivity-exact: the existing theorem is right exact for arbitrary h; the new theorem adds injectivity of the first map under smoothness of h. Right exactness alone does not imply that injectivity.
lem-sfb-smooth-differential-transitivity-short-exact vs def-a1-relative-differentials-pullback-map: the existing node constructs the canonical map over a fixed base, and asserts no exactness or injectivity.
lem-sfb-smooth-differential-transitivity-short-exact vs lem-sfb-etale-localization-relative-differentials: the new theorem is the general smooth transitivity sequence, with possibly nonzero relative quotient; the item concerns a square with two etale horizontal arrows and assembles two different towers. The new theorem does not restate the item or a clause of its conclusion.

I searched the whole DAG for 02K4 and triangle-differentials-smooth, and the blueprint with blueprint_refs.py searches for 02K4, triangle differentials, smooth transitivity, smooth differential, and etale differentials. No blueprint node states the new theorem and no existing node carries Tag 02K4. The broader differentials search found only specialized curve and differential-definition blueprint nodes. No new definition or etale-vanishing lemma is needed.

## Review by Q17

I checked this split against delivery-errors B through E with the node statements and sources open. For the item I read more-morphisms.tex, Tag 04BX (lemma-sheaf-differentials-etale-localization), statement and entire proof. For the sole new node I read morphisms.tex, Tag 02K4 (lemma-triangle-differentials-smooth), its statement and algebraic proof. I also read the supporting exact sequences in Tags 01UX and 01UV, the rank formula in Tag 02G1 and the etale definition and relative-dimension-zero sentence following Tag 02GI. All new objects are introduced in the statement; the new node carries no hidden proof or extra hypotheses.

Step 1 uses the actual conclusion of lem-weil-pbc-etale-smooth-zero-dimensional-fibres, not an inference from the name of etaleness. Its conclusion supplies smoothness of relative dimension zero for each of a and b. The statement of lem-sc-smooth-omega-finite-locally-free applies with d=0 without any properness, Noetherianity or field hypothesis. def-amb-finite-locally-free-module gives the open trivializations by O^{oplus 0}; the zero-sheaf conclusion is then an elementary sheaf uniqueness argument. This replaces the tempting unnecessary new vanishing lemma.

Step 2 uses lem-a1-differential-sheaf-transitivity-exact exactly for the composable morphisms X2 -> S2 -> S1. Its statement gives the canonical right exact sequence, without smoothness assumptions on f2. The zero first term follows from step 1 and the tensor formula in def-pc-module-pullback; a tensor with the zero module is zero. The remaining map has zero kernel and cokernel, hence is invertible in module sheaves. This does not treat the diagram as Cartesian and does not identify schemes by their images.

Step 3 uses the full statement of the new smooth transitivity theorem, for a followed by f. Its smoothness hypothesis is exactly what step 1 supplied for a, not a nonexistent assumption on f. The quotient is Omega(X2/X1), already zero by step 1. Short exactness, including injectivity on the left, is necessary here: the existing right exact theorem alone would not prove the claim. This is the sole non-elementary prerequisite not already available as a node.

Step 4 checks equality of the actual maps: p sends 1 tensor du to d over S1 of a-sharp u, and q sends this to d over S2 of a-sharp u. The defining affine description in def-sc-relative-differential-sheaf and the quotient by generators-and-relations in def-weil-pbc-kahler-differentials show that these du generate locally. def-pc-module-pullback gives the tensor generators after pullback. Equality on these generators proves equality with the specified canonical arrow. The same formula commutes with restrictions, and the defining differential sheaf already includes restriction-compatible derivations; this proves the restriction clause, without assuming all local sections globally lift. This last step is elementary, with its generator argument written out.

For C4 I opened every cited node and copied a literal quote from its statement into citations.json; the quotes include the actual rank, exactness, tensor formula and generator assertions used. In particular I do not cite fixed-base functoriality as if it asserted a general square, nor cite a definition for the smooth transitivity theorem. For C1 all non-elementary inputs now have cited nodes. The three off-unit generic theorem uses are declared individually in split_report.tool_uses. Definitions are notions; they do not change the route.

I tested the new theorem on h the identity (the sequence becomes 0 -> Omega -> Omega -> 0), on a smooth affine-line projection (nonzero quotient, so it is genuinely more general than the etale case), and on an empty source (all sheaves zero). The item also covers identity horizontal maps, etale open restrictions, and non-Cartesian squares. The necessity of smoothness in the new theorem is visible for k -> k[t] -> k with t sent to zero: the differential pullback k dt -> 0 is not injective. The statement explicitly assumes h smooth and does not assume g smooth. All steps are below 2000 characters, so no long inline comparison hides another lemma.
