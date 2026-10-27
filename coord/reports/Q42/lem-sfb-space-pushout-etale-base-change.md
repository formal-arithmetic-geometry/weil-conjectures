# Worker report — Q42

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-pushout-etale-base-change.json: item, split, four proof steps. Retained the earlier sandbox proof and search records.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-pushout-etale-morphism-criterion.json: one new statement-only lemma, unsplit, no Mathlib match. This is the forward etaleness assertion of Stacks 07W3(5) for arbitrary compatible triples.
- citations.json: one literal statement quotation for each step/node pair.
- report.md: this report.

## Attachments

None. Searched lean/WeilConjectures by the exact item tag and by etale/pushout/thickening terminology; also searched the new lemma id and infinitesimal-pushout terminology in both library roots. The ring-theoretic pushout-etale declarations concern extension of scalars (geometrically pullbacks), and the finite-etale gluing module does not state the item for arbitrary algebraic spaces and arbitrary thickenings. There is no exact project declaration to attach.

## Wanted literature

None. All sources used are in literature/stacks-project/.

## Corrections and scope

The repository item was unsplit. An earlier sandbox attempt already supplied a four-step proof, the one new node, citations, and searches.jsonl, but no report. I ran the required initial dry run; it exited because report.md was missing. I preserved the proof, original fields, citations and logged searches, then audited them against the live repository and sources. The earlier correction of doubled TeX escapes changes formatting only; the mathematical statement and all its hypotheses are retained. No statement dispute was found.

The item is an etale counit statement. It would be a poor split to replace it by a new flat-counit statement and merely specialize. Instead the proof constructs Z from the restricted triple, proves Z -> Q etale using a separately stated forward criterion, proves Z -> E etale by permanence, and detects its isomorphism along C_E -> E. The final universal-property argument is written out. The new criterion asserts only etaleness of the constructed object for arbitrary compatible etale pieces; it assumes neither an ambient space realizing that triple nor a counit isomorphism.

No Lean, compiler, Lake, repository mutation, or agent delegation was used. Only this item's sandbox files were written. The item's chapter and unit records were read and left alone, since this is not their key node.

## Searches and blueprint

Read the earlier searches.jsonl results before reusing them. LeanFinder in two phrasings, LeanSearch, Loogle and grep found scheme etale permanence and Spec/ring-pushout results, not the new algebraic-space criterion. I additionally ran msearch grep against AlgebraicGeometry/Morphisms/Etale.lean and read the actual declarations: the Etale class is for schemes, line 74 gives stability under base change, and line 130 gives cancellation against an unramified morphism. These do not supply gluing along a thickening. The extra actual query is recorded in both node search lists. No search was invented and no failed service is claimed as absence.

Searched the whole DAG for 07W3 and pushout/etale terminology, and ran tools/blueprint_refs.py search for 07W3 and for pushout etale; both blueprint searches found no matching blueprint node. The command tools/blueprint_refs.py ancestor for the item prints None, reflecting the inherited broken created.item chain; the item's inherited from.node = null is preserved, and the new node uses the same computed value with the item prepended to via. Both from.place strings retain the precise supporting route and same_as = []. I read the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its direct-images node and proof. The item remains a low-level infinitesimal-gluing prerequisite in that inherited route; it changes neither the chapter nor the unit argument. The generic fibre-product and etale-permanence nodes from other units are declared in split_report.tool_uses.

## Not duplicates

lem-sfb-space-pushout-etale-morphism-criterion vs lem-sfb-scheme-colimit-upgrade-space-targets: the existing node upgrades a scheme colimit's universal property to algebraic-space targets, assuming etale patching; the new node proves etaleness of a constructed algebraic-space pushout map.
lem-sfb-space-pushout-etale-morphism-criterion vs lem-sfb-scheme-pushout-flat-patching: the existing result concerns schemes, flatness/local finite presentation and a flat counit; it does not assert etaleness for algebraic-space pieces.
lem-sfb-space-pushout-etale-morphism-criterion vs lem-sfb-proper-space-square-zero-effectivity: the existing node algebraizes an inverse sequence of proper flat families, not compatible etale triples over a single pushout.
lem-sfb-space-pushout-etale-morphism-criterion vs lem-sfb-fibre-product-algebra-flat-presentation: the existing node concerns commutative algebras, flatness and finite presentation; it does not assert the algebraic-space etale property.
lem-sfb-space-pushout-etale-morphism-criterion vs lem-sfb-infinitesimal-pushout-affine-charts: the existing statement concerns scheme pushout charts and recovery identities, without an etaleness criterion for arbitrary algebraic-space triples.
lem-sfb-space-pushout-etale-morphism-criterion vs lem-sfb-scheme-infinitesimal-etale-patching: the existing equivalence is for scheme pushouts and scheme triples; the new node allows algebraic-space bases and pieces and asserts just the forward etaleness direction.
lem-sfb-space-pushout-etale-morphism-criterion vs lem-sfb-space-pushout-etale-base-change: the item starts with an existing etale E over Q and proves its counit and universal property; the new node starts with arbitrary compatible pieces and concludes only that their pushout map is etale.
lem-sfb-space-pushout-etale-morphism-criterion vs lem-sfb-curve-infinitesimal-pushout: the existing equivalence glues proper flat curves, not arbitrary etale pieces; neither properness nor fibre dimension is imposed in the new node.
lem-sfb-space-pushout-etale-morphism-criterion vs lem-sfb-space-etale-thickening-detects-iso: detection of an isomorphism across one thickening assumes etaleness already; the new node supplies etaleness across a pushout.
lem-sfb-space-pushout-etale-morphism-criterion vs lem-sfb-space-pushout-compatible-etale-charts: the existing node constructs compatible surjective scheme charts over a scheme-base pushout; it does not give the stated arbitrary-base etaleness criterion. It depends on the item and is deliberately not cited in its proof.
lem-sfb-space-pushout-etale-morphism-criterion vs lem-sfb-space-thickening-etale-scheme-equivalence: the existing equivalence lifts scheme objects across one thickening, not etale triples across a pushout.
lem-sfb-space-pushout-etale-morphism-criterion vs lem-sfb-flat-lfp-space-pushout-gluing: the existing node states flat locally finitely presented gluing over a scheme-base pushout, not the arbitrary algebraic-space etale criterion.
lem-sfb-space-pushout-etale-morphism-criterion vs lem-sfb-space-affine-thickening-pushout: the existing statement supplies existence, the thickening coprojection, and canonical recovery for arbitrary pieces; it says nothing about etaleness of the induced map. Its statement is reused directly.

## Review by Q42

I read spaces-pushouts.tex Tag 07W3 (lemma-equivalence-categories-spaces-pushout-flat), including its forward assertion (5), its flat counit, and its proof using the two cartesian cubes. This supplies the source for the item and the new criterion. I also read the recovery proof of Tag 07W0 and the existence statement of Tag 07VX. The new criterion faithfully isolates the forward assertion (5), including arbitrary algebraic-space bases, rather than silently assuming the very counit this item proves. Its objects and compatibility isomorphism are introduced within its own statement, and its notions are cited or defined inline. Its proof is empty, as required for a new unsplit node.

Step 1 takes existence and the thickening C -> Q from lem-sfb-space-affine-thickening-pushout, whose statement explicitly gives both. Uniqueness of a pushout identifies the given Q with that constructed object. It takes base-change stability of arbitrary thickenings from lem-sfb-space-thickening-base-change, whose statement has no finite-order restriction (also checked against spaces-more-morphisms.tex Tag 09ZX). The affine property of A_E -> C_E is proved on each scheme test by its displayed identification with the pullback of A -> C, so no additional affine-stability lemma is hidden. The fibre-product node supplies the categorical products used in associativity. In particular both A_E -> A_E^+ and C_E -> E have the required thickening hypothesis.

Step 2 again uses the pushout/recovery statement, now for (C_E,A_E^+), and constructs f from its universal property. The canonical recovery maps in the cited statement, not a claim buried in its proof, give Z times_Q C = C_E and the analogous A^+ identification. The two component maps are base changes of the representable etale e. The chartwise-etale permanence node explicitly gives base change and the equivalence with representable etale when the source is a scheme; these supply exactly the hypotheses of the new criterion. Thus the criterion is applied to a compatible triple with precisely the specified overlap and gives e f etale. It does not provide the sought isomorphism f.

Step 3 uses the permanence node's explicit assertion that a map between two etale objects over Q is etale. This applies because step 2 gives e f etale and e is etale by hypothesis. Fibre-product associativity then identifies the pullback of f to C_E with the canonical recovery isomorphism from step 2. The identification concerns the projection itself: its inverse is induced by C_E -> Z, and f composed with that coprojection is the original map C_E -> E. The detection node explicitly applies to a chartwise-etale morphism and any thickening with an isomorphism as base change. Those hypotheses are now established. I read its source spaces-more-morphisms.tex Tag 05ZH (theorem-topological-invariance); it allows arbitrary thickenings, with no finite-order or separation condition.

Step 4 is elementary from the already established pushout of Z and f inverse: it constructs h f inverse for a compatible pair and proves uniqueness after composition with f. It introduces no new geometric theorem. Every non-elementary step has citations, and citations.json gives actual verbatim text from their statements. All four step texts are below 2000 characters; none hides a separate comparison lemma. The total assembly proof is below 3000 characters.

I tested the new criterion with identity thickenings (Z identifies with one piece), empty pieces, the affine dual-number thickening Spec k -> Spec k[epsilon]/(epsilon squared), and disjoint unions of compatible etale objects. It behaves correctly in each case: the base pushout map reduces respectively to the given etale map, the empty etale map, usual infinitesimal etale patching, or its componentwise form. The statement neither requires an etale cover to be surjective nor infers flatness over B. Arbitrary, possibly non-finite-order thickenings remain allowed by the cited source. The item also handles empty E: all three restrictions are empty, so both sides of its displayed bijection have one element.

The B--E audit found no further missing hypothesis, duplicate, circular citation, unjustified elementary geometric assertion, or source error. The new criterion is a genuine input; the rest of the assembly is carried by the item's own steps. Stage 1 below the new criterion remains future work, as required by the one-level brief.

## Unfinished work

None for this item's one-level split. The new statement-only criterion remains unsplit by design. Validation and delivery results follow from the required tool invocations.
