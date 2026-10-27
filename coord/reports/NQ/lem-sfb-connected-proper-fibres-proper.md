# Stage-1 report: lem-sfb-connected-proper-fibres-proper

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-connected-proper-fibres-proper.json: item, split into five steps; Mathlib searches found scheme properness primitives, no exact criterion.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-henselian-proper-clopen-lift.json: statement-only, unsplit; Stacks 0CWI, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-proper-fpqc-descent.json: statement-only, unsplit; Stacks 0422 restricted to scheme targets and covers, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-proper-strict-local-test.json: statement-only, unsplit; strict-local corollary of 08K1 and etale descent, no Mathlib match.
- citations.json: one verbatim full-statement quote per step/node pair. Searches are retained in searches.jsonl, and recorded honestly in the nodes with their actual hit names.

## Attachments

None. Searched WeilConjectures for the item tag and the connected/proper-fibre criterion, and for henselian clopen lifting, properness descent, and strict-local properness. No project declaration states the item or the three space inputs exactly. isProper_of_field_baseChange is scheme-only. Mathlib AlgebraicGeometry.IsProper (Morphisms/Proper.lean:42), its base-change instance (:72) and Zariski locality (:77) are likewise scheme-only and do not state these algebraic-space results. No Lean files were written or compiled.

## WANTED

WANTED: Deligne, Le lemme de Gabber, Asterisque 127 (1985), Section 1.1, for the item's original historical reference. Its absence from literature is retained from the imported source record. This delivery does not rely on its unseen text: the actual proof is explicitly marked agent-assembled from available Stacks statements. No download or repository change was made.

## Corrections and scope

No hypothesis or conclusion was changed. Added the existing locally-Noetherian and space-morphism-property definitions to the statement references and stmt_deps, because the item used those notions without explicit links. Preserved the inherited source, creation fields, null blueprint ancestor, and via list. The item is not a unit key node, so no unit realization file is written. blueprint_refs.py ancestor returns None for the inherited chain. I read the current latest sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3): this supporting relative-Picard criterion stays within its inherited alteration/moduli input route and changes no chapter or unit route.

The local EGA IV-3 PDF, Corollaire 15.7.10 and Proposition 15.7.9, printed pp.245--247, gives the scheme criterion. That is evidence for the intended statement, not a proof for algebraic spaces. The space version is supplied through 0CWI. The existing fppf locality statement does not assert fpqc descent, so it cannot descend properness from an algebraic closure: this is why the fpqc input is necessary.

## Arguments retained for the unsplit inputs

The clopen input is exactly the algebraic-space theorem Stacks 0CWI (spaces-more-morphisms.tex, lemma-split-off-proper-part-henselian, lines 8483 onward). Its source proof uses a proper surjective Chow envelope by a quasi-projective scheme, lifts the proper clopen part there by the scheme lemma 0CT9, and descends its closed images; the two images cannot intersect since their proper intersection would meet the henselian closed fibre. It has no proof embedded in its new statement.

The fpqc input is 0422 (spaces-descent.tex, lemma-descending-property-proper, lines 1666 onward), interpreted by definition-property-morphisms-local at 03YH: properness descends because finite type, separatedness and universal closedness each descend. Its restriction to a scheme base and a scheme covering family is direct. It neither assumes nor concludes flatness of the morphism being descended.

The strict-local input is an agent-extracted corollary, not a claim that 08K1 literally states it. Fix an affine neighbourhood of a geometric point. Its strict localization is the inverse limit of a small cofiltered skeleton of affine pointed etale neighbourhoods (04HX and the existing strict-localization definition). Since the arrow is finitely presented, it is an arrow of the system obtained by base change from that fixed affine neighbourhood. If its limit is proper, 08K1 makes its pullback to some affine pointed etale neighbourhood proper. The finite-presentation assumption supplies all the quasi-compactness/quasi-separatedness and finite-type hypotheses of that limit theorem. A cofiltered category may be replaced by a cofinal directed system to apply its directed-set formulation. Doing this for each geometric point gives a jointly surjective etale family of neighbourhoods. Etale descent of properness (083R, alternatively 0422 and finite affine refinements of etale covers) proves properness globally. Conversely properness is stable under arbitrary base change (04WP). This result needs neither flatness nor connectedness and therefore is a smaller independent descent tool, not a restatement of the item.

## Not duplicates

lem-sfb-space-proper-strict-local-test vs lem-sc-strict-henselization-dvr: the existing node concerns preservation and reflection of the DVR property of a Noetherian local ring, not properness of a finitely presented space morphism.
lem-sfb-space-proper-strict-local-test vs def-per-strict-localization-point-change: the existing definition identifies strict localizations under a change of geometric point; it says nothing about properness detection.
lem-sfb-space-proper-strict-local-test vs compatible-strict-henselization-core-data: the existing node provides compatible strict henselization rings, maps and residue factorizations, not a properness criterion.
lem-sfb-space-proper-strict-local-test vs compatible-strict-henselization-core-existence: the existing node supplies the two strict local rings and geometric residue maps, explicitly without even a map between the rings; it has no properness assertion.
lem-sfb-space-proper-strict-local-test vs compatible-strict-henselization-residues-core: the existing node supplies compatible residue data with the final residue equality replaced by True; it is not a theorem about a finite-presentation space morphism.
lem-sfb-space-proper-strict-local-test vs def-weil-pbc-etale-residue-triples: the existing definition describes etale residue triples and their morphisms, not spreading or detection of properness.
lem-sfb-space-proper-strict-local-test vs def-weil-pbc-relative-separable-closure: the existing definition constructs the relative separable algebraic closure of fields; it does not concern proper morphisms.
lem-sfb-space-proper-strict-local-test vs def-weil-pbc-strict-henselization-point-evaluation: the existing definition constructs the evaluation map from a strict-henselization ring to the geometric field; it has no properness assertion.
lem-sfb-space-proper-strict-local-test vs lem-weil-pbc-compatible-strict-henselization-residue-image: the existing node asserts containment of two residue-field images, with no map between the local rings; it does not detect properness.
lem-sfb-space-proper-strict-local-test vs lem-weil-pbc-compatible-strict-henselization-residue-lift: the existing node lifts a specified compatible residue-field homomorphism to a local-ring homomorphism; it gives no properness assertion.
lem-sfb-space-proper-strict-local-test vs lem-weil-pbc-compatible-strict-henselization-residue-polynomial: the existing node gives a separable-polynomial witness for residue-field elements, not properness of algebraic spaces.

lem-sfb-space-henselian-proper-clopen-lift vs lem-per-henselian-pair-proper-clopen-lift: the existing 0CT9 statement requires X to be a scheme; the new 0CWI statement permits a nonrepresentable algebraic space. An etale chart need not be proper over the base, so this is not a direct application of the scheme lemma.
lem-sfb-space-henselian-proper-clopen-lift vs lem-per-elkik-finite-etale-away-completion: the existing node is an algebraization/lifting statement for finite etale covers; it does not lift proper clopen subspaces of an arbitrary separated finite-type space.
lem-sfb-space-proper-fpqc-descent vs lem-sfb-space-flat-proper-fp-locality: the latter descends only along fppf coverings; field extensions used here need not be locally finitely presented, so that statement is insufficient. The new statement gives fpqc descent and no separate flatness/finiteness properties.
lem-sfb-space-proper-fpqc-descent vs lem-sfb-curve-descent-isom-spaces: the existing curve-specific isomorphism descent does not state properness descent for arbitrary algebraic spaces.
lem-sfb-space-proper-fpqc-descent vs lem-a1-space-fpqc-separated-valuative-descent: the latter gives separatedness and a full valuative lifting property, not finite type or properness. A separate space valuative criterion would still be required.
lem-sfb-space-proper-strict-local-test vs lem-sfb-space-eventually-proper: the existing node concerns an explicitly given affine inverse system, not detection on all strict localizations of a scheme; assembling etale neighbourhoods and descent is a separate generic comparison.
lem-sfb-space-proper-strict-local-test vs lem-sfb-space-flat-proper-fp-locality: fppf covers are families locally of finite presentation. Strict localization maps are ind-etale, generally not of finite presentation; the missing spreading of properness is supplied by 08K1.
lem-sfb-space-proper-strict-local-test vs lem-sfb-space-proper-base-change: arbitrary base-change preservation is only the easy direction, not detection by strict-local pullbacks.

I searched DAG source records and keywords for 0CWI, 0CT9, 0422, 04WP, 08K1, proper/clopen/henselian and strict-local/fpqc properness, and ran blueprint_refs.py searches for 0CWI, proper henselian, clopen proper, proper local, proper strict henselization, proper fpqc, proper descent, proper connected and connected proper fibres. No blueprint node states any new input. The same-tag pair for 0422 is addressed above. No existing node with source 0CWI was found.

## Review by NQ

I read delivery-errors B--E whole, the stage-1 brief and contract, the three-level rule in SETUP, GOAL, the chapter and unit records, and the current latest blueprint's direct-image proof. For the item I read EGA IV-3 15.7.9--15.7.10, and I checked the actual algebraic-space argument against Stacks 0CWI and the openness statement 042S. For each new node I read its named Stacks text: 0CWI for proper clopen lifting, 0422 plus its definition 03YH for fpqc properness descent, and 08K1 together with the strict-localization definition and 083R for the extracted strict-local test. The distinction between scheme and space statements is essential throughout.

Step 1 uses the new strict-local test precisely to reduce properness; strict-henselization-functoriality clause (1) actually says its ring is strictly henselian local and locates the closed point. The existing space-flat-proper-fp-locality statement explicitly preserves flatness and finite presentation by arbitrary base change. Fibre-product associativity identifies every geometric fibre after base change with a geometric fibre in the hypothesis. Separatedness is the diagonal closed-immersion test: every scheme test of the new diagonal is a scheme test of the old one by pasting the pullback square. No Noetherianity of the strict-local ring is being asserted or used.

Step 2 uses field-extension-fpqc-cover, which states all of flatness, surjectivity and quasi-compactness, and the new fpqc properness equivalence, which applies to a scheme target with an algebraic-space source. Thus the ordinary closed fibre really is proper; it is not silently identified with its algebraic closure base change. A point of the nonempty geometric fibre maps to an ordinary fibre point.

Step 3 uses henselian-terminology to turn strictly henselian local into a henselian maximal-ideal pair. The clopen-lifting statement asks only for separated finite type X and a proper clopen subspace of X_0. Finite presentation supplies finite type, the whole closed fibre is clopen in itself, and step 2 supplied its properness. The lifted W is proper and clopen, exactly as its statement promises, with no surjectivity clause invented.

Step 4 obtains openness from flat-lfp-space-universally-open, whose actual statement is valid for algebraic spaces and arbitrary base changes. Restriction to the open subset W is enough: the map q itself is open, so no separate permanence theorem for q|W is needed. An open of Spec A containing its closed point contains D(a) for a unit a and hence all of Spec A. The field-point and sheaf-fibre-product definitions give a common extension point in each W_bar_t. Thus a nonempty clopen subspace of a connected geometric fibre is the whole fibre. This is a written elementary argument, not a hidden properness theorem.

Step 5 uses field-point representatives to rule out even one point of the complement. The open subspace with the entire underlying set is the original space with its restricted structure sheaf, not a claim that a general closed immersion factors merely from image containment. It then applies exactly the strict-local test used at the start. No long non-elementary step exceeds 2000 characters (all five are below 800); no lemma is hidden by shortening a step.

I tested empty base, Spec of an algebraically closed field, identity and P^1 families, and finite etale families of rank one. The empty base is vacuous and proper; the other examples give the whole clopen part. Removing connectedness permits an extra component supported over an open part of a local base, showing why the connectedness step cannot be omitted. Removing nonemptiness makes an open immersion with empty omitted fibres a counterexample. Nonreduced proper fibres cause no problem: only connected topology and properness are used. New clopen lifting permits Z empty (choose W empty), and I=0 (choose W=Z). Fpqc descent includes empty targets and arbitrary field extensions. The strict-local test includes the empty target and imposes finite presentation exactly where spreading is needed.

The three new nodes are statement-only with self-contained objects and hypotheses, existing definition links, exact source tags/labels, and recorded searches actually run through msearch.py. Second phrasings were tried; returned Mathlib HenselianLocalRing/HenselianRing and scheme IsProper/valuative/locality declarations do not state a space lifting or descent theorem. No unavailable service was reported as no match, no new node restates the item's conclusion, and the properness argument stays in the item. Every cited statement was opened, and citations.json uses its unmodified statement verbatim. Cross-unit uses are declared only in split_report.tool_uses with their precise generic purposes.

## Unfinished

The first dry run required additional same-tag nonduplicate explanations for the background tag 04HX. I opened all eleven statements and added a separate comparison for each; none concerns properness. Required server dry run and push remain. The three new inputs deliberately remain unsplit for future items. No statement dispute was found.
