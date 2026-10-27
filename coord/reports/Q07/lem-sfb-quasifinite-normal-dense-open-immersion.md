## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-quasifinite-normal-dense-open-immersion.json`: existing statement, now split into seven steps, statement and statement dependencies unchanged; not an exact Mathlib match.
- `citations.json`: 16 verbatim statement quotes, one for every cited node in every proof step.
- `searches.jsonl`: actual searches made by msearch.py, retained in the sandbox.

## New nodes

None. Zero new Mathlib leaves. Every substantive ingredient already has a node; elementary open-subspace, generic-point and inverse-gluing arguments remain steps.

## Attachments

None. Searched `lean/WeilConjectures/` by the blueprint tag, birational/normal, Zariski Main and monomorphism/open-immersion concepts. No declaration of the project states this whole criterion. Existing project results on normal dense opens and Mathlib's normalization open immersion are ingredients, not attachments of this item.

## WANTED

None needed for this proof. All sources used are the local Stacks files. The historical BLR reference is retained in the item; the proof is an agent assembly of the stated Stacks results, not a claim to have read or reproduced BLR in this session.

## Findings and changes

The item was unsplit with an empty proof, and its statement is correct. There is no STATEMENT-DISPUTED correction. The hypotheses are not strengthened: X need only be reduced, Z may be disconnected, and no flatness, properness, excellence, or finite normalization is used. In particular the normalization factor is integral, and it is the integral variant of 0AB1 that applies, not just its finite variant.

The entire DAG was searched for 02LR, 0CT8, 0AB1 and the relevant concepts before deciding against new nodes. Read the existing monomorphism, normal decomposition, local birational algebra, normal integral neighbourhood, normal dense-open section, and Zariski Main nodes. The local algebra and integral-neighbourhood nodes are unnecessary: the given dense open directly makes the source integral over an integral target open. Thus we do not need to establish the stronger global generic-component definition of birationality before restricting the target.

The imported blueprint was searched with `blueprint_refs.py search` for birational, monomorphism, normalization; the output has no duplicate of this statement. The ancestor command returns null for this existing, newly created chain. Retained its inherited `blueprint.from.node: null`, `via`, and precise BLR support place. Read the current `literature/blueprint/latest/` (main-20261024) chapter, unit and direct-images statement/proof; this remains a below-unit supporting scheme argument for the graph-chart lemma, not a replacement of a chapter or unit route. The current unit has no realization recorded; this item is not its key node, so no unit record is changed.

Mathlib searches from the live item are retained. Additional searches were run with msearch.py in this sandbox, including LeanSearch, LeanFinder (two phrasings), Loogle (normal and birational patterns) and grep of AlgebraicGeometry. Read the actual results and Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean lines 355–365. The candidate `instIsOpenImmersionToNormalizationOfLocallyQuasiFiniteOfLocallyOfFiniteType` is precisely the existing leaf pqf-lem-normalization-open. It does not identify the normalization with Z. `IsOpenImmersion.of_flat_of_mono` assumes flatness, which this item must prove indirectly and does not assume. The other hits are definitions, converse implications, or properties of the normalization construction. No exact or one-line match for the whole item was found.

## Not duplicates

No new node was created. Reused pqf-lem-normalization-open for 02LR, lem-weil-pbc-relative-normalization for integrality of its scheme, rem-pc-regular-normal for the normal component decomposition, and lem-trf-integral-birational-normal-isomorphism for 0AB1. The existing finite birational node was not sufficient for the integral factor, so the already-existing integral variant was used instead.

## Review by Q07

I read Stacks more-morphisms.tex, label lemma-quasi-finite-separated-quasi-affine (02LR), and morphisms.tex, labels lemma-monomorphism-loc-finite-type-loc-quasi-finite (0CT8) and lemma-finite-birational-over-normal (0AB1). These give the intended route, with the normal-target conclusion obtained by an argument rather than attributed to 02LR verbatim. For the disconnected reduction I read properties.tex, labels lemma-normal-locally-finite-nr-irreducibles (0357) and lemma-normal-Noetherian (033M). I checked these tag-label pairs against tags/tags and corrected an initial draft's wrong 0358 reference to 033M. I also read the normalization definition/characterization (035H/035I), its reducedness property (0AXN, as recorded by the cited node), the generic rational-function lemma (01RV), schemes.tex lemma-scheme-sober (01IS), the monomorphism diagonal/separatedness lemmas (01L3/01L4), and morphisms.tex lemma-unramified-over-field (02G7). No new-node source needs review because none is created.

Step 1 uses clause (2), not clause (1), of rem-pc-regular-normal: its statement explicitly gives normal integral OPEN components under exactly normal plus Noetherian, with no regularity assumption. The affine-opens-basis node explicitly permits an affine open contained in each component. The empty target is not forced into a nonempty component. These two cited statements were opened and copied to citations.json.

Step 2 is the elementary missing argument that rules out extra source components. For each nonempty affine V within a component, H intersect V is a nonempty irreducible open. Its inverse image is isomorphic to it and is dense in W, because W is an open of X. The closure of this irreducible subspace is all of W; hence W is irreducible. Reducedness restricts to opens because the local rings are unchanged, exactly the definition in def-pc-reduced-scheme. Def-pc-integral-scheme explicitly states the reduced/nonempty/irreducible equivalence. No theorem about components of a dense open, or birationality with unexplained component hypotheses, is smuggled in.

Step 3 uses the affine-cover definition of finite type, on affine opens of V which are also affine opens of Z. It applies lem-trf-monomorphism-finite-type-composite-lqf with g the identity and the restricted monomorphism f_V. That statement explicitly gives separatedness and unramifiedness. I checked the additional isolation citation: lem-weil-pbc-unramified-fibre-point-isolated gives that every point is isolated in its actual fibre, not just the definition of quasi-finite at a prime. Thus the precise finite-type/isolated-fibre definition in pqf-def-quasifinite is met. This extra citation avoids silently interchanging the two formulations of quasi-finiteness.

Step 4 checks the qcqs target using the affine-scheme-qcqs statement. The precise statement of pqf-lem-normalization-open gives a quasi-compact open immersion to the RELATIVE normalization, plus an integral map to V. It is not the normalization of W. The statement of lem-weil-pbc-relative-normalization identifies the same construction and its clause (iv) explicitly says it is integral when the source is integral. W is integral from step 2; f_V is quasi-compact by finite type and quasi-separated by separatedness. Thus the result is applicable without a finite-normalization hypothesis.

Step 5 is elementary from the two cited statements and the definitions of generic point and open subscheme. Sober schemes have the needed unique generic points; an integral scheme's generic point lies in each nonempty open. The open immersion j and the isomorphism over H intersect V identify the generic local rings. The identity p composed with j equals f_V identifies the map induced by p as the composite of those isomorphisms. The function-field node identifies those actual generic local rings with function fields. This verifies the specific map, not merely an abstract isomorphism of fields.

Step 6 applies the integral variant of 0AB1, whose node I opened: both schemes are integral, the map is integral, its generic point maps correctly with an isomorphism of function fields, and the target's local rings are integrally closed domains. These are precisely the hypotheses listed by lem-trf-integral-birational-normal-isomorphism. The normality is on V, not mistakenly on W or N. Composition with that isomorphism identifies W with the open image of j, giving exactly def-weil-open-immersion.

Step 7 is the elementary assembly of the open identifications. The images on overlaps are equal because each is the image of f restricted to the inverse image of that overlap. Their inverse maps agree because they invert that same restricted morphism. Gluing them gives an inverse on the union of the images, and hence the exact open-immersion definition. No intersection of affine opens is asserted affine. The empty cover gives the empty isomorphism.

Off-unit generic tools are declared only in split_report.tool_uses for maintainer review: rem-pc-regular-normal, lem-trf-monomorphism-finite-type-composite-lqf, lem-weil-pbc-unramified-fibre-point-isolated, lem-weil-pbc-relative-normalization and lem-trf-integral-birational-normal-isomorphism. No top-level maintainer tool_uses field is written. The other nontrivial Zariski Main ingredient is already a Mathlib leaf. These tools implement the stated normal-target Zariski Main argument; they do not import a different unit's proof route.

I checked B1–B10: there are no new statement-only nodes to violate shape or self-containedness, the item statement and definition citations stay intact, TeX is singly escaped in decoded JSON, all named source tags were checked, all new search records are actual runs, and no attachment substitutes a partial or sorried proof. I checked C1–C8 by opening every used node's statement, copying 16 quotes, and reading the full transitive dependency sets for cycles: none reaches this item. The proof cites result statements, not their internal proofs. D1–D5 are satisfied by the seven actual arguments and zero replacement nodes. There is no moved clause or circular induction.

For E1–E7 I tested: identity maps and dense open immersions; disjoint unions of normal integral targets (componentwise proof); empty target/source; a map from only H to Z (still open); a cusp normalization (excluded by target normality); a blow-up (excluded by monomorphism); and adjoining an extra component over the boundary to a dense-open isomorphism (excluded by source density). Reducedness is used precisely in step 2. The affine locality avoids assuming Z globally separated. Normality and Noetherianity are used precisely where the cited normal component result requires them. The generic-point comparison uses nonempty integral schemes, obtained before choosing any point. Each step is under 2000 characters; none conceals a lemma in a long paragraph.

## Unfinished work

None in the stage-1 split. No Lean file was written and no compiler, Lake or build command was run. The server review_split check passed with zero new nodes; the final delivery dry run and push are run after this report is written.
