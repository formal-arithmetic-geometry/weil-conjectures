# Worker report: lem-sfb-point-blowup-local-chart-package

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-point-blowup-local-chart-package.json: statement, split into nine proof steps; not a Mathlib match.
- citations.json: verbatim statement excerpts for every cited node in every proof step.
- No new nodes; no new Mathlib leaves. The existing item statement, statement dependencies, provenance and earlier searches are retained.

## Attachments

None. I searched the project source under lean/WeilConjectures for the exact blueprint tag and the point-blowup terminology and read the existing affine-blowup definitions, chart algebra, gluing and flat-comparison interfaces. They provide pieces, but no declaration states this whole regular-point package under its hypotheses. In particular a general Proj chart theorem is not an attachment of this item.

## Literature wanted

None. All proof sources needed here are present under literature/stacks-project.

## Corrections and scope

The imported item had a statement and searches, but no proof. Its statement is correct, including the empty zero-dimensional case; I made no statement change. The proof does not assume that T is globally Noetherian, integral or separated: regularity supplies the regular Noetherian affine neighbourhood, and properness is proved for the finitely generated ideal on that neighbourhood. Flat base change is applied along the canonical spectrum-of-stalk map, not along an arbitrary map. The direction and order of the comparison's fibre-product factors are explicit. Global/affine comparison and coefficient maps are justified by the existing Rees presentation and cover comparison, rather than by importing properties from a definition's proof.

The ancestor command reports blueprint.from.node = None for this already-created item's ancestry; I retain the inherited null node and its detailed place/via chain. I searched all blueprint nodes for blowup, regular local, and standard open and found no equivalent statement. This item realizes the local geometry prerequisite of the inherited stable-curve rigidity/point-blowdown route, without altering that route or any unit/chapter.

## Not duplicates

No new nodes were created. In particular the regular-local-domain, regular-parameter regular-sequence, affine-blowup chart-cover, flat-comparison, affine restriction, properness, basic-open sections and Proj chart-ring coherence statements already exist and are cited directly. The empty and one-generator cases and the final map on overlap fractions are short applications of these statements, not separate nodes.

## Review by Q73

I read divisors.tex Tags 0804 (lemma-blowing-up-affine) and 0805 (lemma-flat-base-change-blowing-up), algebra.tex Tags 00NP (lemma-regular-domain), 00NQ (lemma-regular-ring-CM), and 00CO (definition-localization), and the first proof paragraph of resolve.tex Tag 0AGS (lemma-cohomology-of-blowup). I also read schemes.tex Tag 01HV (lemma-spec-sheaves) and Tag 01I3 (lemma-standard-open-affine), properties.tex Tag 02IZ (lemma-codimension-local-ring), and constructions.tex Section 01M3 and Lemma 01M4 for the actual homogeneous-localization restriction maps. No SGA source is used. There are no new nodes requiring separate source checks.

For step 1 I checked the statement of def-weil-regular-scheme: it supplies the affine neighbourhood and regular local stalks. The affine-open-stalk localization node supplies the actual germ localization and its canonical coefficients, and the localization-at-prime definition supplies the maximal ideal. The domain node proves nonzeroness and absence of zero divisors. The generalization-chain dimension node states its assertion for every scheme and every point, not only finite-type schemes over fields; its irreducible-closed-chain formula, together with the dimension definition, gives precisely the required bound without an extra finite-type hypothesis.

For step 2 I checked the affine restriction clause in lem-sfb-blowup-rees-symmetric-presentation, which applies to an arbitrary scheme and quasi-coherent ideal and specifies the structural comparison. On V the centre's ideal is p. The Noetherian-ring definition gives finite generation of that ideal. lemma-nagata-affine-blowup-proper assumes just finite generation, which is now available. This avoids using any unwarranted global finite-generation assumption on the centre.

For step 3 I checked lem-sbc-canonical-stalk-spectrum-flat at V and x; its statement really is flatness of this map. The flat-base-change definition introduces the actual comparison for a flat map and the extended ideal, and thm-nagata-blowup-flat-base-change states that this comparison is an isomorphism. The local quotient calculation identifies the inverse-image ideal with pA. The factor exchange is proved from the projection universal property, which def-pc-fibre-product actually states, and not assumed as an unrecorded geometric comparison.

For step 4 the Rees presentation states that its affine identifications commute with coefficientwise restriction. The affine-blowup definition identifies that Proj with the affine model and specifies its structural coefficient map. The cover-independent statement characterizes the gluing comparison by its affine refinements; the one-element affine cover therefore gives the same comparison. The flat-comparison definition explicitly states its degree-zero coefficient map, so the equality of the maps on functions is justified by those statements, not by an inaccessible internal construction.

For step 5 the localization-at-prime definition gives the residue field A/m. Since p is maximal, localizing R/p changes nothing. I wrote the two projection-preserving inverse maps of fibres and used uniqueness from the fibre-product definition to verify their composites. This is a universal-property calculation; no extra theorem about fibres is being smuggled in.

For step 6 the d=0 argument uses m=0 from regular locality, the existing chart cover, and the chart-subalgebra definition inside A_0. The zero ring has no proper prime ideal, so the only chart is empty. In d=1 the regular-parameter theorem applies because exactly dim A generators were chosen; it gives a nonzerodivisor s, hence injectivity of A to A_s. Every generator a/s of the chart algebra is an element of A because a is a multiple of s. This proves the one-chart identity, including the structural coefficient map. I deliberately did not create nodes restating either dimension clause.

For step 7 the regular-parameter theorem assumes a regular local ring and a dimension-sized generating family, both supplied in step 1 and the choice of s,t. It proves a regular sequence; its nonzero quotient and injectivity clauses exclude s=0 and t=0. The affine chart cover gives the two charts, and prop-nagata-affine-blowup-chart with its defining chart map and homogeneous-fraction map gives the opens D_+(su), D_+(tu) and the coefficient formula. These statements say precisely what is used, including the A-scheme structures.

For step 8 I checked that the projective-spectrum basic-opens statement includes the intersection formula. The elementary fraction equation tu=(su)((tu)/(su)) inside the localization identifies the intersection with the basic open at t/s, and symmetrically at s/t. The affine-basic-open theorem states that its section ring and restriction map are the localization. The existing Proj chart-ring coherence statement concerns the canonical localization-induced overlap identifications, while def-pc-proj explicitly fixes restriction maps to be graded localization maps. Together they justify use of the same rational fractions on both sides.

For step 9 I wrote the actual formula c/(t/s)^n -> c(s/t)^n in A_st and verified its domain and invertibility conditions. I checked the second composite on A and s/t, which generate C_t since m=(s,t); the Proj restrictions invert t/s and fix A. Agreement on those algebra generators proves agreement of the maps. A section has equal restrictions to the intersection by the composition rule of the structure presheaf, hence its two chart values have equal images. This final calculation is elementary and is not a new comparison lemma.

I tested the small cases on Spec k (m=0 and empty blowup), a one-dimensional regular local ring with a nonzero principal maximal ideal (one chart with ring A), and k[s,t] localized at (s,t) (the ratio charts, with intersection at invertible t/s). The construction works equally in mixed characteristic, for example the regular parameters p,t of Z_(p)[t]_(p,t); no field or equicharacteristic hypothesis entered. Disconnected regular T is allowed: every argument occurs on V or at A and never assumes R is a domain. Only A and the ratio charts in the local cases require the domain property, which is proved before use.

Against delivery-errors B--E: all cited statements were opened; citations.json uses literal excerpts, not paraphrases; no new-node statement conceals a proof, and no clause was moved into a duplicate node. Every non-elementary step names its tools. Each step is under 2000 characters. Cross-unit uses are generic tools listed in split_report.tool_uses. The mathematical statement and the unit/chapter route were preserved.

## Unfinished work

None in this stage-1 split. The required server dry run and delivery are recorded by the delivery tool.

## Repair of the 2026-10-23 return

The return identifies approved delivery head e0844703125 and a landing failure caused by side completion not being promoted to the live DAG. I compared the retained split with the current read clone: the current item is unsplit, has no proof, and has exactly the same statement, statement dependencies, source and blueprint ancestry as the retained split. I preserve that statement and ancestry and all recorded searches, rather than treating the old side completion as a live completion. The required deliver.py reconstructs the delivery on the current origin/sheaf-dag and retains its maintainer fields.

I re-opened the complete current statements of every statement and proof dependency, not only their citation excerpts: the regularity, dimension, local algebra, affine/stalk, blowup Rees and gluing, flat comparison, chart and Proj interfaces. Every existing excerpt still occurs verbatim in the current node. In particular the flat comparison definition still fixes Y as the first product factor, its theorem proves that constructed map is an isomorphism, the Rees presentation still supplies coefficientwise affine restriction, and the overlap theorem still supplies localization-induced equivalences. Thus none requires a different route or a statement change. This re-reading also checks every potentially changed citation without assuming the earlier reader's approval remains valid.

I adjusted step 3 to cite the affine-stalk theorem explicitly for V itself: O_(V,x) and O_(T,x) both identify with R_p via the fixed coefficient map. Hence the map to which the flatness theorem applies really is the map used for base change. I added its verbatim citation and expanded the regularity excerpts to include the dimension-sized generator condition and affine regular neighbourhood, rather than quoting only the opening words. I replaced the generic repeated tool-use explanations by the precise statement each step needs and why it is a generic geometric or algebraic prerequisite. These are concrete proof and citation repairs in addition to the rebase; the nine-step argument and all its earlier source checks are retained.

I checked the revised steps again against delivery-errors B--E: no new nodes, no clause relabelled as a lemma, no extra global or finite-type hypothesis, and no uncited comparison in the stalk-map clarification. The zero-dimensional empty blowup, principal one-dimensional case, two-variable regular local example and mixed-characteristic parameter example remain valid. Every step remains below 2000 characters. The final dry run must validate this revised sandbox before its push.
