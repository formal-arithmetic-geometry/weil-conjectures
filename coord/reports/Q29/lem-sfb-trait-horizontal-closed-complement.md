# Stage-1 report: lem-sfb-trait-horizontal-closed-complement

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-trait-horizontal-closed-complement.json`: statement, split; no Mathlib match. The statement and statement dependencies are unchanged. Added eight proof steps using existing nodes, exact proof dependencies, proof origin, split report and the searches actually performed in this sandbox.
- `citations.json`: 21 step/node entries with verbatim excerpts of the cited statements.
- `report.md`: this report. `prepare.py` and `searches.jsonl` are sandbox working records, not additional DAG nodes.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched the read-only live `lean/WeilConjectures/` for the exact item id and docstring tag and for horizontal closure/complement, trait thinness and generic closed subsets. The scheme-image comparison declarations found do not prove the item. The item has no existing Lean audit identifying a completed declaration. No Lean file was written or compiled.

## Wanted literature

WANTED: Bosch--Lütkebohmert--Raynaud, *Néron Models*, local `literature/bosch-lutkebohmert-raynaud-neron-models.pdf`, §6.5 Theorem 1 proof, printed p.162 (PDF p.168), for lem-sfb-trait-horizontal-closed-complement. The primary scan at https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf was read online. That page asserts the trait-thinness of the schematic closure; it does not give the affine ideal proof. Accordingly `proof_origin.by` is `agent`, and the omitted calculation is supplied explicitly. No file was downloaded or written into the shared repository.

## Corrections and scope

The imported statement is correct; no STATEMENT-DISPUTED and no changed hypotheses. The empty imported proof needed the actual horizontal-closure argument. No hypothesis of generic irreducibility, pure relative dimension, perfect residue field, excellence, completion or properness is added. Separatedness is retained as stated, although the local argument does not require it.

The inherited `blueprint.from.node` is null; `python3 tools/blueprint_refs.py ancestor lem-sfb-trait-horizontal-closed-complement` confirms that a new child would also have null ancestor. I preserved the existing specific place and full via chain. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its proof and the unit and chapter records. Searches for trait, schematic closure, dense open and horizontal assertions found no blueprint node stating this item. This split supplies the local scheme-theoretic lemma below the existing effective-dense-affine argument, without replacing any unit step.

## Not duplicates

There are no new nodes to compare. Existing smooth-trait volume infrastructure already states the Noetherianity, regularity, and special-component DVR stalk facts, so I cite it. Existing scheme-image, affine generic-fibre, normal-component, unit-times-uniformizer, sobriety, and fibrewise-density base-change nodes supply the other non-elementary facts. In particular, I did not create a node for saturation of a contracted ideal or its persistence under localization: both arguments are written in the proof.

## Review by Q29

I read the source passage in BLR §6.5 p.162 in the primary scan and compared the asserted trait-thinness with every clause of the item. I also read the actual statements of all 16 distinct cited nodes. For the local algebra and topology I checked Stacks `morphisms.tex`, Tag 01R8, label `lemma-quasi-compact-scheme-theoretic-image` (kernel and restriction to opens); `algebra.tex`, Tag 00PD, `lemma-characterize-dvr` (uniformizer powers); `schemes.tex`, Tag 01IS, `lemma-scheme-sober`; `topology.tex`, Tag 004W, `lemma-irreducible`; and the normal Noetherian decomposition in `properties.tex`, `lemma-normal-locally-Noetherian`. The cited affine stalk statement explicitly identifies germs with localization, so its use does not require borrowing anything from its proof. I read the field-openness statement Tag 0383 underlying the existing base-change theorem as well. There are no new nodes needing separate sources or searches.

Step 1 uses the DVR definition to choose a uniformizer and the existing smooth-trait infrastructure for Noetherianity, regularity, reduced special fibre and DVR stalks. Its hypotheses are precisely a smooth finite-type morphism over a DVR, as here; its optional pure-dimension clause is unused. The regular-normal statement then gives integral clopen components of the Noetherian scheme. This replaces no missing proof with a definition.

Step 2 uses the affine generic-fibre model; its reduced-closed-fibre hypothesis is supplied by step 1. The closed-immersion statement supplies the quotient ring on the affine generic open. These affine preimages prove that the composite immersion is affine, so the affine-morphism permanence statement supplies quasi-compactness and quasi-separatedness before applying the quasi-compact image-kernel statement. That last statement gives exactly the ideal kernel on each affine open. Saturation and extension-contraction are then proved with actual numerators, using invertibility of the uniformizer in the target. In particular the image-kernel statement is not being used to claim flat base change or an unstated stalk formula.

Step 3 invokes the open-restriction image theorem with both of its finiteness hypotheses now proved, and the separate statement that a closed immersion has itself as image. Together they identify the generic closed subscheme, not merely its underlying set. Step 4 invokes normal decomposition and the integral-scheme definition to choose a domain chart, the affine-stalk localization statement to preserve the uniformizer in the stalk, and smooth-trait infrastructure for its nonzero DVR uniformizer. The argument identifying the clopen generic component and forcing J nonzero is written out using irreducibility; it does not assume that all components have the same dimension.

Step 5 is elementary ideal arithmetic relative to those identifications. For a nonzero fraction in J its numerator is nonzero in the domain chart and belongs to I; domain localization keeps it nonzero. For saturation after localization I explicitly inserted the denominator t outside the prime, applied saturation before localization, and divided back. This addresses the usual hidden 'clear denominators' error. Step 6 uses exactly the unit-times-uniformizer-power statement on the DVR stalk supplied in step 1. A nonzero element of the saturated ideal then forces 1 into it, proving the special generic point is outside the affine closed subscheme. I checked the conversion from the unit stalk ideal to an element of I outside the prime, rather than confusing the ideal with its vanishing locus.

Step 7 uses sobriety for component generic points and the components-cover statement for arbitrary fibre points. Its argument is the explicit closure inclusion for each generic point, so there is no appeal to an unstated fibre-dimension semicontinuity theorem. The same uniformizer-power result shows a DVR has just its generic and closed points; there are no omitted ordinary fibres. Step 8 applies the existing smooth fibrewise-density base-change theorem only after all ordinary fibres have been checked. With base Spec Omega this gives the exact geometric-fibre density requested, for arbitrary algebraically closed extensions, including inseparable residue-field situations.

I checked small cases: empty Y; empty special fibre such as Y=Spec F; Z_F empty; Y=Spec R, where the hypothesis forces Z_F empty; Y=A^1_R with Z_F cut out by x (closure x=0); and Z_F cut out by pi*x-1 (closure with empty special fibre). A disjoint union of smooth schemes of different relative dimensions causes no change. Nonreduced Z_F is allowed because the contraction/saturation argument uses its ideal, with no radical assumption. I also checked that a component of the special fibre need not be the whole special fibre: the proof is performed separately at every component generic point.

Against delivery-errors B--E: no new or duplicate node, no proof hidden in an unsplit statement, no invented Mathlib search, no weakened clause, no uncited non-elementary assertion, and no proof-only citation. All proof steps are shorter than 1,000 characters. The sandbox graph traversal found no path from any cited dependency back to the item. Cross-unit general scheme/algebra statements are explicitly declared as generic tools in `split_report.tool_uses`; they supply infrastructure rather than replacing a unit route. The imported search records are retained; five new actual searches (LeanSearch, Loogle, two LeanFinder phrasings and grep) are in the command's log and node, and the returned signatures were read. They give only dominance, specialization, rational-map domains or general nowhere-density, so none attaches the whole item as a Mathlib leaf.

## Unfinished work

None in the mathematical split. The first server dry run exited successfully with `OK (not pushed)` at `37c440fc612`, including the maintainer preflight, DAG check and split review. The final package is validated again after recording this result and expanding the infrastructure citation excerpt to include every clause used. The direct push follows that successful final dry run.
