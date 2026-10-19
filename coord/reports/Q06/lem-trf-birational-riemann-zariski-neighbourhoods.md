# Worker report: lem-trf-birational-riemann-zariski-neighbourhoods

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-birational-riemann-zariski-neighbourhoods.json`: statement, split into 14 steps; Mathlib search verdict no match; statement unchanged.
- `citations.json`: verbatim statement quotations for every step/node citation.
- `searches.jsonl`: actual Q06 Mathlib searches, including a second semantic phrasing; results read.
- `report.md`: this report.

No new nodes, and no new Mathlib leaves. The sandbox initially contained only dispatcher marker files; there was no earlier split, report or search log to preserve. No Lean files were written, and no compiler, Lake, local preflight, local DAG checker, or git command was run.

## Attachments

None. Searches of the project `WeilConjectures/` source for the exact blueprint id and for Riemann--Zariski, centred valuations and birational neighbourhoods found no declaration stating this item. Upstream master was also checked read-only; its declarations are not treated as finished proofs.

## Wanted literature

WANTED: `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`, Section 3.2, printed pp. 15--17, for this item. The primary PDF at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf was read online, including the opening model conventions, Proposition 3.2.1, Lemmas 3.2.2--3.2.3, Corollaries 3.2.4--3.2.5, Proposition 3.2.6, and Corollary 3.2.7. There is no local archival copy. In accordance with the brief the proof is marked `proof_origin.by = agent`; nothing was downloaded into the read-only repository.

## Findings and changes

The node's statement is correct with its fixed common function field F. Its proof and proof dependencies were empty. I supplied the argument, retaining all clauses and all original statement dependencies. In particular I did not impose Noetherianity, finite presentation, separatedness of Z over the integers, finite valuation height, or separable closure of F. These would change the scope of the item. The meaning of birational quasi-model includes integrality and the same specified function field, by the preceding definition of model and the word 'instead'.

I read the chapter and unit records, SETUP's three levels, GOAL, dag-sync and the stage-1 contract. The inherited blueprint ancestry is retained: this node supplies the fixed-field input in the semistable-alteration branch through its creating item. It is not the unit's key statement, so no unit realization fields are changed. Whole-blueprint search for Riemann and DAG searches for model/valuation/compactness inputs found no blueprint node stating this fixed-field result. The current item already is the node that other recent deliveries were instructed to reuse.

The existing `lem-trf-riemann-zariski-local-colimit` has a finite-type-over-Z base and a separable-closure field, and indexes centred quasi-models. The `lem-trf-qcqs-separable-riemann-zariski-refinement` allows qcqs bases but requires a separable closure. The `lem-trf-riemann-zariski-finite-refinement` additionally has a finite-type-over-Z base and a finite-height conclusion. None supplies the present arbitrary fixed F statement as a specialization. I read the finite-refinement proof to locate reusable general tools, then opened each cited node and used its statement only. There is no dependency on any of these three Riemann--Zariski nodes, and no duplication by a newly created node.

The fresh leanfinder searches returned quasi-compactness, normalization and valuative-criterion infrastructure, not a theorem for this space or diagram. Loogle and the Mathlib grep for RiemannZariski returned zero hits. LeanSearch returned ordinary quasi-compactness definitions and restriction criteria. The signatures were read. The prior mathematical search entries are retained with the results of the actual fresh Q06 invocations; no unavailable service is reported as absence.

## Not duplicates

No new nodes were created. Every non-elementary tool needed by the proof already exists in the DAG; the finite-type/separated composition calculation, directed-union universal property, smallness argument and cofinal restriction argument are written out as steps rather than packaged as new nodes. The elementary steps are 3, 8 and 14; the non-elementary steps cite their actual tools.

## Review by Q06

I reviewed this as the author against delivery-errors B--E, with the item, the cited node statements and the sources open. There are no statement-only children to audit and no claim that an isolated clause has been proved merely by renaming it. All proof dependencies are exactly the union of step uses, and all 14 steps have explicit sources and Boolean elementary fields. Each step is at most 1093 characters; no non-elementary step crosses the 2000-character hidden-lemma threshold.

For the item I read Temkin Section 3.2 in the primary PDF, with F equal to the base function field rather than a separable closure. The argument follows its inverse-limit, projective graph, valuation-union, and open quasi-modification route. I also read local Stacks sources: `properties.tex` lemma-quasi-compact-quasi-separated-spectral (094L), `topology.tex` lemma-directed-inverse-limit-spectral-spaces (0A2Z), `schemes.tex` lemma-reduced-closed-subscheme (01J3), lemma-morphism-from-spec-local-ring (01J6), separated-permanence and valuative uniqueness, and `morphisms.tex` composition-proper (01W3), base-change-proper (01W4), closed-immersion-proper (01W5), image-proper-scheme-closed (01W6), and characterize-proper. These confirm the general hypotheses of the existing black boxes, including applicability without Noetherianity. No SGA source is used.

Step 1 uses the reduced-induced-closed-subscheme node's affine quotient and uniqueness statements, and the closed-immersion-proper node's proper composite clause. The reduced closure of the specified generic point is integral. I checked the field equality: its generic field injects into F, and the dominant map to Z gives the reverse map whose composite is the identity of F. This prevents accidentally admitting alteration fields into the fixed-field model category.

Step 2 uses proper base change and composition for the product; the proper definition says that the target model's diagonal is closed; closed-immersion base change constructs the equalizer; the integral-stalks-in-function-field statement detects its zero ideal. Thus common refinements and uniqueness are proved, not borrowed from a compactification category with stronger hypotheses. Step 3 uses the actual finite-type definition to obtain finite covers and the integral function-field injection to encode affine rings as subrings of the set F. Overlap opens and gluing maps are sets, which gives a small representative category without assuming finite presentation.

Step 4 uses the qcqs permanence node exactly in its source-over-qcqs-base clause. Proper implies quasi-compact and separated, and a closed diagonal is quasi-compact, so its morphism is quasi-separated. The proper-to-separated-target node applies to the triangle consisting of two proper Z-models. Thus refinements are spectral maps. The qcqs-scheme-spectral node gives spectral objects; the directed-spectral-limit node explicitly allows precisely their compatible-point space and initial topology. The spectral definition includes quasi-compactness, proving the compactness used here.

Step 5 uses the integral local-ring embeddings to form the actual union inside F. I checked locality: local transition maps keep every earlier nonunit a nonunit, so the union of the maximal ideals is exactly the nonunits. The morphism-from-spec-local-ring node gives the morphism with its specified centre and local map, including its uniqueness; this is needed to retain a prescribed morphism to a possibly nonseparated base.

Step 6 uses proper projective space and the projective chart cover (the Proj construction node), together with the affine-chart identification, to test every nonzero a in F on a proper graph model. The two chart coordinates give respectively a and its inverse. This proves the valuation property; it does not cite a new node restating that property. Step 7 checks the exact fraction field F in each valuative square. The proper-separated-valuation-extension node says existence and uniqueness, not merely separated uniqueness. The valuation-intersection node applies with both fields equal to F and a dominating inclusion, giving O = R_x. The local-spectrum correspondence also recovers the map to Z, rather than only the subring O. These establish a topology-compatible bijection.

Step 8 is the explicit short proof needed for separated finite-type composites. The finite-type-composition node states its required clause without extra base hypotheses. The closed-immersion base-change node applies to the second diagonal factor, and the definition's affine-surjection characterization proves composition of closed immersions. Thus the later compactification does not silently assume a permanence lemma that is missing from the citations.

Step 9 applies the qcqs Nagata theorem to the separated finite-type U/Z that is actually present. Its compactification-data node gives an open immersion and a proper map. The reduced-closure node's uniqueness shows that replacement preserves the open U because U is reduced and integral. The separated-valuation-lift-unique node gives injection even though U/Z is not proper. The equality of the image with a centre-projection open is proved by the closed-point factorization criterion for a local spectrum.

Step 10 checks continuity by pulling any proper Z-model back to U and taking its reduced generic closure; proper base change and closed-immersion properness give exactly a proper U-model. Proper lifting uniqueness identifies its centre map with the restricted target centre map. Step 11 separately checks inverse continuity on every generating source open by compactifying its proper U-model over Z (whose separated finite type was proved in Step 8). Nagata, reduced closure and proper lifting uniqueness give the required equality of opens. The qcqs permanence node guarantees U is qcqs. Neither direction of the topology comparison is omitted.

Step 12 constructs the affine-centre indexing category and proves it small, nonempty and cofiltered using earlier constructions. Uniqueness is the same integral-source/closed-diagonal argument as Step 2, and the proper lifting statement makes any allowed arrow respect O. At a common dominating model the intersection of the inverse-image opens contains the lifted centre, so it has an affine neighbourhood; no claim that arbitrary intersections of affine opens are affine is made.

Step 13 uses every needed clause of the integral-stalks-in-function-field node: injective germs, local-ring fraction field F and section injection. The fraction field of an affine ring equals that of its localization, by the elementary fraction computation. A local germ b/s is represented in the affine D(s), where s does not vanish at the centre. Hence the union of the affine rings is exactly the already identified O. The universal property of the directed union is written out, not just called a colimit. Step 14 proves cofinality after imposing the prescribed model and neighbourhood conditions by taking common refinements and then shrinking around the centre; elements remain represented. These steps preserve all indexing and injectivity clauses of (iii).

I tested a field base: the only valuation containing F is F, every integral birational model over Spec F is Spec F, and the construction reduces to its identity diagram. The valuation O=F over an arbitrary integral base has generic centres; the union is F even when no single affine neighbourhood has ring F, since each fraction becomes regular after a principal shrinking. For a non-Noetherian valuation-ring base, no finiteness or rank assertion about O enters the proof. For a nonseparated integral base such as the doubled-origin line, the valuation ring alone can have two centres; Step 7 explicitly keeps the prescribed centre morphism, so it does not merge those two points. A nonproper quasi-model is handled by its centre open in its compactification, rather than by assuming its morphism to Z is an open immersion. Empty quasi-models are excluded by integrality and the specified function field; every affine neighbourhood used contains a centre. Prescribed neighbourhood intersections are nonempty for that same reason.

All off-unit non-leaf tools are declared in `split_report.tool_uses` with the fact used and why the unit lacks it. They are generic topology, valuation, projective-geometry and compactification tools, not replacements of the unit's geometric route. Citations.json copies actual statements verbatim for all uses; no definition-only citation is standing in for a non-elementary theorem. There is no new statement dispute or source error. The corrected omission is the previously absent proof, including the two topology directions and the small/cofinal affine-index details.

## Validation

The server `review_split` check passed before the full delivery dry run. Full `deliver.py --no-push` validation and push results are recorded below after execution.

## Unfinished work

No mathematical part remains. The local Temkin archival copy remains a WANTED literature item for maintenance; the primary PDF was read online and proof provenance is explicit.

Full dry run completed successfully: `deliver.py Q06 lem-trf-birational-riemann-zariski-neighbourhoods --no-push` printed `OK (not pushed) ... at 0b6b5c1602: preflight passed`. Its process exited before the push invocation. No node or citation file changed after this successful validation. The final delivery command performs its normal validation again before pushing.
