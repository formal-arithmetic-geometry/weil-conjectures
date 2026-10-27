# Stage-1 report: lem-sfb-space-etale-sheaf-realization

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-etale-sheaf-realization.json: existing statement, now split into eleven steps; no Mathlib match.
- citations.json: one entry for every cited node in every step, quoting the actual statement.
- report.md and searches.jsonl: review and actual search records.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag, AlgebraicSpace/algebraic-space terminology and etale/sheaf realization terminology. The scheme and topological declarations found do not state realization over an algebraic-space base. No Lean was written or compiled.

## WANTED

None for the mathematics. All sources used are present under literature/stacks-project. The historical brief mentions coord/dag-sync.md, which does not exist in the current read clone; the direct-delivery brief and current read clone were used.

## Corrections and scope

No change to the statement, its hypotheses, statement dependencies or the explicit coproduct size convention. The item had no proof. In particular I did not use the source's sentence claiming colimit preservation merely from the inverse-image functors: evaluation of global sections need not preserve colimits sectionwise. Instead the proof constructs the quotient, identifies its small-etale sheaf using effective epimorphisms, and evaluates inverse image only on represented sheaves using an explicit adjunction calculation.

The blueprint ancestor tool prints blueprint.from.node = None for this inherited chain. I retained that actual value and the detailed existing place/via, rather than inventing an ancestor. The latest blueprint unit and direct-image proof were read: this is a low-level etale realization input for the chart descent route already recorded in the inherited blueprint place; no unit or chapter route changes. Whole-blueprint searches for 0GF6, sheaf gives space, etale sheaf and realization found no equivalent blueprint statement. lem-a1-etale-sheaf-algebraic-space-realization has a scheme base and additional pro-etale assertions; it is not an algebraic-space-base attachment or a substitute for this statement.

## Mathlib searches

Retained the existing records and added only actual msearch.py records from this run. Item searches used LeanFinder (sheaves over an algebraic space), Loogle ("Sheaf", "Etale"), grep (AlgebraicSpace|sheaf.*gives.*space|etaleRealization) and a second semantic phrasing through LeanSearch (espace etale). Additional local-representative searches were read but became unnecessary when the representable-adjunction calculation removed that need. Results were scheme etale categories, affine-versus-small-etale comparison, generic sheafification interfaces, and the topological espace etale. Read Mathlib/AlgebraicGeometry/Sites/AffineEtale.lean, Morphisms/Etale.lean and Topology/Sheaves/EtaleSpace.lean to distinguish these: none supplies the algebraic-space-base result or a one-line specialization of it. No new node required searches.

## Review by N8

I read spaces-properties.tex Tag 0GF6 (lemma-sheaf-gives-space), including its preceding definition, size footnote and full proof, and Tags 03G1/03G2/03LP on the enlarged site and localization. For the open equality relation I read Tag 04K8 and the scheme version 04HV; the proof uses the latter on the scheme P times_H P, not a theorem for an unavailable scheme base H. I read sites.tex Tag 00WS and its generator proof, and the cited quotient theorem statement in spaces.tex Tag 02WW. These supply the same generator/open-relation/quotient route as 0GF6. There are no new nodes whose sources need separate review.

Step 1 uses the actual fppf-sheaf definition of an algebraic space, the scheme-as-space definition, flat/local-finite-presentation in the etale definition, and the fppf-site definition. Those statements really imply the descent assertion; limits-sectionwise is used only for finite kernel pairs. Step 2 uses the scheme coproduct's open disjoint summands, the representable diagonal of H, and etale locality on the source after base change to each scheme T. Thus the locality theorem has a scheme target T, as required. Yoneda supplies the map from the glued section. The index set is small relative to the explicitly enlarged bound, and the coproduct's existence within the ambient site is an assumption of the item, not an unstated closure property of the original skeleton.

Step 3 uses chartwise permanence to ensure every test map into the scheme W is etale. Only then does 04HV apply to the equality subsheaf on W_et. Step 4 constructs the actual reflexivity/symmetry/transitivity scheme maps using Yoneda on etale scheme objects; their identities consequently hold on arbitrary B-scheme tests. This avoids checking an equivalence relation only on the small site. The kernel-pair coequalizer node applies to the epimorphism explicitly proved in Step 2.

Step 5 checks each hypothesis of the quotient node: R and P are schemes, R maps monomorphically into P times_B P, both projections are etale, and its point functor is an equivalence relation. Its statement gives the algebraic space, etale surjective atlas, kernel pair and universal property needed here. The atlas-detection node's clause (3) accepts the scheme atlas P and a representable etale composite P to H; its conclusion is chartwise etaleness only. Step 6 obtains local lifts on a covering of each small-site object, proves epimorphy by cancellation using the sheaf axiom, and uses the quotient's stated kernel-pair identity and the effective-epimorphism coequalizer theorem. Nothing is taken only from a cited node's proof.

Step 7 explicitly proves subcanonicity on the enlarged site rather than silently assuming it: scheme atlases reduce a covering to etale scheme maps, these are fppf by their definitions, and descent on every scheme test defines the required morphism of fppf sheaves. The scheme-density node actually states the needed atlas existence/refinement and restriction equivalence. Step 8's three-line adjunction/Yoneda calculation uses the exact direct-image evaluation in enlarged-chart-ringed-morphism, not merely the definition of a geometric morphism. The enlarged-site model supplies its comparison with the specified small inverse images. This proves the formula also for nonrepresentable chartwise etale A.

Step 9 applies that formula to Q and c, evaluates at T/T and writes both directions of the fibre-product section bijection. The isomorphism commutes with arbitrary maps of test schemes by the actual Yoneda and inverse-image adjunction naturalities, so it identifies the presheaf E_H(F), not only its pointwise cardinalities. Step 10 repeats the canonical represented calculation for any V to obtain a presentation-independent counit, natural under every H-morphism of spaces. Step 11 uses the localization clause of the enlarged-site model, which actually identifies inverse image along etale u with restriction. The component formula proves naturality of the unit in restrictions and all sheaf maps. Both functors on arrows are the stated operations on maps/sections.

I checked empty sheaves and the empty base: the indexing coproduct and relation may be empty, their quotient is empty, and sections on the empty test scheme are the unique empty-cover gluing. The final sheaf gives H itself. For a non-quasi-compact or nonseparated etale space the atlas and quotient arguments use no finite cover, properness or separation assumption. A chartwise etale map need not be representable; only its scheme charts and the displayed atlas are tested as representable etale. All eleven steps are shorter than 2000 characters. General site and quotient inputs from other units are declared in split_report.tool_uses, with no change to the unit route.

## Not duplicates

No new node was created. The scheme-base realization node was read and distinguished above; its statement was not silently generalized.

## Unfinished

None in this stage-1 split. Delivery checks and the push are performed by the required delivery tool.
