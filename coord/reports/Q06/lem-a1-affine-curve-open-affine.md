# Q06: lem-a1-affine-curve-open-affine

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-affine-curve-open-affine.json`: item, statement, split. The statement is unchanged. Seven proof steps realize Stacks 09N9 with its local-ring and compactness hypotheses checked.
- `dag/nodes/sec-deligne-laumon-a1/lem-a1-open-dimension-one-higher-image-vanishing.json`: one new statement-only unsplit node, Stacks 09N8. Mathlib verdict: no match after LeanFinder, LeanSearch, Loogle and source grep, including a second semantic phrasing.
- `citations.json`: one entry for each of the fifteen step/node citations, quoting the cited statement verbatim.
- `report.md`: this report. `searches.jsonl` is maintained by the authorized search command.

New nodes: 1. New Mathlib leaves: 0. No unit or chapter record is changed: this item is a tool beneath the endpoints unit's key node, not the key node itself.

## Attachments

None. Read-only searches of `WeilConjectures/` for the exact blueprint tag returned no declaration. Concept searches found smooth proper-curve open affineness in `AlgebraicGeometry/Curve/Compactification.lean`, `IsConnectedCurve.isAffine_of_ne_top`, and existence of an affine open with finite complement in `Curve/HighDegreeVanishing.lean`. Neither proves every open of an arbitrary Noetherian affine scheme of dimension at most one affine. In particular the proper smooth connected curve theorem cannot be attached to this item, and the existence theorem gives only some affine open. Searches for retrocompactness and one-dimensional Noetherian direct images found no project proof of the new node. Master-source sorry declarations were not treated as proofs.

## WANTED

None. All sources used are present in `literature/stacks-project/`.

## Corrections and scope

The imported statement already correctly specializes Stacks Tag 09N9; there is no statement dispute and no hypothesis was changed. The import had no proof. The split supplies the missing proof, retaining the original source, creation record, unit, chapter and blueprint ancestry, and retaining all prior Mathlib searches. The new node has exact local-ring hypotheses of Tag 09N8 rather than silently replacing them by global dimension or smoothness. Step 2 proves that the stalks are Noetherian, and Step 3 separately verifies their dimension bound.

The existing `lem-sc-affine-noetherian-underlying-space` source metadata points to a topology lemma rather than the precise affine result. Its *statement* is exactly the fact needed here and its Mathlib match is `AlgebraicGeometry.noetherianSpace_of_isAffine`; I read Algebra Tag 00FQ, `lemma-Noetherian-topology`, for the source of the application. I did not edit that other node.

The endpoints unit is `sk-l-dl-a1-endpoints`, whose chapter and unit records were read. The current blueprint proof `literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-l-dl-a1-endpoints/lem-a1-middle-extension-endpoints.proof.md`, opening paragraph, expressly needs affineness of the open curve after removing finitely many closed points. The split supplies this assertion via the exact Stacks source already recorded on the item. The current blueprint/unit route is unchanged.

## Not duplicates

`lem-a1-open-dimension-one-higher-image-vanishing` vs `lem-a1-affine-curve-open-affine`: the new node concludes vanishing of higher *module direct images* on a general scheme whose local rings satisfy a dimension bound. It neither assumes an affine ambient scheme nor concludes affineness. The item still proves its conclusion through quasi-coherent pushforward, affine cohomology vanishing, Leray and the cohomological affineness criterion. Thus the new node is an actual input of the source proof, not a renamed clause of the item.

`lem-a1-open-dimension-one-higher-image-vanishing` vs `lem-pc-affine-morphism-hi`: the latter assumes the morphism is affine; invoking it here would require first proving the item. The new node uses retrocompactness and conditions on local rings of the target, with no affine-morphism hypothesis.

`lem-a1-open-dimension-one-higher-image-vanishing` vs `lem-sc-open-curve-gm-direct-image-cohomology`: the latter concerns etale cohomology of the units sheaf on curves. The new result concerns Zariski quasi-coherent structure-sheaf modules, without a field or smoothness assumption. These coefficient categories and conclusions are different.

The exact tag/label search for 09N8 and `lemma-affine` in its varieties context found no existing statement of the new node. Whole-DAG searches by higher direct images, retrocompact opens and Noetherian local rings, and whole-blueprint searches with `tools/blueprint_refs.py search` for `09N8`, `retrocompact`, `Noetherian local rings`, `higher direct images` and `quasi-coherent`, found no duplicate. Existing pushforward, affine vanishing, Serre, stalk dimension, affine-stalk localization, Noetherian topology and compactness nodes were reused. `blueprint_refs.py ancestor` gives `lem-a1-middle-extension-endpoints`; the new node records that ancestor and the intermediate item in `via`.

## Review by Q06

I read the full statement and proof of Varieties Tag 09N9 (`lemma-open-in-affine-curve-affine`, lines 7773–7794), and the preceding Tag 09N8 (`lemma-affine`, lines 7747–7770). The item keeps precisely its original Noetherian affine specialization of 09N9, with topological dimension at most one, and includes the empty open. The only new node is exactly 09N8: every local ring is Noetherian of ring dimension at most one; the open is retrocompact; the coefficients are arbitrary quasi-coherent modules; every positive higher direct image is zero. I checked its full local-ring hypotheses, not merely those of the intended smooth-curve application. Its statement introduces X, U, j, F and p, defines retrocompactness inline, and cites definition nodes for its rings, dimension, stalks, module cohomology and open immersion. It contains no proof or hidden proof sketch, and has no proof dependencies. Its source place names the exact Stacks tag and TeX label.

For Step 1 I opened `lem-sc-affine-noetherian-underlying-space` and `lem-sfb-noetherian-space-compact-subsets`. Their statements respectively give Noetherianity of the topology from the Noetherian ring of global sections and compactness of **every** subset. Thus they cover U and every intersection U with an open V, not just X. This proves both compactness of U and retrocompactness of the inclusion. I also opened the definitions of quasi-compact morphism, quasi-separated morphism and open immersion. The step verifies quasi-separatedness directly: the fibre product of an open inclusion with itself is U, its diagonal is the identity under that identification, and inverse images by an isomorphism preserve compactness. No assertion that arbitrary intersections of affine opens are affine is used. I read Algebra 00FQ and Topology 04ZA for these source hypotheses.

For Step 2 I opened `lem-weil-pbc-spec-domain-stalks-function-field`. Its **first** clause applies to an arbitrary commutative ring and identifies every prime stalk with the prime localization. The domain assumption belongs only to clause (2), which is not used. The citation quotes only clause (1). I opened the Noetherian-ring and prime-localization definitions and read Algebra 00FN (`lemma-Noetherian-permanence`), first proof sentence. The step writes out the entire needed elementary argument: contract an ideal J, choose finite generators in A, and multiply each fraction in J by its invertible denominator to obtain the required linear combination. Thus no uncited localization permanence theorem is assumed and no redundant elementary new node is introduced.

For Step 3 I opened `lem-sc-scheme-stalk-dimension-generalization-chains` and the topological Krull dimension definition. The former explicitly states the codimension formulation in terms of irreducible closed chains beginning at the closure of x, so its statement really gives the formula this step uses. The chains are a subset of all chains defining dim X. Taking the supremum proves the required local bound immediately. I read Properties 02IZ (`lemma-codimension-local-ring`) to check that this comparison is valid for arbitrary schemes, without a finite-type field hypothesis.

Step 4 applies exactly the new node's statement. Step 1 supplies retrocompactness, Step 2 supplies Noetherianity of every local ring, and Step 3 supplies ring dimension at most one. F is an arbitrary quasi-coherent O_U-module. The new node says R^q j_* F=0 for all positive q, which is exactly what this step takes from it. It does not infer this from a definition of direct image.

For Step 5 I opened the full statements of `pqf-lem-pushforward-qcoh` and `pqf-lem-affine-vanishing`, and read Schemes 01LC (`lemma-push-forward-quasi-coherent`) and Cohomology of Schemes 01XB (`lemma-quasi-coherent-affine-cohomology-zero`). Step 1 has supplied both morphism hypotheses of 01LC, so j_*F is quasi-coherent; 01XB is then applied on the affine scheme X to this actual module. This is the Zariski module theorem, with no coefficient-category change to etale sheaves.

For Step 6 I opened `lem-pc-m1-leray-acyclic-pushforward-linear-comparison`, whose statement gives the needed cohomology comparison for arbitrary scheme maps and any module whose positive higher direct images vanish. The auxiliary map is the identity of X; this avoids any extraneous structure or base-ring hypothesis. The needed vanishing is precisely Step 4. I read Cohomology 01F4 (`lemma-apply-Leray`), part (1), which states this same comparison. Step 5 then gives the claimed zero cohomology on U.

For Step 7 I opened `lem-pqf-quasicompact-h1-zero` and read Cohomology of Schemes 01XF (`lemma-quasi-compact-h1-zero-covering`). Its hypotheses are compactness and vanishing of H^1 for all quasi-coherent ideals, exactly as proved in Steps 1 and 6. Taking F to be each ideal is legitimate because all quasi-coherent modules were allowed in Step 4. The cited node does not require separatedness, finite generation of the ideals, or nonemptiness.

I tested the item and the new statement on U empty, U=X, X empty (A the zero ring), dimension-zero Artinian rings including nonreduced ones, a DVR with its punctured open, and a reducible Noetherian affine curve such as Spec(k[x,y]/(xy)). The local-dimension comparison allows both zero- and one-dimensional stalks. Zero modules on the empty open satisfy the vanishing statement, and the empty scheme is affine as Spec of the zero ring. Nilpotents and multiple branches are allowed throughout, so none of these checks forces a missing reduction, normality or irreducibility assumption. The bound cannot simply be dropped: the punctured affine plane has nonzero higher direct image of its structure sheaf, consistent with the dimension hypothesis of 09N8.

I checked delivery-errors B–E against the actual files: self-contained statement-only child, correct sources and definitions, genuine logged searches with actual hits, no proposed attachment based only on a docstring, all non-elementary inputs cited by nodes whose statements say them, no source-proof content borrowed from a cited node, and no restatement of the item's conclusion moved into a child. The elementary localization calculation and chain-supremum comparison are written out rather than hidden in new nodes. Each proof step is under 600 characters, so none exceeds the 2000-character long-step review threshold. The new node's blueprint reference has the ancestor, exact purpose and intermediate-item list. Every quote in citations.json was checked as a literal substring of its cited statement. The server `review_split` check passed before this report was written. The independent maintainer review remains part of the normal delivery process.

## Unfinished work

No required part of this one-level split is left unfinished. The one unsplit new node is intentionally statement-only for the next stage-1 item. No Lean file was written and no compiler, Lake or build tool was run. The final required validation is the server dry run of the delivery tool, followed by direct push when it succeeds.
