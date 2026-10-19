# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-symmetric-family-block-restriction.json`: existing item split in place; no new nodes.
- `citations.json`: verbatim statement quotations for all cited nodes in all eight proof steps.
- `searches.jsonl`: recorded LeanSearch, Loogle, LeanFinder and Mathlib grep queries run on 2026-10-17.

## Attachments

No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` states this item. A repository-wide search for the blueprint tag and the operative phrases found no declaration to attach.

## WANTED

- An archived copy of Lurie's *Higher Algebra* (September 18, 2017), Theorem 3.1.2.3, proof step (1), pp. 336–337, for the operadic block-restriction argument. The online PDF was read at the cited place; it is not stored under `literature/`.
- An archived proof/source for the coherent partial universal-arrow criterion used in `lem-coef-parametric-universal-arrows` (Kerodon tag 03NQ / Proposition 8.3.4.1 and its dual). The existing node records this as agent-formulated and the online source was checked.

## What was checked and changed

The item statement was compared with the current node and with the blueprint route in `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`. It introduces the symmetric operadic family, the parameter-zero active incoming slices, an active arrow over a pointed map, its inert output projections and chosen inert lifts, and the induced functor to the product of block slices, including coherent choices, empty blocks, and the case `s=0`. No statement change was needed.

The proof is eight steps. Step 1 uses the definition of the active wide subcategory, the right-fibration slice construction, its arrow-model equivalence, and the enhanced cone mapping-space formula. I checked each cited statement: they provide the quasicategorical slices, the source projection, the equivalence to fixed-target arrows, and the mapping-space/triangle description. The pointed-map calculation showing that a triangle between active arrows has an active source map is written out in the step.

Step 2 uses the relative-slice sections node and the slice-arrow equivalence. Their statements explicitly provide coherent postcomposition transport along `b -> b_j`, including higher simplices, and identify that construction with the arrow slices. Step 3 is elementary from the symmetric operadic-family definition: the maps `rho_{D_j}` and `gamma_j` are written explicitly, their composite equality is checked, and the restriction map on a triangle is given. It covers `D_j = empty`.

Step 4 uses the family inert-active factorization and the cocartesian mapping criterion. The former states stationary inert/active factorization with its composition homotopy; the latter states the mapping-space homotopy-pullback criterion for a cocartesian edge. I verified that the family projection is an inner fibration, that the selected inert lift is stationary in the parameter-zero fibre, and that the criterion supplies the active factor and its triangle. Step 5 uses the exact orthogonality mapping-space equivalence from the factorization node, the cone/slice mapping formula, and the slice-arrow equivalence. Taking the specified homotopy fibre gives precisely the universal-arrow mapping-space equivalence, with the unit triangle and naturality in the active target written explicitly.

Step 6 uses the opposite partial-left-adjoint assertion of `lem-coef-parametric-universal-arrows`; its statement says universal arrows assemble coherently, with a contractible choice space and compatibility for all coherent diagrams. I checked that the inclusion `J_{b_j} -> C_{b_j}` is the functor to which the criterion is applied and that Step 5 supplies its hypothesis for every object. Step 7 uses the stated inert-active orthogonality and the coherent diagram clause of the universal-arrow node to construct the block fillers for slice edges and all higher simplices; it spells out the square and the composite commutation homotopy. Step 8 collects the block functors and checks the zero-arity cases, including the unique map to the empty product.

I read the full statement of every cited node and put the exact sentence or displayed formula used in `citations.json`; every `uses` entry is present in `proof_deps`. Existing DAG and blueprint searches found no duplicate node for this block-restriction statement. The Mathlib searches were rerun and retained in `mathlib_searches`: ordinary category/slice and strict-Segal declarations were inspected, but none states symmetric infinity-operadic families or this active block-slice functor, so the item remains a non-Mathlib statement. No Lean declaration or compiler was used, per the stage-1 restriction.

## Review by Q111

I reviewed the item against the HA proof place and the imported blueprint proof, then opened each statement named in every proof step. The citations are substantive: the slice nodes say what Steps 1–2 use; the inert-active node says both factorization and the mapping-space orthogonality used in Steps 4, 5, and 7; the cocartesian criterion says the homotopy-pullback test used in Step 4; and the parametric universal-arrow node says exactly the coherent reflector, contractible choice space, and higher-diagram compatibility used in Steps 6–7. The only elementary steps are 3 and 8, whose pointed-set equations and empty cases are written directly from the family definition.

I checked the hypotheses at each use: smallness and the fixed universe in the slice construction; repleteness and parameter-zero source fibre in Steps 1–2; stationarity and cocartesianness of the chosen inert lifts in Step 4; inner-fibration hypotheses for the cocartesian criterion; full-subcategory hypotheses for the universal-arrow application; and all higher simplex compatibility through the coherent-diagram clause. I tested the edge cases of an empty block, an arrow to `〈0〉` (forcing zero inputs), and `s=0`; the formulas remain defined and the target product is the terminal empty product. The review found no missing hypothesis or duplicated node. On resumption I corrected Step 1 to call the overcategory formula the cone mapping-space formula (its displayed orientation already was correct), and replaced the short duality quotations in citations.json with the actual cone mapping-space formula used in Steps 1 and 5. I reread HA Theorem 3.1.2.3, proof (1), especially the output-product comparison on printed p.337, and Kerodon Proposition 8.3.4.1; the proof remains an agent expansion of that comparison, using the existing parametric node for its coherent-diagram assertion. All eight steps are under 1100 characters; none crosses the 2000-character long-step threshold. The retained statement equals the current repository statement, and the current source search again found no project declaration to attach.
