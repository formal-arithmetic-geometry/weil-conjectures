## Worker report

Files written: `dag/nodes/sec-trace-formula/lem-trf-fitting-ideal-sheaf-pullback.json`, with a seven-step proof, unchanged statement and statement dependencies, filled split report and blueprint search. `citations.json` records all 20 step/node citations with verbatim statement quotations. There are no new nodes and no new Mathlib leaves.

Attachments: none. The search in `lean/WeilConjectures/` for the blueprint id and `Fitting|fitting` found only an unrelated occurrence of the word “fitting” in Blowup/QuasiAffineGeneralReduction.lean, not a declaration about Fitting ideals. No sorry declaration is treated as a completed proof.

WANTED: none.

The original item has a correct statement, but no proof. Its strongest obligation is attainment of the affine bounds by the largest quasi-coherent ideal. We prove this by constructing a candidate from the localization-compatible affine minor ideals and comparing inclusions, rather than assuming that a largest bounded ideal automatically attains every bound. There is no statement dispute or correction.

Nothing remains unfinished in this one-level split. Six generic off-unit proof tools are declared in `split_report.tool_uses` with their purposes. They supply affine module foundations and closed-subscheme base change, without changing the trace-formula unit route. The separate existing node `lem-trf-fitting-sheaf-arbitrary-pullback` overlaps the pullback clause, but not affine attainment or closed strata; we do not cite it to avoid making this proof merely an application of an overlapping theorem.

## Sources and searches

I read Divisors Tag 0C3C (`section-fitting-ideals`), including its principal-localization justification and alternative local-presentation construction; 0C3D (`lemma-base-change-fitting-ideal`), including its reduction to 07ZA(3); and 0C3I (`lemma-base-change-and-fitting-ideal-omega`), for the closed-subscheme interpretation. The last tag has differential-module hypotheses; our proof uses only the general closed-subscheme mechanism, not that lemma applied to an arbitrary module. I read More on Algebra 07ZA (`lemma-fitting-ideal-basics`), notably (3), Schemes 01I9 (`lemma-widetilde-pullback`) and 01IA (`lemma-quasi-coherent-affine`), Properties 01PB (`lemma-finite-type-module`), Modules 01BG (`lemma-pullback-quasi-coherent`), Morphisms 01QQ (`lemma-closed-immersion-bijection-ideals`), and Schemes 01JU (`lemma-fibre-product-immersion`). The existing independence/base-change node supplies the full kernel-row-minor theorem of 07Z8 and 07ZA(3).

The chapter and sk-i-curve-zero unit were read. The current main-20261015 ancestor `lem-trf-local-term-locality` was read; this is an auxiliary algebraic-geometric tool in its alteration branch, not a replacement of the chapter's contraction argument. `tools/blueprint_refs.py ancestor` confirmed the recorded ancestor. Whole-blueprint searches “Fitting”, “quasi-coherent”, and “closed subscheme” and DAG title/statement searches located the existing generic tools. “Fitting” has no imported counterpart, so `blueprint.same_as=[]` is retained.

All new Mathlib queries were run with msearch.py and logged in searches.jsonl. LeanFinder was tried with the pullback statement and a second phrasing about largest bounded ideals attaining the affine minors. LeanSearch returned ideal-sheaf infrastructure. Loogle queries `"fittingIdeal"` and `"Fitting"` returned no ideals or only Lie-module Fitting decompositions. The grep `Fitting|fittingIdeal` in AlgebraicGeometry returned none. I read Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean: ofIdeals is indeed the largest bounded family, and ofIdeals_ideal recovers an already compatible ideal family; those facts do not supply the module-minor compatibility needed for this complete item. No query is inferred from a search I did not run. The inherited searches are preserved; the current searches and their exact log records were appended.

## Not duplicates

No new nodes were created. The general affine-compatible-ideals gluing statement already exists as `lem-weil-pbc-affine-ideals-closed-subscheme`, and the two general closed-subscheme base-change tools already exist; none was copied into a new lemma. All citations are to existing nodes whose statements I opened.

## Review by Q125

I checked the item against 0C3C/0C3D hypothesis by hypothesis: finite type and quasi-coherence suffice, the index is nonnegative, there is no finite-presentation or flatness requirement, and arbitrary kernels are allowed in the finite generating surjections. No new statement-only nodes need source or definition audits.

Step 1 cites the affine finite-type criterion precisely for finite generation of F(U), the independence node precisely for equality of the presentation ideals, and the definition precisely for its sum over those ideals. Nonemptiness of that family is established before identifying the sum with a single ideal. The case n <= r uses the convention actually in the cited statement.

Step 2 uses parts (2)--(3) of the affine tilde/gamma adjunction and the associated-module principal-open section formula to identify F(U_f) with F(U)_f. This makes the independence node's last sentence applicable, so the affine-ideals gluing statement has exactly its principal-open compatibility hypothesis. Its clause (0) supplies affineness and the ring localization. Arbitrary affine intersections are never assumed affine.

Step 3 uses the gluing node's assertion of a closed immersion with exactly those ideal sections. The ideal-sheaf definition explicitly says its ideal is quasi-coherent and restricts to the associated ideal module. That supplies a candidate in the largest-ideal definition. The two inclusions are then proved: maximality gives one, and affine-local membership and sheaf gluing give the other. The quotient affine model is a conclusion of the gluing node itself, not something borrowed from its proof.

Step 4 uses the pullback-quasi-coherence statement for precisely that property, the affine pullback comparison for its canonical tensor section isomorphism, and the affine finite-type criterion to conclude finite type on a cover and globally. Finite generation of the tensor product is written explicitly as an expansion of pure tensors; no kernel finiteness or preservation of injections is invoked.

Step 5 uses the ring base-change clause (2) of the independence node and the affine comparison. Its module is finite by step 1. The module isomorphism does not alter a presentation's kernel, so using the formula through that isomorphism requires no unquoted Fitting invariance theorem. Reapplying the construction of steps 1--3 is legitimate because step 4 has verified both sheaf hypotheses on T.

Step 6 uses the base-changed-closed-subscheme node for closedness and exactly the image ideal stated there, and the affine comap-extension node for its affine sections. Thus equality on the affine cover proves equality of the subsheaves. The equality with the inverse-image-generated ideal is checked using the tensor construction in the pullback definition, by local finite sums. I deliberately use the image, without assuming the pullback map of the ideal is injective. The existing product-image lemma is not needed, and is not cited.

Step 7 uses both directions of the closed-immersion factorization/ideal-inclusion node. The inverse and uniqueness argument uses only injectivity of the topological inclusion and surjectivity of the structure-sheaf quotient in the cited closed-immersion definition: these force a map into the immersion over T to be unique. The morphisms respect the given closed immersions because the factorization node states that equation.

Small cases checked: the empty scheme/zero ring; F=0 (all nonnegative Fitting ideals are the unit ideal and the closed subscheme is empty); a finite free module of rank n (ideal zero for r<n, unit for r>=n); and a nonflat quotient base change. For example A=Z, F=Z/2 and B=Z/2 at r=0 give ideal (2) upstairs and zero downstairs, so the pullback closed stratum is all of Spec B, as required. The map (2) tensor B -> B is zero with nonzero source, confirming why an injectivity assertion would be wrong. None of these cases forces a hypothesis change.

I checked B--E against the actual proof and opened sources: no new elementary or duplicate nodes, no clauses moved into new nodes, all non-elementary tools have statement citations, all quoted node statements give the asserted inputs, and all proof steps are under 1000 characters. The statement, original provenance, existing searches and blueprint ancestry are retained. The repair made during self-review was to use the explicit general gluing node for affine attainment instead of treating attainment as part of the Fitting definition; the closed-subscheme base-change node replaces an unnecessary tensor-exactness argument.
