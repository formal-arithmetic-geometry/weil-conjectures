# Stage-1 delivery: lem-trf-locally-principal-supported-kernel

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-locally-principal-supported-kernel.json`: statement, split; no Mathlib match for the whole assertion. Six proof steps, using existing nodes only.
- `citations.json`: verbatim statement excerpts for every citation of every proof step.
- `searches.jsonl`: actual searches run through msearch.py; the earlier searches in the live item are retained.

No new nodes and no new Mathlib leaves. The unchanged statement introduces local principality explicitly; no Cartier or regularity assumption is added. Its chapter, unit, blueprint ancestor, provenance, and prior search records are retained. `same_as` remains empty after searching the whole blueprint.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint id, locally principal ideals, and supported kernels. `Scheme.IdealSheafData.IsLocallyPrincipal.comap` in `WeilConjectures/Mathlib/AlgebraicGeometry/IdealSheaf/Invertible.lean:146` proves only the local-principality clause. The supported-section definitions in `Topology/Sheaves/GrothendieckVanishing.lean` concern abelian sheaves and do not give the quasicoherence and scheme-complement assertions. Neither is an attachment for the item.

## WANTED

None. All mathematical sources used here are present in `literature/stacks-project/`.

## Existing material and corrections

The item was unsplit; there was no earlier split or report in its sandbox and no repair note for this item. No mathematical error or statement dispute was found. The import's no-flatness qualification is essential: the base-change ideal is an image ideal, not an asserted injective pullback of the original ideal. I made this distinction explicit in Step 1. I did not replace locally principal closed subschemes by effective Cartier divisors.

I searched the DAG for Tags 07ZT and 07ZP, the pullback/complement labels, and the relevant notions; I also searched the entire blueprint using blueprint_refs.py for locally principal, supported, principal open, quasi-compact locality, and closed-subscheme base change. The generic supported-section theorem already exists as `lem-trf-supported-sections-quasi-coherent`, and the generic base-change ideal formula exists as `lem-pc-closed-subscheme-base-change-ideal-image`. I reused them. The other blueprint matches concern zero schemes of sections, relative Cartier conditions, or unrelated support/trace statements, and do not state this item.

The only off-route non-leaf tool requested in `split_report.tool_uses` is `lem-pc-closed-subscheme-base-change-ideal-image`: its general image-ideal formula is precisely the algebra needed to expand the omitted proof of 053P. This does not change the finite-after-blowup/strict-transform route below the blueprint ancestor `lem-trf-local-term-locality`. The item is not its unit's key node, so no unit realization fields are changed.

## Mathlib searches

I ran leanfinder, leansearch, loogle, and a grep through msearch.py, then a second semantic phrasing specifically about vanishing on a retrocompact open. All services returned normally. The returned `SheafOfModules.IsQuasicoherent` constructors and presentation-data declarations define or construct quasicoherence; they do not prove it for supported subsheaves. `Scheme.Hom.support_ker` and `Scheme.ker_morphismRestrict_ideal` concern ideal sheaves of morphisms of schemes, not an arbitrary module H. `exists_of_res_zero_of_qcqs` concerns structure-sheaf sections on a qcqs open, and does not identify our module kernel. The searched Mathlib subdirectory had no locally-principal or quasicoherent-module-kernel matches. The exact queries and actual hits are retained in the node and the search log. No new search was invented to fill a schema field.

## Review by Q20

I read Divisors Tag 053P (`lemma-pullback-locally-principal`), which states arbitrary pullback and omits its proof, and 07ZT (`lemma-complement-locally-principal-closed-subscheme`), whose proof passes to Spec A with complement D(f). I read Properties 07ZP (`lemma-sections-supported-on-closed-subset`), in particular its exact sectionwise sequence and proof of (3). These agree with the unchanged item, including arbitrary quasi-coherent H and nonregular local equations. I also read Schemes 01JU, 01L4, 01L7 and the separated/quasi-separated paragraph, Algebra 00E4 and the compactness statements, Spaces Morphisms 03KG(6), and Sheaves 0095 for ordinary module pushforward. There are no new-node statements or sources to audit.

For Step 1 I opened `lem-pc-closed-subscheme-base-change-ideal-image`: its statement supplies both that D is closed and exactly the image ideal Im(q^* I_E -> O_Y). I opened `def-pc-module-pullback`: its tensor formula is what sends a tensor a ⊗ cf to acb on a chart where I_E=(f). Both contain exactly the cited formulas. The additional citation `lem-weil-pbc-affine-opens-basis` states that every open neighbourhood contains an affine neighbourhood of its given point, and supplies W inside q^{-1}U; I checked its Schemes source 01IT (`lemma-basis-affine-opens`). The image contains b and is contained in (b); no assertion about left exactness of q^*, faithful flatness, or a nonzerodivisor is used.

For Step 2 I checked both clauses of `lem-weil-pbc-spec-localization-away-basic-open`: a basic-open basis and the homeomorphism Spec B_c -> D(c). `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact` supplies compactness of every spectrum. These give compactness of D(c). To avoid silently assuming that local equations trivialize on every affine open globally, the step takes an arbitrary affine A inside a chosen equation chart, covers it by finitely many basic opens, and writes its intersection with D(b) as the finite union of D(bc_i). `def-weil-finite-type-morphism` gives precisely the affine-preimage definition of quasi-compact morphism. `lem-pc-quasi-compact-local-on-target` then applies to the equation-chart cover, proving global quasi-compactness and thus exactly the retrocompactness required later. Neither the cover nor Y itself is assumed quasi-compact or quasi-separated.

For Step 3 I opened all three statements: `lem-weil-pbc-open-immersion-monomorphism` gives monomorphism, `lem-trf-scheme-monomorphism-separated` gives separatedness for an arbitrary scheme monomorphism, and `lem-pc-separated-quasi-separated` gives the desired relative quasi-separatedness. No finite-type condition occurs in any of them.

For Step 4 the only cited statement, `def-weil-sheaf-of-modules-category`, explicitly gives sectionwise kernels. I wrote the ordinary pushforward and its action out directly, and explained why the formula is a sheaf and why the restriction map is linear. Thus this is an elementary construction from sheaf gluing and the cited sectionwise-kernel rule, not a purported theorem about pushforward extracted from the module-pullback definition. For Step 5 I opened `lem-trf-supported-sections-quasi-coherent`: it defines exactly our K(W) and explicitly asserts its quasicoherence under retrocompactness. Step 2 discharges that hypothesis, and the closedness supplied in Step 1 discharges its closed-subset hypothesis. I use its statement, not its unsplit proof. For Step 6 the zero-germ equivalence is written using open neighbourhoods and sheaf uniqueness; it makes no claim about commuting stalks with internal Hom or arbitrary limits.

I checked delivery-errors B through E: no new node carries a hidden proof, restates a clause, duplicates an existing node, or needs unrecorded searches; all notions in the unchanged statement retain their definition dependencies. All substantive facts used in the proof have explicit node citations with literal quotations. No step uses a source tag in place of a missing non-elementary dependency. All six steps are below 2000 characters; the local computation, finite-union argument, gluing, and germs contain their actual arguments rather than an omitted comparison lemma.

The edge cases are E empty (V=Y, K=0), E=T (V empty, K=H), H=0, and Y empty. They all give the asserted kernels and morphism properties. For a nonflat example take q:Spec k -> Spec k[t] at t=0 and E=V(t); its equation pulls back to zero, and the tensor-image calculation gives D=Y and K=H. For a zero-divisor equation take Y=T=Spec k[e]/(e^2), q=id and E=V(e); again V is empty topologically and K=H. These cases confirm why no effective-Cartier assumption may be inserted. No corrections to existing other nodes or project files were necessary.

## Unfinished work

None within this one-level split. Existing cited unsplit nodes remain their own future items; this delivery neither changes their statements nor claims their proofs are completed. The first server dry run passed at f677a9b0e98. A final citation audit then added the existing Mathlib affine-open basis leaf to Step 1, making the affine-neighbourhood choice explicit; the final dry run and push follow this update.
