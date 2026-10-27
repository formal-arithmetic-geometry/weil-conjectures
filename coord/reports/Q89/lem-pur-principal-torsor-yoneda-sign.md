# Q89 stage-1 report: lem-pur-principal-torsor-yoneda-sign

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-principal-torsor-yoneda-sign.json: statement, split into seven proof steps; no complete Mathlib match.
- citations.json: one verbatim statement quotation for each step/node citation.
- report.md, searches.jsonl and write_split.py: sandbox research and delivery records.

New nodes: 0. New Mathlib leaves: 0. The item statement, its statement dependencies, chapter, unit and provenance are unchanged. Its existing searches are retained and the actual Q89 searches appended. No unit realization is changed: this is a subsidiary node, not the unit's key statement.

## Attachments

None. I searched lean/WeilConjectures by the exact item id, principal-torsor and relative-torsor terminology, and Yoneda-sign terms. There is no project declaration stating all of this item. Mathlib's generic Ext connecting and injective-resolution statements are tools, not an attachment of the framed relative assertion.

## WANTED

None. Every source used is already in literature/.

## Findings and corrections

There was no prior sandbox split, report, or search log. The live node was unsplit, created by Q108 for the already reviewed divisor-class split; no repair note exists for this item. I preserved the statement and its accepted negative normalization. The blueprint ancestor's original clause (a) uses a positive frame boundary; the live ancestor's reviewed correction and this item's statement explicitly use the negative Yoneda normalization. I do not reopen that settled ancestor statement.

The item is not a restatement of lem-pur-divisor-torsor-boundary-signs: that node gives raw signed-cone representatives and a double-boundary identity. It does not identify the actual relative supported extension with the inverse-section pushout or with that cone class. Steps 1–4 supply that identification, including the explicit cochain homotopy. No new node is required. I do not cite lem-per-supported-yoneda-localization, which the ancestor review explicitly forbids as a dropped route node.

The potentially misleading sign is made explicit: for 0 -> G -> E -> Q -> 0 and h:E -> I^0 extending G -> I^0, factor dh as c b. In the project's cone triangle with boundary -p, the extension class is represented by -c, not +c. The homotopy with component -h proves that assertion directly. For u=hF(e), restriction is -g and du=cp(1); thus (-du,0)+D(u)=(0,-g). The coefficient connecting of this representative is (0,dr), the negative of the localization representative (0,-dr). This proves the sign in the stated splice.

## Not duplicates

No new nodes. Whole-DAG searches for Tags 03AJ and 06XU and torsor/Yoneda/Ext concepts, and blueprint_refs searches for torsor, relative and Yoneda, found the existing relative torsor, supported-Hom, raw-boundary, injective-resolution and Ext-comparison statements reused here. The blueprint ancestor is lem-pur-divisor-class; no blueprint node states the full arbitrary-abelian-sheaf framed principal-torsor assertion in another form, so same_as remains [].

## Review by Q89

I read coord/delivery-errors.md B–E in full, the item and ancestor's statement/proof and reviewer normalization note, the chapter/unit route, the statement of every cited node, and the local Stacks source. For the item I read sites-cohomology.tex lemma-torsors-h1 (03AJ), its free-sheaf/pushout construction and lifting-torsor argument, and derived.tex definition-cone (014E), lemma-functorial-cone (014F), lemma-derived-canonical-delta-functor (0152), lemma-compute-ext-resolutions (06XR), and the Yoneda-class roof and classification around lemma-yoneda-extension (06XU). I read homology.tex section-extensions (010I) at the pushout paragraph; etale-cohomology.tex lemma-ses-associated-to-open (095L); sites-modules.tex lemma-extension-by-zero (03DI); and the compatible-injective-resolution statement (013T). This is an agent-written relative refinement, so proof_origin.by is agent, not a claim that Stacks states the full refinement. No SGA source is used.

Step 1 uses the open-closed node for exactly its displayed short exact sequence, the extension-by-zero adjunction for Hom(j_!Z,-)=sections on W, and the pushout-short-exact node for its cokernel construction and exactness. The remaining Hom(Z,-)=sections assertion is the explicit generator calculation, not an uncited general Yoneda theorem. These hold for arbitrary schemes and arbitrary abelian etale sheaves; no finite type, regularity, invertibility or coefficient-module hypothesis is added.

Step 2 uses the relative-torsor-extension node's uniqueness, after checking its hypotheses: the exact row and its additive Hom/section identification are established in Step 1, and the image of t corresponds to one. The actual map [a,1] is equivariant, lies over supported one and sends the specified s to zero because [-g,-1] is a relation. The map on each fibre is a bijection, being equivariant for the identity on G. This is a few-line application, not a new torsor lemma.

Step 3 uses enough injectives for the abelian sheaf category, the definition of injectivity to extend along G -> E, the cone/shift convention to write the extension roof, and Ext-via-injective-resolution to read its cocycle. I checked the homotopy in both degrees: (-h)a=-epsilon and d_{I[1]}(-h)=dh. The proof does not infer the sign from a forgotten-support class, which would lose the relative datum.

Step 4 uses the supported-Hom isomorphism only for the Hom/cone comparison; its statement is supplemented by the item's specified normalization z -> (zp,0). The divisor-relative-cone node supplies the kernel inclusion and its quasi-isomorphism to the signed cone, and the raw-boundary node supplies alpha_g=(0,g). The explicit coboundary calculation gives the comparison for this extension, rather than citing a theorem about ordinary torsor H^1 as though it classified the relative extension.

Step 5 uses compatible injective resolutions, including their optional degreewise biproduct splitting. Thus Hom(Q,-), sections on both T and W, and their signed relative complexes all preserve these particular short exact rows, without assuming general exactness of sections or of Hom. The long-exact-naturality node says exactly that a commuting morphism of short exact complex sequences commutes with connecting maps. The Ext-resolution-derived-connecting node identifies the coefficient connecting morphism with postcomposition by k[1]; it applies in the abelian sheaf category with enough injectives, not just to O-modules. This justifies the Yoneda comparison rather than hiding it in a phrase about naturality.

Step 6 uses the raw-boundary node's actual statement delta(alpha_g)=partial(delta_W(g)), its lift/dr representatives, and the divisor-relative-cone node's identification with derived kernel-of-restriction support. Negation is explicit. Step 7 uses the uniqueness of the specified relative extension and the naturality clauses of those two existing comparison/boundary statements. Componentwise maps send the actual relation [-g,-1] to its image; no assertion about arbitrary base change of direct images is needed. Etale restriction is the requested scope.

I checked every citation against its statement (C4) and placed its verbatim statement in citations.json. No proof-internal assertion is used as a black box. All non-elementary inputs are cited (C1). Generic tools outside the affine-line unit are declared in split_report.tool_uses, with the reason that this subsidiary calculation needs general abelian extension/resolution/adjunction tools; the affine-line unit's geometric route is unchanged. The dependency closure has no path back to this item.

I tested W empty, W=T (and hence Q=0), g=0, a split coefficient sequence, the zero group sheaf, and a g that extends globally. In the last case (0,-g) is a relative coboundary, as the relative extension must be; the pushout splits via the global extension of -g. W=T makes every relative group zero. None of the steps divides by 2, so characteristic-two coefficients satisfy the same signed formulas. Nonreduced closed immersions require no reducedness assumption: the open-closed sequence is on the etale site. For G_m, additive negation is inversion, so the first map is the inverse unit exactly as stated.

B: no new node to be self-contained or searched; item retained with full TeX and provenance, actual searches recorded, no false Mathlib leaf. C: cited statements opened, every substantive input named, no cycle, off-unit generic tools declared. D: actual pushout and homotopy calculations remain in the item, with no relabelled clause node. E: hypotheses, objects, signs and restriction naturality checked as above. All seven steps are under 2000 characters; none hides a long standalone lemma.

## Unfinished work

None in stage 1. No Lean file was written, no compiler/Lake/build tool was run, and the repository and launcher files were read only. Required server dry run and final push are performed after this report is written.
