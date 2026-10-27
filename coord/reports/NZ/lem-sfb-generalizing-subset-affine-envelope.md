# NZ stage-1 delivery: lem-sfb-generalizing-subset-affine-envelope

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-generalizing-subset-affine-envelope.json`: statement, unchanged; replaced its empty imported proof with ten steps, status split. Mathlib searches do not identify the full statement with a declaration or a one-line specialization.
- No new nodes and no new Mathlib leaves. The split uses 25 existing nodes.
- `citations.json`: one entry for each step/node citation, quoting the corresponding existing node's statement verbatim.
- `searches.jsonl`: the search command's actual log, retained across the interruption. `write_split.py` is a sandbox-only helper for the item and citation file. No project source or launcher script was changed.

## Attachments

None. Searches of the live `lean/WeilConjectures/` by the blueprint tag and by generalizing/retrocompact subset, ringed-subspace and affine-envelope terminology did not find a project declaration proving all clauses without sorry. Mathlib's canonical map to Spec of global sections supplies some components, not the boundary criterion or the localization assertion for a possibly nonschematic induced ringed space. Nothing was compiled.

## Literature wanted

WANTED: Raynaud, *Un critère d'effectivité de descente*, Séminaire Samuel 1967–1968, exposé 5, §2 Propositions 2.3(ii)–(iii), 2.4(A),(B), Corollary 2.5 and the complement argument in Theorem 3.3, proof 4°, printed pp.4–8 and 13, for lem-sfb-generalizing-subset-affine-envelope. The inherited path `literature/raynaud-critere-effectivite-descente.pdf` is absent in this read clone. I read the primary Numdam scan online at https://www.numdam.org/article/SAC_1967-1968__2__A5_0.pdf; no PDF was downloaded. The inherited source's reference to `sandbox sources/raynaud.pdf` is provenance of the earlier node author, not a file created by NZ.

WANTED: the same Raynaud document, §1 Proposition 1.5(i), printed p.3, for the existing input lem-sfb-qc-flat-monomorphism-affine-neighbourhood. Its statement and the primary source were read; this delivery does not create or alter that node.

The proof is marked agent-written: the assembly uses the local Stacks sources and already-stated Raynaud input rather than pretending the missing archival PDF is available locally. No SGA source is used.

## Findings and corrections

There is no statement dispute. I retained the statement and all statement dependencies exactly. The original item had no proof. In particular the local comparison cannot be justified by saying that E is already a scheme: establishing schematicity is part of this item. The split first obtains the tensor formula for sections of an intersection of quasi-compact opens, then the affine-envelope base change, then the point-fibre and boundary-image equalities. Schematicity enters only afterwards.

During my citation audit I corrected a draft inference that attributed separatedness to lem-weil-pbc-affine-scheme-qcqs: its statement gives only quasi-compactness and quasi-separatedness. Final Step 3 instead proves quasi-compactness of the relevant inverse images by a finite principal-open cover. It uses only the precise basis, localization-prime and affine-open statements cited there. I also made the tensor/localization comparison explicit using the two universal properties, and obtained equality of boundary images through the localization embeddings, rather than assuming arbitrary set-theoretic images commute with base change.

The latest blueprint's direct-image proof, clause (3), is the motivating unit branch; the inherited chain through lem-sfb-integral-descent-flat-monomorphism-subset is retained. `blueprint_refs.py ancestor` returns null for this imported auxiliary lineage, so I retained the null ancestor and its full via chain, and filled the exact place. Whole-DAG searches for the relevant notions and tags, and whole-blueprint searches for generalizing, ringed subspace and proconstructible, located the existing generic inputs but no blueprint duplicate of this full statement. This item is not the unit key node, and no unit realization is changed.

Generic tool uses from other units are declared in `split_report.tool_uses`. In particular the two a1 intersection lemmas give an induced-ringed-space embedding and flat base change of its sections. They are not being used as descent or direct-image theorems. The same unit has no substitute statement for these generic tools. The spectral presentation and directed-limit lemmas are likewise topology tools. This preserves the existing Raynaud auxiliary route rather than replacing a unit proof step.

## Unfinished work

None within stage 1. Subsequent formalization is outside this delivery. The absent archival PDF is recorded above; the actual proof inputs and their sources were accessible. Server check results are recorded below when completed.

## Not duplicates

No new nodes. In particular I reused lem-a1-intersection-canonical-affine-embedding, lem-a1-intersection-sections-flat-base-change, lem-a1-qc-open-intersection-spectral-presentation and lem-sfb-qc-flat-monomorphism-affine-neighbourhood instead of creating specializations. The latter three assertions of this item (boundary criterion, affine equivalences and localization of the boundary image) are proved in its steps, not moved into new nodes.

## Mathlib search review

I retained the inherited search records and read the actual results of all NZ searches in searches.jsonl. Searches were run only through msearch.py. The queries include full statements and second phrasings for the generalizing retrocompact subset, the canonical affine envelope, and section base change; LeanFinder, Loogle, grep and LeanSearch were all tried. The hits concern spectral/generalization conditions, quasi-affineness, localizations, or the canonical map to Spec of global sections. They do not prove this full item. I did not declare a new leaf for any of these existing component facts. One Loogle query (`"IsLocalization" "toΓSpec"`) returned a pattern error, recorded in its raw result; I do not use that failed query as evidence of absence. Later concept searches and well-formed queries supply the comparison. No service failure was converted into a theorem absence claim.

## Review by NZ

I read delivery-errors B–E against the final node, the cited statements and the source passages. For the item I read Raynaud §2 Propositions 2.3–2.4 and Corollary 2.5 in the primary scan, and the local Stacks text around More on Groupoids 0API (`lemma-sits-in-functions`) and 0APJ (`lemma-affine-base-change`). I checked Topology 0A31 (`lemma-make-spectral-space`), the localization-prime description Algebra 00E3 (`lemma-spec-localization`), and the affine principal-open result Schemes 01I3 (`lemma-standard-open-affine`). There are no new statements whose sources require a separate review.

1. Step 1 uses affine-scheme-qcqs only for qcqs, qcqs-scheme-spectral for spectrality, and spectral-generalizations-of-quasi-compact for the intersection of all quasi-compact open neighbourhoods. I checked that retrocompactness makes H quasi-compact because S is itself quasi-compact. The formula in the last cited statement describes generalizations of H, exactly H by the hypothesis. This is a set of opens, not a large diagram; it is nonempty even for empty H.

2. Step 2 uses intersection-canonical-affine-embedding with Y=S. Every quasi-compact open of S is a quasi-compact open of an affine scheme, exactly its stated notion of quasi-affine. The node states the actual locally ringed map and induced-ringed-image identification, not merely a point embedding. Locally-ringed-space-affine-adjunction states the required natural bijection for arbitrary locally ringed spaces, not only schemes. Equal restriction maps therefore give hk=i without assuming E a scheme.

3. Step 3 uses localization-spectrum-flat-monomorphism for flatness only. The principal-open basis node supplies the finite cover after quasi-compactness is applied; localization-spectrum-embedding states that the point map is contraction, giving the inverse-image equality of principal opens. Affine-open-section-vanishing-prime gives their affineness and affine-scheme-qcqs their quasi-compactness. The same qcqs node supplies quasi-separatedness of S'. The family includes S', is set-indexed and directed by finite intersections. The qc-open-intersection-spectral-presentation node states the topological limit and spectral transition maps, including empty members. Spectral-directed-limit-spectral then states that its projection to S' is spectral, which is the asserted retrocompactness. Generalization stability follows directly from being an intersection of opens. No finite type or Noetherian hypothesis was used.

4. Step 4 uses intersection-sections-flat-base-change with Y=S, R=A and T=M^{-1}A. I verified its required quasi-separatedness, nonempty indexing family and flat affine change from Steps 1 and 3. Its statement includes the precise canonical tensor formula and functorial compatibility. Fibre-product-affine-spectra identifies the spectrum of that tensor product with the fibre product. Naturality of the locally-ringed affine adjunction, together with the displayed restriction maps, checks the comparison with k and k', including sheaves. It does not invoke a base-change theorem for E as a scheme.

5. Step 5 uses algebra-tensor-pushout-universal-property and ring-localization-universal-property only for the map classifications they state. The inverse comparison maps agree on C and on the localized A, which proves the ring isomorphism. Localization-spectrum-embedding then gives the image and unique lifts of points. Spec-local-ring-canonical-morphism identifies the image of S_s with the generalizations of s. This is why later complement images can be compared exactly, without a false claim about images after general base change.

6. Step 6 again uses the local-spectrum node for H_s=S_s when s lies in H, and the affine-spectrum node for the identity affine envelope of S_s. The fiber uniqueness comes from Steps 4–5, already proved for every point before schematicity. This gives h^{-1}H=k(H). Applying this universal result to the localized pair is legitimate because Step 3 proved its hypotheses. The complement statement follows point by point from the embedding in Step 5; it is not merely an inclusion of images.

7. Step 7 uses topological-inverse-image-stalk for the actual induced-sheaf stalk and map; flat-morphism for the stalkwise definition; topological-inverse-image for its adjunction on sheaves of rings; and ringed-subspace for the specified sheaf and inclusion. Thus flatness comes from an isomorphism of local rings. Quasi-compactness is the given retrocompactness applied to affine opens. For monicity the equality of base maps follows from injectivity of the subset map, and equality of sheaf maps follows from the stated inverse-image adjunction. These are explicit elementary arguments, not an invocation of an unstated theorem about arbitrary injective scheme maps.

8. Step 8 invokes qc-flat-monomorphism-affine-neighbourhood only after all three of its hypotheses have been proved in Step 7. I read its full statement and Raynaud Proposition 1.5(i); it provides E->U affine, exactly what is needed, without finite presentation or a Noetherian assumption. The principal-open basis and affine-section localization nodes provide the affine D(a) inside U. Affine-morphism-permanence supplies affineness of their inverse images. Open-preimage-fibre-product identifies the open pullback. The affine-spectrum statement and affine adjunction imply that an affine E_a is its own envelope. Step 4 is applied also to principal localization, not just point localization, so it identifies that envelope with h^{-1}D(a). The union is an actual open neighbourhood of H disjoint from B, hence from its closure along H.

9. Step 9 uses only the definition of open immersion after the two set inclusions, both written out, show k(H)=h^{-1}(S minus closure B). Step 2 supplies the isomorphism of the actual sheaves, so this is the open subscheme structure, not just a homeomorphism. Step 7 then supplies qc flat monicity. This direction does not assume what it proves.

10. Step 10 uses the induced-ringed-image identification from Step 2, affine-spectrum's contravariant functoriality and global-sections property, and the affine adjunction's uniqueness. These suffice for surjective=>isomorphism=>affine and affine=>isomorphism; no finiteness hypothesis is added.

I tested H empty, H=S, a principal open H=D(f), and the generic point of a domain. In the empty case C=0 and V is empty, so all equivalences and the boundary criterion remain valid. For a principal open the envelope is Spec A_f and its boundary is empty. I also checked the punctured affine plane: its envelope can fill the missing origin, so B need not be empty even when E is a scheme; its closure still avoids H, precisely as the statement requires. The localization proof retains all generalizations of s, rather than replacing the local spectrum by its closed point or residue field. The zero ring and a localization containing zero cause no exception to the arguments.

For B, no unsplit node contains a proof and no new notion or Mathlib match was invented. For C, I opened every cited node's statement and used only the quoted statement, repaired the separatedness mismatch, and generated one verbatim quotation per step/node pair. For D, the ten steps contain the actual assembly and all clauses; no new node repeats a clause. For E, the hypotheses above are checked where used, and all scheme assumptions are introduced after the schematicity branch starts. No proof step is longer than 2000 characters (the longest is 1423), and I found no hidden independent comparison lemma needing a new node. The tensor comparison and the inverse-image adjunction arguments are explicitly supplied. The server's initial review_split passed before the final citation correction; the delivery dry run will check the final tree.

## Server checks

The first srvcheck process had disappeared after the provider interruption, so I repeated that read-only check, not a delivery or other mutation. The repeat exited 0: review_split PASS, 0 new nodes, with declared tool uses and the existing unit-realization notice. Final delivery results follow below.

The first deliver.py --no-push exited 0 with `OK (not pushed)` at 4bf34a23cba: maintainer preflight passed. After that check I made the malformed Loogle query's verdict explicitly `query error`, preserving its exact query and raw result. No mathematical content changed. A final dry run checks this metadata correction before pushing.
