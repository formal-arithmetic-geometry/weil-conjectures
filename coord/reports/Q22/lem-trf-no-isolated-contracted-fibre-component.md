# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-no-isolated-contracted-fibre-component.json`: the statement is unchanged; thirteen proof steps, using existing DAG nodes, give the noncontraction argument. Mathlib searches give no exact match.
- `citations.json`: 43 entries, one for each step/cited-node pair, quoting the actual cited statements verbatim.
- No new nodes or Mathlib leaves. The tentative trait-special-case node was removed from this sandbox before delivery.

## Attachments

None. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item blueprint tag, isolated/contracted components, and the relevant geometric notions found no project declaration proving this statement. Unrelated declarations and sorry-bearing trace-formula material are not attachments. The upstream master is reference material, not evidence of a finished proof.

## WANTED

WANTED: `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`, proof of Theorem 1.1, p. 3, for the source attribution of `lem-trf-no-isolated-contracted-fibre-component` (the non-isolated contracted-subcurve input extracted by Q83).

The local PDF is absent. The attributed stable pointed-subcurve passage does not by itself spell out this auxiliary assertion. I therefore mark the proof as agent-written and give its entire argument from the existing scheme-theoretic nodes, rather than claiming to have followed an archived Temkin proof. I read the local Stacks statements and proofs at 054F (properties.tex, lemma-locally-Noetherian-specialization-dvr), 03H2 (more-morphisms.tex, theorem-stein-factorization-general), 0539 (more-algebra.tex, lemma-valuation-ring-torsion-free-flat), 02KH (coherent.tex, lemma-flat-base-change-cohomology), 02O5/02O6 (proper coherent cohomology), 0H7K (fields.tex, lemma-common-extension-field), and 0GSK (more-morphisms.tex, remark-flat-equidimensional). These are the actual sources for the proof.

## What was wrong and corrected

No error in the imported statement was found, so its hypotheses and both conclusions are retained verbatim. I read the current blueprint ancestor `lem-trf-local-term-locality`, the chapter and `sk-i-curve-zero` records, and the marked-nodal dualizing-degree chain through which this item was created. The auxiliary argument addresses the isolated connected-component obstruction in that chain. Whole-blueprint searches for isolated contracted components found no duplicate statement. The general Stein tools are reused, not recreated.

My first sandbox draft put almost the whole content into a trait-special-case node. That was a D1/D2 relabelling, and its valuative-lifting citation did not supply all the hypotheses claimed. I replaced it with the actual argument and deleted that node. The final reduction uses the exact Noetherian specialization-to-DVR statement, without an unsupported finite-height or strict-henselian assumption. A common field extension handles the mismatch between the chosen geometric residue field and the DVR residue field. The final proof uses the valuation torsion-free-flat node already in this unit rather than an off-unit PID specialization. No claim of flat base change on the special fibre is made.

## What could not be finished

Nothing remains in the stage-1 split. The cited existing theorem nodes retain their own states; this delivery does not claim Lean proofs of them. The missing archival Temkin source is recorded above. No Lean file, compiler, Lake, library build, live-project file, or launcher file was written or run.

## Not duplicates

There are no new nodes and therefore no new/existing-node pairs to justify. The existing `lem-trf-stein-smooth-generic-curve` is not applicable: it assumes excellence, integrality, dominance and relative properness not supplied for the affine-local situation here. The existing valuation contracted-component inclusion and exceptional-locus criteria concern comparisons or unstable rational components, and do not prove this noncontraction assertion. The proof instead applies general affine Stein factorization where its stated hypotheses hold.

## Review by Q22

I checked B--E of delivery-errors.md against the node files and the sources, including the places where my draft had failed. There is no new statement-only leaf, no renamed clause, and no circular appeal to this item. The original definitions, source field, creation record and blueprint ancestry are retained. All thirteen steps are below 2000 characters; the arguments for clopen components, tensor flatness, torsion-freeness, generic density and the saturation of a clopen are written explicitly rather than hidden behind “standard.”

Step 1 uses `lem-sfb-finite-type-composition-base-change` and `lem-weil-pbc-finite-type-over-noetherian` to obtain a Noetherian geometric fibre. The finite-components statement and irreducible-components-cover statement give exactly the finite closed covering used in the intersection-chain argument; that elementary argument proves that connected components are clopen. `lem-sc-quasi-compact-kolmogorov-closed-point` supplies a closed point of nonempty W, and `lem-weil-pbc-closed-point-residue-field-base` applies because W is finite type over the algebraically closed field Omega. Only then is its image called rational. If the point of T is generic, the isomorphism already contradicts contraction of a clopen union of one-dimensional components.

Step 2 uses `lem-sbc-noetherian-specialization-trait` with the distinct specialization eta to s in the locally Noetherian T. Its statement really gives a DVR whose two points have the required images. `def-sc-discrete-valuation-ring` identifies the resulting ring as a Noetherian domain/PID and valuation ring. No normality or excellence of T is inferred.

Step 3 uses the full common-extension-fields statement for Omega and kappa(r) over kappa(s), and the existence part of the algebraic-closure statement. It does not assume that kappa(r) embeds into the initially chosen Omega. A second use of common extensions proves nonemptiness after scalar extension. The nilradical calculation proves that the image remains the one rational point, without assuming that topological constancy automatically means a schematic factorization. It works even with nilpotents, so nodal reducedness is not silently invoked.

Step 4 proves the needed flat base-change rule by the displayed tensor identity and the definition of flatness, then applies the affine criterion and localization-preserves-flatness. The finite-type base-change node states this permanence for arbitrary base morphisms. No finiteness hypothesis is imposed on the DVR morphism to T or on the field extensions. Open restriction is checked with the same affine criterion.

Step 5 uses proper-fp-permanence specifically for its proper-base-change clause, twice, and finite-type composition/Noetherianity for V and U. Properness is required for V over its affine target U, where it is available. The final quasi-separatedness assertion follows from the Noetherian topology, by quasi-compactness of the open intersections; it does not suppose affine intersections or separatedness of X/T or Y/T.

Step 6 uses `lem-weil-pbc-stein-factorization-affine` for properness and geometric connectedness of q, including its nonempty fibres. `pqf-lem-coherent-ft-locnoeth` supplies coherence of the structure sheaf, and the affine degree-zero clause of `lem-pc-coherent-hi` supplies finiteness of B over the Noetherian A. The finite-morphism definition then applies to the actual affine h. These are stronger statements than the henselian connectedness tools, and say precisely what this step needs.

Step 7 uses the affine flatness criterion and the injection formulation in `def-weil-pbc-flat-ring-map` to prove that each affine chart has no R-torsion. Restriction of global sections to those charts detects zero by the sheaf condition. Thus the exact torsion-freeness hypothesis of `lem-trf-valuation-torsionfree-flat` is verified for B; the base ring is the DVR from Step 2. This is the unit's own flatness input.

Step 8 applies `lem-weil-pbc-flat-base-change-global-sections-qcqs` only after Step 5 proves that V is quasi-compact and quasi-separated as a scheme. Localization-preserves-flatness supplies the flat generic map R to K. Since f_K is an isomorphism, V_K is the affine U_K; the canonical ring map identifies h_K with an isomorphism. In particular I did not replace B tensor_R L by closed-fibre global sections, a base-change assertion that is not available.

Step 9 checks pure dimension over the possibly nonclosed field K. Algebraic-closure existence and common field extensions supply the geometric comparison and lifts of points. The equidimensional-open node gives local topological dimension one on X_Kbar; `lem-weil-pbc-dimension-at-point-field-extension` gives precisely equality of local topological dimensions on finite-type affine charts, rather than equality of local-ring dimensions. Open restriction preserves this local topological dimension directly from its definition. Finally `lem-sbc-constant-local-dimension-components` applies to the locally Noetherian U_K. No smooth-curve theorem with an extra separated/integral hypothesis is used.

Step 10 first proves density of the generic fibre in the actual Spec B by the nilpotence/torsion calculation. For `lem-trf-flat-dense-generic-fibre-pure-dimension` I checked integrality of Spec R, flatness of Z/R, local finite type, density and generic pure dimension separately. Its statement includes arbitrary algebraically closed residue-field extensions, so it gives the asserted pure dimension for Z_L. Its source 0GSK explicitly allows the structure sheaf as the flat finite-type module with full support.

Step 11 uses the geometric connectedness clause of the affine Stein node after extension to L and proper-base-change to know that q_L is closed. The two images of the complementary clopens are complements because every fibre is nonempty and connected; the argument is written in the step. Finiteness of h_L is justified directly by tensoring finite module generators, and the finite-closed-map-finite-fibres node supplies finiteness of its point fibre. This does not depend on Stein factorization commuting with the closed base change.

Step 12 uses `lem-weil-pbc-finite-dimensional-domain-is-field` on the prime quotients of the finite-dimensional fibre algebra, so its points are all closed. Thus the finite clopen subset really has isolated points. The equidimensional-open-local-dimension statement applies to the locally finite type, pure one-dimensional Z_L and contradicts their local dimension zero. Step 13 uses only the finite irreducible covering again: an irreducible component disjoint from the others is a connected clopen component, so the first assertion gives the particular assertion.

I tested the conclusion on the identity modification and on ordinary exceptional curves meeting strict transforms: the former has no contracted component, and the latter do not give a clopen W. Empty fibres cannot furnish the hypothesized nonempty W. Disconnected fibres cause no problem, since the finite-component argument treats each connected component separately. The proof also allows disconnected W_L after extension: it only needs it to be nonempty and clopen. These checks explain why no stability, marking, rationality of exceptional components, global separatedness, or relative properness hypothesis has been added.

Every cited statement was opened, and `citations.json` copies those actual statements, not a proof hidden inside a cited node. Off-unit scheme, field and dimension lemmas are declared in `split_report.tool_uses` as general tools. The local trace-formula route provides no replacements for these general statements; its own valuation-flatness and flat-equidimensionality nodes are used where available. Mathlib searches retain the earlier records and append exactly the tool/query strings logged by msearch.py. The two unknown-identifier Loogle queries are marked invalid, not unavailable or successful absence searches; the later qualified query ran successfully and found no match.
