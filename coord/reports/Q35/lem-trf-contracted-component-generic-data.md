# Stage-1 repair: lem-trf-contracted-component-generic-data

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-contracted-component-generic-data.json`: five-step split; current main's statement and statement dependencies are retained verbatim.
- `dag/nodes/sec-trace-formula/lem-trf-contracted-component-no-extra-generic.json`: statement-only enumeration on an integral finite étale cover, including the fixed contracted sublist and properness of its generic fibres; no properness of the total component closures is asserted.
- `dag/nodes/sec-trace-formula/lem-trf-contracted-component-generic-spread.json`: statement-only numerical spreading for an already proper flat component family in a possibly nonproper ambient marked curve. The marking need not be finite over the base.
- `citations.json`: verbatim statement quotations for all sixteen step/node citations.
- `searches.jsonl`: retained prior searches and appended searches for the changed auxiliary statements. The JSON search records use the actual logged query strings and results.

Two new statement nodes, zero Mathlib leaves. The existing sandbox work, citations, source references and search log were read before repair. I compared the retained item with the current read-only repository; the final item statement and `stmt_deps` now agree with current main. No git command was run in either read-only checkout; the delivery tool performs the rebase/packaging.

## Attachments

None. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, the blueprint tag, contracted-component language, nodal incidence and arithmetic-genus declarations found no project declaration giving this theorem. `EulerChar.lean` defines arithmetic genus but does not give contracted-component generic constancy. A sorry in upstream master is not treated as a proof.

## WANTED

WANTED: local archival copy of Temkin, *Stable modification of relative curves*, arXiv:0707.3953v3, Lemma 5.1(ii), printed p. 34. I read the primary author PDF at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf, §1.2 and the full proof of Lemma 5.1(ii).

WANTED: EGA III2, 7.6.9, cohomology semicontinuity, for `lem-trf-contracted-component-generic-spread`. EGA III1 is present locally, but III2 is not. The split and numerical refinement are marked agent-written. EGA IV3 **is** present locally: I read 9.7.7–9.7.12 and 13.1.3 in `literature/ega/EGA-IV-3_PMIHES-28-1966.pdf` using pdftotext; it is not a wanted document.

## Repair of the return

The return identified E1: the old Step 3 applied a theorem requiring the whole family Y/T to be proper although the item expressly allows a nonproper family. This is repaired in the proof itself, not by assuming Y proper. Step 2 now proves properness of each contracted component closure H_i after shrinking. It applies the **existing** Stacks 081F node to H_i/S, with the generic point presented as the limit of principal opens of the integral affine base. The limit fibre is proper; the qcqs and locally-finite-type hypotheses are checked explicitly. Then the numerical theorem takes this proper H_i as input. Y never becomes an argument to a proper-family theorem.

The initial dry run of the retained split completed with a citation diagnostic (the changed spread sentence no longer matched its old quote). The final citations were regenerated from the statements actually used. I also checked the proof beyond that mechanical error: the old no-extra statement claimed individual geometric components descend to T and the earlier repair added an eta-modification assumption. Both changes were wrong for the intended use.

## Statement and descent correction

STATEMENT-DISPUTED: the **earlier sandbox repair**, not current main, added an eta-modification hypothesis. Temkin Lemma 5.1 says modification, not eta-modification, and the parent `lem-trf-stable-modification-constructibility` Step 4 explicitly does not preserve modifications on the closed strata used in its Step 5. The final delivered item restores current main's statement verbatim, including its explicit absence of a generic-isomorphism or modification assumption. For example, over a field the proper constant map P¹ → A¹ with empty markings has one contracted component and satisfies the current item; it is not a generic isomorphism. The previous added hypothesis would exclude this legitimate case.

A second correction concerns labelled geometric components. Over R, a pair of conjugate lines, mapped properly to a closed point of A¹, has two geometric components that cannot be defined individually over R. A finite étale splitting extension is needed even when the base has one point. The repaired enumeration node gives S → U finite étale, integral and surjective; its component families live on S, not necessarily on U. The final proof descends the **multiset** and an open subset, without descending the labels.

## Mathematical scope of the two new statements

The no-extra node is a geometric enumeration theorem, with no numerical decoration. Its source inputs are Stacks `more-morphisms.tex`, 0551 (`lemma-make-components-generic-fibre-geometrically-irreducible`), 0559 (`lemma-geom-irreducible-generic-fibre`), and the closure argument in 055A (`lemma-nr-geom-irreducible-components-good`), all read in the local source. On a split generic fibre, take reduced closures, apply generic flatness and geometric reducedness/irreducibility shrinking, and eliminate missing or repeated fibre components as in 055A. These closures are finite-presentation closed subschemes over the Noetherian base.

For the contracted labels, EGA IV3 13.1.3 makes the positive-dimensional fibre locus of h closed in Z. In a geometric curve fibre that locus is precisely the union of components contracted by h. For each component closure H_i, apply constructibility of images to H_i minus this closed locus: if its generic fibre is empty, shrink to make it empty; if nonempty, its image contains a generic neighbourhood. Thus the contracted/noncontracted label is fixed after one shrinking. For a contracted component R over an algebraically closed field, the proper map h restricts to a proper map on the closed reduced component, with singleton closed image x; the residue field of x is the base field. Since R is reduced, the ideal of x pulls back to zero, so the map factors through x, and proper base change gives R proper over that field. The same argument over the generic field, with a finite residue extension at x, gives properness of H_i,ξ. No assertion about properness of H_i/S is hidden in this node.

The spread node is a single-component statement with H/S proper **as an explicit input**. Its ambient family and marking can be nonproper. On a nodal geometric curve a component is singular only at its self-nodes; intersections with other components are smooth on that component. The marked and ambient-singular point loci on H are closed with finite geometric fibres. Their generic reduced points have separable residue fields (nodes of a nodal curve and the given étale marking), so they spread to finite étale loci after shrinking; properness of H rules out loss at infinity. The self-node sublist is separated from the two-component node sublist after shrinking. Cohomology semicontinuity for the proper flat component makes h¹ generically constant; coherent cohomology commutes with field extension, and finite étale ranks are constant on an integral base. This is the numerical content left for the next splitter; no proof is embedded in the auxiliary JSON.

Neither auxiliary restates the decorated multiset theorem: one supplies geometric families and their contraction labels, the other concerns a supplied proper component family. The item itself proves properness of closures using 081F and performs the descent back to T.

## Review by Q35

I read the item, the parent constructibility split, the chapter and unit records, the Temkin passages just named, EGA IV3 9.7 and 13.1.3, and Stacks 0551, 0559, 055A and 081F with their hypotheses. The unit's historical stable-modification input is retained; no chapter or unit record is changed. The item is an agent-stated generic numerical refinement of the paper's argument, not a verbatim claim that the paper states all the loop/marking conventions. The needed cohomology reference is explicitly wanted above.

Step 1 uses the new enumeration statement for proper geometric contracted components, component closures and fixed contracted labels. I checked that it assumes precisely flat finitely presented curve families, nodal source and a proper map; it does not need modification or ambient properness. `def-trf-multipointed-curve` gives the needed family conditions. The full statement of `lem-trf-semistable-marked-base-change` gives arbitrary base change of the marked nodal family and explicitly allows nonproper ambient curves. The step does not claim that individual geometric components descend from S to T.

Step 2 uses the statements of finite-type-over-Noetherian, locally-Noetherian-quasi-separated, affine-transition limits, eventually-proper and proper base change. I checked each against the application: H_i is finite presentation over Noetherian affine S, hence Noetherian, quasi-compact and quasi-separated; S is affine; H_i → S is locally of finite type. The index system is nonzero b in the domain B with refinements by products; its affine ring colimit is Frac B. The generic fibre is proper by the enumeration node. These are exactly the hypotheses and conclusion of `lem-weil-pbc-eventually-proper`; the statement does not demand H_i already be separated or proper. Products of finitely many nonzero b remain nonzero. Proper base change handles the subsequent restrictions. This is the specific correction demanded by the return.

Step 3 uses the revised spread statement only after H_i is proper. The flatness, finite presentation and reduced-geometric-component conditions persist on open restrictions and come from Step 1; the marking conditions come from arbitrary base change. The spread statement supplies finite p and the two finite counts, independent of algebraic closure. The application over Spec Ω verifies finiteness in the item's arbitrary geometric fibres, not merely on its final open. Flatness and finite presentation of a closed reduced component over a field hold because it is a finite-type scheme over that field. There is no ambient properness inference and no assumption that the marking is finite over T.

Step 4 is the written elementary descent argument: the reduced closed complement of V in S maps finitely to U (a quotient of the finite algebra). The finite-proper and proper-closed-image nodes say exactly that its image is closed; the reduced-induced-subscheme node provides that structure. Because S is integral and finite dominant over integral U, the generic fibre is the spectrum of one field, contained in V, so the discarded image misses the generic point. The resulting open T° is nonempty. This uses the statements of the cited nodes, not their proofs.

Step 5 is elementary descent of the list already constructed. A geometric point over t lifts along the finite étale surjection using an embedding of a finite separable residue extension into Ω. The resulting geometric marked curve is literally the same Ω-fibre by fibre products. Enumeration gives every contracted component once; numerical spread gives its triple. The multiset is therefore independent of the lift as well as t and Ω. Empty J gives the empty multiset.

I tested empty curves and empty J, a constant proper P¹ component attached to a nonproper ambient family, a smooth rational contracted component, a self-nodal component (one self-node and one distinct incidence point), incidence with another component (no self-node on the chosen component), and conjugate generic components. The ambient-nonproper case still uses properness only for H. No marking is forced to be finite globally. Every step is shorter than 2000 characters. Both auxiliary files remain statement-only with empty proofs; searches cover their changed statements with two phrasings. All citations were copied verbatim from the cited statements. No SGA source, Lean writing, compiler, Lake, build, other agent, or direct git command was used.

## What remains

The two auxiliary statements intentionally remain unsplit for the next stage-1 items. The item itself has a complete one-level split. The previous report's claim that generic-fibre isomorphism was required is superseded by the correction above.

## Not duplicates

lem-trf-contracted-component-no-extra-generic vs lem-sbc-etale-generic-residue-field-model: the existing node states “A prescribed finite etale generic extension has an etale residue-field model”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-reduced-generic-fibre-field-embedding-core: the existing node states “Core affine reduced fibre embedding”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-generic-geometric-irreducibility-shrink: the existing node states “Spread geometric irreducibility of one finite type generic fibre”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs new-lem-sbc-geometric-generic-cover-model-refinement: the existing node states “Fibre and intersection refinement of a spread model”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-affine-reduction-preparation: the existing node states “Reduction of an affine family before flatness”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-generic-components-split: the existing node states “Finite separable extension splitting the generic components”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-common-generic-hypersurface-affine-open: the existing node states “A common affine open with a generically geometrically integral hypersurface”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-geometric-generic-cover-model: the existing node states “A supplied geometric generic cover spreads on an etale model before incidences are spread”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-affine-source-geometric-irreducibility-shrink: the existing node states “Spread geometric irreducibility for an affine source with affine target image”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-field-hypersurface-integral-presentation: the existing node states “Integral hypersurface presentation of a separable function field”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-generic-radicial-geometrically-reduced-model: the existing node states “Reduced affine flat model with geometrically reduced generic fibre after radicial base change”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-radicial-reduced-flat-generic-fibre: the existing node states “Radicial reduced generic fibre”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-radicial-preparation-construction: the existing node states “Affine radicial preparation construction”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-generic-geometrically-integral-affine-chart: the existing node states “A spreading geometrically irreducible affine chart in a generically integral family”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-purely-inseparable-generic-base-spread: the existing node states “Purely inseparable generic base spread”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-radicial-preparation-fibre-comparison: the existing node states “Radicial preparation fibre comparison”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-radicial-generic-reduced-preparation: the existing node states “Affine radicial preparation with geometrically reduced generic fibre before generic-flat shrinking”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-geometric-generic-cover-spread: the existing node states “Spreading a supplied finite geometric closed generic cover”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-field-hypersurface-function-field-model: the existing node states “Hypersurface presentation of an affine function field over a field”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-affine-preparation-restriction: the existing node states “Affine restriction of a reduced preparation”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-compatible-etale-generic-fibre-model: the existing node states “A specified finite etale generic field extension spreads with compatible fibre maps”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-generic-fibre-birational-hypersurface-model: the existing node states “A birational hypersurface model of the geometrically integral generic fibre”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-reduced-generic-fibre-field-embedding: the existing node states “Reduced generic-fibre field embedding”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-generic-polynomial-hypersurface-descent: the existing node states “Descent of a generic polynomial hypersurface to base sections”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-radicial-separating-generic-field: the existing node states “Radicial base extension with a separating generic field map”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-generic-open-geometric-fibre-density: the existing node states “Spread density of an open into every geometric fibre”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-generic-fibre-dominant-field: the existing node states “Generic-fibre dominant field”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-closed-family-geometric-fibre-shrink: the existing node states “A finite closed family with geometrically irreducible generic traces stays so near the generic point”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-generic-fibre-incidence-spread: the existing node states “Generic component covers spread with their incidence edges”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-generic-fibre-hypersurface-function-field-model: the existing node states “Generic hypersurface model with a compatible fraction field”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-reduced-flat-affine-preparation: the existing node states “Reduced affine flat preparation”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-field-fraction-ring-geometric-integrality: the existing node states “Geometric integrality transfers through a base-compatible fraction-field isomorphism”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-reduced-generic-fibre-field-embedding-core-map: the existing node states “Dominant map from the reduced generic fibre”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-sbc-generic-fibre-partial-iso-spread-open: the existing node states “Spreading a generic-fibre partial isomorphism to a common open”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-trf-geometric-component-count-generic-constancy: the existing node states “Generic constancy of the number of geometric irreducible components”; it does not give a list of reduced component families with a fixed contracted sublist for a proper map of nodal curves. The new statement supplies that enumeration and generic component properness, without any numerical invariant.

lem-trf-contracted-component-no-extra-generic vs lem-trf-contracted-component-generic-data: the item asserts the decorated numerical multiset; the auxiliary supplies only geometric component families, their contracted labels and generic fibre properness, before the item proves properness of the closures.

lem-trf-contracted-component-generic-spread vs lem-trf-nodal-normalization-adjunction: the existing statement describes normalization and adjunction over one algebraically closed field; the auxiliary concerns numerical and incidence spreading for a supplied proper component family over an integral base.

lem-trf-contracted-component-generic-spread vs lem-trf-geometric-fibre-component-count-base-change: field-extension invariance of the number of all components does not give genus or self-node/incidence constancy for a proper component family.

lem-trf-contracted-component-generic-spread vs lem-trf-contracted-component-generic-data: the auxiliary starts with a proper flat component family; the item must construct proper closures inside a nonproper family and descend the whole multiset from a finite cover.

lem-trf-contracted-component-generic-spread vs def-trf-birational-quasi-modification: the definition specifies integral-source birational quasi-modifications; the new theorem spreads numerical data on a supplied proper flat component family and assumes no birational map.

lem-trf-contracted-component-generic-spread vs def-trf-centred-valuation: the definition specifies a valuation-ring morphism realizing a centre; the new theorem concerns cohomology and nodal incidence of a family, with no valuation datum.

lem-trf-contracted-component-generic-spread vs def-trf-modification: the definition specifies properness and a schematically dense isomorphism locus; the new theorem makes no modification assumption and concludes numerical constancy.

lem-trf-contracted-component-generic-spread vs def-trf-multipointed-curve-modification: the definition packages morphisms, eta-modifications, semistability and geometric stability; it does not prove proper-family cohomology or incidence spreading.

lem-trf-contracted-component-generic-spread vs def-trf-multipointed-curve: the definition specifies the flat marked curve, without ambient properness; the new theorem uses such a curve and a proper component to prove numerical constancy.

lem-trf-contracted-component-generic-spread vs def-trf-multipointed-eta-modification: the definition specifies base-changed proper pair maps and generic isomorphisms; the new theorem uses neither and proves numerical constancy for a supplied proper component.

lem-trf-contracted-component-generic-spread vs def-trf-nodal-dualizing-datum: the definition specifies a normalized adjunction module and its Jacobian formula; the new theorem concerns arithmetic genus and distinct incidence counts, without choosing dualizing data.

lem-trf-contracted-component-generic-spread vs def-trf-rational-rank: the definition concerns rationalization of an abelian group; the new theorem concerns numerical invariants of geometric curve components.

lem-trf-contracted-component-generic-spread vs def-trf-schematically-dense-open: the definition specifies injectivity of structure-sheaf restriction; the new theorem has no schematic-density assumption and concludes numerical constancy.

lem-trf-contracted-component-generic-spread vs def-trf-semistable-multipointed-curve: the definition specifies nodal fibres and a smooth étale marking; it does not state numerical or cohomological spreading for a proper component.

lem-trf-contracted-component-generic-spread vs def-trf-semistable-multipointed-pair: the definition specifies pairs, their base changes and fibrewise stability; the new theorem proves constancy for an already proper component family, rather than defining stability.
