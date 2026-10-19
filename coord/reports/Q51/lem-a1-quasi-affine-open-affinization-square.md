## Files written

- dag/nodes/sec-purity-real-sheaves/lem-a1-quasi-affine-open-affinization-square.json: the item, split in six steps; statement unchanged.
- dag/nodes/sec-purity-real-sheaves/lem-a1-qcqs-affinization-basic-open-sections.json: statement, Mathlib leaf; AlgebraicGeometry.isIso_ΓSpec_adjunction_unit_app_basicOpen, Mathlib/AlgebraicGeometry/Morphisms/QuasiSeparated.lean:450–462.
- citations.json: a verbatim used clause for every step/node citation.

The sandbox had no prior node or report. The imported item's previous Mathlib search records were retained, and searches performed in this session were logged by msearch.py in searches.jsonl. One new node, one new Mathlib leaf. No Lean files, compiler, Lake, build, live-project writes, launcher edits, or manual git commands.

## Attachments

None for the item. Searches of WeilConjectures/ by the exact blueprint id, by quasi-affine terminology and by cartesian/affinization terminology found no declaration asserting Tag 0ARY. Existing QuasiAffine.lean declarations concern other results. The new leaf matches an imported Mathlib declaration, not a newly proved project theorem. The project localization wrappers in WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/QuasiSeparated.lean assert localization of section rings; the new node instead records exactly the canonical map on sections over D(f), with its Mathlib instance.

## WANTED

None. All mathematical sources used are available in literature/stacks-project/.

## Problems corrected or clarified

There is no statement dispute. Tag 0ARY really has U in both left corners, with the identity left arrow, and its bottom arrow is U → V → Spec Γ(V). The similarly named Mathlib isPullback_toSpecΓ_toSpecΓ instead has V at bottom left and assumes an affine morphism. That additional assumption cannot be used here. For instance, the punctured affine plane over a field embeds openly in the affine plane, both are quasi-affine, but the inclusion is not affine. Its affinization is the whole plane. This also tests why one must prove the inverse-image equality for the image of U, rather than the image of all V.

The source's use of Tag 01P8 is expanded into its ingredients: an isomorphism on basic-open section rings, affineness of both restricted schemes, and construction of the inverse affine-scheme morphism. Only the section-ring fact needs a new node. Creating a separate node restating Tag 01P8 would duplicate a few-line deduction from these cited statements. The final cartesian test is an explicit universal-property argument rather than an uncited locality/gluing theorem.

The inherited unit sk-p-real-rankin is not itself a unit about quasi-affine schemes. This item is a lower generic geometric tool in the already recorded representability/Gabber-descent chain below lem-a1-affine-hc0; no unit realization or unit route was changed. The current blueprint ancestor file gives only its H_c^0 vanishing statement. The new blueprint reference records this inherited ancestry and identifies the precise Tag 0ARY subargument being supported, rather than attributing a nonexistent geometric proof paragraph to that blueprint file.

## Unfinished work

None in the authorized one-level split. The new node is already a Mathlib leaf, with no postponed proof or further nodes.

## Not duplicates

No existing node's source carries Tag 01P7, the source of the new node, in the shared DAG searched for this delivery. The full-DAG searches also inspected occurrences of this tag in proof/search text; those are not statements of the new fact:

- lem-a1-qcqs-affinization-basic-open-sections vs sk-lem-nagata-boundary-divisor: the latter constructs an admissible blow-up and boundary divisor, not a section-ring isomorphism.
- lem-a1-qcqs-affinization-basic-open-sections vs det-ctf-finite-comparison-whole: the latter is a derived-category generation theorem, not the qcqs lemma.
- lem-a1-qcqs-affinization-basic-open-sections vs lem-sfb-etale-geometric-fibre-compact-sections: the latter computes compactly supported sections of a finite geometric fibre.
- lem-a1-qcqs-affinization-basic-open-sections vs lem-sbc-punctured-completion-matching-affine-sections: the latter proves bijectivity of a particular punctured-completion matching model's section map, with Noetherian completion and finite-morphism hypotheses.
- lem-a1-qcqs-affinization-basic-open-sections vs lem-weil-pbc-basis-sheaf-cofinal-coverings: the latter is an abstract criterion for gluing over a basis, not localization of sections.
- lem-a1-qcqs-affinization-basic-open-sections vs lem-sc-affine-open-pseudo-coherent-localization-point: the latter finds principal neighborhoods on which a complex is pseudo-coherent, not the map of structure-sheaf sections.

The existing lem-trf-quasi-affine-canonical-affine-embedding was reused for the canonical open immersions and the qcqs hypotheses. It does not assert the new section-map isomorphism for arbitrary qcqs schemes. The existing lem-weil-pbc-spec-localization-away-basic-open gives the spectrum's basis and a topological localization homeomorphism; the existing lem-weil-pbc-affine-ideals-closed-subscheme clause (0) gives affineness of principal opens; neither gives the canonical sections map for nonaffine qcqs schemes. The existing lem-weil-pbc-basic-open-pullback was reused rather than repeated. Whole-blueprint searches for quasi-affine, invert-f, 01P7, 01P8, adjunction_unit_app_basicOpen, and canonical morphism found no equivalent imported statement. No new node restates the item or its cartesian conclusion.

## Review by Q51

I read properties.tex, Tag 0ARY (lemma-cartesian-diagram-quasi-affine), its full proof, and the two lemmas it invokes: Tag 01P8 (lemma-invert-f-affine) and Tag 01P9 (lemma-quasi-affine). The statement in the item is exactly the outer square of 0ARY, not the affine-morphism square in Mathlib. I retained its hypotheses and both its cartesian and open-inverse-image descriptions. For the new node I read Tag 01P7 (lemma-invert-f-sections), including its proof with the canonical morphism, and Mathlib's QuasiSeparated.lean:450–462. The latter asserts precisely IsIso of the canonical map's app on D(f), under CompactSpace X and QuasiSeparatedSpace X, without requiring X or X_f affine. The new statement explicitly introduces X, C, j, f, D(f), X_f and the homomorphism; quasi-compactness and quasi-separatedness are defined inline. Its proof and proof_deps are empty, as a leaf requires. Its source is an exact tag and label. The four new-node searches ran through msearch.py; the matching instance and source lines were read, and no service failure was reported as absence.

Step 1 uses the statement of lem-weil-pbc-morphism-into-affine-scheme, whose bijection makes the two composites equal since both induce r. The statement of lem-trf-quasi-affine-canonical-affine-embedding explicitly gives both open immersions and both qcqs conditions. The definition of open immersion actually identifies the scheme and its restricted sheaf with its image, so the composite j_V u identifies U with the open H. It is enough to compose these two open-subscheme identifications; no theorem about an arbitrary morphism's image is being assumed.

Step 2 uses only the basis clause (i) of lem-weil-pbc-spec-localization-away-basic-open, not its topological-only clause as a sheaf claim. I read the supporting Algebra tag 00E0, lemma-Zariski-topology (11), (14). The affine-adjunction node explicitly says j_V^{-1}(D(g))=V_g. Clause (0) of lem-weil-pbc-affine-ideals-closed-subscheme explicitly says the principal open of an affine scheme is affine; I read Schemes Tag 01I3, lemma-standard-open-affine. The identification V_g ≅ D(g) comes directly from restricting the already obtained open-subscheme isomorphism, not from assuming every open of an affine scheme is affine.

Step 3 uses the full statement of lem-weil-pbc-basic-open-pullback: u^{-1}(V_g)=U_{r(g)}. Since V_g is contained in the image of u, restriction of the given isomorphism with that image makes U_f ≅ V_g. The same affine-adjunction node gives q^{-1}D(g)=D(r(g)), since q corresponds to r on sections. These are elementary substitutions in the cited formulas. They justify both affineness of U_f and the cover of U without assuming u is affine.

Step 4 applies the new section-map leaf only to U, whose two necessary hypotheses were established in step 1. Its target open D(f) is affine by the existing affine-principal-open clause, and its source U_f is affine by step 3. The map whose section homomorphism is an isomorphism is exactly j_U restricted to those opens, with the inverse-image identification supplied by the affine-adjunction node. Constructing the inverse ring homomorphism and applying the same bijection produces an inverse scheme morphism; composing gives identity ring maps and hence identity morphisms. This verifies the precise map compatibility that an unspecified localization isomorphism alone would not give. This is the source's 01P8 argument written out, not a new postponed clause of the item.

Step 5 takes unions of the equalities already proved. Because j_U is an open immersion, its image has exactly the restricted structure sheaf, not just the same underlying set. Commutativity identifies the map to H with the canonical map from U, yielding the identity after both identifications. Step 6 uses the universal property actually stated by def-pc-fibre-product. The inverse-image equality forces any compatible map b to land in j_U(U), so its structure-sheaf map restricts to give a unique c. The composite j_V u is an isomorphism onto H and therefore cancels, forcing c=a. This proves the required universal property with left projection id_U. Both final arguments are elementary from the cited open-immersion and fibre-product definitions; no uncited local-isomorphism or descent lemma is used.

I tested the new statement for f=0 (both section rings are those of the empty open, hence the zero ring), for f a unit (the app is the identity on global sections under the canonical identification), and for X empty (again zero rings). A nonaffine punctured affine plane has an isomorphism on global sections but is not its affinization, so the affineness check in step 4 is essential and present. The item's u=id case gives the tautological square, and its U empty case gives an empty inverse-image open. No reducedness, Noetherian, finite type, separated-morphism, nonzero-ring, or nonemptiness hypothesis has been introduced. All six proof steps have fewer than 2000 characters. I checked B–E: new-node self-containment, source and Mathlib lines, exact statement citations rather than proof-internal constructions, no hidden non-elementary inference, no duplicate, no circular citation, and no replacement of a unit step. No change of statement was required.
