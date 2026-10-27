# Q74 stage-1 report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-square-action-proj-translation-extension.json`: item split into five steps; statement preserved; Mathlib searches do not give the translation-extension theorem.
- `dag/nodes/sec-six-functors-basics/lem-sfb-cofinal-section-opens-proj-neighborhood.json`: one new statement-only lemma comparing two full section-ring Proj targets under mutual refinement of section opens; unsplit, not in Mathlib after the recorded searches.
- `citations.json`: one verbatim statement quote for every step/node pair (16 entries).
- `searches.jsonl`: actual search-command records, retained without inventing a query or result.
- This report. Sandbox helper scripts only construct these JSON/report files; they do not change the repository or launcher.

One new node, zero Mathlib leaves. No Lean written or compiled.

## Attachments

None. Searched the live project's WeilConjectures source for the blueprint tag and the translation/Proj and square/Picard notions. No project declaration gives every clause without sorry. Mathlib chart, stalk and open-immersion results are not attachments and do not give the comparison lemma.

## Literature wanted

WANTED: Ning Guo, Divisors on coherent schemes and homogeneous spaces, sections 5.6, Corollary 5.8, section 6.1 and Proposition 6.2, printed pages 14--15, for lem-sfb-square-action-proj-translation-extension. The expected repository PDF is absent. I read the online author PDF at https://ningguomath.com/wp-content/uploads/2026/03/amplenew-1.pdf without downloading it into the repository. Proposition 6.2 refers the proof to Raynaud rather than providing the comparison argument.

WANTED: Raynaud, Faisceaux amples sur les schémas en groupes et les espaces homogènes, chapter V, Proposition 3.1 and Corollary 3.6, for lem-sfb-square-action-proj-translation-extension and the comparison background for lem-sfb-cofinal-section-opens-proj-neighborhood. That proof was unavailable. Accordingly the parent proof is marked agent-written, and the new node is explicitly an agent-formulated lemma, not a theorem purportedly quoted from Stacks.

## What was wrong and what changed

The imported item had an empty proof. Its statement agrees with the translation-extension assertion used in Guo Proposition 6.2, after accounting for the convention that Guo's translation uses the inverse group element. The inherited affine-base, smooth-test-base hypotheses suffice. I did not change the statement or weaken its conclusion. In particular the isomorphism is over B, both opens contain the whole canonical image, and the conclusion imposes no coherence in g.

The proof supplies the missing argument: use the square identity and its translate to multiply sections, proving mutual refinement of the two section-open families; then use one genuinely general comparison lemma and the graded pullback isomorphism. No new node is a clause saying that group translations extend. The new lemma has no group, square condition, or translate; its two refinement hypotheses are proved in the item rather than moved into a black box.

The current blueprint's six-functor unit and its inherited Guo ampleness chain were read. Whole-DAG and whole-blueprint searches found no equivalent comparison theorem. The inherited nearest blueprint ancestor is null; the full inherited via-chain is preserved, and from.place and same_as are filled. No unit realization is claimed for this auxiliary item. Generic off-unit tools are declared in split_report.tool_uses.

## What remains unfinished

Nothing remains for this one-level stage-1 split. The single new lemma is deliberately statement-only and joins the stage-1 queue; the detailed argument below records why I believe it true. No stage-2 or Lean completion is claimed.

## Review by Q74

I read the worker brief, stage-1 contract, the human's three levels in SETUP, GOAL, and delivery-errors B through E in full. I checked the actual JSON statements of every cited node, not just their titles. The quotes in citations.json are verbatim statement substrings. The source read for the parent is Guo 5.6, 5.8, 6.1 and 6.2 online; its cited Raynaud proof is not represented as locally read. For the new node I read Stacks properties.tex, Tag 01PW (lemma-invert-s-sections), including the quasi-compact quasi-separated localization hypothesis. I also read the affine-target and gluing statements in schemes.tex (01I1, 01JB) and arbitrary graded Proj separatedness in constructions.tex (01MC). These explain the agent argument below; 01PW alone is not falsely advertised as the comparison theorem.

Step 1 uses lem-pc-smooth-flat exactly for flatness of B over S; lem-pc-quasi-compact-base-change and lem-weil-pbc-separated-base-change for the two properties of X_B over B; and lem-weil-pbc-qcqs-over-affine to obtain qcqs of the scheme Y. Finite presentation supplies quasi-compactness of X over S, and separatedness over the affine S supplies its quasi-separatedness. Thus the arbitrary quasi-coherent sheaf version of lem-pc-flat-base-change-cohom applies to every tensor power of M in degree zero. I checked coherent.tex Tag 02KH as well. A tempting structure-sheaf-only flat-base-change node was rejected because it would not justify M^n. The graded product formula is written on pure tensors. The statement of lem-nagata-affine-proj-scalar-extension gives the actual chart comparison and cover, and lem-sc-ample-proj-canonical-map gives the fraction formula identifying the canonical maps. No arbitrary nonflat base change is used. During review I corrected an initially implicit qcqs inference by adding the three existing qc/separatedness statements and their quotes.

Step 2 uses only the local rank-one definition def-sc-invertible-module and the pullback/composition identifications in def-pc-module-pullback, together with the given group identities and square hypothesis. Applying the square identity to g and g inverse yields L^2 = K tensor J tensor q*N0. Pulling that very identity back by tau gives K^2 = D tensor L tensor q*N1; one could choose N1=N0. Nothing requires a coherent choice of these identifications. The section covers for all translates are the pullbacks of the cover for L along automorphisms. Invertibility under pullback is checked in local frames.

Step 3 uses lem-weil-pbc-affine-finite-type-generating-sections for N0^(nm), which is a quasi-coherent finite-type module on the affine B. Its actual statement supplies global generators. Some generator has nonzero residue at q(y), hence its pullback has nonzero residue at y. The definition of section nonvanishing is in def-weil-pbc-ample-invertible-module. The explicit product t^m u^n q*v is an L^(2nm) section; in each residue field its product coefficient proves both nonvanishing at y and containment in Y_t. This is an elementary section multiplication argument using the cited generation statement, not an uncited ampleness theorem.

Step 4 uses the same two nodes for N1^(de) and the nonvanishing definition. The explicit product u^d s^e q*v is a K^(2de) section by the second identity of Step 2. Its residue gives the reverse refinement. I checked both exponents and the direction of each containment. These steps do not trivialize a base line bundle globally and do not assume section divisors are Cartier.

Step 5 uses the new lemma with exactly its hypotheses: affine B and qcqs Y from Step 1, invertibility and both covers from Step 2, the two pointwise refinement conditions from Steps 3 and 4. Its conclusion supplies theta with theta r_L=r_K, not an open immersion assertion about either canonical map. Pullback by the automorphism gives an honest graded T-algebra isomorphism, so prop-nagata-relative-proj-functoriality applies in the isomorphism case. The fraction formula in lem-sc-ample-proj-canonical-map verifies F r_K=r_L tau and fixes the contravariant direction. Hence F theta is the required extension. Surjectivity of tau proves the second target open contains the entire original image.

I checked the main return modes individually. B: the statement is self-contained with all the original hypotheses, and all ids and notions are present. C1: every non-elementary input of each step is a cited statement; local tensor products, inverse group identities and residue-field products are written out rather than hidden behind a new node. C4: the cited statements supply the precise sheaf, base-change, cover and fraction clauses used; citations.json records them. D1/D2: the sole new node is a comparison of unrelated invertible modules, with the substantive square-to-refinement deduction retained in the parent. Duplicates: localization, one canonical map, ample reconstruction and already-given graded isomorphisms do not state this comparison; every same-tag pair is discussed below. E: the statement-only lemma is plausible on its full hypotheses and all its searches are real; source attribution distinguishes Stacks inputs from the agent formulation. Each parent step is under 2000 characters, so no long-step sublemma is concealed.

For small cases I tested Y empty (both relevant Projs empty), L=K and trivial invertible modules (the comparison reduces to the same affinization), and L=O(1,0), K=O(2,0) on P1 x P1 (the maps contract a factor, so assuming open immersions would be wrong). The different rulings O(1,0), O(0,1) fail mutual refinement, as they should. The dual-number affine scheme preserves its nilpotents; the gluing argument below uses injectivity of structure sheaves, never reducedness. For the parent I checked g=e, X empty, and a nontrivial base twist N: affine generation, rather than a global frame, is exactly what is needed. No statement dispute was found.

## Mathematical argument for the new statement-only node

This is recorded here for review and takeover; the new JSON node remains unsplit as required.

For each positive homogeneous s of A_L, the standard chart D_L(s) has coordinate ring (A_L[s^-1])_0. The section-localization bijection of lem-sc-section-ring-localization-bijective (Stacks 01PW) identifies this ring with Gamma(Y_s,O_Y); its qcqs hypotheses hold. The canonical-map fraction formula identifies this with the map induced by r_L, and the same holds for K. Standard charts form an affine basis. Thus O_(P_L) -> (r_L)_*O_Y and its K counterpart are isomorphisms of sheaves. In particular their restrictions to every open are injective. Consequently each restricted canonical map is schematically dominant: a closed subscheme containing its inverse image has defining ideal pulling back to zero, hence has zero ideal by that injectivity. The image is topologically dense as well: an open with empty inverse image has zero structure sheaf, hence is empty. This formulation does not assume the source is reduced.

Whenever Y_s is contained in Y_t, restriction of regular functions gives Gamma(Y_t,O) -> Gamma(Y_s,O), and hence a B-morphism D_L(s)=Spec Gamma(Y_s,O) -> D_K(t)=Spec Gamma(Y_t,O). The affine-target description makes its composite with r_L on Y_s equal r_K on Y_s. Mutual refinement ensures that the union W_L of these D_L(s) contains r_L(Y). The morphisms glue on chart intersections. Indeed two such maps into P_K agree after composition with the restricted r_L; P_K is separated over B (Proj is separated over Spec of its degree-zero part, which is affine over B), so their equalizer is a closed subscheme. The preceding injectivity forces its ideal to vanish. This proves equality without a reduced-source dominant-extensionality shortcut. Gluing produces alpha:W_L -> P_K with alpha r_L=r_K.

The reverse refinement similarly produces beta:W_K -> P_L with beta r_K=r_L, and W_K contains r_K(Y). Put O_L=W_L intersect alpha^-1(W_K) and O_K=W_K intersect beta^-1(W_L). They contain the respective canonical images. On O_L, beta alpha equals the identity by the same closed-equalizer/injective-sheaf argument; on O_K the analogous identity holds. Thus alpha carries O_L into O_K, beta carries O_K into O_L, and the restrictions are inverse B-isomorphisms. Taking V_L=O_L, V_K=O_K proves precisely the new statement. All maps of rings are B-linear restriction maps. No properness, ampleness, finite generation of either whole section algebra, or canonical open immersion was used.

## Mathlib and duplicate search review

The item was searched by its tag and notion in the project source; all new-node searches used the required msearch command. I read the returned source for Proj.fromOfGlobalSections and basicOpenIsoAway, projIsoSpec/projIsoSpecTopComponent, stalkIso', isoOfRangeEq, hom_ext_of_forall and separated-target dominant extensionality. The chart statements concern one graded ring; isoOfRangeEq assumes the maps are open immersions; the dominant extensionality result with reducedness cannot establish this nonreduced comparison. None is the node or its one-line specialization. Alternate natural-language searches and corrected names were used before declaring no match. The unsuccessful Loogle identifier IsIso query is recorded as invalid rather than counted as evidence; the corrected CategoryTheory.IsIso query and Proj/Iso searches were run. No service outage is claimed.

The whole blueprint was searched for Picard, section ring, section-ring, affinization, nonvanishing, cofinal affine, Proj, 01PW, 01I1 and 01JB. The whole DAG was searched for the tag and semantic alternatives, and the matching statements were read. The inherited blueprint ancestor is null, consistently with the item's existing chain.

## Not duplicates

lem-sfb-cofinal-section-opens-proj-neighborhood vs def-sc-section-ring-veronese-fraction-map: the existing node states Explicit Veronese numerator-to-fraction map; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs def-sc-tensor-power-open-restriction-comparisons: the existing node states Canonical restriction tensor, tensor-power and numerator comparisons; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sc-affine-open-section-fraction-localization: the existing node states Ordinary section localization over an ambient affine open; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sc-affine-section-localization: the existing node states Degree-zero localization of sections on an affine scheme; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sc-ample-ideal-section: the existing node states Ample powers supply a section of an ideal near a point outside its zero set; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sc-ample-proj-local-chart: the existing node states The canonical Proj map identifies an affine principal chart; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sc-ample-proj-open: the existing node states An ample invertible sheaf realizes a scheme as an open subscheme of Proj; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sc-invert-s-cohomology-affine-case: the existing node states Localization comparison on an affine open; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sc-invert-s-cohomology-affine-open-zero: the existing node states Degree-zero localization on an ambient affine open; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sc-invert-s-cohomology-affine-open: the existing node states Localization on an ambient affine open; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sc-invert-s-cohomology: the existing node states Localization of graded cohomology at a section; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sc-section-ring-coefficient-data-numerator: the existing node states Existence of coefficient numerator map; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sc-section-ring-localization-bijective: the existing node states The section-ring restriction-and-division map is bijective; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sc-section-ring-veronese-fraction-kernel: the existing node states Kernel of the explicit Veronese fraction map; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sc-section-ring-veronese-fractions-core: the existing node states Core additive equivalence for Veronese fractions; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sc-section-ring-veronese-fractions-formula: the existing node states Formula for Veronese fraction generators; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sc-section-ring-veronese-fractions: the existing node states Veronese section fractions present homogeneous localization; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sc-section-ring-veronese-numerator-transition: the existing node states Veronese numerator compatibility with tensor-power transitions; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sc-tensor-power-section-open-restriction-N: the existing node states Canonical tensor-power restriction comparison preserves section powers; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sc-tensor-power-section-open-restriction-T: the existing node states Canonical restriction numerator comparison intertwines transition sheaf morphisms; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sc-tensor-power-section-open-restriction: the existing node states Tensor-power section equations and transitions under open restriction; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs new-affine-cohomology-localization-zero: the existing node states Degree-zero affine cohomology localization comparison; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-per-relative-ample-absolute-twist: the existing node states Absolute ampleness after twisting a relatively ample invertible module; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs def-sc-section-fraction-presentation: the existing node states Fraction presentation of localized tensor-power sections; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sc-p1-invertible-section-localization: the existing node states Localization of graded sections at an invertible-module section; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sc-p1-section-clearing-denominators-qcqs: the existing node states Clearing denominators of sections on the nonvanishing locus, qcqs case; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sc-p1-section-fraction-restriction-map: the existing node states Restriction and division of section fractions; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sc-p1-section-restriction-s-torsion: the existing node states Restriction-zero sections are killed by a power of an invertible section; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sc-p1-serre-section-module-comparison: the existing node states Serre comparison for the graded section module; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-weil-pbc-affine-section-cover-twist-generation: the existing node states Eventual finite generation from a fixed finite affine section cover; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-weil-pbc-ample-very-ample-immersion-affine-base: the existing node states An ample invertible module over an affine base: a power is the pullback of O(1) along an immersion into projective space; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-weil-pbc-coherent-twist-global-generation: the existing node states A sufficiently positive ample twist of a coherent module is globally generated; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-weil-pbc-nonvanishing-section-trivializes: the existing node states A section of an invertible module trivializes it where it does not vanish; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-weil-pbc-section-nonvanishing-zero-locus: the existing node states Stalk nonvanishing equals the complement of the zero-locus support; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-a1-affine-principal-affinization-isomorphism: the existing node states Canonical affinization isomorphism on an affine principal open; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-a1-quasi-affine-open-affinization-square: the existing node states Cartesian affinization square for an open inside a quasi-affine scheme; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sfb-ample-twist-hypercohomology-detection: the existing node states Ample positive twists detect a nonzero quasi-coherent complex; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sfb-proj-section-module-reconstruction: the existing node states Reconstructing a quasi-coherent sheaf on standard Proj from all twisted sections; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sfb-proper-ample-section-proj-reconstruction: the existing node states Proper ample section-algebra reconstruction and polarized naturality; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sfb-relative-ample-absolute-twist: the existing node states Absolute ampleness after twisting a relatively ample invertible module; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sfb-square-action-affine-orbit-criterion: the existing node states Affine section loci and a group action detect ampleness for square-condition lines; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs new-sbc-local-free-map-extension: the existing node states Extend a local finite free morphism after clearing denominators; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs new-sbc-quasi-affine-local-free-global-map: the existing node states A local basis extends to a global finite free map near one point; it does not compare two full section-ring Proj targets from mutually refining section-open families.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sc-ample-proj-canonical-map: the existing node constructs one canonical map and its fraction formula, not an isomorphism between neighborhoods for two unrelated invertible modules.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-sfb-proper-ample-section-proj-reconstruction: the existing node reconstructs a proper scheme from an ample module; the new node assumes neither properness nor ampleness and can involve canonical maps that contract fibres.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-trf-local-proj-isomorphism-compatibility: the existing node starts with supplied compatible graded algebra isomorphisms; here mutual refinement supplies no graded algebra isomorphism, and the comparison must be constructed by affine chart restriction.

lem-sfb-cofinal-section-opens-proj-neighborhood vs lem-a1-quasi-affine-open-affinization-square: that statement assumes quasi-affineness and constructs an open immersion into one affinization; the new statement permits non-quasi-affine Y and compares two Proj targets whose canonical maps need not be immersions.
