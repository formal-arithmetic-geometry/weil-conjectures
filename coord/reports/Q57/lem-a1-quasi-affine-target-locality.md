# Stage-1 repair: lem-a1-quasi-affine-target-locality

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-a1-quasi-affine-target-locality.json`: existing statement unchanged; five-step assembly, 2420 characters in proof text.
- `dag/nodes/sec-purity-real-sheaves/lem-a1-relative-affinization-compatible-charts.json`: statement; unsplit; no Mathlib match.
- `dag/nodes/sec-purity-real-sheaves/lem-a1-affine-base-open-immersion-gluing.json`: statement; unsplit; no Mathlib match.
- `citations.json`: a verbatim statement quotation for every node used by each numbered parent step.
- `report.md`: this report, including the preserved old argument and the two extracted proof assignments.

The sandbox initially contained only dispatcher `.brief*` markers, not the node files, report or searches described in the repair brief. The required first dry run exited with `FAILED: no node files under .../dag/nodes/`. I copied the current read-only repository item, which carries the returned six-step proof, and retained its statement, citations, recorded searches and metadata. There was no earlier sandbox search log to reuse. New searches were actually run through msearch.py and their actual log records are included in the new nodes. No repository or launcher file was written; no git command, Lean compiler or Lake command was run.

## Attachments

None. The live `lean/Sheaf/AlgebraicGeometry/QuasiAffineTargetLocality.lean:82` states the item as `AlgebraicGeometry.isQuasiAffineHom_iff_of_affine_open_cover`, but its proof is `sorry` (line 86). Searches of `lean/WeilConjectures/` by blueprint tag, quasi-affine terminology and relative-affinization terminology found no completed declaration of this equivalence or either extracted lemma. The existing local algebra maps theorem gives only part of the compatible-chart construction, and the relative-spectrum theorem does not give maps from an arbitrary non-affine source.

## WANTED

None: morphisms.tex, constructions.tex, schemes.tex and properties.tex are present, together with the existing node statements and the relevant Mathlib sources.

## Return repaired

The return asks for at least two comparable statement-only unsplit nodes and an assembly of at most 3000 characters, preserving every old argument. It is repaired by two independent jobs:

1. `lem-a1-relative-affinization-compatible-charts` carries old step 3 and the local construction/identity-on-sections part of old step 4. It states the quasi-coherence of the direct image algebra, its affine relative-spectrum realization, the maps over each affine open, their canonical chart identification, and compatibility on arbitrary overlaps.
2. `lem-a1-affine-base-open-immersion-gluing` carries the gluing part of old step 4 and the global open immersion and quasi-compactness argument of old step 5. It assumes compatible local maps rather than a global map, constructs the latter, proves its injectivity using the common base point, proves it an open immersion, and proves quasi-compactness using the affine target charts.

These are comparable pieces: the former needs direct-image quasi-coherence, relative spectra, local algebra maps and chart identification; the latter needs morphism gluing, the over-base equation, global injectivity, open-immersion locality and quasi-compactness locality. Neither assumes or concludes the parent's quasi-affine-morphism equivalence. Both have `proof: []`, `proof_deps: []`, `proof_origin: null`, `status: unsplit`; neither statement contains a proof sketch. Their proofs are reserved for subsequent workers. The full old argument is preserved below, not replaced by abbreviated prose.

The parent keeps old steps 1, 2 and 6 verbatim (now 1, 2 and 5). The diagonal argument is not hidden inside the extracted nodes. Its new step 3 invokes compatible relative-affinization charts; its new step 4 applies the canonical quasi-affine embedding and then the gluing lemma. The proof text totals 2420 characters; every step is below 2000 characters. The statement and its unrestricted hypotheses are unchanged.

## Extracted argument assignment: compatible relative-affinization charts

Read Stacks Constructions Tag 01LY, `lemma-canonical-morphism`, including its affine restriction assertion and proof, and Tag 01LX, `lemma-spec-properties`, (1) and (3). Read Morphisms Tag 01SM, `lemma-characterize-quasi-affine`, proof (2) implies (4), for its use in this item. This is the canonical-morphism construction before the global gluing, not a new relative-spectrum definition.

The worker's argument to carry out is the following. For qcqs h, the structure sheaf is quasi-coherent (locally the module of rank one), so `pqf-lem-pushforward-qcoh` gives quasi-coherence of A = h_* O_Z. Apply clause (2) of `lem-weil-pbc-affine-morphism-relative-spec` to obtain pi:Y->S, alpha:A≅pi_* O_Y and the affine identifications q_U:Y_U≅Spec A(U). Apply `lem-weil-pbc-affine-algebra-local-maps` to alpha inverse. It supplies maps k_U:Z_U->Y over S, agreeing on all overlaps, including when U∩V is non-affine. Since pi k_U = h on Z_U and its image lies in U on the base, k_U factors uniquely through the open Y_U, giving e_U. The map on sections of q_U e_U is alpha_U inverse composed with alpha_U = identity of A(U), using A(U)=Gamma(Z_U,O). The bijection of `lem-weil-pbc-morphism-into-affine-scheme` identifies q_U e_U with the specified canonical map j_U. The compatibility of k_U is exactly the asserted compatibility of the composites of e_U into Y. No nonunique existence witness is used as a new definition.

## Extracted argument assignment: gluing over an affine base

Read Stacks Morphisms Tag 01SM, proof (2) implies (4), from its restriction of can to each inverse-image open through its assertion that can is a quasi-compact open immersion. The extracted lemma spells out the general gluing assertion used there. Read Schemes Tag 01K4, `lemma-quasi-compact-affine`, and the Mathlib proof of `IsOpenImmersion.of_openCover_source` at lines 73–85 of AlgebraicGeometry/Morphisms/OpenImmersion.lean, followed by `of_forall_source_exists` at 87–95. The existing node for that criterion states both the injectivity hypothesis and the local-source hypothesis.

The worker's argument is the following. The composites iota_a e_a glue by `lem-weil-pbc-scheme-morphism-gluing` to a unique c:Z->Y. Equality of pi c with h holds on the open cover Z_a and hence globally by the uniqueness clause of the same gluing node. If c(z)=c(z')=y, choose a with pi(y) in S_a. The over-base equation puts both z and z' in Z_a. On this one chart c is iota_a e_a, which is injective, hence z=z'. Each composite iota_a e_a is an open immersion, since a composite of isomorphisms onto open subschemes has that property directly from the definition. Apply `lem-weil-pbc-open-immersion-injective-local-source` to obtain that c is an open immersion. Each Y_a is affine by the definition of affine pi, so it is quasi-separated by `lem-weil-pbc-affine-scheme-qcqs`. Since Z_a is quasi-compact, `lem-weil-pbc-qcqs-morphism-permanence` (1) makes e_a quasi-compact. The equation pi c=h gives c^{-1}(Y_a)=Z_a, identifying the restricted map with e_a. The Y_a form an open cover of Y. Apply `lem-pc-quasi-compact-local-on-target` to c. These are all the subarguments of old step 5, plus the gluing part of old step 4; none was dropped.

## Mathlib and blueprint searches

Read the actual hits of every msearch invocation before recording the verdict. For the compatible-chart node, two natural-language phrasings returned normalization charts, absolute Gamma-Spec maps and the canonical map for an absolute quasi-affine scheme; the grep for relativeSpec/affinization/canonical Spec produced absolute Spec and Proj material, not a relative affinization of an arbitrary qcqs morphism. Loogle `"Spec", "pushforward"` concerns tilde modules and etale sites. The quasi-coherent pushforward Loogle hits concern generic module-sheaf adjunctions, not the relative-spectrum scheme and its maps. These cannot specialize in one line to the full new statement.

For the gluing node, LeanSearch and two LeanFinder phrasings produced ordinary gluing data, relative gluing over a locally directed diagram, absolute quasi-affine immersion facts, and quasi-compactness tests. Loogle `"IsOpenImmersion", "openCover"` gives the source-local criterion requiring an existing globally injective map. Read it, the target-local instance at line 110, and Mathlib AlgebraicGeometry/RelativeGluing.lean. None gives the construction and all the conclusions of this new statement in one specialization: one must construct the global map, obtain its over-base equation and injectivity, identify its chart preimages, and establish compactness. Generic morphism gluing and open immersion locality are ingredients of the extracted job, not replacements for the complete statement. No Mathlib leaf is claimed.

Whole-DAG searches included tags 01SM and 01LY, relative affinization/spectrum and canonical morphism terminology, and titles about open-immersion locality or covers. Blueprint searches used `relative affinization`, `affinization`, `canonical morphism`, `relative spectrum`, `compatible local maps`, `glue open immersions`, `01SM`, `01LY`, and `quasi-compact open immersion`; all chapters were included by blueprint_refs.py. No blueprint node states either new lemma. Both inherit chapter sec-purity-real-sheaves and unit sk-p-real-rankin, with nearest blueprint ancestor lem-a1-affine-hc0 and via=[lem-a1-quasi-affine-target-locality]. Their places specify which parts of the ancestor's Tag 01SM affine-cover argument they carry. I read that chapter and unit and made no changes to either route. These are generic geometric tools below the imported ancestor, not a replacement for the unit's Rankin–Selberg route.

## Review by Q57

I read the six-step returned item against Morphisms Tag 01SM and its exact hypotheses. I read Constructions Tags 01LY and 01LX for the first new node, and the end of Tag 01SM's (2)->(4) proof, Schemes Tag 01K4 and the explicit Mathlib open-immersion locality proof for the second. The parent still proves both directions for an arbitrary affine cover, with no finite-type condition on h and no compactness or separation condition on S.

Parent step 1 uses only `def-nagata-quasi-affine-morphism`, whose statement quantifies over every affine open. It therefore applies to each member of the chosen cover.

Parent step 2 uses exactly the same six statements as the returned proof. I opened all six. `lem-trf-quasi-affine-canonical-affine-embedding` says each quasi-affine Z_a is quasi-compact and separated, hence quasi-separated. `lem-weil-pbc-affine-scheme-qcqs` gives quasi-separatedness of each affine S_a. Clause (1) of `lem-weil-pbc-qcqs-morphism-permanence` gives quasi-compactness and quasi-separatedness of h_a from these source hypotheses. `lem-pc-quasi-compact-local-on-target` works for an arbitrary open target cover, so it applies both to h and to its diagonal, without requiring the product chart Z_a times_(S_a) Z_a to be affine. The fibre-product universal property in `def-pc-fibre-product` identifies the restricted diagonal and its inverse image. `def-weil-quasi-separated-morphism` then converts quasi-compactness of that diagonal into the stated property of h. Schemes Tag 01KO, `lemma-characterize-quasi-separated`, confirms this locality argument. No intersection of arbitrary affine opens of S was declared affine.

Parent step 3 cites `lem-a1-relative-affinization-compatible-charts`, whose complete statement gives each object, the affine pi, compatible local maps, and their identification with the canonical j_a. Its qcqs hypothesis was established in step 2. In particular this is a theorem about maps out of Z_a even when Z_a is not affine; the affine-only anti-equivalence alone would not give it.

Parent step 4 cites `lem-trf-quasi-affine-canonical-affine-embedding` and `lem-a1-affine-base-open-immersion-gluing`. I checked both statements: the former gives exactly compactness and open immersion of j_a; the chart isomorphism of step 3 makes the same true for e_a. The latter takes precisely an affine pi, compact Z_a, maps over S_a and equality on overlaps, all supplied here. It concludes both pi c=h and the quasi-compact open immersion. I did not assume global injectivity from source-local open immersions: the new gluing job explicitly retains the common-base-point argument required by the earlier reviewer.

Parent step 5 retains old step 6. Clause (2) of `lem-weil-pbc-affine-morphism-relative-spec` gives an affine Y_U for every affine U of S, not just the selected cover. `def-weil-open-immersion` identifies c^{-1}(Y_U) with an open subscheme of Y_U. The quasi-compact-morphism condition of `def-weil-finite-type-morphism` says that this preimage of an affine open is quasi-compact. Since pi c=h it is h^{-1}(U). `def-nagata-quasi-affine-morphism` gives the conclusion. This last step is a direct definition check, not an additional geometric theorem.

I tested both new statements on S empty (all schemes mapping to it are empty; unique maps and empty covers cause no failure), Z empty, zero chart rings, a one-member affine cover, redundant/infinite covers, non-quasi-compact base and non-separated base. The compatible charts require only qcqs h, not finite type or an affine source. The gluing statement requires each Z_a compact: without it an arbitrary non-quasi-compact open of an affine Y would invalidate quasi-compactness. The requirement that e_a be over the same base and agree as morphisms into Y prevents doubled-point failures of injectivity. Non-affine overlaps are allowed; their equality is a stated hypothesis of gluing and a conclusion of the compatible-chart node. There is no statement dispute or altered hypothesis.

For B1–B10 I checked self-contained objects, notion citations, TeX, exact Stacks labels, actual search records, blueprint references, and absence of an attachable complete theorem. For C1–C8 I read every cited statement rather than relying on its proof, supplied verbatim citations.json entries, kept the existing route and used no new reverse dependency. For D1–D5 the two new nodes carry separate constructions, not clauses of the parent's equivalence; all displaced reasoning is assigned above and retained verbatim below. For E1–E7 I checked the affine/quasi-separated and over-base hypotheses at each use, the correct relative diagonal, the order alpha inverse after alpha, compactness of inverse images, and the empty and non-separated cases. No prohibited SGA source is used. The only retained off-unit tool citation is the previously approved canonical quasi-affine embedding; the new nodes stay in this item's unit.

## Unfinished work

The two new nodes deliberately remain statement-only unsplit jobs for independent future workers, as the return requires. No mathematics of the parent remains unassigned. Delivery awaits the required server dry run, then push; its outcome is recorded after completion.

## Preserved returned proof

### Old step 1

The forward implication is immediate from [def-nagata-quasi-affine-morphism]: if $h$ is quasi-affine, then the inverse image of every affine open of $S$, in particular each $S_a$, is a quasi-affine scheme.

Cited nodes: def-nagata-quasi-affine-morphism.

### Old step 2

Assume that every $Z_a=h^{-1}(S_a)$ is quasi-affine. By [lem-trf-quasi-affine-canonical-affine-embedding], each $Z_a$ is quasi-compact and quasi-separated. The restricted map $h_a:Z_a\to S_a$ is therefore quasi-compact by [lem-weil-pbc-qcqs-morphism-permanence](1) (its target is affine and hence quasi-separated by [lem-weil-pbc-affine-scheme-qcqs]); applying [lem-pc-quasi-compact-local-on-target] to the affine cover $(S_a)$ gives that $h$ is quasi-compact. To see that $h$ is quasi-separated, cover $Z\times_S Z$ by the opens $Z_a\times_{S_a}Z_a$. The inverse image of the $a$-th open under the diagonal is $Z_a$, and the restricted diagonal is the diagonal of $h_a$, which is quasi-compact because $h_a$ is quasi-separated by [lem-weil-pbc-qcqs-morphism-permanence](1). The same target-local criterion [lem-pc-quasi-compact-local-on-target] applied to $\Delta_h$ makes $\Delta_h$ quasi-compact; by [def-weil-quasi-separated-morphism], $h$ is quasi-separated. (If the cover is empty, then $S$ and $Z$ are empty and the conclusion is vacuous.)

Cited nodes: lem-trf-quasi-affine-canonical-affine-embedding, lem-weil-pbc-qcqs-morphism-permanence, lem-weil-pbc-affine-scheme-qcqs, lem-pc-quasi-compact-local-on-target, def-weil-quasi-separated-morphism, def-pc-fibre-product.

### Old step 3

Put $\mathcal A=h_*\mathcal O_Z$ with its natural $\mathcal O_S$-algebra structure. Since $h$ is quasi-compact and quasi-separated, [pqf-lem-pushforward-qcoh] makes its underlying module quasi-coherent. Apply [lem-weil-pbc-affine-morphism-relative-spec](2) to obtain the affine morphism $\pi:Y=\underline{\operatorname{Spec}}_S(\mathcal A)\to S$ and an algebra isomorphism $\alpha:\mathcal A\xrightarrow{\sim}\pi_*\mathcal O_Y$, with each $Y_a=\pi^{-1}(S_a)$ affine and identified with $\operatorname{Spec}\mathcal A(S_a)$.

Cited nodes: pqf-lem-pushforward-qcoh, lem-weil-pbc-affine-morphism-relative-spec, pqf-def-coherent.

### Old step 4

Use the inverse algebra map $\alpha^{-1}:\pi_*\mathcal O_Y\to h_*\mathcal O_Z$ in [lem-weil-pbc-affine-algebra-local-maps]. For every $a$ it gives a morphism $c_a:Z_a\to Y$ over $S$, and the maps agree on all overlaps. By [lem-weil-pbc-scheme-morphism-gluing] they glue to $c:Z\to Y$ with $\pi c=h$. The restriction $c_a$ factors through $Y_a$. Under the affine chart $Y_a\simeq\operatorname{Spec}\mathcal A(S_a)$, the induced map on global sections is $\alpha_a^{-1}\alpha_a=\operatorname{id}_{\mathcal A(S_a)}$. Thus [lem-weil-pbc-morphism-into-affine-scheme] identifies this restriction with the canonical map $j_a:Z_a\to\operatorname{Spec}\Gamma(Z_a,\mathcal O_{Z_a})$.

Cited nodes: lem-weil-pbc-affine-algebra-local-maps, lem-weil-pbc-scheme-morphism-gluing, lem-weil-pbc-affine-morphism-relative-spec, lem-weil-pbc-morphism-into-affine-scheme.

### Old step 5

Each $j_a$ is an open immersion by [lem-trf-quasi-affine-canonical-affine-embedding], so the composite $Z_a\hookrightarrow Z\xrightarrow{c}Y$ is an open immersion into the open subscheme $Y_a$. To check that $c$ is injective on points, suppose $c(z)=c(z')=y$. Since $\pi c=h$, both $z$ and $z'$ map to $\pi(y)\in S$. Choose $a$ with $\pi(y)\in S_a$. Then both points lie in $Z_a$, and injectivity of $j_a$ gives $z=z'$. Thus $c$ is injective on points. Therefore [lem-weil-pbc-open-immersion-injective-local-source] makes $c$ an open immersion. It is quasi-compact: $Z_a=c^{-1}(Y_a)$ is quasi-compact, while $Y_a$ is affine and hence quasi-separated by [lem-weil-pbc-affine-scheme-qcqs], so [lem-weil-pbc-qcqs-morphism-permanence](1) makes $c|_{Z_a}:Z_a\to Y_a$ quasi-compact; [lem-pc-quasi-compact-local-on-target] then makes $c$ quasi-compact.

Cited nodes: lem-trf-quasi-affine-canonical-affine-embedding, def-weil-open-immersion, lem-weil-pbc-open-immersion-injective-local-source, lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-qcqs-morphism-permanence, lem-pc-quasi-compact-local-on-target.

### Old step 6

For any affine open $U\subseteq S$, the relative-Spec chart in [lem-weil-pbc-affine-morphism-relative-spec](2) makes $Y_U=\pi^{-1}(U)$ affine. Since $c$ is a quasi-compact open immersion and $\pi c=h$, the inverse image $h^{-1}(U)=c^{-1}(Y_U)$ is a quasi-compact open subscheme of the affine scheme $Y_U$. By [def-nagata-quasi-affine-morphism], this is exactly that $h$ is quasi-affine.

Cited nodes: lem-weil-pbc-affine-morphism-relative-spec, def-weil-open-immersion, def-nagata-quasi-affine-morphism, def-weil-finite-type-morphism.

## Not duplicates

lem-a1-relative-affinization-compatible-charts vs lem-weil-pbc-affine-morphism-relative-spec: the existing node constructs the relative spectrum and the anti-equivalence for affine S-schemes, but not the compatible canonical maps from an arbitrary qcqs non-affine source.

lem-a1-relative-affinization-compatible-charts vs lem-weil-pbc-affine-structure-algebra-fully-faithful: the existing node is full faithfulness with both source and target affine over S; the new chart node constructs maps from an arbitrary qcqs source into its relative affinization and specifies compatibility and identity chart maps.

lem-a1-relative-affinization-compatible-charts vs lem-trf-quasi-affine-relative-spec-embedding: the existing node is the equivalence between a quasi-affine morphism and existence of some open embedding in a relative spectrum; the new chart node works for every qcqs morphism, and the new gluing node works for arbitrary compatible local embeddings without assuming global quasi-affineness.

lem-a1-affine-base-open-immersion-gluing vs lem-a1-ind-quasi-affine-permanence: the existing node treats ind-quasi-affine permanence for all compact opens; the new gluing node assumes an affine-over-base target and compatible local open immersions and constructs their global map.

lem-a1-affine-base-open-immersion-gluing vs lem-a1-quasi-affine-target-locality: the parent states the local-cover equivalence for quasi-affineness; the new node is a proper intermediate construction and does not assert either implication of that equivalence.

lem-a1-affine-base-open-immersion-gluing vs lem-trf-quasi-affine-base-change: the existing node is stability of quasi-affine morphisms under arbitrary base change; the new gluing node constructs a global quasi-compact open immersion from compatible local maps.

lem-a1-affine-base-open-immersion-gluing vs lem-trf-quasi-affine-relative-spec-embedding: the existing node is the equivalence between a quasi-affine morphism and existence of some open embedding in a relative spectrum; the new chart node works for every qcqs morphism, and the new gluing node works for arbitrary compatible local embeddings without assuming global quasi-affineness.

lem-a1-relative-affinization-compatible-charts vs lem-weil-pbc-affine-algebra-local-maps: the existing node supplies compatible maps from an algebra homomorphism with a specified affine target; the new node must first construct the quasi-coherent direct-image relative spectrum and identify its local maps with the identity-section canonical maps.

lem-a1-affine-base-open-immersion-gluing vs lem-weil-pbc-scheme-morphism-gluing: ordinary gluing supplies a unique morphism, but does not prove it a quasi-compact open immersion or its required global injectivity.

lem-a1-affine-base-open-immersion-gluing vs lem-weil-pbc-open-immersion-injective-local-source: the existing criterion assumes a globally injective map; the new node constructs that map, proves injectivity using the over-base equations, and also proves quasi-compactness.

lem-a1-affine-base-open-immersion-gluing vs lem-galois-fpqc-descend-open-immersion: the existing node descends open immersion of a pre-existing morphism along an fpqc cover; the new node constructs a morphism from compatible chart maps and proves quasi-compactness from compact sources and affine target charts.
