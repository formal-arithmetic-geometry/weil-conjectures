# Worker report — Q56

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-a1-quasi-affine-open-affinization-square.json`: existing statement, unchanged; split repaired into four assembly steps (1829 characters).
- `dag/nodes/sec-purity-real-sheaves/lem-a1-quasi-affine-open-principal-comparison-cover.json`: new statement, status unsplit, no Mathlib match. A common chart family and its three ambient identifications; no proof steps.
- `dag/nodes/sec-purity-real-sheaves/lem-a1-affine-principal-affinization-isomorphism.json`: new statement, status unsplit, no Mathlib match. Tag 01P8 with the canonical restriction-and-division map specified; no proof steps.
- `citations.json`: verbatim statement quotations for every parent step/node pair. `searches.jsonl`: actual msearch records. `returned-baseline.json`: read-only repository baseline retained locally for comparison, not a delivery file.

## Attachments

None. Searched the live `lean/WeilConjectures/` by item tag, quasi-affine names, affinization, and canonical-principal-open names. The project's `lean/Sheaf/AlgebraicGeometry/QuasiAffineOpenAffinizationSquare.lean` states the item at `AlgebraicGeometry.Scheme.isPullback_toSpecΓ_of_isOpenImmersion` but its whole proof is `sorry`. The source library's quasi-affine results concern relative quasi-affineness, affine-space embeddings and compactifications; they do not state this square. A section-fraction theorem is not the scheme-isomorphism assertion of the new chart node.

## WANTED

None. All geometric sources are available in `literature/stacks-project/`.

## Repair of the return

The return requires at least two comparable new work items, delivered statement-only, and a parent assembly of at most 3000 characters. The sandbox initially contained only dispatcher marker files: no earlier JSON, report, citations or search log existed to resume. I copied the current shared-repository node (whose six proof texts are exactly the returned 3778-character proof) and retained all its fields, original statement and original search records. No git command was run in the shared repository. This is a substantive decomposition, not a rebase-only delivery.

Old steps 1–3 (1427 characters) are the common-principal-comparison-cover work item: canonical-map commutativity, open image H, distinguished opens inside H, affine opens V_g inside u(U), the equality U_r(g)=u^{-1}(V_g), the isomorphisms induced by the open immersion, coverage, and q^{-1}D(g)=D(r(g)). Its statement does not assert the parent's inverse-image equality, nor cartesianness; U is allowed to be non-quasi-compact. The old step-1 use of U being qcqs and j_U open stays in parent step 1 through the existing canonical-embedding lemma.

Old step 4 (1203 characters) is the affine-principal-affinization-isomorphism work item. It concerns an arbitrary qcqs scheme X with a single affine X_f, with no open immersion U into V in its hypotheses. It must compare the fraction map, the actual canonical scheme morphism, and an inverse on affine spectra. The parent uses the resulting isomorphism, rather than redoing this argument. The new node is strictly smaller than the parent, independent of the cover construction, and neither new node cites the parent.

Old steps 5–6 (1148 characters) remain the parent's union calculation, restricted structure-sheaf identification, identity on U, and explicit test-scheme universal property. The source's local-to-global argument has not been omitted. The full old proof is retained below, with its allocation, so every argument remains available to the workers. No new proof step is longer than 2000 characters.

## Not duplicates

lem-a1-quasi-affine-open-principal-comparison-cover vs lem-a1-quasi-affine-open-affinization-square: both use Stacks 0ARY, but the new node constructs and identifies the common affine chart family for an arbitrary open U in quasi-affine V; it gives neither the global inverse-image equality nor the cartesian square, and assumes no quasi-affineness of U.
lem-a1-quasi-affine-open-principal-comparison-cover vs lem-a1-intersection-canonical-affine-embedding: that node constructs the canonical locally ringed-space embedding for an intersection E of quasi-compact opens in a scheme Y whose quasi-compact opens are quasi-affine; the new node concerns a single open immersion and an adapted chart family, with no intersection E or inverse-image sheaf on E.
lem-a1-quasi-affine-open-principal-comparison-cover vs lem-trf-quasi-affine-canonical-affine-embedding: the existing node gives the canonical embedding and qcqs property of one scheme; it does not provide the chart family adapted to u(U), the restrictions to U, or the comparison under Spec(r).
lem-a1-affine-principal-affinization-isomorphism vs lem-sc-p1-invertible-section-localization: the existing theorem gives an isomorphism of sections from degree-zero localization of a graded module; the new node gives an isomorphism of schemes for the canonical morphism restricted to an affine principal open, including comparison with that ring isomorphism. The existing theorem is the ring-theoretic input, not a duplicate scheme-level assertion.
lem-a1-affine-principal-affinization-isomorphism vs lem-sc-affine-open-section-fraction-localization: that node works over an ambient affine open and identifies additive section-fraction presentations for arbitrary modules; the new node allows nonaffine qcqs X and identifies a canonical scheme morphism with D(f).
lem-a1-affine-principal-affinization-isomorphism vs lem-coef-infinity-mapping-excision: the apparent common string 01P8 denotes a Kerodon tag about mapping spaces in the existing node, whereas the new node cites Stacks 01P8 about schemes.
lem-a1-affine-principal-affinization-isomorphism vs lem-coef-infinity-isofibration-exponentiation: again the existing node's 01P8 is a Kerodon tag, about functor quasicategories and fibrations, not the Stacks affine-principal-open lemma.

I searched the whole DAG by 0ARY, 01P8, canonical/principal-open/affinization wording and the source labels. I read the relevant returned matches; the affine-cap dictionary is about invertible modules on an already affine scheme, and the Proj chart nodes concern a different target and ampleness hypotheses. Whole-blueprint searches were made with `tools/blueprint_refs.py search` for quasi-affine, localization, principal, affine principal, affinization and invert-f-affine. None states either new node. `ancestor` gives lem-a1-affine-hc0; both new `from.via` lists extend the parent's existing list by the parent item. The main-20261015 ancestor remains the H_c^0 vanishing statement; this is inherited geometric support, not a replacement of a Rankin–Selberg unit step.

## Mathlib search assessment

Every new node has LeanFinder, Loogle, grep and LeanSearch queries run through the required msearch command and recorded with their exact query text. Both have a second semantic phrasing. Every hit was inspected by type, with relevant source read in QuasiAffine.lean, AffineScheme.lean, Morphisms/QuasiSeparated.lean and Morphisms/Affine.lean. No unavailable service has been treated as absence.

For the cover node, `IsQuasiAffine.isBasis_basicOpen` (QuasiAffine.lean:60–72) and `openCoverBasicOpenTop` (:103–110) give a basis and a cover of V. They do not choose the subfamily D(g) contained in H or identify its lifts through u and Spec(r). Those are separate comparisons and use the canonical embedding and affine-spectrum pullback formulas. This is not an exact declaration or a one-line specialization.

For the principal-chart node, `isIso_ΓSpec_adjunction_unit_app_basicOpen` (Morphisms/QuasiSeparated.lean:450–464) gives a section-ring isomorphism. `IsAffineOpen.fromSpec_toSpecΓ` (AffineScheme.lean:459–461) gives compatibility with the spectrum of sections of an affine open. Identifying that spectrum with D(f), identifying the actual restricted morphism, and exhibiting the inverse scheme morphism still requires an argument. Thus the complete scheme-isomorphism statement is unsplit, with these component results logged rather than falsely called an exact match. The previous review specifically removed an ordinary section-map leaf as redundant; this repair does not reintroduce that leaf.

The item's searches again find `isPullback_toSpecΓ_toSpecΓ` and `preimage_opensRange_toSpecΓ` (QuasiAffine.lean:115–150). They assume the morphism is affine and have bottom-left V; the item has bottom-left U and left identity. An open immersion of quasi-affine schemes can be nonaffine, as A² minus the origin into A² shows. `IsOpenImmersion.isPullback` (OpenImmersion.lean:767–776) is a generic criterion requiring the image-preimage equality we prove.

## Review by Q56

I read the item against Stacks `properties.tex`, Tag 0ARY (`lemma-cartesian-diagram-quasi-affine`), including its unusual bottom-left U and left identity. I read Tag 01P8 (`lemma-invert-f-affine`) for the new principal-chart node and Tag 01P9 (`lemma-quasi-affine`) for the cover's canonical embedding; the tag/label mappings were checked in `tags/tags`. I also read the degree-zero localization statement and fraction formula in 01PW (`lemma-invert-s-sections`) supporting old step 4. This preserves the existing proof route and no SGA source is used.

For parent step 1 I read the entire new cover statement: it explicitly supplies commutativity, coverage by D(g) inside H, the equalities U_r(g)=u^{-1}(V_g) and q^{-1}D(g)=D(r(g)), and the affine isomorphisms. I separately opened `lem-trf-quasi-affine-canonical-affine-embedding`: its statement supplies qcqs and the open immersion j_U under exactly U's given quasi-affineness. `def-weil-open-immersion` describes an isomorphism onto an open subscheme, so composition here needs only composition of the two given isomorphisms and inclusion of their open images.

For parent step 2 I read the full new principal-chart statement. The hypotheses are qcqs U (step 1), a global section r(g), and affine U_r(g) (the cover statement), so the induced canonical map really is the isomorphism to D(r(g)) asserted there. The remaining equalities are preimage and image of unions; the index I covers both H and U, as the new cover statement expressly requires. There is no use of an unspecified localization isomorphism in place of the canonical map.

For parent step 3, `def-weil-open-immersion` identifies both the topology and restricted structure sheaf; an equality of open subsets therefore identifies the open subschemes. Commutativity, supplied in step 1, shows the induced map is the identity under the two identifications with U. For parent step 4, I opened `def-pc-fibre-product`, which states exactly the test-scheme existence and uniqueness property. The only further input is the open-subscheme description in `def-weil-open-immersion`: restrict b to the inverse-image open and cancel the isomorphism U to H. This works for arbitrary T; it does not rely on an unjustified pointwise lifting through a general immersion. Citations.json contains literal quotations from each of these statements.

I checked the new statements without assuming U or V is nonempty. For U empty, H and all relevant opens are empty, and the cover assertions are vacuous (I can contain nilpotent g with D(g) empty). For the chart node f=0, X_f and D(f) are empty and both section rings are zero; for a unit f the assumption X_f affine forces X affine and the conclusion is its canonical affine-spectrum isomorphism. The zero ring and nilpotent f cause no exceptional case. No finite type, Noetherian, affine-morphism, or affineness of U was added. In particular the nonaffine quasi-affine example does not invalidate either new statement.

The review of B–E found and corrected the coarse split, rather than changing the item statement. Both new statements introduce all objects, define quasi-affine/principal-open/quasi-separated terminology inline or cite the exact definition, have no proof or proof dependencies, and carry source labels and searched blueprint references. They are independent, acyclic subarguments; neither restates a clause of the original conclusion. The parent keeps the actual global assembly, not merely “apply a new theorem”. The elementary final steps are justified explicitly, not labelled elementary while hiding localization or an open-immersion theorem. There are no unproved claims inserted into definitions and no Lean changes or compiles.

## Preserved argument and allocation

The following are the six proof texts of the returned repository node, preserved verbatim. Steps 1–3 allocate to the new cover node except for the canonical-embedding assertion for U retained in parent step 1. Step 4 allocates to the new principal-chart node, with its variable U replaced by general X. Steps 5–6 allocate to parent steps 2–4. These paragraphs are the retained work brief, not proof fields on the new unsplit nodes.

### Returned step 1

Write $q=\operatorname{Spec}r$. The morphisms $q\circ j_U$ and $j_V\circ u$ correspond to the same homomorphism $r:B\to A$: the canonical maps induce identities and the map induced by $u$ is restriction. Thus [lem-weil-pbc-morphism-into-affine-scheme] gives $q\circ j_U=j_V\circ u$. By [lem-trf-quasi-affine-canonical-affine-embedding], both $j_U$ and $j_V$ are open immersions and both schemes are quasi-compact and quasi-separated. In particular $j_V\circ u$ identifies $U$ with an open subscheme $H\subseteq\operatorname{Spec}B$.

Cited statements: lem-weil-pbc-morphism-into-affine-scheme, lem-trf-quasi-affine-canonical-affine-embedding, def-weil-open-immersion.

### Returned step 2

Apply the basis assertion of [lem-weil-pbc-spec-localization-away-basic-open] to the open $H$. The opens $D(g)\subseteq H$, for $g\in B$, cover $H$. Their inverse images under $j_V$ are $V_g$, by [lem-weil-pbc-morphism-into-affine-scheme]. The identification of $V$ with its image in step 1 identifies $V_g$ isomorphically with $D(g)$. By clause (0) of [lem-weil-pbc-affine-ideals-closed-subscheme], $D(g)$ is affine, so $V_g$ is affine, lies in $u(U)$, and these $V_g$ cover $u(U)$.

Cited statements: lem-weil-pbc-spec-localization-away-basic-open, lem-weil-pbc-morphism-into-affine-scheme, lem-weil-pbc-affine-ideals-closed-subscheme.

### Returned step 3

For each $g$ chosen in step 2 put $f=r(g)$. By [lem-weil-pbc-basic-open-pullback], $u^{-1}(V_g)=U_f$. Since $V_g\subseteq u(U)$, the given open immersion identifies $U_f$ with all of $V_g$. Hence $U_f$ is affine, and these opens cover $U$. Moreover [lem-weil-pbc-morphism-into-affine-scheme], applied to $q$ and the element $g$, gives $q^{-1}(D(g))=D(f)$. The pullback section is $f$ since $q$ is induced by $r$.

Cited statements: lem-weil-pbc-basic-open-pullback, lem-weil-pbc-morphism-into-affine-scheme.

### Returned step 4

The inverse image of $D(f)\subseteq\operatorname{Spec}A$ under $j_U$ is $U_f$ by [lem-weil-pbc-morphism-into-affine-scheme]. Apply [lem-sc-p1-invertible-section-localization] with $X=U$, $\mathcal L=\mathcal F=\mathcal O_U$, and $s=f$: $U$ is qcqs by step 1, and the structure module is quasi-coherent and free of rank one. Its tensor powers identify with $\mathcal O_U$. Its degree-zero fractions are ordinary fractions $a/f^n$: equality is exactly $f^k(f^m a-f^n b)=0$ for some $k\geq0$. The cited map is therefore the bijection $A_f\to\Gamma(U_f,\mathcal O_U)$ sending $a/f^n$ to $a|_{U_f}/f|_{U_f}^n$. By clause (0) of [lem-weil-pbc-affine-ideals-closed-subscheme], $\Gamma(D(f),\mathcal O)=A_f$ compatibly with restriction. The section ring map of $j_U|_{U_f}$ is this bijection: it is the identity on global sections of $U$ and hence has the displayed value on every fraction. Thus it is a ring isomorphism. Both $U_f$ (step 3) and $D(f)$ (clause (0)) are affine. Use [lem-weil-pbc-morphism-into-affine-scheme] to realize the inverse ring homomorphism as an inverse scheme morphism; the composites induce identity ring maps and hence are identities by that bijection. Consequently $j_U(U_f)=D(f)$.

Cited statements: lem-weil-pbc-morphism-into-affine-scheme, lem-sc-p1-invertible-section-localization, lem-weil-pbc-affine-ideals-closed-subscheme.

### Returned step 5

Taking unions in the equalities of steps 2–4 gives $q^{-1}(H)=\bigcup_g q^{-1}(D(g))=\bigcup_gD(r(g))=\bigcup_gj_U(U_{r(g)})=j_U(U)$. Because $j_U$ is an open immersion [def-weil-open-immersion], this equality identifies the inverse-image open subscheme, including its restricted structure sheaf, with $U$. The restricted morphism to $H$ agrees with $j_V\circ u$ by the commutativity in step 1, so under the two identifications with $U$ it is the identity.

Cited statements: def-weil-open-immersion.

### Returned step 6

For completeness check the fibre-product universal property [def-pc-fibre-product]. Given a scheme $T$ and $a:T\to U$, $b:T\to\operatorname{Spec}A$ with $(j_V\circ u)\circ a=q\circ b$, the image of $b$ lies in $q^{-1}(H)=j_U(U)$. The description of an open subscheme in [def-weil-open-immersion] restricts $b$ uniquely to $c:T\to U$ with $j_U\circ c=b$ (restrict its structure-sheaf map to this open). Commutativity then gives $(j_V\circ u)\circ c=(j_V\circ u)\circ a$; this open immersion is an isomorphism onto $H$, so $c=a$. This is exactly the unique factorization through the displayed top-left $U$ with its left projection $\mathrm{id}_U$. It proves that the stated square is cartesian.

Cited statements: def-pc-fibre-product, def-weil-open-immersion.

## Unfinished work

The two new nodes intentionally remain unsplit for separate workers, as required by the return. No gap remains in the parent assembly beyond its cited nodes. The first required server dry run passed preflight at 0f4f2c9939e. After correcting the duplicate-comparison description against the current intersection node, the final dry run and push follow this signed review.
