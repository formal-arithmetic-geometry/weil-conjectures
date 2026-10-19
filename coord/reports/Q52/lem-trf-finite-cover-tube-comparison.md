# Report: lem-trf-finite-cover-tube-comparison

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-finite-cover-tube-comparison.json`: repaired split; the statement now explicitly defines all lifted oriented points.
- `dag/nodes/sec-trace-formula/lem-trf-finite-base-strict-localization.json`: new statement-only scheme lemma, unsplit; no Mathlib match and no Lean attachment.
- `item.json`: synchronized item copy.
- `citations.json`: verbatim node-statement quotations for every dependency of every proof step.

## Attachments

None. Searches of `WeilConjectures/` in `/home/ubuntu/weil-src-slopmaster2` for the item's blueprint tag, finite/Milnor terminology, and finite/strict-henselization terminology found no project declaration stating the item or the new lemma exactly. The source's sorry declarations would not count as attachments.

## WANTED

WANTED: `literature/orgogozo-modifications-cycles-proches.pdf`, Lemmas 2.6 and 2.6.1, printed pp. 4–5, for this item. The retained source URL and earlier online citation are preserved. I did not obtain a local archival copy, and the item's proof remains marked `proof_origin.by: agent`. The repair is checked against the locally available Stacks sources named below.

## Returned points repaired

1. **E3/E4, finite factors at the wrong point.** The retained Step 2 decomposed $P_q$ directly over $S_0$ and incorrectly indexed its local factors by the geometric fibre over $b$. The review's counterexample is valid: over a strictly henselian DVR $R$, the ramified double cover $R[s]/(s^2-t)$ can be local although its geometric generic fibre has two points. The corrected step first decomposes $S_{(b)}\times_{S_0}P_q$, whose factors are indexed by that fibre. The finite factors of $P_q$ over the closed point of $S_0$ are used separately to define $H_{q,i}$ and $a_{q,i}$. Several $i$ can have the same $H_{q,i}$.

2. **E1/E4/C4, strict-base lemma used for a finite base change.** A new general scheme lemma supplies the finite strict-localization decomposition and the cartesian strict-localization square (Stacks 03QP/05WR/0GIP). The proof now derives
   $$(X_{P_q})_{(x_{q,i})}\simeq X_{(x)}\times_{S_0}(P_q)_{(a_{q,i})},$$
   retaining the finite local factor. Pullback along $c_{q,i}$ gives the desired tube, rather than falsely identifying $(X_{P_q})_{(x_{q,i})}$ with $X_{(x)}$. The old strict-base citation is used only for the actual strict-local base changes $X\times_SS_0\to X$ and $X_U\times_UU_0\to X_U$. Step 4 no longer applies it to $Q_q\to P_q$.

3. **E5/C4, unsupported naturality in restriction and slice-to-sections identification.** Step 1 has been rewritten as a counit chase on the site triples. A section on $E\times_VW$ is sent by the comparison to its pullback on the inverse image of the pulled-back triple. Restricting further to $N$ is the same as restricting first to $M$ and then along $N\to M$, since both maps have the same projections. The cited point-cohomology statement explicitly defines its isomorphism by these neighbourhood restriction maps. The equality is therefore for that specified isomorphism, then for its derived version on resolutions; no extra naturality theorem is assumed. `lem-trf-nearby-specialization-slice` has been removed from the proof dependencies, so the argument makes no unsupported identification of $i_a^*Rj_{b*}$ with $R\Gamma(M)$.

4. **B2, undefined lifts.** The statement defines $a,a_U$, the component points $p_i,p^U_j$, the local factors $H_{q,i},H^U_{q,j}$, their closed geometric points $a_{q,i},a^U_{q,j}$, the pairs $x_{q,i},x^U_{q,j}$, the factored strict-local maps $c_{q,i},c^U_{q,j}$, both oriented points, and both tubes. The residue-field clause in the new lemma ensures the unique closed lift with the field of $x$ or $x_U$. This is a statement clarification, with no hypothesis added or conclusion weakened.

## Review by Q52

I read the full return entry, the retained delivered item/report/search results, the current shared item, and its parent `lem-trf-nearby-finite-base-descent`. The parent's consumption is unchanged: it needs the actual ordinary comparison stalk, the finite-product decomposition, and Cech compatibility, rather than just abstract isomorphisms between cohomology objects. I read `SETUP.md`'s three levels, `GOAL.md`, `coord/dag-sync.md`, the chapter/unit records, and delivery-errors B–E. The unit route remains the normal-cone specialization input to `lem-trf-local-term-locality` through Orgogozo's finite-surjective descent.

For the new lemma I read `etale-cohomology.tex` at Tag 03QP, label `proposition-finite-higher-direct-image-zero`, including its proof: base change to a strict henselization is finite, the finite algebra splits into henselian local rings, and the residue fields are separably closed. I read `algebra.tex` at Tag 05WR, label `lemma-quasi-finite-strict-henselization`: a finite local map of strict henselizations, identified by localization of the tensor product, with finite purely inseparable residue extension. I read Tag 0GIP, label `lemma-base-change-strict-henselization-quasi-finite`, especially case (1): $B^{sh}\otimes_{A^{sh}}C^{sh}\simeq(B\otimes_AC)^{sh}$, with no finiteness condition on $A\to C$. Tag 04GH, label `lemma-finite-over-henselian`, supplies the finite algebra decomposition used in 03QP. These give the new lemma's two assertions for a finite $T\to S$ and arbitrary $Y\to S$. The lemma does not state a nearby-cycle or tube-comparison clause: reassociation and the tube construction stay in the item's proof. The new node has no proof or proof dependencies, and every notion has its definition citation, including finite purely inseparable extensions.

For Step 1 I opened the complete statements of `def-trf-oriented-nearby-cycles`, `lem-trf-oriented-point-cohomology`, `lem-weil-pbc-strict-henselization-functoriality`, and the fibre-product and strict-localization definitions. The nearby-cycle definition gives the actual counit transpose, not an unspecified base-change map. The point-cohomology node gives the affine-neighbourhood restriction construction and naturality in $K$ only. The step uses the construction to check the equality of maps on each triple, and hence on their stalk colimits and derived resolutions; it does not take extra restriction naturality from that node. Constant-$\Lambda$ module coefficients, exact inverse images and K-injective derived functors are the ones in those statements. No slice lemma is needed.

For Step 2 I opened `lem-trf-finite-radicial-basechange`, a Mathlib leaf whose statement explicitly gives both finite base change and composition. It establishes finiteness of $P_q,Q_q$. The new lemma's first clause is applied once at $b$ (the tube decomposition) and separately at the closed point $a$ (the local factors of $P_q$). Its second clause is applied with finite $P_q\to S_0$ and arbitrary $Y=X\times_SS_0$. I opened `lem-weil-pbc-strict-base-closed-point-localizations` and checked its strict-base and closed-geometric-point hypotheses exactly for $S_0=S_{(f(x))}$; here it gives the localization of $Y$ as $X_{(x)}$. No such invocation is made with a merely finite base. The cancellation after pullback to $(P_q)_{(p_i)}$ is the fibre-product universal property. The argument is repeated with the four specified substitutions on the $U$ side. Lifting the closed point uses the finite purely inseparable residue extension: a power equation has a unique root in an algebraically closed field (in characteristic zero the extension is trivial).

Step 3 is the elementary finite-disjoint-union computation. Module complexes on finitely many disjoint components form a product category; sections are the product functor, and finite products are exact. Derived sections and all restriction maps consequently decompose as asserted.

For Step 4 I opened `lem-trf-finite-base-cech-components`; it states exactly the projection-induced geometric-component bijection for a finite morphism and arbitrary base change. It does not supply a cohomology comparison. The step itself checks the local-factor maps: the inverse image of an open-and-closed factor is open and closed, the source factor is connected, and the local base map takes closed points to closed points. Thus the lifted points and factored structural maps commute. The isomorphisms in the new lemma preserve projections, so the component tube map is the same fibre-product map as in Step 1. Cech projections and repeated coordinates give equal projections for each composite, and uniqueness gives equality of the maps. Only then are derived sections applied. The same strict-localization functoriality statement used in Step 1 supplies these maps.

I tested the new scheme lemma and its applications on the review's ramified DVR example, on a split two-point cover, on a purely inseparable field extension (one factor, which need not equal the base), on a nonreduced finite algebra such as $k[\epsilon]/(\epsilon^2)$, on a closed immersion with a nontrivial kernel, and on an empty finite fibre. The ramified example now has two generic factors but a single closed local factor, as required. Also checked $q=0$, identity base change, empty tube, and zero coefficient complex. None requires reducedness, etaleness, properness, or smoothness. All proof steps are shorter than 2000 characters; the comparison chase and factor reassociations remain the item's argument.

I searched the full DAG by 03QP, 04GH, 05WR, 0GIP, finite/strict-localization terms, and the source declarations, and ran `tools/blueprint_refs.py search` for the tags and the geometric statement. No existing node states the full finite scheme decomposition and the finite cartesian strict-localization square. The existing ind-etale, strict-base, and closed-immersion lemmas have different hypotheses; none covers the ramified finite case. The source-tag pairs are distinguished below. The new lemma's Mathlib searches were rerun under the assigned item's log after the first dry run correctly rejected the entries logged under a different item. The exact results, including the unknown-identifier Loogle response, are now recorded with their actual query texts; two distinct semantic phrasings were inspected. The original item's searches and their results are retained, and a second phrasing is added.

The generic off-unit tool uses are declared in `split_report.tool_uses`: strict-henselization functoriality, and the strict-base lemma used only for actual strict-local base changes. The finite permanence lemma is already a Mathlib leaf. There is no SGA source in this repair.

## Not duplicates

lem-trf-finite-base-strict-localization vs lem-sbc-closed-coefficient-source-transition-iso: the existing assertion concerns a closed-coefficient transition in higher direct images; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-sbc-finite-strict-henselian-algebra-etale-section: the existing assertion produces a section of a surjective etale map over a finite algebra; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-sbc-closed-coefficient-target-transition-iso: the existing assertion concerns a closed-coefficient target transition in higher direct images; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-fd-finite-etale-adic-cohomology: the existing assertion concerns cohomology and coefficient realizations for finite etale maps; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-trf-closed-immersion-strict-localization-cartesian: the existing assertion is restricted to closed immersions; ramified finite covers need not be closed immersions; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-trf-ind-etale-strict-local-invariance: the existing assertion requires an ind-etale map and identifies the strict-local map with an isomorphism; finite ramified maps are not ind-etale and retain a nontrivial factor; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs sk-lem-geo-finite-boundary: the existing assertion detects constructibility and isomorphisms with a proper map and finite boundary; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-zl-finite-adic-direct-image: the existing assertion is t-exactness and a sheaf-stalk decomposition for finite maps over a finite field; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-a1-finite-weil-sections-decomposition: the existing assertion decomposes cohomology of a finite finite-field scheme and describes Frobenius; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-a1-finite-etale-weil-fibre-comparison: the existing assertion identifies a Weil-sheaf stalk with finite-fibre cohomology and Frobenius; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-weil-pbc-finite-pushforward-unit-edge-compatibility: the existing assertion compares unit and edge maps for direct-image cohomology; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-weil-pbc-ind-etale-affine-strict-local-base-change: the existing assertion requires an affine ind-etale base map, unlike the finite ramified factor here; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-weil-pbc-finite-split-pieces-cofinal: the existing assertion is initiality of the piece functor on pointed etale neighbourhoods; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs sk-lem-pbc-finite: the existing assertion is the finite pushforward stalk formula, exactness and cohomological base change; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-weil-pbc-finite-over-henselian-local-product: the existing assertion is an algebraic product decomposition and does not identify its scheme factors as strict localizations or give their cartesian square; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-weil-pbc-finite-surjective-unit-mono: the existing assertion is injectivity of an adjunction unit on sheaves; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-weil-pbc-sets-finite-pushforward-stalk-map-bijective: the existing assertion is bijectivity of a sheaf-of-sets stalk map; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-weil-pbc-sets-finite-pushforward-stalk-fiber-finite: the existing assertion only states finiteness of the geometric fibre; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs g1-finite-pushforward-pullback-comparison: the existing assertion compares cohomology pullback maps for torsion sheaves on curves; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-weil-pbc-strict-base-closed-point-localizations: the existing assertion concerns a base change by a strict localization itself; it cannot be applied to a finite cover of that base; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-weil-pbc-finite-pushforward-cohomology: the existing assertion identifies the cohomology edge map for a finite direct image; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-weil-pbc-finite-split-sections-product: the existing assertion decomposes sections over split neighbourhoods; it does not identify the limit schemes or cartesian strict localizations; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-weil-pbc-finite-stalk-formula-restriction: the existing assertion is the abelian-sheaf stalk restriction product formula; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-weil-pbc-sets-finite-pushforward-stalk: the existing assertion is the sheaf-of-sets stalk restriction product formula; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs g1-finite-pushforward-cohomology-comparison: the existing assertion is a cohomology equivalence for torsion sheaves on curves; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-weil-pbc-finite-local-henselian: the existing assertion says a finite local algebra over a henselian ring is henselian; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-weil-pbc-finite-split-neighbourhoods-cofinal: the existing assertion is cofilteredness and initiality of split etale neighbourhoods; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs g1-finite-pushforward-coefficient-control: the existing assertion descends torsion and constructibility properties of sheaves; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-weil-pbc-sets-pushforward-stalk-strict-henselization: the existing assertion identifies sheaf-of-sets sections over the strict-base change, not its scheme decomposition or a strict-localization square; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-weil-pbc-sepclosed-finite-extension-unique-embedding: the existing assertion concerns field extensions and their embeddings, not schemes or strict-localization squares; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-weil-pbc-curve-assertions-dense-open: the existing assertion reduces eight curve-cohomology assertions to a dense open; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-weil-pbc-curve-assertions-finite-pushforward: the existing assertion transports eight curve-cohomology assertions along a finite map; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs lem-asd-supported-kummer-scalar-source: the existing assertion is a derived scalar-extension identification for a closed immersion; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.

lem-trf-finite-base-strict-localization vs sk-lem-curve-finite-support: the existing assertion is a cohomology and direct-image statement for sheaves on curves; the new statement gives the finite scheme decomposition into strict localizations and the cartesian strict-localization square.
