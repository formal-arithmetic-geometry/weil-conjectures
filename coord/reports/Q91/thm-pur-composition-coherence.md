# Worker report — Q91

Item: thm-pur-composition-coherence. Stage 1 only, 2026-10-22. Direct-delivery repair of the human's 2026-10-21 re-split instruction, applied on 2026-10-22.

## Files written

- dag/nodes/sec-smooth-purity/thm-pur-composition-coherence.json: statement unchanged; three-step assembly, 1897 characters instead of 11322.
- dag/nodes/sec-smooth-purity/lem-pur-composition-tensor-mate.json: statement, unsplit; no Mathlib match. Owns old Steps 1–3, 3385 characters: domains, specified exceptional mate, orientation-free tensor comparison and its two-counit verification.
- dag/nodes/sec-smooth-purity/lem-pur-composition-compatible-dnc-charts.json: statement, unsplit; no Mathlib match. Owns old Steps 4–6, 3061 characters: local diagonal assembly, simultaneous charts, tangent splitting, section pasting and the normalized DNC square.
- dag/nodes/sec-smooth-purity/lem-pur-composition-model-orientation-descent.json: statement, unsplit; no Mathlib match. Owns old Steps 7–9, 3267 characters: affine coordinate comparison, unit cases, canonical twist/shift identification and rank-one descent. The logical order within this package is 9,7,8.
- citations.json: verbatim statement excerpts for all eight step/node citation pairs in the parent.
- report.md: this report, substantive self-review and the full retained proof-work handoff below.

All three children have proof=[], proof_deps=[], proof_origin=null, status=unsplit. They are separate intermediate arguments; none asserts the final equality of purity maps for general K. Their statements have respectively 3101, 3695 and 3551 characters. They introduce their own coefficient datum, schemes, maps and domains. No Lean was changed or compiled.

## Attachments

None. I searched lean/WeilConjectures by the blueprint id and by composition/purity terminology. AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_comp in EtaleCohomology/Purity/Smooth/Basic.lean, line 281, asserts only existence of an isomorphism, not equality of the specified orientations or purity maps. Trace.lean assumes the composition identity when proving trace transitivity. The exact project statement WeilConjectures.PurityFiniteSetting.smoothPurityCompositionCoherence in lean/Sheaf/Paper/PurityCompositionCoherence.lean still has a sorry. It is not an attachment.

## WANTED

None. The current main-20261015 composition proof and its supporting orientation-chart, diagonal-dualizing and affine-composition proofs are present locally. No SGA source was used.

## What was wrong and what changed

The returned issue was the size and concentration of the proof, not a false target statement. I kept the parent statement byte-for-byte. The full ten-step argument has been partitioned into three comparable proof tasks, each delivered statement-only, and a final explicit substitution. This is not an unchanged push or a compressed restatement. All three new nodes are cited in the parent proof. Their statements include the actual maps and intermediate diagrams whose proofs are assigned to them; the detailed earlier arguments are retained verbatim below, not discarded.

The sandbox initially contained only dispatcher brief markers, with no DAG files, report or search log. As required I first tried the dry run; it exited with “no node files under .../dag/nodes/”. I restored the current repository version of the item into the sandbox and preserved its full prior metadata, proof, review, original citations and original search records in original-item.json. There was no sandbox work to overwrite. The delivery tool performs the current-main rebase in its temporary worktree; I do not run git in the shared clone.

There is inherited prose in def-pur-smooth-purity-map requiring separated X,Y, whereas the current target, current exceptional-functor definition, chart-normalization and section-pasting statements, and the already-reviewed Lean formulation work without absolute separatedness. This repair does not add absolute separatedness: all DNC and vector-bundle calculations take place on affine charts, as in the existing ten-step proof. The existing definition is used only for its explicit formula for the specified maps. No statement correction of this item is needed.

## What could not be finished

Nothing in the requested repair is left unresolved. The three child proofs are deliberately not supplied: their unsplit status is the human's explicit request so separate workers can undertake them. The final assembly is complete relative to their statements. Delivery verification is recorded at the end after the tool exits.

## Sources and division of the work

I read stages/1-dag.md, coord/brief-stage1.md, roles/worker.md, GOAL.md, the three blueprint levels in SETUP.md, and both copies of delivery-errors.md B–E. The fixed chapter record is sec-smooth-purity, with the inherited unit sk-thm-smooth-purity. I read that unit's two proof paragraphs, including the diagonal/DNC/vector-bundle route and agreement on the model; this item is not the unit's key statement, so no realization file is edited. I also read current sk-prop-sp-composition/_section.md and its item statement/proof. The current source is literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-composition/thm-pur-composition-coherence.proof.md, Steps 1–2. As it is an agent-written blueprint and the explicit expansions are agent work, proof_origin.by remains agent.

For the tensor-mate child I read that source's tensor-formula paragraph and sk-prop-cohsm/thm-pur-cohomological-smoothness.proof.md. I opened the statements of def-pur-co-smoothness, pur9-def-upper-shriek-composition, thm-sf-comp-composition, def-weil-pbc-composite-adjunction, def-weil-pbc-adjunction-conjugate, def-weil-exceptional-inverse-image, lem-sf-proetale-constructible-origin and fix-prop-projection-formula. They specify the exact tensor transpose, the direction and transpose of c, the pasted counit, the bounded-below witnessed domain, constructible finite-Tor preservation and the projection pentagon. The child requires the equality of the two actual transposes, not merely an unspecified isomorphism of endpoints. Its transpose is explicitly that of c sigma, because the composite adjunction lands in Rf^!Rg^!.

For the chart/DNC child I read the composition proof's twofold-diagonal and tangent-sequence paragraphs, sk-prop-sp-orientation/sk-prop-sp-orientation-charts.proof.md Steps 1–4, and thm-pur-diagonal-dualizing-object.proof.md Steps 1–2. I opened lem-pur-diagonal-dnc-chart-normalization in full, lem-pur-diagonal-section-pasting in full, sbc-thm-etale-local-normal-form, lem-pur-dnc-section-geometry and lem-pur-diagonal-regular-immersion. The new assertion is the simultaneous choice and comparison for f,g,gf, with the ordered split tangent sequence and the DNC square. Each alpha, delta, beta, kappa and nu is specified by an existing node; the statement does not choose arbitrary identifications of rank-one objects. In particular the coordinate normalization uses the actual source-coordinate and normal-bundle coordinate comparisons, not an unjustified trivialization of the DNC map.

For the model/descent child I read the same composition proof, the four steps of sk-prop-sp-composition/prop-pur-affine-space-composition-law.proof.md and the model agreement in lem-pur-projection-purity-agreement. I opened the statements of prop-pur-affine-space-composition-law, cor-pur-vector-bundle-purity, def-pur-affine-space-comparison, def-coefficient-twists-detailed, def-pur-composition-comparisons, det-prop-sfb-cartesian-coefficients-twists, lem-pur-twist-sheaf-locally-free, lem-weil-pbc-derived-single-fully-faithful and lem-pur-sheaf-hom-cover-gluing. The assigned work is to rewrite affine composition at K=Lambda using the tensor definition, pull it to the zero section, incorporate the rank-zero normalization, compare the diagonal assemblies, and descend their equality using the sheaf Hom uniqueness assertion. The sign is explicitly +1. This work is entirely below the fixed lecture-notes route.

## Searches and duplicate checks

I searched the whole DAG by the parent id, sigma, normalized DNC, compatible charts, orientation/composition and the concrete nu_{d,e} formula; I searched the whole imported blueprint with tools/blueprint_refs.py search for composition, tensor formula, diagonal, orientation, composition tensor, compatible etale, diagonal DNC and orientation composition. The exact ancestor command returns thm-pur-composition-coherence, so each child's from.node is that imported node and via=[]. Its from.place names the appropriate current proof paragraph and the old steps it now owns. No equivalent imported blueprint statement was found that can replace a whole child without circularity. same_as=[] on each child. Existing chart and pasting nodes are reused, not copied or edited.

Each new node has six real msearch.py calls: LeanFinder, Loogle, grep, LeanSearch, a second LeanFinder phrasing and another grep. All queries are preserved exactly in that node's mathlib_searches and searches.jsonl; the complete service outputs are in its *-search-results.txt. All eighteen service calls succeeded. Search-plan.json records which queries belonged to which child. LeanFinder and LeanSearch returned scheme-gluing, standard-smooth algebra, differential-manifold, generic adjunction and generic monoidal facts, not any of these purity statements. The direct source hits for Mathlib.CategoryTheory.Adjunction.comp_counit_app (Basic.lean:580) give only the pasted counit, and RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial (StandardSmooth.lean:253) gives only standard-smooth algebra coordinates. I read those declarations; neither proves the new node in one specialization. The rigid-monoidal tensor mate results concern chosen duals in an arbitrary rigid category, not these compact-support projection transposes. The final broad grep for Tate also matched “stated” and similar ordinary words, which are not twist declarations. No new node is a Mathlib leaf.

## Not duplicates

lem-pur-composition-tensor-mate vs thm-pur-cohomological-smoothness: the latter's composition clause gives no explicit sigma, transpose t, witnessed-domain/counit typing or equality of the two full composite transposes; this is the precise missing mate calculation rather than a repetition of smooth cohomological smoothness.
lem-pur-composition-tensor-mate vs lem-pur-co-smooth-composition: the existing node states stability and existence of a dualizing isomorphism, not the specified natural K-form identity or its transposes.
lem-pur-composition-tensor-mate vs lem-sf-composition-projection-mate: the existing node proves compact-support projection compatibility on a compactification triangle; it does not transpose to the three exceptional tensor maps, specify sigma, or give their domain and invertibility assertions.
lem-pur-composition-tensor-mate vs lem-pur-system-tensor-transpose-composition: the existing node concerns simultaneous normalized strict semilinear derived systems with extra section models and assumed projection and tensor inverses; evaluating such a system and identifying every finite-level map is additional work, not a one-line instance for an arbitrary intrinsic finite-level K. The new node states the standing finite-level constructible functors and verifies their typing, inverses and specified transposes.
lem-pur-composition-tensor-mate vs det-sp-composition-factors: that node includes both orientation and tensor conclusions in different finite-general-ring/tower categories and depends transitively on this item (det-sp-composition-factors -> det-sp-tower-gamma -> thm-pur-finite-coefficient-smooth-purity -> cor-pur-dualizing-object-purity -> thm-pur-composition-coherence). Citing it would be circular; the new result is orientation-free and has no dependency back to the parent.
lem-pur-composition-compatible-dnc-charts vs lem-pur-diagonal-dnc-chart-normalization: the existing lemma handles one smooth map and its individually chosen coordinates; the new lemma asserts simultaneous composable charts, splitting of the tangent sequence and the joint section/DNC square for the three morphisms.
lem-pur-composition-compatible-dnc-charts vs lem-pur-diagonal-section-pasting: the existing lemma defines kappa and its coordinate model without any orientation or DNC map; the new lemma additionally constructs compatible tangent frames and compares all three actual DNC maps with that kappa.
lem-pur-composition-compatible-dnc-charts vs lem-pur-diagonal-orientation-compatibility: the latter is compatibility under changing Z/l^r coefficients to Z/l^m for one smooth section; it gives no simultaneous charts for two morphisms and no composition comparison for arbitrary A_{E,n}.
lem-pur-composition-model-orientation-descent vs prop-pur-affine-space-composition-law: the existing theorem concerns affine projection maps with d,e>=1; the new lemma rewrites it as the unit-dualizing and zero-section comparison for all d,e>=0 and descends that comparison for arbitrary smooth f,g.
lem-pur-composition-model-orientation-descent vs det-sp-composition-factors: the new node gives the actual zero-section model calculation, canonical source factors, rank-zero cases and the rank-one detection assertion, only at A_{E,n}; it does not restate the complete K-form identity. The existing broad composition node is downstream of this item by the explicit path above, so cannot serve as a premise.
lem-pur-composition-model-orientation-descent vs lem-pur-twist-sheaf-locally-free: local rank-one structure alone does not assert affine multiplicativity, the orientation identity or its compatible-diagonal comparison.
lem-pur-composition-model-orientation-descent vs lem-pur-sheaf-hom-cover-gluing: the existing statement glues module-sheaf maps; the new work identifies the relevant derived quotient with such a map and identifies its chart restrictions with the normalized affine models.
lem-pur-composition-tensor-mate vs thm-pur-composition-coherence: only the orientation-free tensor equation is asserted, not equality of the three smooth purity maps; the final substitution still needs both other children.
lem-pur-composition-compatible-dnc-charts vs thm-pur-composition-coherence: only the local chart geometry and DNC comparison are asserted, with no orientation multiplication or K-form equality.
lem-pur-composition-model-orientation-descent vs thm-pur-composition-coherence: this node compares unit-dualizing orientations and source reassociations; the general-K tensor-mate identity, naturality expansion and cancellation remain separate.

## Review by Q91

I checked the returned requirement against the actual rewritten JSON: there are exactly three new unsplit statement nodes, not a single replacement for the entire proof, and the parent now has 1897 characters. The workload blocks are the original 3385-, 3061- and 3267-character arguments. The final K-form algebra remains in the parent. None of these new statements contains a proof sketch; their proof fields are empty, and the full former argument has a named owner in the handoff below. Thus the repair distributes work instead of erasing or blurring it.

For parent Step 1, I read the tensor-mate child's statement and checked that it asserts every fact the step uses: smooth dimension d+e, finite-Tor typing of Rg^!K, invertibility and exact direction of c, and the displayed natural equation with r_K. Its specified adjunctions use the bounded-below etale-origin domain, not a falsely assumed ambient right adjoint. The transpose of c sigma is t; applying the same two Hom bijections to the K-equation is its assigned substantive proof.

For parent Step 2, I read both new statements. The chart child supplies the covering compatible affine charts, actual alpha/kappa equation, actual normalized DNC square and restriction compatibility. The model/descent child assumes exactly these assemblies, then asserts the zero-section comparison, the local beta/delta identity and the resulting global orientation equality. It also fixes mu and I_K, including the ordered source factors and even-degree sign, so the parent does not silently choose a different endpoint isomorphism. Its global comparison uses a rank-one sheaf automorphism after removing a common shift; no claim is made that arbitrary derived morphisms form a sheaf or that isomorphism conservativity detects equality.

For parent Step 3, I opened def-pur-smooth-purity-map, def-coefficient-twists-detailed and def-pur-co-smoothness and checked their literal formulas: gamma is theta after 1 tensor inverse orientation after twist reassociation. Theta is the transpose of a natural projection/counit composite, so its naturality follows from the Hom bijection, without another geometric assertion. Write V=vartheta_f tensor f^*vartheta_g. The inverse orientation product has type V^{-1}mu^{-1}:Lambda_X(d+e)[2d+2e] -> omega_f tensor f^*omega_g. The orientation equation gives sigma V^{-1}mu^{-1}=vartheta_gf^{-1}; substituting it into the tensor equation yields c gamma_gf in the precise arrow order. The citation excerpts in citations.json are literal substrings of these statements, checked before writing the file.

I tested the three new statements at d=0, e=0 and d=e=0: the chart and normal-bundle frames become the rank-zero identity data and the affine comparison Gamma_P0 is the identity. I did not apply the d,e>=1 affine composition theorem in these cases; the old unit-law argument is assigned explicitly to the model child. I checked empty X: the chart cover can be empty, and its derived module category has only the zero object up to its unique maps, so detection and the orientation equality still hold. I checked the identity-morphism tower and the projections A^{d+e}_B -> A^e_B -> B: kappa is precisely the zero-section pullback of sigma, not an undefined “section sigma”. For arbitrary finite E, including ramified E and n=1, I used the already stated all-n extension of Gamma and the A_{E,n} normalization lemma, not the more restricted affine-line datum. All shifts are 2d and 2e and the sign is +1 even when ell=2. No affine-intersection assertion is needed: charts are shrunk individually, and Hom uniqueness uses sheaf descent on actual cover pullbacks. Normal-bundle statements are isomorphisms of derived section invariants and vector bundles, not per-cohomology surrogates.

I also checked B1–B10, C1–C8, D1–D5 and E1–E7 against the files. All new notions have inline definition or construction citations and matching stmt_deps; each new source names the current blueprint paragraph, not a guessed Stacks section number. This result has no Stacks tag of its own. Existing theorem statements, rather than their unpublished proofs, are the only cited interfaces. The package boundary is genuine: the first lemma has no orientation, the second has no affine orientation multiplication, and the third has no general-K purity composition equation. The parent performs the missing explicit substitution. I followed the fixed diagonal/DNC route and used no SGA. The main new dependency graph has edges from model/descent to the other two children and no edge back to the parent; downstream det-sp-composition-factors was expressly excluded to avoid its cycle. There is no parent proof step longer than 2000 characters. No off-unit theorem is newly applied by the parent: all three new nodes inherit its unit, and its remaining citations are definitions. Existing maintainer-owned metadata, including historical reviews and tool_uses, is preserved unchanged.

## Full retained proof-work handoff

The following is the complete earlier proof, retained verbatim step by step. The task owner is specified for each step; these arguments are handoff material in the report, not illicit proofs inside new unsplit nodes. References to old step numbers mean the steps in this handoff. Each future worker has both its self-contained statement and its assigned argument. The existing dependencies named in these passages were opened and their statements checked above; no new nodes were invented for those already existing tools.

### Original Step 1 — lem-pur-composition-tensor-mate

Domains and the composition comparison. Work with $\Lambda=A_{E,n}$ on the finite-type $k$-schemes of the purity conventions. By [lem-sbc-smooth-relative-dimension-permanence](2), $gf$ is smooth of relative dimension $d+e$. Its separatedness and finite type are preserved by composition, so the maps in [def-pur-smooth-purity-map] are defined. Let $\alpha_{g,f}:Rg_!Rf_!\xrightarrow{\sim}R(gf)_!$ be [thm-sf-comp-composition]. The adjunctions in [def-weil-exceptional-inverse-image] and [def-weil-pbc-composite-adjunction] give the composite adjunction, with counit $\varepsilon_g\circ Rg_!(\varepsilon_fRg^!)$. As specified in [pur9-def-upper-shriek-composition], define $c_{g,f}:R(gf)^!\to Rf^!Rg^!$ as the conjugate of $\alpha_{g,f}$. By [def-weil-pbc-adjunction-conjugate] it is an isomorphism; its transpose is $\varepsilon_{gf}\circ\alpha_{g,f}$. Finite-Tor preservation in [def-weil-exceptional-inverse-image] puts $Rg^!K$ and $\omega_g=Rg^!\Lambda_Z$ in $D^b_{ctf}$ whenever $K\in D^b_{ctf}(Z,\Lambda)$. Bounded constructible inputs have etale-origin witnesses by [lem-sf-proetale-constructible-origin](ii), so the compact-support composition is used on its stated witnessed domain.

Existing statements used: lem-sbc-smooth-relative-dimension-permanence, def-pur-smooth-purity-map, thm-sf-comp-composition, def-weil-exceptional-inverse-image, def-weil-pbc-composite-adjunction, def-weil-pbc-adjunction-conjugate, pur9-def-upper-shriek-composition, lem-sf-proetale-constructible-origin.

### Original Step 2 — lem-pur-composition-tensor-mate

The specified tensor comparison. Let $\theta_{h,K}$ be [def-pur-co-smoothness](2) and $\omega_h=Rh^!\Lambda$. For $h=f,g,gf$, [thm-pur-cohomological-smoothness](1) makes $\theta$ invertible. Define
$$\sigma=c_{g,f,\Lambda}^{-1}\circ\theta_{f,\omega_g}\circ\mathrm{sym}:\omega_f\otimes^LLf^*\omega_g\xrightarrow{\sim}\omega_{gf}.$$
This fixes the comparison underlying [lem-pur-co-smooth-composition]. With $r_K$ the canonical reassociation
$$L(gf)^*K\otimes^L\omega_f\otimes^LLf^*\omega_g\cong Lf^*(Lg^*K\otimes^L\omega_g)\otimes^L\omega_f,$$
the composition formula is
$$(*)\quad c_{g,f,K}\theta_{gf,K}(1\otimes\sigma)=\theta_{f,Rg^!K}(Lf^*\theta_{g,K}\otimes1)r_K.$$
Here pullback composition is [lem-weil-pbc-proetale-derived-pullback-composition]. The following step verifies this precise reading of the composition clause of [thm-pur-cohomological-smoothness](4).

Existing statements used: def-pur-co-smoothness, thm-pur-cohomological-smoothness, lem-pur-co-smooth-composition, lem-weil-pbc-proetale-derived-pullback-composition.

### Original Step 3 — lem-pur-composition-tensor-mate

Verification of $(*)$ by adjunction. Put $T_f=\varepsilon_{f,\Lambda}:Rf_!\omega_f\to\Lambda_Y$. Under $Rg_!Rf_!\dashv Rf^!Rg^!$, the transpose defining $\sigma$ is the map
$$Rg_!Rf_!(\omega_f\otimes Lf^*\omega_g)\xrightarrow{Rg_!\mathrm{PF}_f^{-1}}Rg_!(Rf_!\omega_f\otimes\omega_g)\xrightarrow{Rg_!(T_f\otimes1)}Rg_!\omega_g\xrightarrow{T_g}\Lambda_Z.$$
This follows by applying the hom bijections in [def-weil-pbc-composite-adjunction] to the specified transpose in [def-pur-co-smoothness], with $K=\omega_g$, and the defining mate in [pur9-def-upper-shriek-composition]. Transpose both sides of $(*)$ under that same composite adjunction. The right side first uses the inverse projection formula for $f$, then its counit, then those for $g$. On the left, naturality moves $\sigma$ through the inverse projection formula for $gf$; substitute the displayed transpose of $\sigma$. The composition pentagon and naturality in [fix-prop-projection-formula] identify the resulting inverse projection maps with the successive ones for $f,g$. Both transposes are therefore the displayed map tensored with $K$, after the same projection and tensor reassociations. The composite counit is $\varepsilon_g Rg_!(\varepsilon_f)$ by [def-weil-pbc-composite-adjunction]. The hom bijection gives $(*)$. No orientation enters this calculation.

Existing statements used: def-weil-pbc-composite-adjunction, def-pur-co-smoothness, pur9-def-upper-shriek-composition, fix-prop-projection-formula.

### Original Step 4 — lem-pur-composition-compatible-dnc-charts

Local orientation assembly. For $h=f,g,gf$, write $\vartheta_h:\omega_h\xrightarrow{\sim}\Lambda(m_h)[2m_h]$, with $m_f=d,m_g=e,m_{gf}=d+e$. Apply [lem-pur-diagonal-dnc-chart-normalization]: on affine source and target opens the specified orientation is $\beta_h\delta_h\alpha_h^{-1}$, and these assemblies restrict compatibly. Here $\alpha_h:C_h\to\omega_h$ is diagonal base change, $\delta_h:C_h\to C(\pi_{N_h},0)$ is normalized DNC, and $\beta_h$ is zero-section vector-bundle purity. We will prove
$$(\ast\ast)\quad\vartheta_{gf}\circ\sigma=\mu\circ(\vartheta_f\otimes Lf^*\vartheta_g),$$
where $\mu$ is the twist/shift identification constructed in Step 9. The cited lemma states the assembly and its coordinate-adjunction normalization for every $A_{E,n}$.

Existing statements used: lem-pur-diagonal-dnc-chart-normalization.

### Original Step 5 — lem-pur-composition-compatible-dnc-charts

Compatible charts. Apply [sbc-thm-etale-local-normal-form] to $g$ near $f(x)$ and then to $f$ near $x$. Shrink to affine opens $U\subseteq X$, $V\subseteq Y$, $Z'\subseteq Z$ with $f(U)\subseteq V$, $g(V)\subseteq Z'$ and etale charts $U\to\mathbf A^d_V$, $V\to\mathbf A^e_{Z'}$. This is possible at every $x$, hence the $U$ cover $X$. The composite chart $U\to\mathbf A^d_V\to\mathbf A^{d+e}_{Z'}$ is etale: its second arrow is the base change of the second etale chart, followed by the identification $\mathbf A^d_{\mathbf A^e_{Z'}}=\mathbf A^{d+e}_{Z'}$. The coordinates are the ordered blocks $(x_1,\ldots,x_d,y_1,\ldots,y_e)$. By [lem-pur-dnc-section-geometry](2) the corresponding coordinate differences carry the three diagonal sections to standard zero sections. Their normal bundles are the tangent bundles by [lem-pur-diagonal-regular-immersion]; in these frames the tangent maps are inclusion into and projection from $\mathcal O_U^d\oplus\mathcal O_U^e$. Thus the normal sequence is split with $N_{gf}=N_f\oplus f^*N_g$ on $U$. All bases and total spaces used for DNC here are separated finite-type $k$-schemes, since the chosen schemes are affine and the diagonal projections are separated.

Existing statements used: sbc-thm-etale-local-normal-form, lem-pur-dnc-section-geometry, lem-pur-diagonal-regular-immersion.

### Original Step 6 — lem-pur-composition-compatible-dnc-charts

The normalized DNC maps and the section decomposition. On a chart $U$ of Step 5, use the map $\kappa$ of [lem-pur-diagonal-section-pasting], which states
$$\alpha_{gf}\kappa=\sigma(\alpha_f\otimes Lf^*\alpha_g).$$
Its coordinate clause specifies $\kappa$ as $\nu_{d,e}$, the zero-section pullback of $\sigma_{q,P_e}$ for the standard projection tower over $U$; thus no undefined section version of $\sigma$ is used. By [lem-pur-diagonal-dnc-chart-normalization], the three $\delta$ maps, under these coordinate identifications, are $1_{D_d},1_{D_e},1_{D_{d+e}}$. The same frames identify the normal bundles with $\mathcal O_U^d$, $\mathcal O_U^e$, $\mathcal O_U^d\oplus\mathcal O_U^e$. Consequently, under these specific identifications,
$$\delta_{gf}\kappa=1_{D_{d+e}}\nu_{d,e}=\nu_{d,e}(1_{D_d}\otimes1_{D_e})=\nu_{d,e}(\delta_f\otimes Lf^*\delta_g).$$
This is the required compatibility of DNC with the decomposition on this chart: its two sides are the same explicitly defined morphism $\nu_{d,e}$. The normalization lemma supplies compatibility of the identifications with etale restriction.

Existing statements used: lem-pur-diagonal-section-pasting, lem-pur-diagonal-dnc-chart-normalization.

### Original Step 7 — lem-pur-composition-model-orientation-descent

The coordinate model and the orientation identity. Over $B=U$ let $P_r,z_r,D_r,\nu_{d,e}$ be as in Step 6. Write $b_r=Lz_r^*(\Gamma_{P_r,\Lambda}^{-1})$, with the twist restriction; these are exactly the zero-section bundle orientations by [lem-pur-diagonal-dnc-chart-normalization]. Use [prop-pur-affine-space-composition-law] at $K=\Lambda_B$. By [lem-pur-projection-purity-agreement] its affine maps are the smooth tensor-form maps on these projections. Substituting their definition [def-pur-smooth-purity-map] and the definition of $\sigma$ from Step 2, and cancelling the invertible $\theta_{q,\omega_{P_e}}$, rewrites this law as
$$\Gamma_{P_{d+e},\Lambda}^{-1}\sigma_{q,P_e}=\mu(\Gamma_{q,\Lambda}^{-1}\otimes Lq^*\Gamma_{P_e,\Lambda}^{-1}).$$
Here the orientation for $q$ is the base change of the rank-$d$ bundle orientation by [cor-pur-vector-bundle-purity]. Pull back along $z_{d+e}$ to get
$$b_{d+e}\nu_{d,e}=\mu(b_d\otimes b_e).$$
The affine composition theorem assumes $d,e\geq1$. If either is zero, the same identity is the unit law, since $\Gamma_{P_0,-}=1$ by [def-pur-affine-space-comparison] and rank-zero normalization is part of the chart lemma. Combine this $b$ identity with the explicit DNC identity of Step 6 to get $\beta_{gf}\delta_{gf}\kappa=\mu((\beta_f\delta_f)\otimes Lf^*(\beta_g\delta_g))$. Substitute the assembly $\vartheta_h=\beta_h\delta_h\alpha_h^{-1}$ of Step 4 and the $\alpha$ identity of Step 6. Cancelling $\alpha_f\otimes Lf^*\alpha_g$ proves $(**)$ on $U$. The even-shift sign in $\mu$ is computed in Step 9.

Existing statements used: lem-pur-diagonal-dnc-chart-normalization, prop-pur-affine-space-composition-law, lem-pur-projection-purity-agreement, def-pur-smooth-purity-map, cor-pur-vector-bundle-purity, def-pur-affine-space-comparison.

### Original Step 8 — lem-pur-composition-model-orientation-descent

From charts to $X$. Both sides of $(\ast\ast)$ are isomorphisms to $T=\Lambda_X(d+e)[2d+2e]$. Their quotient is an automorphism $h$ of $T$. The restriction assertions in [lem-pur-diagonal-section-pasting] and [lem-pur-diagonal-dnc-chart-normalization], and twist pullback in [det-prop-sfb-cartesian-coefficients-twists], identify its restrictions with the comparisons in Step 7. Hence $h|_U=1$ on the covering charts. By [lem-pur-twist-sheaf-locally-free] and the tensor-power definition [def-coefficient-twists-detailed], removing the common shift makes $T$ a rank-one sheaf in degree zero. Full faithfulness [lem-weil-pbc-derived-single-fully-faithful] makes $h$ a sheaf automorphism. The uniqueness clause of [lem-pur-sheaf-hom-cover-gluing] now gives $h=1$, proving $(\ast\ast)$ globally. For empty $X$ this is the unique morphism in the zero category, so no chart is required.

Existing statements used: lem-pur-diagonal-section-pasting, lem-pur-diagonal-dnc-chart-normalization, det-prop-sfb-cartesian-coefficients-twists, lem-pur-twist-sheaf-locally-free, def-coefficient-twists-detailed, lem-weil-pbc-derived-single-fully-faithful, lem-pur-sheaf-hom-cover-gluing.

### Original Step 9 — lem-pur-composition-model-orientation-descent

The canonical source identification. By [def-coefficient-twists-detailed], $\Lambda(m)$ is the $m$-fold tensor power of $\Lambda(1)$ for $m\ge0$, so associativity of tensor powers gives $\Lambda_X(d)\otimes\Lambda_X(e)\cong\Lambda_X(d+e)$; the twist-pullback isomorphism $Lf^*(\Lambda_Y(e))\cong\Lambda_X(e)$ is [det-prop-sfb-cartesian-coefficients-twists], and the pullback-composition $L(gf)^*\cong Lf^*Lg^*$ is [lem-weil-pbc-proetale-derived-pullback-composition]. The shifts combine as $[2d][2e]=[2d+2e]$; interchanging the two blocks of degrees $-2d,-2e$ carries the Koszul sign $(-1)^{(2d)(2e)}=+1$. Composing these gives $\mu:\Lambda_X(d)[2d]\otimes^LLf^*\Lambda_Y(e)[2e]\cong\Lambda_X(d+e)[2d+2e]$ and the canonical identification of the statement,
$$L(gf)^*K(d+e)[2d+2e]\cong Lf^*Lg^*K(d)[2d](e)[2e],$$
both natural in $K$.

Existing statements used: def-coefficient-twists-detailed, det-prop-sfb-cartesian-coefficients-twists, lem-weil-pbc-proetale-derived-pullback-composition.

### Original Step 10 — thm-pur-composition-coherence (short final substitution)

Transposition to the $K$-form. Let $K$ be in the domain of the purity maps in the statement, i.e. $K\in D^b_{ctf}(Z,\Lambda)$ as required by [def-pur-smooth-purity-map] for $\gamma_{g,K}$ and $\gamma_{gf,K}$. Then $Rg^!K\in D^b_{ctf}(Y,\Lambda)$ by the finite-Tor preservation of [def-weil-exceptional-inverse-image], so $\gamma_{f,Rg^!K}$ is defined. By [def-pur-smooth-purity-map] (with the middle arrow the inverse of $\vartheta$ of [thm-pur-diagonal-dualizing-object]) $\gamma_{h,M}=\theta_{h,M}\circ(1\otimes\vartheta_h^{-1})\circ\rho_{h,M}$, $\rho$ the twist reassociation of [def-coefficient-twists-detailed]. Using naturality of $\rho$ and of $\theta_f$ in the coefficient object (the tensor map is natural, being the transpose of a natural composite in [def-pur-co-smoothness](2)),
$$\gamma_{f,Rg^!K}\circ Lf^*(\gamma_{g,K})(d)[2d]=\theta_{f,Rg^!K}\circ(Lf^*\theta_{g,K}\otimes1_{\omega_f})\circ r_K\circ\bigl(1\otimes(\vartheta_f\otimes Lf^*\vartheta_g)^{-1}\bigr)\circ(\text{source identification of Step 9}).$$
By $(\ast)$ of Step 2 the first three factors equal $c_{g,f,K}\circ\theta_{gf,K}\circ(1\otimes\sigma)$, and by $(\ast\ast)$ of Step 8, $\sigma\circ(\vartheta_f\otimes Lf^*\vartheta_g)^{-1}=\vartheta_{gf}^{-1}\circ\mu$. With the identification of Step 9 the remaining factors are $(1\otimes\vartheta_{gf}^{-1})\circ\rho_{gf,K}$. Therefore $\gamma_{f,Rg^!K}\circ Lf^*(\gamma_{g,K})(d)[2d]=c_{g,f,K}\circ\gamma_{gf,K}$ under the canonical identification, i.e.
$$\gamma_{gf,K}=c_{g,f}^{-1}\circ\gamma_{f,Rg^!K}\circ Lf^*(\gamma_{g,K})(d)[2d],$$
the displayed composite, in the stated order.

Existing statements used: def-pur-smooth-purity-map, def-weil-exceptional-inverse-image, thm-pur-diagonal-dualizing-object, def-coefficient-twists-detailed, def-pur-co-smoothness.

## Validation

The initial required dry run exited because the retained sandbox had no node files. After reconstruction, the server review_split check passed. The first full delivery check required a longer literal excerpt for def-coefficient-twists-detailed; I expanded the quote to include its surrounding statement, without changing the mathematics. The next deliver.py --no-push exited 0 and printed OK (not pushed), at f28714768fd, with server preflight passed. The final report now records that result; the complete exact delivery is checked once more before pushing.
