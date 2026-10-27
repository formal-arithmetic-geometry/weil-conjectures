# Q125 stage-1 delivery

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-ordinary-unit-site-sections-transport.json`: item split, statement unchanged, five assembly steps (2228 characters in total); existing searches and provenance retained.
- `dag/nodes/sec-smooth-purity/lem-pur-site-derived-sections-unit-pasting.json`: one new statement-only lemma, unsplit; no Mathlib match. Generic derived-section unit/Leray pasting on small sites with constant coefficients.
- `citations.json`: eight verbatim statement quotations for the eight step-node pairs.

## Attachments

None. Searches of `lean/WeilConjectures/` for the item tag, ordinary-unit transport, section comparison, units, Leray, and the actual relevant modules found no declaration stating every clause. Etale/Derived/GlobalSections.lean supplies the etale Leray isomorphism but expressly leaves the general derived pullback map as a TODO. ProEtale/Comparison/CohomologicalDimension.lean supplies comparison Leray, and RightDerivedFunctor/PlusAdjunction.lean supplies generic derived-unit composition. None states geometric two-site section-map compatibility with arbitrary finite-ring sheaf L, so this is not an attachment. The item is not a Mathlib leaf.

## WANTED

None. All sources used are locally present.

## Existing material and corrections

There was no existing sandbox node or report to repair, and no released repair note for this item. I copied the current repository item and retained its statement, source, ancestry, and all five inherited Mathlib searches. I read GOAL.md, the three blueprint levels in SETUP.md, the chapter and unit records, the worker contract, stage-1 rules, tools documentation, and delivery-errors B through E. No Lean files, compiler, Lake, repository writes, launcher changes, or agents were used.

The source is the transport paragraph (Step 4) in current main-20261015/sec-six-functors-basics/sk-prop-a1-kummer/lem-pur-a1-direct-image.proof.md. The ancestry reaches the ordinary affine-line input needed by the shear paragraph of sec-smooth-purity/sk-prop-an/lem-pur-frame-independence.proof.md. I read those actual files and retained the ordinary-unit and injective-resolution arguments from Q116's report below. The item is not the unit's key statement, so no unit realization fields change.

No statement dispute was found. Two tempting citations would have been insufficient: derived-unit-leray-comp only treats abelian etale sheaves of schemes, and supported-cup-functoriality only treats the prescribed finite-field datum and Tate twists. Neither states the present arbitrary finite ring and arbitrary sheaf L comparison in the derived module category. I therefore did not use them as if they supplied the required generic theorem. The one new lemma is about arbitrary geometric morphisms on small sites and the normalization of ordinary derived sections, with no etale/pro-etale comparison theorem, no qcqs hypothesis, and no invertibility-of-unit assertion. It is a genuine generic tool, rather than a renamed clause asserting the item's transport theorem. In particular, the item's proof itself still carries the unit transpose calculation, invertibility argument, geometric square substitution, and application to cohomology.

## Source and search review

For the item I read Stacks proetale.tex, section-comparison (099R), lemma-relative-comparison (099V), lemma-compare-cohomology (099W), and lemma-morphism-comparison (09A6). They explain bounded-below site and direct-image comparisons; the exact named-mate normalization is taken from the existing DAG statement, not inferred from an anonymous isomorphism. No SGA source is used.

For the new lemma I read derived.tex, Tag 015M / lemma-compose-derived-functors (and its general comparison construction), sites-cohomology.tex Tag 071J / section-derived-functors (ordinary module-valued sections by injective resolutions), and sites.tex Tag 04IA / definition-2-morphism-topoi (mates of natural transformations on sheaves of sets). I also read the injective preservation and Leray arguments in sites-cohomology.tex. The complete pasting formulation is agent-written from this material, not represented as a verbatim Stacks theorem.

The new lemma has seven actual logged searches: two differently phrased LeanFinder searches, LeanSearch, two Loogle searches, and two Mathlib grep searches, all through the required msearch.py. The item additionally has its own semantic query and inherits these relevant generic searches. The actual log entries are copied into results, with exact tools and query strings. All services responded successfully. LeanSearch found unitHomEquiv_comp_apply, pushforwardSections_unitHomEquiv and underived pullback composition; LeanFinder found sheafComposeNatIso, sheafPushforwardContinuousComp'_hom_app_val_app and SheafOfModules.pullbackComp. Loogle found abstract rightDerivedNatTrans_comp and localization comparison lemmas. I read the relevant Mathlib PullbackFree and RightDerived source: these are underived sheaf or abstract Kan-extension results, not a one-line statement of derived sections, its Leray normalization, geometric two-isomorphism pasting and the usual cohomology map together. The second grep for Leray/derived global sections in CategoryTheory returned no hits. No Mathlib leaf is claimed.

I searched the entire DAG and blueprint before creating the helper, by derived sections, Leray, geometric morphism, adjunction unit, functoriality of cohomology, and its source tags 015M, 071J and 04IA. I opened the closest existing statements, including derived-cohomology-pullback-laws, derived-unit-leray-comp/id, derived-leray-composition, derived-sections-pushforward, comparison-global-cohomology, module-derived-restriction-resolution, equivalence-derived-sections, and sections-adjunction-comparison. The scheme-etale restriction in the first group and the equivalence hypothesis in equivalence-derived-sections prevent reuse for the two-site diagram. The source-tag overlaps are distinguished individually below.

## Review by Q125

Step 1 uses the actual adjunction-mate bijection of def-weil-pbc-adjunction-mate and the counit-normalized equation in lem-weil-pbc-comparison-direct-image-canonical-mate. I opened both statements. The latter explicitly supplies both derived adjunctions and exactly the map a used in the item. Applying the pro-etale counit to P(t), naturality moves s(a) to the outside; the cited counit normalization removes P(b); naturality of a^{-1} moves C_X(eta) inside; the etale triangle identity cancels epsilon composed with l(eta). This yields the identity of PC_XL, hence equality of the two maps by transpose injectivity. Every composition has the indicated source and target. This short identity is elementary relative to these adjunction data, and is not made a new node.

Step 2 again uses the canonical-mate statement, now specifically its assertion that every component on D+ is an isomorphism. f is qcqs, Lambda is finite and discrete, and lL is a degree-zero sheaf, so all its hypotheses hold without finite type, separatedness of X, invertibility of torsion on X, or constructibility of L. The functor C_X sends an isomorphism to an isomorphism; together with a and b this proves invertibility of the named pro-etale unit. I do not invoke an unbounded direct-image comparison on arbitrary inputs.

Step 3 uses only the new generic lemma's natural Leray isomorphism and definition of T_f. Its hypothesis of exact constant-coefficient inverse image is satisfied by the etale and pro-etale adjunctions in the item; both sites have the underlying scheme as final object, and their smallness convention is already in the existing site definitions. Applying a functor to each proved invertible unit and composing with lambda_f proves the two displayed derived isomorphisms. All sections are ordinary sections; there is no completion or compact support.

Step 4 uses three statements, all opened. comparison-pullback gives the natural geometric isomorphism between the two inverse-image composites, with identity/composition coherence. The new lemma states both the derived composition equation and its variant for an isomorphism of geometric morphisms. Applying those equations to the two paths from Y_proet to X_et gives exactly the displayed T^p_f T_nuX = RGamma(a) T_nuY T^e_f equation. comparison-global-cohomology states that its specified comparison is RGamma of the derived nu-unit followed by the final-object comparison, exactly T_nu. Thus the substitution really identifies the named section morphisms in the derived category. This does not rely on conservativity of H^q or on equality of their induced maps alone.

Step 5 uses the new lemma's explicit resolution description of H^q(T_f) and its naturality. The comparison equality in step 4 precedes homology. Taking H^q therefore yields equality of usual pullback maps, and functoriality carries the proved isomorphisms to isomorphisms. In degree zero it is ordinary section pullback. For negative q both resolutions of a degree-zero sheaf can start at zero, giving zero groups. Naturality in L follows for every factor, including a and b, not merely for isomorphisms of L.

I checked the new statement independently: all sites, coefficients, categories, morphisms, units and comparison maps are introduced; the statement has no proof or proof dependencies. Small sites ensure enough injective module sheaves. Constant coefficients make geometric inverse image exact, so its right adjoint preserves injectives, and the Leray comparison is an isomorphism. Its geometric-2-isomorphism hypothesis is essential: an arbitrary module inverse-image automorphism such as multiplication by -1 must not silently change the global pullback. The new statement expressly excludes that ambiguity. Neither identity morphisms nor empty sites presenting the empty scheme create an exception: the identities and zero objects give the claimed equations. R=0, L=0, empty X/Y, arbitrary nonconstant L and negative cohomology were also tested. If Y is empty and the etale unit is invertible, that forces L=0, consistent with the conclusion.

For delivery-errors B, I checked statement-only shape, self-contained hypotheses, explicit definition references, single TeX escaping, exact source labels, actual search results, and blueprint ancestry. For C, each proof use is matched to its verbatim statement quote in citations.json; no proof of another node is used as its statement, no missing non-elementary lemma is hidden, and the generic off-unit tools are declared in split_report.tool_uses. For D, one new generic sections lemma does not restate the item; the 2228-character assembly itself proves transport. For E, every boundedness/coefficient/geometry hypothesis and every named map has been checked as above. No proof step exceeds 2000 characters. The parent report's twist-only supported comparison is replaced here by a properly general derived comparison argument; no inherited argument or citation record is discarded.

## Argument retained for the new statement-only node

This argument is report material, not a split proof inside the new node. A reader taking over the helper can start from it. For a geometric morphism with exact constant-module inverse image, the right adjoint preserves injectives: a lifting problem against a monomorphism transposes to a lifting problem against its inverse image, which is still a monomorphism. For bounded-below injective J on the source, f_*J is consequently a bounded-below injective complex on the target. Both RGamma_C Rf_* and RGamma_D are represented by the same section complex, via the canonical underived global-section identification. This proves the named Leray isomorphism, including its resolution normalization.

Choose a bounded-below injective representative I of K on C, an injective representative J of f^{-1}K on D and a lift f^{-1}I -> J, and then a bounded-below injective representative V of g^{-1}f^{-1}K on E and a lift g^{-1}J -> V. Such lifts exist since their targets are bounded-below injective complexes and the source resolutions are exact images; the standard comparison theorem identifies two lifts up to homotopy. Section pullback followed by these lifts represents the derived unit followed by Leray: on a representative this is the ordinary adjunction unit followed by f_* of the resolution comparison, and the final-object section identification. For the composite use the composite lift g^{-1}f^{-1}I -> g^{-1}J -> V. The underived unit formula for a composite adjunction identifies its section map with the two section maps in succession. Passing to the derived category proves the composition equation before taking homology. An isomorphism of geometric morphisms identifies inverse images and adjunctions through their mates and acts canonically on constant rings; transporting these same chain maps proves the alpha equation. Chain-homotopy invariance gives independence of all resolutions and naturality. For sheaves in degree zero the construction is exactly the standard cohomology pullback on injective resolutions; choosing resolutions concentrated in nonnegative degrees proves the negative-degree clause.

## Not duplicates

lem-pur-site-derived-sections-unit-pasting vs def-sp-composite-acyclicity: the existing statement concerns 'Composable pairs with an acyclicity condition'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs thm-sp-grothendieck: the existing statement concerns 'Grothendieck spectral sequence'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs def-weil-pbc-direct-image: the existing statement concerns 'Direct image and its derived functor'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-sc-grothendieck-bottom-resolution-comparison: the existing statement concerns 'The Grothendieck bottom edge computed on an augmented resolution comparison'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-sc-resolution-derived-single-unit-augmentation: the existing statement concerns 'The derived unit transported to a prescribed resolution is the augmented comparison'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-sc-topological-leray-spectral-object-augmentation: the existing statement concerns 'Topological Leray spectral object with its cocycle augmentation'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-weil-pbc-derived-cohomology-pullback-laws: the existing statement concerns 'Identity and composition for canonical derived étale cohomology pullback'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-weil-pbc-derived-finite-product: the existing statement concerns 'Right derived functors of a finite product are the product of right derived functors'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-weil-pbc-derived-leray-composition: that statement pastes etale abelian derived direct images along scheme maps; this also constructs derived pullback on sections and pastes geometric 2-isomorphisms for arbitrary sites with constant-R modules.

lem-pur-site-derived-sections-unit-pasting vs lem-weil-pbc-derived-unit-leray-comp: that statement is for unbounded abelian etale sheaves and composable scheme maps; this is for constant-R module sheaves on arbitrary geometric sites, includes pro-etale/comparison morphisms and geometric 2-isomorphisms, and supplies the normalized Leray and cohomology identification.

lem-pur-site-derived-sections-unit-pasting vs lem-weil-pbc-derived-unit-leray-id: that statement only computes identity pullback on abelian etale sheaves; this handles arbitrary geometric morphisms, composition, geometric 2-isomorphisms and ordinary module cohomology.

lem-pur-site-derived-sections-unit-pasting vs lem-weil-pbc-module-direct-image-left-exact: the existing statement concerns 'Direct image of etale sheaves of modules over a constant ring: module structure, additive and left exact'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs def-pc-canonical-resolution-derived-iso: the existing statement concerns 'Canonical comparison for a prescribed injective resolution'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-pc-canonical-resolution-composite-unit-comparison: the existing statement concerns 'Composite unit transport for the canonical prescribed-resolution comparison'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-pc-canonical-resolution-homology-comparison: the existing statement concerns 'Homology of the canonical prescribed-resolution comparison'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-pc-grothendieck-hypercohomology-edge: the existing statement concerns 'Resolution comparison for the hypercohomology edge'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-pc-grothendieck-resolution-unit-comparison: the existing statement concerns 'Compatibility of prescribed resolutions with the composite derived unit'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-sc-ext-derived-composite-natural: the existing statement concerns 'Naturality of the derived-composite isomorphism in the exact functor'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-sc-ext-derived-composite: the existing statement concerns 'Derived functors after an exact functor'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-sc-ext-locally-free-second-naturality: the existing statement concerns 'Second-variable naturality of Ext-cohomology for a locally free first argument'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-sc-p1-duality-pairing-naturality: the existing statement concerns 'Naturality and connecting-square compatibility of projective-line duality maps'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-pe-ringed-site-derived-evaluation-slice: the existing statement concerns 'Derived module evaluation is abelian cohomology on the slice'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-weil-pbc-abelian-etale-sheaves-grothendieck: the existing statement concerns 'Abelian sheaves on the small etale site form a Grothendieck abelian category'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-weil-pbc-affine-etale-essentially-small-cover: the existing statement concerns 'A set of affine etale schemes covers every object of the small etale site'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-weil-pbc-free-yoneda-presheaf-module: the existing statement concerns 'Morphisms out of the free presheaf of modules on a representable are sections'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-weil-pbc-grothendieck-spectral-sequence: the existing statement concerns 'Grothendieck spectral sequence for a composite'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-weil-pbc-module-sheaves-colimits-forgetful: the existing statement concerns 'Colimits of sheaves of modules and the forgetful functor to abelian sheaves'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-weil-pbc-module-sheaves-grothendieck-abelian: the existing statement concerns 'Sheaves of Lambda-modules on the small etale site form a Grothendieck abelian category'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-weil-pbc-module-sheaves-limits-sectionwise: the existing statement concerns 'Limits of sheaves of modules exist and are computed sectionwise'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-weil-pbc-presheaf-modules-colimits-sectionwise: the existing statement concerns 'Colimits of presheaves of modules are computed sectionwise'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-weil-pbc-qs-scheme-cohomology-directed-colimit: the existing statement concerns 'Cohomology on a quasi-compact open commutes with directed colimits of modules (Stacks 01FF, for schemes)'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison: the existing statement concerns 'Module and abelian cohomology over an object of a ringed site agree'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs thm-sf-direct-image-tor-amplitude: the existing statement concerns 'Direct image and finite Tor amplitude'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-sfb-ordinary-proetale-direct-image-plus-comparison: the existing statement concerns 'Ordinary intrinsic pro-étale direct image: K-injective and bounded-below comparison'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-sbc-raw-affine-complex-system-map-coherence: the existing statement concerns 'Identity, composition and cone equations of canonical complex cohomology maps'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-exc-equivalence-derived-sections: that statement requires an additive equivalence and produces individual R^q comparisons; neither f nor nu is assumed an equivalence here, and this asserts derived section-map pasting.

lem-pur-site-derived-sections-unit-pasting vs thm-exc-curve-open-dimension-general: the existing statement concerns 'Open direct-image dimension on arbitrary curves'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-trf-derived-sections-finite-pushforward-modules: the existing statement concerns 'Derived sections through finite pushforward for module sheaves'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-trf-finite-base-cech-hypercohomology: the existing statement concerns 'Natural bounded-below finite-cover etale hypercohomology descent'; it does not assert normalized derived-section pullback and geometric-2-isomorphism pasting on arbitrary constant-R module sites, including the two-site diagram.

lem-pur-site-derived-sections-unit-pasting vs lem-trf-module-derived-restriction-resolution: that statement compares a specified resolution arrow for a scheme morphism on the etale site; this additionally treats arbitrary geometric sites and two-isomorphism/composition pasting, needed for nu and the pro-etale site.

lem-pur-site-derived-sections-unit-pasting vs lem-weil-pbc-derived-cohomology-pullback-laws: the existing assertion is restricted to scheme-etale cohomology, the one comparison morphism, abstract adjunction Hom bijections, or prescribed finite twists; it does not give the general normalized derived-section composition and geometric-2-isomorphism law needed here.

lem-pur-site-derived-sections-unit-pasting vs lem-weil-pbc-derived-sections-pushforward: the existing assertion is restricted to scheme-etale cohomology, the one comparison morphism, abstract adjunction Hom bijections, or prescribed finite twists; it does not give the general normalized derived-section composition and geometric-2-isomorphism law needed here.

lem-pur-site-derived-sections-unit-pasting vs lem-weil-pbc-comparison-global-cohomology: the existing assertion is restricted to scheme-etale cohomology, the one comparison morphism, abstract adjunction Hom bijections, or prescribed finite twists; it does not give the general normalized derived-section composition and geometric-2-isomorphism law needed here.

lem-pur-site-derived-sections-unit-pasting vs lem-kun-sections-adjunction-comparison: the existing assertion is restricted to scheme-etale cohomology, the one comparison morphism, abstract adjunction Hom bijections, or prescribed finite twists; it does not give the general normalized derived-section composition and geometric-2-isomorphism law needed here.

lem-pur-site-derived-sections-unit-pasting vs lem-pur-supported-cup-functoriality: the existing assertion is restricted to scheme-etale cohomology, the one comparison morphism, abstract adjunction Hom bijections, or prescribed finite twists; it does not give the general normalized derived-section composition and geometric-2-isomorphism law needed here.

## Parent argument retained verbatim

### Returned step 6 -> lem-pur-ordinary-unit-site-sections-transport

Transport the actual unit to the pro-etale site, with constant ring $A$ and the etale finite twist as witness. Use the notation $A_T=\nu_T^*$, $l=p_{\mathrm{et}}^{-1}$, $r=Rp_{\mathrm{et},*}$, $P=Lp_{\mathrm{proet}}^*$, $s=Rp_{\mathrm{proet},*}$, $a:A_{\mathbf A^1_X}l\cong PA_X$ and $b:A_Xr\to sA_{\mathbf A^1_X}$ in [lem-weil-pbc-comparison-direct-image-canonical-mate]. Its hypotheses hold because $p$ is qcqs and the input $lL$, $L=A(r)_X$, is in degree zero. By that node $b$ is an isomorphism and is the transpose of $A_{\mathbf A^1_X}(\varepsilon^e)a^{-1}$. Transposing
$$s(a_L)\circ b_{lL}\circ A_X(\eta^e_L):A_XL\longrightarrow sPA_XL$$
and using naturality of $a$ gives $A_{\mathbf A^1_X}(\varepsilon^e_{lL}\circ l\eta^e_L)$ conjugated by $a_L$, hence the identity by the etale triangle identity. This composite is consequently the pro-etale unit $\eta^p_{A_XL}$, since an adjunction transpose is a bijection. Every factor is invertible by step 5 and the cited comparison, so the pro-etale unit is invertible. Step 1 identifies its coefficient object with the specified detailed finite twist. This proves equality under comparison of the canonical unit maps, not merely existence of abstract isomorphisms of their endpoints.

Original uses: lem-weil-pbc-comparison-direct-image-canonical-mate

Original source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/lem-pur-a1-direct-image.proof.md", "place": "Transport paragraph of lem-pur-a1-direct-image.proof.md, with named-unit verification; Stacks 099R and 0B65"}

### Returned step 7 -> lem-pur-ordinary-unit-site-sections-transport

For the etale cohomology conclusion apply $R\Gamma(X,-)$ to the unit proved invertible in step 5. Its target identifies canonically with $R\Gamma(\mathbf A^1_X,A(r))$. To see this at the resolution level, take a bounded-below injective resolution $I$ on $\mathbf A^1_X$. By [prop-weil-pbc-inverse-image-modules-exact] the inverse image is exact and left adjoint to $p_*$; hence $p_*$ sends an injective to an injective, since lifting a morphism into $p_*I$ along a monomorphism transposes to lifting into $I$ along its inverse-image monomorphism. Thus $p_*I$ computes both $Rp_*$ and its derived sections. The section complexes agree termwise by [def-weil-pbc-direct-image], $\Gamma(X,p_*I)=\Gamma(\mathbf A^1_X,I)$. The resulting map is the ordinary cohomology pullback, since the unit first pulls back sections and then maps to the resolution. It is therefore an isomorphism in every degree. For the pro-etale cohomology conclusion use the natural global comparison [lem-weil-pbc-comparison-global-cohomology] for both $X$ and $\mathbf A^1_X$. It applies to arbitrary schemes and degree-zero etale twists with finite ring $A$. Compatibility with pullback is the all-support case $C=X$ of [lem-pur-supported-cup-functoriality]. In its commuting square the horizontal comparisons and the etale vertical pullback are isomorphisms, so the pro-etale vertical pullback is an isomorphism as well. For $q<0$ both groups are zero by the nonnegative injective resolution convention [def-weil-pbc-sites-and-cohomology].

Original uses: prop-weil-pbc-inverse-image-modules-exact, def-weil-pbc-direct-image, lem-weil-pbc-comparison-global-cohomology, lem-pur-supported-cup-functoriality, def-weil-pbc-sites-and-cohomology

Original source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/sk-prop-a1-kummer.proof.md", "place": "Consequences of the unit: derived sections, all degrees and canonical site comparison"}


## Unfinished work and validation

No open mathematical part of the item remains outside its cited nodes. The single new helper is intentionally unsplit. The authorized server dry run and final push are performed after this report is written; their actual output is the validation record.
