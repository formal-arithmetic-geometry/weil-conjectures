# Stage-1 repair: lem-sfb-finite-field-proetale-direct-image

## Worker report

Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-field-proetale-direct-image.json`: existing statement, statement dependencies, source, Lean declaration and maintained records retained; five-step short assembly, status split.
- `dag/nodes/sec-six-functors-basics/lem-sfb-ordinary-proetale-direct-image-plus-comparison.json`: new statement, status unsplit, no proof steps or proof dependencies, no Mathlib match. It isolates existence/computation of the full ordinary direct images, their bounded-below restriction, and identification of the intrinsic comparison interface.
- `citations.json`: verbatim statement quotes for every cited node in every assembly step.
- `report.md`: this report, including the complete returned argument and the extraction map.

Attachments: none. I searched `lean/WeilConjectures/` by the item tag and its notions. The actual item declaration is `AlgebraicGeometry.Scheme.finiteField_proEtale_directImage_bounded_constructible` in `lean/Sheaf/AlgebraicGeometry/FiniteFieldProEtaleDirectImage.lean`; its body is `sorry`. Its existence is not a finished proof and does not cancel the explicit re-split assignment. No Lean was edited or compiled.

WANTED: none.

The returned split had a long seven-step proof. The mathematical statement is retained verbatim. The human explicitly requested spreading proof work, even though the node had been reviewed and stated in Lean. The sandbox contained dispatcher markers only, with no node, report or search log to continue; I copied the current reviewed item and preserved its citations/search history and all maintained fields. The unchanged parent chain is through `lem-sfb-finite-field-internal-hom-finiteness` to blueprint `lem-sfb-dc-hom-preserves`.

All work requested for this repair is complete apart from the delivery checks recorded below. No statement dispute was found.

## Repair of the return

The new independently claimable node is a comparison theorem for arbitrary schemes and a qcqs morphism, with finite commutative coefficients. It has no constructibility assertion, field-of-definition hypothesis, finite-type hypothesis, or geometric finiteness conclusion. Thus it does not restate the item or move its whole conclusion down one level. Its proof obligation contains the substantive ordinary-derived interface argument previously inline in steps 3, 5, 6 and 7. Its statement explicitly restricts the comparison to bounded-below étale inputs, while defining the two direct-image functors on the full ordinary categories.

The assembly is 1855 characters in five steps. The extracted theorem is statement-only (2320 characters), and all its seven actual msearch calls are recorded. No new node has a proof sketch inside its statement. None of the assembly steps exceeds 2000 characters.

Argument destinations:
1. Returned step 1: assembly step 1, using the same three geometric permanence theorems.
2. Returned step 2: assembly step 2 cites the existing `lem-sfb-noetherian-global-constructibility`, which already carries precisely the finite-affine-cover, actual stratum factorization and local-model pullback argument for either site. This avoids duplicating its independently claimable work. The finite-field module identifications are elementary linear algebra.
3. Returned step 3: assembly step 3 applies the same constructible equivalence and cohomology compatibility. Its final intrinsic-versus-site module inverse-image identification is now an explicit conclusion of the new node, used in assembly step 5. No change to coefficients or completion is involved.
4. Returned step 4: assembly step 4 uses the same arbitrary-field étale finiteness theorem and verifies the same annihilator/invertibility hypotheses.
5. Returned step 5: new node's full-category existence and K-injective computation conclusions. The complete construction argument is retained below; its future worker must use ringed-site Grothendieckness, K-injective existence, and the total-derived theorem, including the exactness on homotopy categories of degreewise additive direct image.
6. Returned step 6: new node's natural bounded-below compatibility and common injective computation conclusions. A future worker must supply bounded-below injective representatives, K-injectivity and unit-compatible derived comparison; the statement does not merely assert an unrelated objectwise isomorphism.
7. Returned step 7: the new node identifies the geometric D+ comparison with the full ordinary intrinsic comparison; assembly step 5 composes it with the image of alpha and applies the original cohomology and constructibility theorems. The finite vanishing interval and the global convention remain explicit.

## Complete retained argument from the returned split

The following is the original argument, reproduced verbatim for review of the extraction. It is report material, not a proof attached to the new unsplit node.

### Returned step 1

First check the geometric hypotheses for comparison. A field is Noetherian (its only ideals are $(0)$ and $(1)$), and $\operatorname{Spec}k$ is quasi-compact. By [lem-weil-pbc-finite-type-over-noetherian], both $T$ and $V$ are Noetherian, hence quasi-compact. By [lem-weil-pbc-locally-noetherian-quasi-separated], both are quasi-separated. Finally [lem-weil-pbc-qcqs-morphism-permanence] (1), applied to $f:T\to V$, makes $f$ quasi-compact and quasi-separated. These implications require no separatedness of $f$ or of the structure morphisms.

Cited statements: lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-locally-noetherian-quasi-separated, lem-weil-pbc-qcqs-morphism-permanence.

### Returned step 2

We identify the constructibility convention before using comparison. Since $A$ is a finite field, it is Noetherian and its finitely generated modules are precisely its finite-dimensional vector spaces, which are finite sets. On either site, a finite global constructible locally closed stratification is in particular such a stratification locally. Conversely, on a qcqs scheme choose a finite affine open cover carrying the local stratifications. Apply [lem-weil-pbc-etale-stratification-local-gluing-core] to obtain a finite global stratification whose stratum maps factor through the local stratum maps. Pull back each local constant model along this factorization: its trivializing covering pulls back to a covering, on which the same finite $A$-module is constant. Thus the local and global constructibility conditions agree. The argument uses actual stratum morphisms, not only inclusions of their images. In particular the intrinsic pro-étale category $\mathcal B_A(W)$, for $W=T,V$, is the bounded constructible category appearing in [sk-thm-pe-constructible-comparison].

Cited statements: lem-weil-pbc-etale-stratification-local-gluing-core, sk-thm-pe-constructible-comparison.

### Returned step 3

Take $K\in\mathcal B_A(T)$. Apply the bounded constructible equivalence of [sk-thm-pe-constructible-comparison] with the discrete Noetherian coefficient ring $\Lambda=A$. It gives $G\in D^b_c(T_{\mathrm{et}},A)$ and an isomorphism $\alpha:\nu_T^*G\xrightarrow{\sim}K$ in the ordinary pro-étale derived category. Here $\nu_T^*$ is the actual intrinsic module inverse image, not a change to condensed or completed coefficients: [lem-pe-coefficient-comparison-derived-functor] identifies its derived functor with termwise inverse image and says that it commutes with every cohomology functor. The module inverse image $\nu_W^*$ of [def-weil-pbc-site-comparison-morphism], used by the comparison theorem and in step 7, and the intrinsic module pullback along the constant-section ring map of [lem-pe-coefficient-comparison-data] are both left adjoint to the same module direct image $\nu_{W,*}$ (sections on étale objects, with the $A$-action through the constant-section map), so they are canonically isomorphic by uniqueness of adjoints; we use this identification for $W=T,V$ throughout. All comparison hypotheses hold by step 1; $G$ is in particular bounded below.

Cited statements: sk-thm-pe-constructible-comparison, lem-pe-coefficient-comparison-derived-functor, def-weil-pbc-site-comparison-morphism, lem-pe-coefficient-comparison-data.

### Returned step 4

The coefficient ring $A$ is finite and is annihilated by $\ell$. The image of $\ell$ in the field $k$ is nonzero since $p\ne\ell$, hence is invertible. Apply [thm-dg-finite-type-constructibility] to the given morphism between finite-type $k$-schemes, with this ring $A$ and the complex $G$. It gives $H:=Rf_{\mathrm{et},*}G\in D^b_c(V_{\mathrm{et}},A)$ in the ordinary derived category. The cited statement explicitly allows $f$ not separated and places no finiteness, perfection, or separable closedness assumption on $k$.

Cited statements: thm-dg-finite-type-constructibility.

### Returned step 5

We also verify that the derived direct image in the assertion exists on the full ordinary category. Use the small-site universe convention already included in the item. For each of the étale and pro-étale constant-ring sites, [lem-pur-ringed-site-grothendieck-abelian] makes the category of $A_W$-module sheaves Grothendieck abelian. By [lem-sfb-grothendieck-k-injective] every complex has a K-injective resolution. Applying [lem-weil-pbc-kinjective-total-derived] to degreewise $f_*$ followed by derived localization constructs $Rf_*$ and computes it as $f_*I$ on a K-injective representative $I$. Degreewise application of the additive functor $f_*$ respects homotopies, shifts and mapping cones, which is exactly the exact-functor hypothesis on the homotopy categories in the cited theorem.

Cited statements: lem-pur-ringed-site-grothendieck-abelian, lem-sfb-grothendieck-k-injective, lem-weil-pbc-kinjective-total-derived.

### Returned step 6

On a bounded-below input, this full-category functor agrees with the usual bounded-below right derived direct image. Indeed, the Grothendieck categories in step 5 have enough injectives by [lem-sp-grothendieck-enough-injectives]. By [lem-weil-pbc-dplus-injective-representative], any bounded-below input on either site has a bounded-below complex $I$ of injectives representing it, and this $I$ is K-injective. The usual bounded-below derived value is represented by $f_*I$; the full-category value is represented by the same $f_*I$ by [def-sfb-right-derived-functor]. Therefore comparison on $D^+$ computes the ordinary uncompleted $Rf_*$ of the item on $K$, and the ordinary étale $Rf_*$ on $G$.

Cited statements: lem-sp-grothendieck-enough-injectives, lem-weil-pbc-dplus-injective-representative, def-sfb-right-derived-functor.

### Returned step 7

Apply [prop-weil-pbc-comparison-direct-image] to the qcqs morphism $f$ and the bounded-below étale complex $G$. Together with $Rf_{\mathrm{proet},*}(\alpha)$ and step 6, it gives an isomorphism in the full ordinary derived category
$$\nu_V^*H=\nu_V^*Rf_{\mathrm{et},*}G\xrightarrow{\sim}Rf_{\mathrm{proet},*}\nu_T^*G\xrightarrow{\sim}Rf_{\mathrm{proet},*}K.$$
By [lem-pe-coefficient-comparison-derived-functor], $\mathcal H^q(\nu_V^*H)\cong\nu_V^*\mathcal H^q(H)$. By the forward direction of [sk-thm-pe-constructible-comparison], these are constructible and vanish outside the finite cohomological interval for $H$ from step 4. Step 2 identifies this constructibility with the global finite-stratification condition defining $\mathcal B_A(V)$. Hence $Rf_*K\in\mathcal B_A(V)$, as required.

Cited statements: prop-weil-pbc-comparison-direct-image, lem-pe-coefficient-comparison-derived-functor, sk-thm-pe-constructible-comparison.

## Sources and searches

I read Bhatt–Scholze, *The pro-étale topology for schemes*, Lemma 5.4.3 and its proof, Remark 5.4.4, Theorem 6.7.1, and the finite-field specialization of Lemma 6.7.2. The last theorem supplies the descent/finiteness/comparison route; the existing current-blueprint `thm-dg-finite-type-constructibility` supplies exactly the arbitrary-field ordinary étale finiteness input. I read its statement in the current `main-20261015` blueprint. No SGA route is used.

For the new node I read Stacks `derived.tex`, Tag 070K, label `lemma-enough-K-injectives-implies`, and Tag 070J, label `lemma-bounded-below-injectives-K-injective`; `sites-cohomology.tex`, Tag 07A5, label `section-unbounded`, opening paragraphs; and `injectives.tex`, Tag 079P, label `theorem-K-injective-embedding-grothendieck`. These give the full-category construction and computation behind the extracted comparison interface. I also read `proetale.tex`, Tag 099R, label `lemma-morphism-comparison`, and Tags 09AJ/09AK/09AL, labels `definition-constructible`, `lemma-compare-constructible`, `lemma-compare-constructible-derived`. The geometric comparison is applied to D+ input as in Bhatt–Scholze 5.4.3, not to all unbounded inputs.

Before creating the new node I searched the whole DAG by these tags, K-injective/full-category/bounded-below/direct-image/comparison words, and the blueprint using `tools/blueprint_refs.py search` for “comparison direct image”, “unbounded comparison”, “bounded below direct”, “global stratification”, “constant ring” and “K-injective”. `ancestor` gives `lem-sfb-dc-hom-preserves`. I read the current blueprint node and its chapter and unit records; this is the finite-field input to its internal-Hom route. No blueprint node states the new interface theorem. Existing constructible comparison and global constructibility were reused.

Seven Mathlib searches were run through the prescribed msearch command: two different LeanFinder phrasings, LeanSearch, two Loogle patterns and two grep patterns. Each actual query and output digest is in searches.jsonl and in the new node. All services answered. LeanFinder found ordinary sheaf pushforward natural isomorphisms, left Kan pullback/sheafification, general exact-functor localization and abstract total-derived infrastructure. Loogle found `Functor.rightDerivedFunctorPlus` and generic `IsRightDerivedFunctor` comparisons. Grep found the D+ definitions and `CochainComplex.isKInjective_of_injective`, but no pro-étale total-derived comparison. I read `Mathlib/Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus.lean`, especially lines 29–69, and the project's `WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/PlusCompatibility.lean`: the latter assumes enough injectives and K-injective resolutions and compares two generic constructions. Neither supplies the intrinsic ringed-site existence, identification of the coefficient presentations, and étale/pro-étale comparison together. The new node is unsplit, not a Mathlib leaf. The item's inherited searches were retained; this repair does not change their question.

## Review by Q52

I checked the return by comparing the old and new JSON rather than merely shortening the prose. The unchanged item asks for arbitrary positive-characteristic k, finite-field coefficients of the other characteristic, finite-type schemes and morphism, with no separatedness assumption and no completion. The new node is independent of constructibility and finiteness: its hypotheses are just small site representatives, a finite commutative coefficient ring and a qcqs scheme morphism. This is the exact amount needed for the comparison step. The complete previous argument appears above with an explicit destination for each part. The one new proof obligation is large enough for separate work, and existing overlapping work has been cited instead of duplicated.

For assembly step 1 I opened all three geometric nodes. `finite-type-over-noetherian` says finite type over a Noetherian scheme gives a Noetherian source; `locally-noetherian-quasi-separated` supplies quasi-separatedness; `qcqs-morphism-permanence` clause (1) gives the exact two morphism properties from quasi-compact source and quasi-separated schemes. A field has only two ideals, and its spectrum is a point, so the starting hypotheses hold. No step assumes that an intersection of affine opens is affine.

For step 2 I opened `lem-sfb-noetherian-global-constructibility`, whose statement gives the local/global equivalence separately on the two small sites over Noetherian schemes. It permits the coefficient module to vary over the trivializing cover and uses finitely presented values. Over a finite field those values are finite-dimensional and finite sets. Its hypotheses are supplied by step 1. I checked its dependency `etale-stratification-local-gluing-core`: it gives actual morphisms through local strata, just as the returned proof required. There is no inference from containment of set-theoretic images to factorization.

For step 3 I opened `sk-thm-pe-constructible-comparison`: it explicitly gives both the constructible sheaf equivalence and the bounded constructible derived equivalence for discrete Noetherian coefficients on a qcqs scheme. The field A is Noetherian. `lem-pe-coefficient-comparison-derived-functor` explicitly identifies the intrinsic termwise derived pullback and its compatibility with every cohomology functor; it does not merely define a comparison object. I retained this citation separately for the final vanishing argument.

For step 4 I opened `thm-dg-finite-type-constructibility` and read every hypothesis. Its finite ring killed by an integer invertible in k applies with that integer ell. Its statement explicitly permits non-separated f. No finiteness, perfection or separable closedness of k is smuggled into this step.

For step 5 I checked every clause against the newly stated interface theorem: it explicitly supplies full ordinary total right derived direct images with the K-injective computation, identifies their D+ restrictions and units, identifies the two actual module inverse-image presentations, and gives the comparison isomorphism only for bounded-below G. G from step 3 is bounded. Applying Rf_* to alpha is functoriality. The two other cited statements supply the cohomology isomorphisms and constructibility of the inverse-image cohomology sheaves; their exact statements are quoted in citations.json. Thus no inference is taken only from a cited node's proof.

For the extracted argument I reopened all of the old foundational cited statements. Ringed-site Grothendieckness requires the sites small in the module universe, now explicit in its statement. K-injective existence applies to these Grothendieck abelian categories. Degreewise additive f_* preserves chain homotopies, shifts and mapping-cone matrices, so localization composed with it is an exact homotopy-category functor for 070K. Enough injectives and the bounded-below representative lemma yield I with injective terms, which is K-injective by 070J. The common f_*I computes both constructions. The site-comparison module inverse image and the intrinsic constant-section inverse image have the same sectionwise right adjoint, and the canonical comparison of left adjoints fixes the coefficient interface. The comparison itself is the D+ one transported through these canonical, unit-compatible identifications. I checked the existing `src-right-derived-functor-plus-compatibility`, `lem-weil-pbc-kinjective-total-derived`, `lem-weil-pbc-dplus-injective-representative`, and `prop-weil-pbc-comparison-direct-image`; each covers a proper part of this interface and is material for the future split, rather than a new copy of the full statement.

Small cases checked: empty source or target whenever a morphism exists, zero input complex, identity f, and B the zero ring. The module categories and resolutions still make sense and the comparison is the unique/identity one in the zero cases. No assertion uses nonzero coefficients, a fixed positive cohomological dimension, or boundedness of the output for arbitrary B. For the item I checked ell=2, an imperfect infinite base field, and a non-separated finite-type source. The only characteristic calculation used is ell nonzero in k. Bhatt–Scholze Remark 5.4.4 excludes extending the extracted comparison to all unbounded-below inputs; that extension is expressly excluded in the new statement.

B1–B10: the new node is a self-contained TeX statement, with named sites, coefficients, universes, functors and bounds, definition dependencies, precise sources and blueprint ancestry; it has no proof or Mathlib match. C1–C8: each non-elementary assembly fact has a cited statement, every use has a verbatim quote, and the existing generic off-unit tools are declared in split_report.tool_uses. The new node depends in its statement only on existing definitions and the existing coefficient interface, never on the item or its finiteness conclusion. D1–D4: the new node has no finiteness/constructibility conclusion, and the assembly still proves finiteness by the étale theorem. E1–E7: all size, qcqs, Noetherian, coefficient and boundedness hypotheses were checked as described above. The repair changes proof organization only; the item and Lean signature are unchanged.

## Not duplicates

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs def-sf-compact-support-site-comparison-construction: the existing node addresses Canonical compact-support site comparison construction; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional compact-support/open/Tate/coherence constructions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-trf-open-base-change-site-transport: the existing node addresses Site comparison preserves the named open base-change map; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional compact-support/open/Tate/coherence constructions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-trf-filtered-hom-complex-invariance: the existing node addresses Homotopy and graded quasi-isomorphism invariance of the shift-filtered Hom complex; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional filtered-Hom, scalar-linearity, local-isomorphism, exchange-square, or adjunction-specific assertions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-trf-proper-open-site-transport: the existing node addresses Site comparison preserves finite proper/open interchange; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional compact-support/open/Tate/coherence constructions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs def-per-site-comparison-pullback-data: the existing node addresses Canonical etale and pro-etale comparison pullback data; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional filtered-Hom, scalar-linearity, local-isomorphism, exchange-square, or adjunction-specific assertions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-weil-pbc-flat-restriction-derived-mate: the existing node addresses FlatRestrictionDerivedMate; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional filtered-Hom, scalar-linearity, local-isomorphism, exchange-square, or adjunction-specific assertions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-weil-pbc-finite-discrete-coefficient-direct-image-conjugation: the existing theorem conjugates internal and module-valued pro-etale direct images under a coefficient equivalence; the new theorem compares intrinsic etale and pro-etale direct images and their full/D+ constructions.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-weil-pbc-finite-discrete-direct-image-origin: the existing theorem asserts essential-image membership for an internal derived direct image; the new theorem gives the intrinsic full-category construction and its identified bounded-below comparison isomorphism.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-weil-pbc-dplus-injective-representative: the existing theorem constructs bounded-below K-injective representatives; the new theorem identifies the full direct-image functors and the etale/pro-etale comparison using those representatives.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-weil-pbc-derived-exchange-module-termwise: the existing node addresses K-injective representative of the module derived exchange mate; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional filtered-Hom, scalar-linearity, local-isomorphism, exchange-square, or adjunction-specific assertions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-weil-pbc-comparison-direct-image-canonical-mate: the existing theorem fixes the D+ counit-mate and its normalization; the new theorem concerns existence/computation on the full intrinsic module derived categories and identification with the D+ functors, without asserting additional mate/coherence equations.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-weil-pbc-kinjective-total-derived: the existing theorem assumes every complex has a K-injective resolution and gives abstract total-derived computation; the new theorem supplies the ringed-site realization, D+ compatibility and the etale/pro-etale comparison.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs def-weil-pbc-derived-local-isomorphism-sheaf: the existing node addresses Sheaf of derived local isomorphisms and canonical local coefficient transport; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional filtered-Hom, scalar-linearity, local-isomorphism, exchange-square, or adjunction-specific assertions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-weil-pbc-derived-exchange-unbounded-transport: the existing node addresses Transport of the exchange equation to arbitrary K-injective representatives; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional filtered-Hom, scalar-linearity, local-isomorphism, exchange-square, or adjunction-specific assertions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs prop-weil-pbc-comparison-direct-image: the existing theorem gives the D+ geometric comparison; the new theorem constructs the full ordinary intrinsic K-injective functors and identifies that D+ comparison with their restriction, including the coefficient-presentation identification.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-weil-pbc-derived-exchange-bounded-comparison: the existing node addresses The bounded below exchange comparison equation; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional filtered-Hom, scalar-linearity, local-isomorphism, exchange-square, or adjunction-specific assertions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-sf-exact-localization-derived-triangle: the existing node addresses Natural derived triangle of an exact localization sequence; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional filtered-Hom, scalar-linearity, local-isomorphism, exchange-square, or adjunction-specific assertions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-kun-right-derived-single-h0: the existing node addresses Zeroth homology of the canonical right-derived single augmentation; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional filtered-Hom, scalar-linearity, local-isomorphism, exchange-square, or adjunction-specific assertions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs def-pur-finite-tate-site-comparison: the existing node addresses Finite Tate tensor generators and root-normalized site comparison predicates; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional compact-support/open/Tate/coherence constructions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-sf-comparison-pullback-exact: the existing node addresses The comparison pullback is exact on sheaves of modules and commutes with cohomology sheaves; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional filtered-Hom, scalar-linearity, local-isomorphism, exchange-square, or adjunction-specific assertions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-sf-proper-open-comparison-site-normalization: the existing node addresses Normalization of the proper/open comparison under the site comparison; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional compact-support/open/Tate/coherence constructions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs def-sf-comparison-derived-pullback: the existing node addresses The derived pullback along the comparison morphism of sites; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional filtered-Hom, scalar-linearity, local-isomorphism, exchange-square, or adjunction-specific assertions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-sp-exact-pullback-derived-adjunction: the existing node addresses Normalized derived adjunction of exact module pullback; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional filtered-Hom, scalar-linearity, local-isomorphism, exchange-square, or adjunction-specific assertions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-amb-finite-tate-site-descent: the existing node addresses Finite Tate coefficients descend from pro-etale to etale sites; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional compact-support/open/Tate/coherence constructions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-cbc-comparison-pullback-sections: the existing node addresses Sections formula for the etale-to-pro-etale inverse image; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional filtered-Hom, scalar-linearity, local-isomorphism, exchange-square, or adjunction-specific assertions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-exc-etale-origin-open-restriction-transport: the existing node addresses Canonical comparison preserves normalized derived open restriction; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional compact-support/open/Tate/coherence constructions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-pur-ringed-derived-pushforward-linear: the existing node addresses Derived ringed-topos direct image preserves compatible central scalars; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional filtered-Hom, scalar-linearity, local-isomorphism, exchange-square, or adjunction-specific assertions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-asd-derived-counit-k-injective-termwise: the existing node addresses Derived counit on a K-injective representative; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional filtered-Hom, scalar-linearity, local-isomorphism, exchange-square, or adjunction-specific assertions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-exc-etale-origin-proper-open-interchange: the existing node addresses Site transport preserves the canonical Cartesian proper/open interchange; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional compact-support/open/Tate/coherence constructions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-amb-compact-support-open-factor: the existing node addresses The open factor of compact-support site comparison; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional compact-support/open/Tate/coherence constructions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-amb-open-site-evaluation-counit: the existing node addresses Evaluation normalization for the open site comparison; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional compact-support/open/Tate/coherence constructions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-pur-vector-integration-site-comparison: the existing node addresses Finite-level site comparison of normalized vector-bundle integration; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional compact-support/open/Tate/coherence constructions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-fix-site-open-exchange-square: the existing node addresses Specialized inverse-image comparison square for open exchange; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional compact-support/open/Tate/coherence constructions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-amb-compact-support-proper-factor: the existing node addresses The proper factor of compact-support site comparison; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional compact-support/open/Tate/coherence constructions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs def-amb-finite-tate-site-comparison-data: the existing node addresses Fixed-scalar finite Tate presentations and root-normalized comparisons; the new theorem constructs ordinary intrinsic derived direct images and identifies their D+ site comparison, without the additional compact-support/open/Tate/coherence constructions of that node.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs def-weil-pbc-kinjective-resolutions: the existing node defines K-injectivity; the new node asserts existence and computation of full derived direct images and their bounded-below site comparison.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs src-right-derived-functor-plus-compatibility: the existing generic isomorphism assumes enough injectives and K-injective resolutions; the new theorem supplies their small ringed-site setting and intrinsic coefficient comparison and also the geometric etale/pro-etale isomorphism.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-sfb-unbounded-direct-image-comparison: that node allows unbounded inputs over finite or algebraically closed base fields; the new node allows arbitrary schemes but keeps the necessary bounded-below input and identifies the intrinsic full/D+ constructions.

lem-sfb-ordinary-proetale-direct-image-plus-comparison vs lem-sfb-finite-field-proetale-direct-image: the item concludes bounded constructibility for finite-type schemes over an arbitrary field; the new node asserts no constructibility or output boundedness and isolates the ordinary-derived comparison interface.
