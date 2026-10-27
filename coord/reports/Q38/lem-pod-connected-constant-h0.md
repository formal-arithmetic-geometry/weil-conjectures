# Worker report

Files written: item lem-pod-connected-constant-h0 (statement and Lean record unchanged); three new statement-only nodes, all unsplit with no Mathlib match:

- lem-pod-finite-sheaf-h0-augmentation: statement, no match.
- lem-pod-constant-direct-image-tower-realization: statement, no match.
- lem-pod-rational-ordinary-cohomology-tensor: statement, no match.

Attachments: none. The recorded theorem in Sheaf/Paper/ConnectedConstantH0.lean ends in sorry (line 399); the upstream global-sections line theorem concerns PadicAlgCl and does not supply finite/integral/rational derived cohomology or the specified maps.

WANTED: none.

The sandbox was empty apart from dispatcher markers; current live JSON supplies the returned nine-step proof. The released repair note explicitly requires a new split even though the item has an older passing review. No repository files or launcher scripts were written and no compiler was run.

## Repair and allocation of the old arguments

The three new nodes do not restate the connected H0 theorem or its clauses: finite augmentation allows any module sheaf without connectedness; integral tower realization asserts the triangle and its actual maps, not the H0 limit isomorphism or scalar computation; rational comparison applies to every integral object and degree, without computing any cohomology. Existing lem-pur-proetale-finite-constant-sections already contains old steps 2-3, so creating that node again would be a duplicate.

- Old step 1: finite-sheaf-h0-augmentation, including nonnegative resolutions, K-injectivity, left exact image, exact point sections, evaluation, negative vanishing and augmentation normalization.
- Old steps 2-3: existing lem-pur-proetale-finite-constant-sections, whose proof explicitly constructs the ring-valued continuous-function sheaf and its sheafification map. Coefficient naturality is checked on open constant-value fibres in new assembly step 1.
- Old step 4: assembly step 1 retains the nonempty clopen-fibre argument, evaluation inverse, scalar action, and reduction on constants.
- Old steps 5-6: constant-direct-image-tower-realization retains the common coefficient category, derived limit, exact point evaluation, canonical finite reductions, restriction-of-scalars comparison and actual transition identification. It does not hide Milnor or adic reconstruction.
- Old step 7: assembly step 2 applies the existing Milnor lemma using vanishing H^-1.
- Old step 8: assembly step 3 uses the existing finite-module completion lemma with M=O_E and retains the unique unit and projection formulas.
- Old step 9: rational-ordinary-cohomology-tensor retains the fraction-field localization and flat kernel/image/quotient argument; assembly step 4 tensors the scalar-unit isomorphism and its inverse.

## Review by Q38

I read Bhatt--Scholze Lemma 4.2.12 (printed p. 30), including its discrete-space conclusion, Milne printed pp. 124-126, and Stacks derived.tex lemma-left-exact-higher-derived (05TD), sites-cohomology.tex lemma-RGamma-commutes-with-Rlim (0D6K), and algebra.tex lemma-flat-localization (00HT). These agree with the realizations being extracted: they assert canonical augmentation, actual limit projections, and ordinary rational tensor, respectively. The blueprint's current Step 7 needs connectedness, neither smoothness nor properness.

Assembly step 1 uses the finite augmentation node for H0=sections and negative vanishing; I read the full statement of the existing pro-etale finite-constant sections node, including its ring operations, constants and restriction normalization. Connectedness is only used for the explicitly written clopen-fibre argument; nonemptiness supplies y and injectivity of constants. Reduction respects constants by the sheafification unit; covering by open constant-value fibres gives equality on all sections. This also handles n=1. Empty Y has zero sections and zero cohomology, so the new finite and tower nodes allow empty Y, while the parent's nonempty condition remains essential. Disconnected Y has independent constants on components, so no new realization claims that its sections are a scalar line.

Assembly step 2 uses precisely the triangle, projection and transition assertions of the new tower node and the countable D(Ab) clause of lem-weil-pbc-mittag-leffler. I opened that node: its hypothesis is finiteness of H^(i-1), not H^i or all higher groups. At i=0 the finite augmentation node gives the required zero groups. The chosen small skeleton is the one in def-weil-pbc-proetale-site; n starts at 1 and reindexing by m+1 matches the standard tower. The tower node explicitly retains finite reduction, exact restriction, and identity on sections from def-trf-point-reduction-units.

Assembly step 3 cites the actual converse (2) of lem-pod-adic-limit-finite-modules, applied to the singly generated module V. This is not an unproved assertion that every inverse limit of finite modules is finite. The tuple of units is compatible by step 1, step 2 gives its unique preimage, and linearity checks the scalar map on each coordinate.

Assembly step 4 takes the canonical cycle-tensor comparison and normalization from the rational node; it does not assume that an arbitrary isomorphism preserves one. The new statement allows every K and degree and introduces its integral model, rationalization, point realization, and cycle formula. At zero complexes it is the zero isomorphism; torsion classes killed by localization map to zero, as expected. E is a localization V[1/varpi] because each nonzero element is a unit times an integral power of varpi; flatness preserves kernels, images and their quotient without a boundedness assumption on the representative. Tensoring an isomorphism with its inverse verifies the last scalar bijection without an additional theorem.

B--E audit: new statements introduce all data, use single TeX escaping, carry exact source places and blueprint ancestry, and have empty proof/proof_deps/proof_origin. All three kinds plus LeanFinder were actually run through msearch, with second semantic phrasings; full outputs are retained in search-*.txt and the exact log in searches.jsonl. Loogle unknown-identifier attempts are retained as diagnostic results and followed by syntactically accepted searches. The rightDerivedZeroIsoSelf hit was read in Mathlib: it does not identify the project's K-injective pro-etale direct image, actual evaluation and augmentation without additional comparisons. EllAdicCohomology only defines Z_l sheaf cohomology; it does not give our maps. No matching full declaration or blueprint node was found. I corrected the proposed redundant constant-function extraction by citing the existing finite pro-etale node instead. No statement dispute or route change was needed.

## Preserved returned proof (verbatim argument archive)

### Old step 1

Put $s=\operatorname{Spec}k$ and $F_n=(A_{E,n})_Y$. The module-sheaf categories on the chosen small pro-etale sites are Grothendieck by [prop-pur-kinjective-resolutions-exist], hence have enough injectives by [lem-sp-grothendieck-enough-injectives]. Choose $F_n\to I_n^\bullet$ with $I_n^j=0$ for $j<0$ using [lem-weil-pbc-left-exact-injective-resolution-degree-zero](1). This bounded-below injective complex is K-injective by [lem-weil-pbc-bounded-below-injectives-kinjective], so [def-weil-derived-direct-image] computes $Ra_{Y*,n}F_n$ by $a_{Y*}I_n^\bullet$. Direct image is left exact by [lem-weil-proetale-module-direct-image-left-exact], and part (2) of the degree-zero lemma gives $\mathcal H^0(Ra_{Y*,n}F_n)=a_{Y*}F_n$. Exact point sections [lem-weil-point-proetale-sections-exact] identify $H^0(\Gamma(s,a_{Y*}I_n^\bullet))$ with $\Gamma(s,a_{Y*}F_n)=F_n(Y)$; the last equality is the evaluation formula in [def-weil-proetale-module-direct-image], since $s\times_sY=Y$. By [def-weil-finite-coefficient-point] and [def-weil-ordinary-compact-cohomology] this is $H^0(Y,A_{E,n})$. All complexes used have zero terms in negative degrees, so $H^{-1}(Y,A_{E,n})=0$ as well. The identifications are induced by the resolution augmentation and evaluation, hence send constant sections to their degree-zero classes.

Uses: prop-pur-kinjective-resolutions-exist, lem-sp-grothendieck-enough-injectives, lem-weil-pbc-left-exact-injective-resolution-degree-zero, lem-weil-pbc-bounded-below-injectives-kinjective, def-weil-derived-direct-image, lem-weil-proetale-module-direct-image-left-exact, lem-weil-point-proetale-sections-exact, def-weil-proetale-module-direct-image, def-weil-finite-coefficient-point, def-weil-ordinary-compact-cohomology

### Old step 2

Give the additive group $T=A_{E,n}$ the discrete topology. Addition and negation are continuous because every map between discrete spaces is continuous. The existing Mathlib leaf [lem-cbc-continuous-functions-fpqc-sheaf] says that $L_T(U)=C(|U|,T)$, with pointwise addition and restrictions by precomposition, is an fpqc sheaf on schemes. Every pro-etale covering is fpqc by [def-weil-pbc-proetale-site], so restriction to $Y_{\mathrm{proet}}$ is a sheaf. A map to a discrete space is continuous exactly when it is constant on some open neighbourhood of every point: inverse images of singletons are open, and conversely the inverse image of any subset is the union of those open fibres. Pointwise multiplication and the constant function $1$ make $L_T$ a sheaf of rings as well: these operations preserve continuity into the discrete ring, and all ring identities are pointwise equalities.

Uses: lem-cbc-continuous-functions-fpqc-sheaf, def-weil-pbc-proetale-site

### Old step 3

The map from the constant presheaf $P_T(U)=T$ to $L_T$ sends $t$ to the constant function with value $t$. It exhibits $L_T$ as the sheafification in [def-weil-pbc-sheafification]: for any presheaf map $P_T\to G$ with $G$ a sheaf, and any $f\in L_T(U)$, cover $U$ by the open fibres $f^{-1}(t)$ and glue the images in $G$ of their constant values $t$. These are pro-etale coverings by [def-weil-pbc-proetale-site]; intersections with different values are empty and an abelian sheaf has only its zero section on the empty object. On overlaps with the same value the images agree by naturality. Intersecting two such open covers proves independence, and pulling back the cover proves compatibility with restrictions; intersecting the covers for two functions proves additivity. Every extension must have these local values, so uniqueness follows from the sheaf condition. For a map $P_T\to G$ of ring-valued presheaves into a sheaf of rings, the same extension preserves multiplication by intersecting the constant-value covers of two functions, and preserves $1$ on every member of the cover. Thus the ring version of [def-weil-pbc-constant-sheaf] identifies $(A_{E,n})_Y$ with $L_T$, carrying each constant section to its constant function. This construction commutes with a coefficient homomorphism $T\to T'$: on every open where $f=t$ both composites give the image of $t$, and uniqueness of gluing gives equality globally.

Uses: def-weil-pbc-sheafification, def-weil-pbc-proetale-site, def-weil-pbc-constant-sheaf

### Old step 4

Choose $y\in Y$, possible by the nonemptiness in [def-weil-connected-scheme]. For $f\in L_T(Y)$ the fibre $f^{-1}(f(y))$ is nonempty and clopen, since both it and its complement are inverse images of open subsets of the discrete space $T$. Connectedness makes its complement empty. Therefore $f$ is the constant function $f(y)$. Conversely distinct constants give distinct functions by evaluation at $y$. Together with Steps 1 and 3 this proves that $A_{E,n}\to H^0(Y,A_{E,n})$ is an isomorphism of additive groups, equal to $a\mapsto a\cdot1$. It is $A_{E,n}$-linear: multiplication by $a$ sends the constant section $b$ to the constant section $ab$, which can be checked before sheafification and then on the same open covers. The coefficient-naturality at the end of Step 3 shows that the reduction maps send the section $a$ to the section $a\bmod\varpi_E^n$; hence these isomorphisms identify the entire inverse system with $(A_{E,n})_n$.

Uses: def-weil-connected-scheme

### Old step 5

Let $B_n=\operatorname{Res}_n Ra_{Y*,n}F_n$ and $B=Ra_{Y*}\widehat{\mathcal O}_{E,Y}$. By [def-weil-completed-integral-coefficients], [lem-weil-constant-coefficient-objects-constructible](2), and [def-weil-derived-direct-image], $B=R\varprojlim_nB_n$ with its canonical projections. Applying [lem-kun-site-rgamma-derived-limit] on $s_{\mathrm{proet}}$ and using exact point sections [lem-weil-point-proetale-sections-exact] gives $\Gamma(s,B)\simeq R\varprojlim_n\Gamma(s,B_n)$ in $D(\operatorname{Ab})$, with the original projection maps. Use the small skeleton fixed in [def-weil-pbc-proetale-site], the ring sheaf $\widehat{\mathcal O}_{E,s}$ and final object $s$; reindex $n=m+1$ for the lemma's $m\geq0$ convention.

Uses: def-weil-completed-integral-coefficients, lem-weil-constant-coefficient-objects-constructible, def-weil-derived-direct-image, lem-kun-site-rgamma-derived-limit, lem-weil-point-proetale-sections-exact, def-weil-pbc-proetale-site

### Old step 6

Restriction of scalars does not change underlying sections. By [def-weil-finite-coefficient-point] and [def-weil-ordinary-compact-cohomology], $\Gamma(s,B_n)$ computes $H^i(Y,A_{E,n})$ and $\Gamma(s,B)$ computes integral cohomology. The map $\widehat{\mathcal O}_{E,Y}\otimes^L_{\mathcal O_E}A_{E,n+1}\to\widehat{\mathcal O}_{E,Y}\otimes^L_{\mathcal O_E}A_{E,n}$ of the tower corresponds to the reduction $F_{n+1}\to F_n$ under the canonical isomorphisms of [lem-weil-constant-coefficient-objects-constructible](2), since both of these isomorphisms are induced by the projections and $\pi_n$ is the reduction composed with $\pi_{n+1}$. Apply [lem-pod-constant-tower-transition] with $f=a_Y$, $A=A_{E,n+1}$, $B=A_{E,n}$ and $u:F_{n+1}\to\operatorname{Res}F_n$ the reduction. The transition in [def-weil-derived-direct-image] is exactly the composite in that node. Exact point sections [lem-weil-point-proetale-sections-exact] therefore identify its $H^0$ map with $F_{n+1}(Y)\to F_n(Y)$. By Step 4, this is coefficient reduction $A_{E,n+1}\to A_{E,n}$.

Uses: def-weil-finite-coefficient-point, def-weil-ordinary-compact-cohomology, lem-weil-constant-coefficient-objects-constructible, lem-pod-constant-tower-transition, def-weil-derived-direct-image, lem-weil-point-proetale-sections-exact

### Old step 7

Step 1 gives $H^{-1}(\Gamma(s,B_n))=0$, which is finite. Therefore the degree-zero case of [lem-weil-pbc-mittag-leffler] applies to the tower in Step 5 and identifies the canonical projection map $H^0(Y,\mathcal O_E)\to\varprojlim_nH^0(Y,A_{E,n})$ as an isomorphism. No finiteness of higher cohomology is needed.

Uses: lem-weil-pbc-mittag-leffler

### Old step 8

Apply [lem-pod-adic-limit-finite-modules](2) to $M=\mathcal O_E$, generated by $1$ as an $\mathcal O_E$-module. It gives the canonical isomorphism $\mathcal O_E\xrightarrow{\sim}\varprojlim_n\mathcal O_E/\varpi_E^n\mathcal O_E=\varprojlim_n A_{E,n}$; the quotient rings and transition maps are exactly those of [def-weil-l-adic-coefficient-extension]. By the inverse-system compatibility of Step 4 and the projection comparison of Step 7, this proves clause (2). Its distinguished element $1_{\mathcal O_E}$ maps to the system $(1\bmod\varpi_E^n)_n$, so the inverse isomorphism $\mathcal O_E\to H^0(Y,\mathcal O_E)$ is $a\mapsto a\cdot1_{\mathcal O_E}$.

Uses: lem-pod-adic-limit-finite-modules, def-weil-l-adic-coefficient-extension

### Old step 9

By [def-weil-rationalization-karoubi], the rational coefficient object is represented by the integral coefficient object and $Ra_{Y*}$ at $E$ is its rationalization, as stipulated in [def-weil-derived-direct-image]. By [def-weil-finite-coefficient-point](3), its cohomology complex is $C^\bullet\otimes_{\mathcal O_E}E$, where $C^\bullet=\Gamma(s,Ra_{Y*}\widehat{\mathcal O}_{E,Y})$. In [def-weil-l-adic-coefficient-extension], every nonzero element of $E$ is $u\varpi_E^m$ for a unit $u\in\mathcal O_E$ and $m\in\mathbf Z$, so $E=\mathcal O_E[1/\varpi_E]$. Its inclusion satisfies the localization conditions (every element is a fraction, powers of $\varpi_E$ are invertible, and the kernel is zero), hence [lem-weil-pbc-localization-flat] gives flatness. Flat tensor product preserves the kernel of $d^0$ and the image of $d^{-1}$, and preserves the quotient of the former by the latter. Therefore $H^0(C^\bullet\otimes E)=H^0(C^\bullet)\otimes E$, which is the equality in clause (3) by [def-weil-ordinary-compact-cohomology]. Tensor the unit isomorphism of Step 8 with $E$: its inverse tensors to an inverse, and $1_{\mathcal O_E}\otimes1=1_E$, so the resulting isomorphism is precisely $\lambda\mapsto\lambda\cdot1_E$.

Uses: def-weil-rationalization-karoubi, def-weil-derived-direct-image, def-weil-finite-coefficient-point, def-weil-l-adic-coefficient-extension, lem-weil-pbc-localization-flat, def-weil-ordinary-compact-cohomology


## Not duplicates

lem-pod-finite-sheaf-h0-augmentation vs lem-weil-pbc-cohomology-pullback-degree-zero-iso-factor: the existing assertion is for a supplied cycle lift on the small etale abelian site; the new assertion realizes the finite pro-etale module direct image to s, its coefficient action and all negative degrees.

lem-pod-finite-sheaf-h0-augmentation vs lem-weil-pbc-complex-injective-resolution-mono: existing constructs an injective resolution in an abstract abelian category; new computes the project point-evaluated pro-etale direct image and normalizes its classes.

lem-pod-finite-sheaf-h0-augmentation vs lem-weil-pbc-dplus-injective-representative: existing supplies representatives, not the section-to-cohomology map of a finite coefficient structure morphism.

lem-pod-finite-sheaf-h0-augmentation vs lem-weil-pbc-left-exact-injective-resolution-degree-zero: existing proves abstract v(X)=H0(vI); new additionally realizes K-injective pro-etale Rf, exact point evaluation, actual finite cohomology and the scalar action.

lem-pod-finite-sheaf-h0-augmentation vs new-lem-pc-derived-bottom-cycle-transport: existing compares bottom-truncation morphisms; new concerns the finite sheaf section augmentation and negative vanishing after point sections.

lem-pod-finite-sheaf-h0-augmentation vs new-lem-pc-derived-bottom-inclusion: existing factors maps from a single object via truncation; new identifies the point cohomology of a finite pro-etale direct image.

lem-pod-finite-sheaf-h0-augmentation vs new-lem-pc-derived-cycles-map-homology: existing gives homology of a specified cycles-derived map; new proves its geometric finite-direct-image realization and section normalization.

lem-pod-finite-sheaf-h0-augmentation vs new-lem-pc-derived-cycles-unit-naturality: existing states an abstract derived-unit equality with truncations; new is the finite pro-etale point realization with negative-degree vanishing.

lem-pod-finite-sheaf-h0-augmentation vs new-lem-pc-derived-single-shift-normalization: existing cancels a shifted classical derived-unit composite; new compares geometric direct image, exact point sections and actual finite ordinary cohomology.

lem-pod-finite-sheaf-h0-augmentation vs lem-pod-constant-tower-transition: existing identifies a coefficient-change H0 morphism under supplied augmentations; new constructs the point-valued augmentation and proves negative vanishing, without the coefficient-change square.

lem-pod-finite-sheaf-h0-augmentation vs lem-weil-pbc-cohomology-pullback-degree-zero: existing treats etale abelian cohomology and pullback; new treats module-valued pro-etale direct image to the algebraically closed point and the recorded finite coefficient functor.

lem-pod-finite-sheaf-h0-augmentation vs lem-weil-pbc-derived-functor-map-via-lift: existing computes abstract R^n of a map via an injective lift; new supplies the geometric realization and actual section augmentation.

lem-pod-constant-direct-image-tower-realization vs new-lem-pc-derived-bottom-cycle-transport: existing is an abstract bottom-truncation transport equation; new realizes a completed coefficient tower and its canonical projections and transitions.

lem-pod-constant-direct-image-tower-realization vs new-lem-pc-derived-bottom-inclusion: existing factors a map through bottom homology; new is a countable coefficient-tower derived-limit comparison.

lem-pod-constant-direct-image-tower-realization vs new-lem-pc-derived-cycles-map-homology: existing computes the homology of a cycles inclusion; new preserves the specified completed direct-image tower maps under point sections.

lem-pod-constant-direct-image-tower-realization vs new-lem-pc-derived-cycles-unit-naturality: existing is a unit/naturality identity; new identifies finite-reduction and scalar-restriction comparisons for an entire tower.

lem-pod-constant-direct-image-tower-realization vs new-lem-pc-derived-single-shift-normalization: existing normalizes a single shifted object under a derived functor; new realizes the completed direct image as a point-sections limit with actual P and Q.

lem-pod-constant-direct-image-tower-realization vs lem-pod-constant-tower-transition: existing treats one arbitrary finite coefficient-change map assuming augmentation identifications; new assembles completed sheaf reductions, derived limit, point sections, projections and transitions of the specified tower.

lem-pod-constant-direct-image-tower-realization vs lem-weil-pbc-cohomology-pullback-degree-zero-iso-factor: existing gives an etale H0 augmentation isomorphism for a supplied cycle lift; new is the completed pro-etale coefficient limit and reduction-map comparison.

lem-pod-constant-direct-image-tower-realization vs lem-weil-pbc-cohomology-pullback-degree-zero: existing is etale H0 sections and pullback, not integral completion or point-evaluated inverse systems.

lem-pod-constant-direct-image-tower-realization vs lem-weil-pbc-derived-functor-map-via-lift: existing computes a single derived map by a lift; new compares the specified integral direct-image triangle and all its finite reductions.

lem-pod-constant-direct-image-tower-realization vs lem-weil-pbc-left-exact-injective-resolution-degree-zero: existing is an abstract H0 augmentation calculation; new realizes the completed tower including its derived-limit projections.

lem-pod-constant-direct-image-tower-realization vs lem-sbc-base-change-homology-zero-underived: existing concerns an etale Cartesian base-change square; new concerns coefficient reduction and completed pro-etale point realization.

lem-pod-constant-direct-image-tower-realization vs lem-sbc-right-derived-base-change-zero-unit: existing is an abstract base-change-unit equality; new includes the whole completed coefficient triangle and its point sections, not only a single equality.

lem-pod-rational-ordinary-cohomology-tensor vs lem-pc-flat-final-coefficient-model-comparison: existing compares two supplied ordinary tensor cohomology models across a final coefficient extension; new identifies the actual project rationalized direct-image point functor with cycle-tensor cohomology.

lem-pod-rational-ordinary-cohomology-tensor vs lem-pc-flat-iterated-scalar-extension-homology-square: existing proves a square for supplied chain isomorphisms and ordinary modules; new constructs the canonical integral/rational cohomology comparison and its unit normalization.

lem-pod-rational-ordinary-cohomology-tensor vs lem-pc-flat-scalar-extension-homology-adjunct: existing proves ordinary flat-module homology adjunct is invertible; new must identify rationalization of sheaf direct image and its specified point functor with that adjunct.

lem-pod-rational-ordinary-cohomology-tensor vs lem-pc-prescribed-tensor-cohomology-model-realization: existing realizes supplied universal ordinary tensor cohomology models over one ring; new concerns the project integral/rational coefficient categories and canonical point evaluation.

lem-pod-rational-ordinary-cohomology-tensor vs lem-pc-scalar-restricted-tensor-retract-flat: existing proves flatness of a sheaf tensor retract; new concerns rational derived cohomology and canonical cycle classes.

lem-pod-rational-ordinary-cohomology-tensor vs lem-weil-pbc-flat-fg-ideal-criterion: existing characterizes flat modules using ideals; new gives an explicit rational cohomology comparison with normalization.

lem-pod-rational-ordinary-cohomology-tensor vs lem-weil-pbc-flat-tensor-exact: existing preserves exact sequences under tensor; new also identifies the project rational point-cohomology functor and cycle formula.

lem-pod-rational-ordinary-cohomology-tensor vs lem-weil-pbc-limit-flat-modules: existing concerns flatness of a limit of adic flat modules and tensor/limit interchange; new concerns field localization of integral cohomology, not a module-limit flatness claim.

lem-pod-rational-ordinary-cohomology-tensor vs lem-trf-parameter-product-closure-kernel: existing computes scheme-theoretic closure ideals for parameter products; new is rational coefficient cohomology.

lem-pod-rational-ordinary-cohomology-tensor vs lem-sc-principal-cokernel-projective-descent: existing descends injectivity and projectivity from principal localizations; new compares rational and integral point cohomology.

lem-pod-rational-ordinary-cohomology-tensor vs lem-sc-affine-standard-cover-finite-free-local-fp-flat: existing proves a finite free module is finitely presented and flat; new identifies the actual rational cohomology map.

lem-pod-rational-ordinary-cohomology-tensor vs lem-pc-affine-associated-module-flat-over: existing proves flatness of an associated affine sheaf; new is a rational derived cohomology comparison.

Additional overlap checked: lem-pur-proetale-finite-constant-sections already supplies old steps 2-3 and is reused directly; lem-kun-site-rgamma-derived-limit is generic and does not identify the project coefficient transitions/projections; lem-pc-flat-tensor-complex-cohom assumes bounded ordinary module complexes and does not identify the rationalized point functor.
