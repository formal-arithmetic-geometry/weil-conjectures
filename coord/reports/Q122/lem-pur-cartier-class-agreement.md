# Repair report: lem-pur-cartier-class-agreement

1. Files written:
- Item: dag/nodes/sec-smooth-purity/lem-pur-cartier-class-agreement.json, statement unchanged, three-step assembly.
- lem-pur-cartier-relative-boundary-realization, statement, unsplit, no Mathlib match.
- lem-pur-supported-root-scalar-site-comparison, statement, unsplit, no Mathlib match.
2. Attachments: none. The current theorem WeilConjectures.PurityFiniteSetting.cartier_class_agreement in lean/Sheaf/Paper/CartierClassAgreement.lean:116 ends with sorry. No project declaration under WeilConjectures states the full item.
3. WANTED: none.
4. Returned fault: the existing seven-step proof concentrates 6773 characters of work in one node. The sandbox was empty apart from brief markers, so its starting material is the current repository node, whose seven step lengths exactly match the return. No prior report or search log was present to discard.
5. Unfinished: the two new nodes deliberately have no proof, as required by the human's re-split decision. Their arguments below are a handoff to independently claimable tasks. No Lean was written or compiled.

## Return repair and distribution

Original steps 1-3 (2518 characters) become lem-pur-cartier-relative-boundary-realization: global frame/trivialization, relative connecting class, signed module/abelian cone comparison. Original steps 4-5 (2629 characters) become lem-pur-supported-root-scalar-site-comparison: exact closed direct image, normalized coefficient unit, flat root target, scalar extension on supported Hom, root-projection identification, and site comparison. Original step 6 is the parent's substitution of the specified recipe for c_D. Original step 7 remains verbatim as assembly step 3. The independent tasks are comparable in argument size, and neither states the full item or its pullback conclusion. The second is formulated for arbitrary closed support and arbitrary supported root class, to expose the actual coefficient comparison independently of Cartier geometry.

The parent proof is 2213 characters, below 3000. Neither new node has proof steps or proof dependencies. The original statement, including its normalization and lack of smoothness hypotheses, is byte-for-byte unchanged.

## Sources and searches

Read main-20261015 thm-pur-localized-top-chern.proof.md, Step 4 (L1), and lem-amb-cartier-kummer-map.proof.md in full. The latter gives the specified relative pair in paragraphs 1-2, its relative Kummer and supported Hom realization in paragraph 3, and scalar extension in the final paragraph. These are agent-authored blueprint arguments: the extracted compatibility statements are refinements of them, not falsely attributed as verbatim Stacks theorems. Read Stacks etale-cohomology.tex, Tag 03PL, label lemma-kummer-sequence, and sites-cohomology.tex, Tag 07A6, label lemma-adjoint. These justify the existing exact Kummer and derived-adjunction nodes used by the retained arguments. No SGA route is used.

DAG and blueprint searches: ancestor gives thm-pur-localized-top-chern; blueprint search queries relative Kummer, scalar extension, coefficient unit, relative divisor, supported Hom and relative torsor. Whole-DAG statement/title searches and source Lean searches for Cartier/relative Kummer/supported scalar terms identified the nearby nodes discussed below. Each new node has its own semantic query and second phrasing, a Loogle query and Mathlib-source grep, recorded by msearch.py in searches.jsonl. Read all printed hits. Generic H1 cocycles and Picard groups do not compare relative signed support realizations; cotangent cohomology and scheme tensor pullbacks do not state the second node. Read Mathlib CategoryTheory/Sites/CartesianMonoidal.lean: tensorUnit_isSheaf is a sheaf condition, not derived scalar-unit normalization. No Mathlib match was found.

## Not duplicates

- lem-pur-cartier-relative-boundary-realization vs lem-pur-divisor-class: it defines the global divisor class and its local negative-boundary convention; the new task identifies its signed module relative-cone realization and global coefficient expression.
- lem-pur-cartier-relative-boundary-realization vs lem-amb-relative-torsor-cohomology: it classifies relative torsor pairs and their connecting maps; it does not identify the module and abelian relative cones or the specified Cartier class.
- lem-pur-cartier-relative-boundary-realization vs lem-pur-divisor-relative-cone: it compares abelian relative and supported cones; the new task compares module forgetting and applies it to the global Cartier boundary.
- lem-pur-cartier-relative-boundary-realization vs lem-asd-ordinary-supported-kummer: it constructs the ordinary etale supported morphism; the new task compares the general divisor class to the signed relative R-module class before scalar extension.
- lem-pur-cartier-relative-boundary-realization vs def-pur-cartier-agreement-maps: it defines a particular agreement map; it asserts no comparison theorem between the module and abelian relative complexes.
- lem-pur-supported-root-scalar-site-comparison vs lem-geo-cartier-coeff-extension: it identifies the scalar-extended supported source and its normalization only; the new task also identifies the class, target unit and full root/site comparison.
- lem-pur-supported-root-scalar-site-comparison vs lem-asd-supported-kummer-boundary-scalar: it states scalar compatibility for normalized Cartier boundary classes on the etale site; the new task concerns any root-supported class on any closed support and its pro-etale realization.
- lem-pur-supported-root-scalar-site-comparison vs lem-pur-sheaf-ring-derived-coefficient-adjunction: it gives the general scalar adjunction on K-flat representatives, not the comparison with signed support-Hom cohomology and roots projection.
- lem-pur-supported-root-scalar-site-comparison vs lem-pur-supported-hom-pullback: it gives fixed-coefficient site and pullback naturality, not the change-of-coefficient identification on supported classes.
- lem-pur-supported-root-scalar-site-comparison vs lem-sfb-closed-supported-scalar-comparison: it concerns an inverse-image-normalized pro-etale closed scalar mate under supplied unbounded open/closed calculus, not root-supported cohomology and the etale-to-pro-etale coefficient formula.
- lem-pur-supported-root-scalar-site-comparison vs lem-asd-supported-kummer-scalar-source: it states the source comparison; the new task additionally compares arbitrary root classes, coefficient units and the final site/root target.
- lem-pur-supported-root-scalar-site-comparison vs lem-pur-cartier-class-agreement: the parent compares two particular constructed Cartier classes and their pullback; the new task is a scalar/site formula with arbitrary input class and arbitrary closed support.

## Review by Q122

I checked the two tasks against their actual blueprint paragraphs and the original seven arguments, not only against metadata. The relative-boundary task retains the global torsor pair, rather than attempting to glue higher cohomology from local restrictions. Its section is the dual ideal-inclusion section; for an ideal generator f_a and dual basis e_a, it is f_a e_a. Changing to f_b changes the basis by f_a/f_b, so this is the same section on overlaps. The signed cone sends k to (k,0); its boundary is (0,-b). Thus the extracted statement keeps the original relative lift and sign; it does not replace it by a characterization by ordinary c_1. Its new derived comparison is stated as an isomorphism of complexes in D(Ab), not only as a list of cohomology isomorphisms.

For parent step 1, I read the entire new relative-realization statement: it explicitly supplies beta_D, b_D and cl(D)=t_*nu^*beta_D and identifies the pair used in both recipes. For step 2, the entire new scalar/site statement supplies precisely the displayed chi equation, the supported-source unit, the degree-zero etale witness and the q normalization. Substitution of the item statement's explicit c_D recipe then gives the first equality. Step 3 uses lem-amb-cartier-kummer-map's stated equality under Cartier-preserving pullback, lem-pur-supported-hom-pullback's exact chi/pullback and site-comparison equations, lem-pur-supported-cup-functoriality's canonical supported pullback on both sites, and lem-pur-supported-hom's natural isomorphism. I opened all four statements and their used clauses are copied verbatim in citations.json. B[0] meets the bounded-below requirement; q transports it to the prescribed twist. The source comparison is inverted in both formulas. Cancellation of chi is legitimate because it is an isomorphism.

For the second new task, the general closed support is justified by lem-geo-cartier-coeff-extension's actual statement for any closed immersion, rather than applying the Cartier-only scalar assertion outside its hypotheses. I read that statement and the nearby scalar-source and scalar-boundary statements. A closed immersion is finite, and the existing finite-direct-image-exact statement applies; coefficient forgetting computes kernels and cokernels so the same exactness holds for modules. The root sheaf is a flat line over R, and its degree-zero complex is K-flat, as the original cited statements assert. No step assumes A flat over R. The normalized adjunction unit is x to x tensor 1; evaluating at the supported constant generator yields the coefficient map, then q(v tensor a)=a sigma rho(v) gives q nu^-1 u=t. Site naturality is applied only to B[0]. These arguments are preserved below for the next workers.

I checked delivery-errors B-E: each new statement introduces all objects and hypotheses, names its notions, has no embedded proof sketch, uses single-escaped TeX, and retains provenance and actual search results. Existing constructions and scalar/source facts are reused, not recreated. The parent has three steps, all with exact node citations, and no hidden long step exceeds 2000 characters. The statement is unchanged, so there is no new statement dispute. I checked empty T and empty D (zero supported class), the identity pullback, nonreduced effective Cartier divisors, and ramified pullback t to t^r (still Cartier). A map landing entirely in D is excluded unless its pullback ideal remains Cartier; no regularity or smoothness is smuggled in. For the scalar task Z may be all of T or empty. Coefficient levels n=1 and levels not divisible by the ramification index still satisfy ell^n A=0, and the root-line computation still has degree zero.

## Original arguments retained for the independent tasks

These are report-only handoff material; neither unsplit node contains proof steps.

### Original step 1 → lem-pur-cartier-relative-boundary-realization

Put $W=T\setminus D$. The general construction explicitly stated in [lem-pur-divisor-class] applies to this Cartier divisor; the smooth-subfamily hypotheses belong to its first clause. Write $L=\mathcal I_D^\vee$ as in [def-pc-divisor-line-bundle]. If $\mathcal I_D=(f_a)$, let $e_a$ be the basis dual to $f_a$; the canonical section is $s_D=f_ae_a$. On overlaps $e_b=(f_a/f_b)e_a$, whence $f_be_b=f_ae_a$. On $W$ this is a frame. Thus both recipes start with the same global line bundle and specified frame, including the trivialization data. By [lem-sc-line-bundle-torsor] its frame sheaf $P_D$ is a $\mathbf G_m$-torsor. By [lem-amb-relative-torsor-cohomology] the pair $(P_D,s_D|_W)$ has a specified class $\alpha_D\in H^1(T,W;\mathbf G_m)$.

Cited node statements to reuse: lem-pur-divisor-class, def-pc-divisor-line-bundle, lem-sc-line-bundle-torsor, lem-amb-relative-torsor-cohomology.

### Original step 2 → lem-pur-cartier-relative-boundary-realization

Take $N=\ell^n$ and $R=\mathbf Z/N\mathbf Z$ as in [def-pur-frame-class]. Since $\ell\ne\operatorname{char}k$, $N$ is invertible on $T$; since $\ell\in(\varpi_E)$, $NA=0$. The exact sequence [lem-amb-kummer-any-base] and the relative connecting map of [lem-amb-relative-torsor-cohomology] give $\beta_D=\delta_{T,W}(\alpha_D)\in H^2(T,W;\mu_N^{\mathrm{et}})$. Write $\nu$ for etale-to-pro-etale comparison and $t=\sigma_T\rho_T:\nu^{-1}\mu_N^{\mathrm{et}}\to A(1)_T$ for the actual coefficient morphism of [def-pur-frame-class]. By the construction stated in [lem-pur-divisor-class] and the coefficient-compatible relative-to-supported identification of [lem-pur-divisor-relative-cone], one has $\operatorname{cl}(D)=t_*\nu^*\beta_D$. This is a global relative class; it is not inferred from equality of restrictions to a trivializing cover. The sequence used is a sequence of abelian sheaves, so $\mathbf G_m$ is never tensored over $R$.

Cited node statements to reuse: def-pur-frame-class, lem-amb-kummer-any-base, lem-amb-relative-torsor-cohomology, lem-pur-divisor-class, lem-pur-divisor-relative-cone.

### Original step 3 → lem-pur-cartier-relative-boundary-realization

Regard $\mu_N^{\mathrm{et}}$ as an $R_T$-module sheaf. The derived module-to-abelian comparison of [lem-weil-pbc-derived-module-underlying-comparison], for the identity and for $W\to T$, commutes with restriction. It consequently identifies their relative cones: its maps on the two derived section complexes are isomorphisms, and therefore so is its cone map, as the cone long exact sequences show. Under [lem-amb-closed-support-hom] let $b_D:i_*R_D\to\mu_N^{\mathrm{et}}[2]$ represent $\beta_D$. The relative-to-supported identification of [lem-pur-divisor-relative-cone] uses the kernel inclusion $k\mapsto(k,0)$ in the signed restriction cone. Use this same restriction cone for support-Hom. Thus this fixes the relative lift and its sign before any coefficient change; no choice of a lift from ordinary first Chern classes occurs.

Cited node statements to reuse: lem-weil-pbc-derived-module-underlying-comparison, lem-amb-closed-support-hom, lem-pur-divisor-relative-cone.

### Original step 4 → lem-pur-supported-root-scalar-site-comparison

A closed immersion is finite: on an affine open it is induced by a quotient ring, generated as a module by $1$. By [lemma-weil-pbc-finite-direct-image-exact], its etale direct image is exact. This also holds for module sheaves, since forgetting to abelian sheaves computes kernels and cokernels. Applying an exact functor to a resolution computes its derived functor, so $Ri_*A_D=i_*A_D$. Let $L_A=-\otimes_R^L A$ and let $\eta$ be its unit against exact scalar restriction, normalized as in [lem-pur-sheaf-ring-derived-coefficient-adjunction]. Put $P_R=i_*R_D$. The scalar-extension clause of [lem-asd-ordinary-supported-kummer] supplies the canonical identifications $L_AP_R=i_*A_D$ and $L_A\mu_N^{\mathrm{et}}=B=\mu_N^{\mathrm{et}}\otimes_R A$. The root sheaf is flat by [lem-asd-finite-etale-twist-line] with coefficient ring $R$, and is K-flat in degree zero by [lem-pc-bounded-above-flat-kflat-site], so $B$ is in degree zero. Denote the extended morphism $L_A b_D$ by $b_{D,A}$. Naturality of the unit gives
$$\operatorname{Res}(L_A b_D)\circ\eta_{P_R}=\eta_{\mu_N^{\mathrm{et}}}[2]\circ b_D.$$
In the supported-Hom realization of [lem-amb-closed-support-hom], this says that $b_{D,A}$ represents $u_*\beta_D$, where $u(v)=v\otimes1$. Explicitly the unit at the supported source sends its local constant generator $1$ to $1_A$, and at the target sends a root $v$ to $v\otimes1$. Evaluating a supported Hom cocycle at the generator therefore identifies the displayed square with the coefficient map on the kernel of restriction, and hence on its derived restriction cone. This uses the normalized adjunction and does not require $A$ to be flat over $R$.

Cited node statements to reuse: lemma-weil-pbc-finite-direct-image-exact, lem-pur-sheaf-ring-derived-coefficient-adjunction, lem-asd-ordinary-supported-kummer, lem-asd-finite-etale-twist-line, lem-pc-bounded-above-flat-kflat-site, lem-amb-closed-support-hom.

### Original step 5 → lem-pur-supported-root-scalar-site-comparison

Let $q:\nu^{-1}B\xrightarrow{\sim}A(1)_T$ be the canonical etale-origin target identification supplied by [lem-amb-cartier-kummer-map], normalized by the roots-projection prescription in [def-pur-frame-class]. On local root tensors, $q(v\otimes a)=a\,\sigma_T\rho_T(v)$, so $q\nu^{-1}u=t$ by substituting $a=1$. This is the projection-induced identification with the specified twist of [def-coefficient-twists-detailed]. Apply the site-comparison equality in [lem-pur-supported-hom-pullback] to the bounded-below etale complex $B[0]$, and then naturality in the target of [lem-pur-supported-hom] to $q$. If $a_T:\nu^{-1}i_*^{\mathrm{et}}A_D\xrightarrow{\sim}i_*^{\mathrm{proet}}A_D$ is the canonical comparison, step 4 gives
$$\chi_{T,D}(t_*\nu^*\beta_D)=q[2]\circ\nu^{-1}b_{D,A}\circ a_T^{-1}.$$
These are comparisons of the whole supported class, including its specified relative lift. All complexes to which the site-comparison assertion is applied are bounded below.

Cited node statements to reuse: lem-amb-cartier-kummer-map, def-pur-frame-class, def-coefficient-twists-detailed, lem-pur-supported-hom-pullback, lem-pur-supported-hom.

### Original step 6 → parent assembly

The right side in step 5 is precisely the explicit recipe for the named $c_D$ fixed in the statement: the relative torsor Kummer boundary is realized over $R$, extended to $A$, and then carried through the supported-source and roots-projection comparisons. The recipes have the identical $\alpha_D$, $\beta_D$, coefficient unit $v\mapsto v\otimes1$, and source comparison. Thus steps 2 and 5 give $\chi_{T,D}(\operatorname{cl}(D))=c_D$. This is a substitution of the constructed map's explicit normalization. The first-Chern-class and base-change properties asserted by [lem-amb-cartier-kummer-map] alone are not being used to characterize it uniquely.

Cited node statements to reuse: lem-amb-cartier-kummer-map.

### Original step 7 → parent assembly

For the given $h:T'\to T$, both $D$ and $D'$ are Cartier, so [lem-amb-cartier-kummer-map] gives $h^{-1}c_D=c_{D'}$ under its canonical source and twist comparisons. The twist has the bounded-below etale-origin witness $B[0]$ of step 5. The pro-etale assertion of [lem-pur-supported-hom-pullback] therefore gives
$$\chi_{T',D'}(h^*\operatorname{cl}(D))=h^{-1}(\chi_{T,D}(\operatorname{cl}(D)))=h^{-1}c_D=c_{D'}=\chi_{T',D'}(\operatorname{cl}(D')).$$
Here pullback of the supported morphism includes precomposition with the inverse supported-constant comparison. The pullback in [lem-pur-supported-cup-functoriality] is the canonical supported pullback on both sites, compatible with localization and the site comparison, hence is the map in this formula. Finally $\chi_{T',D'}$ is injective by [lem-pur-supported-hom], giving the required equality. All inputs use Cartier divisors and the invertible exponent killing $A$; none requires these schemes or divisors to be smooth.

Cited node statements to reuse: lem-amb-cartier-kummer-map, lem-pur-supported-hom-pullback, lem-pur-supported-cup-functoriality, lem-pur-supported-hom.
