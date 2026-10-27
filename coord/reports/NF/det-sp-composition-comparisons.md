# Repair delivery: det-sp-composition-comparisons

1. Files written:
   - dag/nodes/sec-smooth-purity/det-sp-composition-comparisons.json: statement unchanged; six-step assembly, 2316 characters of proof text.
   - dag/nodes/sec-smooth-purity/lem-sp-finite-adjoint-compositor-transposes.json: statement; unsplit; no Mathlib match. Separates composite Hom representability and the exceptional scalar-mate calculation, with the compact-support coefficient equality as a hypothesis.
   - dag/nodes/sec-smooth-purity/lem-sp-tower-adjoint-compositor-realization.json: statement; unsplit; no Mathlib match. Actual tower construction, evaluation of the counit equation, and reduction/normalization argument.
   - dag/nodes/sec-smooth-purity/lem-sp-integral-compositor-limit-realization.json: statement; unsplit; no Mathlib match. Explicit reduction/total-limit realization, including the equivalence counit and integral adjunction comparison.
   - citations.json: one literal statement quotation for every cited node in every parent proof step.
2. Attachments: none. The project search for the blueprint tag returned none. Searches for composition/coefficient/counit notions found UpperShriekCanonicalMapsComposition.lean, which concerns tensor-map invertibility and base-change invertibility, not all clauses of this item.
3. WANTED: none.
4. Returned fault: the previous accepted ten-step proof had 9285 characters and was returned under the human's work-distribution decision. It is now assembled from three separately claimable statement-only nodes and existing exact structural results. No old argument is discarded: the complete baseline is retained below, with a step-by-step destination map. No target or item statement is changed.
5. Unfinished: the three new lemmas intentionally have no proof, proof dependencies, or proof origin. They are the parallelizable work requested in this return. No Lean, compiler, Lake or build tool was used; the repository and launcher were not edited and no git command was run in the read repository.

## Source and search audit

Read the current main-20261015 comparisons.md and comparisons.proof.md, the chapter record sec-smooth-purity, and unit sk-prop-sp-composition. The item realizes structural comparisons used by the unit's finite and tower tensor transpositions; it does not change its diagonal/DNC purity route. The current repository item equals the returned-baseline.json copy at the time of the repair.

Read Stacks more-etale.tex Tag 0F7J (lemma-shriek-composition), including the compatible compactification tower and its proper/open compositor, Tag 0F7I (lemma-shriek-well-defined), and Tag 0GL6 (remark-Rf-lower-shriek-change-of-rings). These are support for the inherited finite compact-support argument, not claims that Stacks itself states the exceptional or tower conclusions. The new lemmas cite the blueprint proof at (1)-(2), (3) tower construction, and (3) integral realization, respectively; their argument is agent-written material already present in the returned proof, reproduced below. No SGA source is used.

Searched the whole DAG by composition/compositor/coefficient/counit titles and statements, the three Stacks tags, and the proposed ids; read the existing candidates listed below. Ran blueprint_refs.py ancestor and searches for composition, exceptional composition, tower composition, integral composition, counit, normalized towers, and composition isomorphisms. The ancestor is det-sp-composition-comparisons, with no intervening created node. The new nodes' from.place names the original paragraphs and returned steps. No other blueprint statement is equivalent under the full arbitrary-field/arbitrary-finite-ring or nonnormalized-tower hypotheses.

For each new node, searches.jsonl contains two distinct LeanFinder phrasings, a Loogle query, a LeanSearch query, and a Mathlib grep, as returned by the required msearch.py. All services responded. Read the hit lists: generic right-adjoint composition, adjunction derivation, module scalar counits, ordinary adic completion transitions, local-cohomology diagrams and equivalence transitivity do not give the stated normalized comparison theorem in one specialization. In particular read Mathlib CategoryTheory/Adjunction/Basic.lean 567-586, Unique.lean 102-114 and Mates.lean 209 onward: these are ingredients, not the geometric coefficient and strict-tower assertions. The original item's searches are retained unchanged. No unrun query is recorded.

## Not duplicates

lem-sp-finite-adjoint-compositor-transposes vs lem-sf-finite-exceptional-compositor-coefficients: the existing node restricts to the global finite-field setting and DVR quotient or finite-free coefficient extensions; the new node permits arbitrary fields of positive characteristic and arbitrary finite commutative ell-primary ring maps, and isolates the full transpose identity conditional on the compact-support identity.
lem-sp-finite-adjoint-compositor-transposes vs lem-weil-pbc-mate-pasting: the existing abstract square-pasting theorem is an ingredient; it does not state the normalized exceptional compositor, the explicit transpose using the specified geometric b and c, or the comparison under a supplied compact-support compositor.
lem-sp-finite-adjoint-compositor-transposes vs lem-pur-normalized-adjunction-composition: the existing node compares ordinary and derived left-adjoint uniqueness under localization; the new one identifies finite exceptional right-adjoint comparisons and coefficient-counit transposes.
lem-sp-tower-adjoint-compositor-realization vs lem-sf-adic-exceptional-compositor-coefficients: the existing node starts with normalized DVR systems over the algebraic closure of a finite field and compatible origin witnesses; the new node works over arbitrary k and on the full uniformly bounded constructible finite-Tor category without normalization, and includes derived reduction formulas and preservation of its normalized subcategory.
lem-sp-tower-adjoint-compositor-realization vs lem-sp-coefficient-tower-shriek-calculus: the existing theorem gives F composition and F reduction; it does not supply the actual H compositor, its evaluated counit equation, or H-compositor reduction compatibility.
lem-sp-tower-adjoint-compositor-realization vs det-sp-tower-gluing: gluing gives each single-map tower adjunction and its reductions, not a compositor or its reduction square.
lem-sp-integral-compositor-limit-realization vs lem-sf-integral-compactification-system-realization: the existing node realizes finite words in inverse images, proper images, open extension and tensor; H is not one of those operations. The new statement includes the exceptional adjoint, the inverse equivalence counit in its compositor, and normalization of both integral adjunctions.
lem-sp-integral-compositor-limit-realization vs lem-sf-package-compactified-tower-comparisons: the existing package supplies integral compact-support composition but does not state realization of the exceptional compositor through the derived reduction/limit equivalence with counits.
lem-sp-integral-compositor-limit-realization vs lem-sf-adic-exceptional-compositor-coefficients: that node's strict systems require compatible etale-origin witnesses and its conclusion compares with a preselected integral compactification compositor across all coefficient stages. The new lemma takes actual normalized-tower compositors and gives the precise equivalence-conjugation formulas for the two integral functors used here, without a compatible witness requirement.
lem-sp-integral-compositor-limit-realization vs det-sp-integral-adjunction-bijection: the latter treats one smooth map and identifies its integral adjunction; the new statement concerns conjugation of the supplied two-map compositors and compatibility of the composite counit.

Reused, rather than duplicated: lem-amb-unbounded-compact-support-comparisons provides the etale compositor for arbitrary finite rings; lem-sp-finite-compact-site-coherence provides its precise pro-etale proper/open transport; lem-sp-et-proet-coefficient-compatibility provides the arbitrary-ring coefficient composition/refinement equation. Thus the large finite-support argument from returned steps 2, 4 and 5 already has independent nodes in the live DAG.

## Review by NF

I checked B-E against the actual files and the source paragraphs, not just the dependency lists. Each new node introduces k, ell, X/Y/Z, f/g, their dimensions, its coefficient rings and categories, and every map used in the displayed equations. Its statement dependencies define the coefficient categories, constructibility, finite Tor amplitude, scalar extension, adjunctions and tower/integral functors. They do not contain proof steps or a proof sketch. All three are narrower tasks than the parent: the finite lemma assumes the b-compositor equation, the tower lemma assumes the finite identities, and the integral lemma assumes actual normalized tower compositors. No new node restates the whole item or is used to establish its own hypotheses. Their sizes are comparable (2577, 3222, 2770 statement characters).

Parent step 1 reads the standing setting for coefficient-independent compactifications, finite-type-over-Noetherian for the scheme hypothesis, smooth-relative-dimension permanence for gf, constructible adjunction preservation for the three functors, and scalar-extension preservation for all b/c domains. A field is Noetherian by its two ideals; its spectrum has one affine chart. These cited statements really give each domain check.

Parent step 2 reads the entire statement of lem-amb-unbounded-compact-support-comparisons: it gives exactly the compatible tower, proper/open formula and independence for arbitrary finite rings. The derived-origin theorem gives bounded intrinsic constructible pro-etale origin for every such ring and full faithfulness through its equivalence. The two equations of lem-sp-finite-compact-site-coherence identify transport of the etale comparator with the pro-etale proper/open comparator and respect refinements. All intermediate schemes are Noetherian by step 1. This retains returned step 2, including the proper counit-mate/open normalization, through existing statements.

Parent step 3 reads the actual statement of lem-sp-et-proet-coefficient-compatibility, not its proof: its displayed composition equation is exactly the b equation here and its refinement and site equations identify the same chosen maps. It has arbitrary finite ell-primary A to B, no finite-field or flatness restriction. Its etale-origin input hypothesis is provided by the derived-origin equivalence; the finite-Tor assumption is already part of M and is preserved by scalar extension. This reuses all the primitive, interchange, site and refinement arguments of returned steps 4-5, which were separately split in the live DAG. I did not create a duplicate node for those equations.

Parent step 4 reads the new finite-adjoint lemma, including the explicit composite-counit equation and the formula for the transpose of D. Its b-identity hypothesis has been established in step 3; all h=f,g,gf adjunctions exist by step 1. I checked the normalization by composing the two Hom bijections, then computed the transpose: naturality of epsilon_f moves c_g, the defining c_f equation replaces its contraction by S(epsilon_f)b_f^{-1}, the c_g equation contracts the g factor, and naturality of b_g^{-1} produces S(epsilon_comp)[F_g(b_f)b_gF_f]^{-1}. The b identity and injectivity of the Hom bijection give exactly theta_B c_gf = H_f(c_g)c_f S(theta_A), with matching source and target. This is the argument allocated to the finite new node, not left implicit in the parent.

Parent step 5 reads the new tower theorem's actual functor isomorphisms and evaluation/reduction clauses. The finite hypotheses are steps 3-4 with A_n to A_m. In its allocated argument, tower-bound supplies the F restriction needed by tower calculus, and tower gluing supplies the actual H adjunction on the same uniformly bounded category. The adjunction comparison exists before finite evaluation. Evaluating the counit equation then identifies theta_n by a finite Hom bijection, which avoids the false assertion that level evaluation is faithful on derived morphisms. Substituting r^FC=F(r)b and r^HC=H(r)c reduces the two reduction squares to those finite b/c identities. Invertibility of r, b and c then proves normalization; uniform bounds come from the existing tower-bound and gluing statements, not from levelwise invertibility alone.

Parent step 6 reads the new integral lemma's two explicit conjugation formulas. Its hypotheses are satisfied by step 5 and by the completed integral functor/adjunction identifications named in the item. In its allocated proof the schemes are Noetherian and ell is invertible, as required by normalized-equivalence. The field here is explicitly the algebraic closure of the finite field, as required by integral-adjunction-bijection; that hypothesis is not used for the earlier arbitrary-k assertions. Every use of kappa_Y is on an already normalized intermediate tower. The second formula has kappa_Y inverted, the required direction for H_gf to H_f H_g. The integral units/counits are identified by the actual integral adjunction theorem, so this is a comparison of the specified functors and adjunctions, not just objectwise limits.

I tested identity f or g, d=0 or e=0, empty schemes, A=B, the zero ring where permitted, and the non-flat quotient Z/ell^2 to Z/ell. No flatness or finite-projective-dimension step occurs. For towers n=m gives the identity reduction, and neither tower construction nor integral realization uses faithfulness of finite evaluation. E=Q_ell yields the requested completed Z_ell coefficients. Every parent citation has a literal quotation in citations.json. There is no proof step over 2000 characters; in particular the parent totals 2316 characters, below 3000. The inherited statement corrections (explicit compositors and the finite-field restriction only for the integral part) are retained, not reintroduced as new disputes.

## Preservation of the returned argument

The live item was compared with the retained baseline and was unchanged before repair. The following is a lossless allocation, not a replacement by a shorter informal explanation:

- Old step 1 remains parent step 1 verbatim.
- Old step 2 is supplied by existing lem-amb-unbounded-compact-support-comparisons and lem-sp-finite-compact-site-coherence, via the existing finite-ring derived-origin equivalence (parent step 2).
- Old steps 3 and 6 become lem-sp-finite-adjoint-compositor-transposes: the Hom formula, counit uniqueness, and complete D-transpose equation are in its statement; the old argument is retained verbatim below for its future worker.
- Old step 4's proper primitive comparison is already the statement of lem-sfb-derived-scalar-mate-composition; its open primitive comparison is already in lem-sp-open-scalar-site-coherence. Old step 5's proper/open coefficient square is already lem-sp-proper-open-coefficient-mate, its refinement square is lem-sf-proper-open-coefficient-refinement, and the complete pasting/site statement is lem-sp-et-proet-coefficient-compatibility. Parent step 3 cites this existing complete result rather than manufacturing a duplicate. The baseline text below retains every generator and pasting argument for source traceability.
- Old steps 7-9 become lem-sp-tower-adjoint-compositor-realization: actual construction, the evaluated counit uniqueness calculation, reduction formulas, and preservation of normalization and uniform bounds.
- Old step 10 becomes lem-sp-integral-compositor-limit-realization, with both conjugation arrows now fully displayed, including kappa and its inverse for the exceptional direction.

### Verbatim returned ten-step proof

#### Returned step 1

The chosen compactifications exist inside the standing setting. Their schemes are Noetherian: a field is Noetherian since its only ideals are $0$ and $1$, and finite type over a Noetherian scheme is Noetherian. The composite $gf$ is smooth of relative dimension $d+e$. Consequently the constructible adjunctions apply to $f,g,gf$ for both coefficient rings. Scalar extension sends each $\Dctf$ object to a $\Dctf$ object, without a flatness assumption. In particular all arguments of $b$ and $c$ below are in their stated domains.

Cited nodes: sk-def-sfb-dc-setting, lem-weil-pbc-finite-type-over-noetherian, lem-sbc-smooth-relative-dimension-permanence, sk-prop-sf-rf-shriek-preservation, det-sp-scalar-extension-functor.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-composition/sk-prop-sp-composition-comparisons.proof.md; (1)-(2), domain checks.

#### Returned step 2

Choose a compatible tower of compactifications: $Y\xrightarrow i\bar Y\xrightarrow s Z$ and $X\xrightarrow a\bar X\xrightarrow p\bar Y$ compactify $g$ and $if$; put $V=\bar X\times_{\bar Y}Y$, with $b:V\hookrightarrow\bar X$, $r:V\to Y$, and $j:X\hookrightarrow V$, so $bj=a$. On the etale site the normalized compositor is
$$Rs_*i_!Rr_*j_!\xrightarrow{Rs_*\Gamma j_!}Rs_*Rp_*b_!j_!\simeq R(sp)_*a_!.$$
The compact-support comparison lemma gives its invertibility and independence of the tower for every finite commutative coefficient ring. Every bounded intrinsically constructible pro-etale input has bounded etale origin, by the arbitrary-finite-ring derived-origin equivalence. Transport the displayed map by the normalized proper site-comparison mates and the exact open-extension comparisons. The site equation for $\Gamma$ in the proper/open coefficient-mate lemma identifies the transported map with the same proper/open prescription on the pro-etale site. This defines $\alpha_R$ on the required objects, independently of the witness and compactifications; the origin equivalence is fully faithful.

Cited nodes: lem-cbc-compactifiable-compatible-tower, lem-amb-unbounded-compact-support-comparisons, lem-weil-pbc-finite-ring-constructible-derived-origin, lem-weil-pbc-comparison-direct-image-canonical-mate, lem-cbc-proetale-extension-zero-comparison, lem-sp-proper-open-coefficient-mate.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-composition/sk-prop-sp-composition-comparisons.proof.md; (1), compact-support composition; Stacks 0F7J (lemma-shriek-composition).

#### Returned step 3

Compose the Hom bijections for $F_f\dashv H_f$ and $F_g\dashv H_g$:
$$\operatorname{Hom}(F_gF_fM,K)\simeq\operatorname{Hom}(F_fM,H_gK)\simeq\operatorname{Hom}(M,H_fH_gK).$$
The inverse sends $u$ to $\varepsilon_g\circ F_g(\varepsilon_f)\circ F_gF_f(u)$, so the composite counit is the one asserted. Transporting this bijection through $\alpha_R$ makes $H_fH_g$ right adjoint to $F_{gf}$. Uniqueness of right adjoints gives $\theta_R$. More precisely $\theta_R(K)$ is the image of $\varepsilon_{gf,R}(K)\circ\alpha_R(H_{gf,R}K)$ in the displayed Hom bijection. Its inverse is obtained by reversing the two representing bijections. Thus it preserves the specified counits, and every counit-preserving comparison has the same Hom image and equals it. This proves (1), including its normalization.

Cited nodes: lem-weil-pbc-mate-pasting, lem-weil-common-left-adjunctions-iso.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-composition/sk-prop-sp-composition-comparisons.proof.md; (1), composition of Hom bijections and counit uniqueness.

#### Returned step 4

Write $q_p:S Rp_{*,A}\to Rp_{*,B}S$ and $t_j:S j_{!,A}\simeq j_{!,B}S$ for the normalized constituents in the definition of $b$. Proper compositors commute with $q$: paste the pullback/scalar squares and apply mate-pasting along the adjunctions. These pullback squares paste to the square for the composite: on a K-flat tensor model both reassociations take an inverse-image generator $x\otimes u$ to the iterated inverse-image generator with the same coefficient $u$; the section formula in scalar/tensor normalization fixes these maps. Hence their mates agree, with the canonical proper compositors inserted. For composable opens, both ways of composing $t$ extend the same tensor section by zero on the composite open and send it to zero off that open. Their sheafifications and termwise derived maps therefore agree with the open compositor. These assertions concern actual coefficient-linear maps: the proper comparison is defined by the $B$-linear adjunction, and the open comparison is the normalized comparison of left adjoints, not an arbitrary underlying-$A$ isomorphism.

Cited nodes: def-sp-reduction-direct-image-comparison, lem-weil-pbc-mate-pasting, lem-sp-proetale-scalar-tensor-normalization, lem-cbc-extension-zero-composition.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-composition/sk-prop-sp-composition-comparisons.proof.md; (2), primitive proper and open composition squares.

#### Returned step 5

In the compatible tower of step 2, put $L=j_!M$ on $V$. It and its scalar extension have bounded etale origins: $M$ has finite Tor amplitude, scalar extension preserves it, and extension by zero is exact and commutes with scalar extension by the comparison $t_j$. Apply the coefficient equation for the cartesian proper/open square $pb=ir$:
$$Rp_{*,B}(t_b)\,q_p\,S(\Gamma_A)=\Gamma_B\,i_{!,B}(q_r)\,t_i.$$
Use its site equation to transport to the pro-etale presentations. The scalar/site squares themselves commute by the generator formula of scalar/tensor normalization and mate-pasting for the proper constituents; for an open both send an extended tensor section to that same section. Paste this interchange square, the proper-composition square and the open-composition square of step 4, and apply $Rs_*$. The resulting outer boundary is exactly
$$b_{gf}\,S(\alpha_A)=\alpha_B\,F_{g,B}(b_f)\,b_gF_{f,A}.$$
Coefficient compatibility with changing a chosen compactification follows by pasting the proper/open refinement coefficient square with the proper-composition square. Thus the boundary is the specified $b$ for the fixed compactifications, not just a map for the specially chosen tower. This proves the first equation of (2) for arbitrary $A\to B$.

Cited nodes: det-sp-scalar-extension-functor, lem-weil-pbc-finite-ring-constructible-derived-origin, def-sp-reduction-direct-image-comparison, lem-sp-proper-open-coefficient-mate, lem-sp-proetale-scalar-tensor-normalization, lem-weil-pbc-mate-pasting, lem-sf-proper-open-coefficient-refinement.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-composition/sk-prop-sp-composition-comparisons.proof.md; (2), b: paste the proper/open coefficient square; Stacks 0GL6 and 0F7I.

#### Returned step 6

Use $F_h,H_h$ with a coefficient subscript when needed, and insert $\alpha,\theta$ as in the statement. Put $L=H_{g,A}K$, $N=H_{f,A}L$, and $D=H_{f,B}(c_g(K))\circ c_f(L)$. Its transpose under the composite $B$-adjunction is
$$\varepsilon_{g,B}\,F_{g,B}(\varepsilon_{f,B})\,F_{g,B}F_{f,B}(D).$$
First naturality of $\varepsilon_f$ moves $c_g$ past it. Substitute $\varepsilon_{f,B}F_{f,B}(c_f(L))=S(\varepsilon_{f,A}(L))b_f(N)^{-1}$, then substitute the defining counit identity for $c_g$. The result is
$$S(\varepsilon_{g,A})\,b_g(L)^{-1}\,F_{g,B}(S(\varepsilon_{f,A}(L)))\,F_{g,B}(b_f(N)^{-1}).$$
Naturality of $b_g^{-1}$ moves $\varepsilon_{f,A}(L)$ to the left, giving
$$S(\varepsilon^{\mathrm{comp}}_A(K))\,[F_{g,B}(b_f(N))\,b_g(F_{f,A}N)]^{-1}.$$
By step 5 this is the transpose of $c_{gf}(K)$ after the prescribed compositors. The Hom bijection is injective, so $D\,S(\theta_A(K))=\theta_B(S K)c_{gf}(K)$. This proves the second equation of (2); only naturality, the two defining counit identities, and the already proved $b$ equation were used.

Cited nodes: det-sp-reduction-direct-image, det-sp-reduction-exceptional, lem-weil-pbc-mate-pasting.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-composition/sk-prop-sp-composition-comparisons.proof.md; (2), c: explicit calculation of both transposes.

#### Returned step 7

For $A_n=\mathcal O_E/\ell^n$, the tower bound gives $F_{h,\bullet}(\mathcal C)\subseteq\mathcal C$ for $h=f,g,gf$, where $\mathcal C$ is the uniformly bounded constructible finite-Tor tower category. Thus the hypothesis on the restricted functors in the tower compact-support calculus is satisfied. Its clause (1) gives an actual isomorphism $\alpha_\bullet:F_{g,\bullet}F_{f,\bullet}\simeq F_{gf,\bullet}$ before evaluation, and identifies its evaluation with the finite proper/open compositor. The tower-gluing theorem gives actual adjunctions $F_{h,\bullet}\dashv H_{h,\bullet}$, whose finite evaluation comparisons preserve units and counits. Apply the Hom-bijection construction of step 3 in these tower categories to obtain an actual $\theta_\bullet:H_{gf,\bullet}\simeq H_{f,\bullet}H_{g,\bullet}$.

Cited nodes: sk-lem-sp-tower-bound, lem-sp-coefficient-tower-shriek-calculus, det-sp-tower-gluing, lem-weil-common-left-adjunctions-iso.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-composition/sk-prop-sp-composition-comparisons.proof.md; (3), construct the tower maps before evaluating.

#### Returned step 8

Evaluate the defining counit equation for $\theta_\bullet$ at $n$. Tower gluing identifies the evaluated units and counits with the finite ones, and the tower calculus identifies $(\alpha_\bullet)_n$ with $\alpha_{A_n}$. The resulting equation is the defining counit equation for $\theta_{A_n}$ in step 3. Injectivity of the finite Hom bijection gives $(\theta_\bullet)_n=\theta_{A_n}$ under those comparisons. This determines the evaluation of an already constructed tower morphism; it does not infer equality of tower morphisms from equality of their evaluations.

Cited nodes: det-sp-tower-gluing, lem-sp-coefficient-tower-shriek-calculus.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-composition/sk-prop-sp-composition-comparisons.proof.md; (3), finite evaluation and counit normalization.

#### Returned step 9

Let $r^C_{n,m}:S_{n,m}C_n\to C_m$ be a tower reduction map. The tower compact-support calculus states $r^{F_hC}_{n,m}=F_{h,m}(r^C_{n,m})b_h(C_n)$, and tower gluing states $r^{H_hC}_{n,m}=H_{h,m}(r^C_{n,m})c_h(C_n)$. Substitute these formulas for $h=f,g,gf$. Naturality moves $r^C_{n,m}$ through the finite compositors; the remaining equality for $F$ is precisely the $b$ equation of step 5 with $A=A_n,B=A_m$, and for $H$ it is precisely the $c$ equation of step 6. Hence the evaluated compositors commute with the stated derived reduction maps. If $C$ is normalized then every $r^C_{n,m}$ is invertible, and so are $b_h,c_h$. The displayed reduction formulas show that $F_hC,H_hC$ are normalized. Their uniform constructible bounds hold already by the tower bound and tower gluing. Consequently both composition isomorphisms restrict to the full subcategories of normalized towers.

Cited nodes: sk-def-sp-normalized-towers, lem-sp-coefficient-tower-shriek-calculus, det-sp-tower-gluing, det-sp-reduction-direct-image, det-sp-reduction-exceptional, sk-lem-sp-tower-bound.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-composition/sk-prop-sp-composition-comparisons.proof.md; (3), write out the reduction-map compatibility and normalization.

#### Returned step 10

Now use the global finite-field setting for the integral assertion. The Noetherian hypothesis of the constructible reduction/$R\varprojlim$ equivalence holds by step 1. Put $r_T=\operatorname{red}_T$ and $L_T=R\varprojlim$; its counit gives $r_TL_T\simeq1$ on normalized towers. The integral direct-image comparison identifies $F_{h,\mathcal O_E}$ with $L_{\mathrm{target}}F_{h,\bullet}r_{\mathrm{source}}$, and the integral adjunction theorem identifies $H_{h,\mathcal O_E}$ with $L_{\mathrm{source}}H_{h,\bullet}r_{\mathrm{target}}$, including their units and counits. Therefore
$$F_{g,\mathcal O_E}F_{f,\mathcal O_E}\simeq L_ZF_{g,\bullet}r_YL_YF_{f,\bullet}r_X\simeq L_ZF_{g,\bullet}F_{f,\bullet}r_X\xrightarrow{L_Z\alpha_\bullet r_X}L_ZF_{gf,\bullet}r_X\simeq F_{gf,\mathcal O_E}.$$
Likewise $L_X\theta_\bullet r_Z$ and $r_YL_Y\simeq1$ give $H_{gf,\mathcal O_E}\simeq H_{f,\mathcal O_E}H_{g,\mathcal O_E}$. Every inserted counit is applied to a normalized tower by step 9. These are functorial isomorphisms on $\Dbc$; the counits agree because the integral adjunction theorem identifies them with the tower counits under this equivalence. Setting $E=\mathbf Q_\ell$ gives the asserted integral comparisons.

Cited nodes: det-sp-normalized-equivalence, det-sp-integral-direct-image-tower, det-sp-integral-adjunction-bijection.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-composition/sk-prop-sp-composition-comparisons.proof.md; (3), transfer the actual tower isomorphisms through reduction and derived limit.

