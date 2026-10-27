# Q106 repair: lem-pur-etale-finite-tor-direct-image-coefficients

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-etale-finite-tor-direct-image-coefficients.json — repaired split, same statement and stmt_deps, 2327 characters in five assembly steps.
- dag/nodes/sec-smooth-purity/lem-pur-etale-residue-direct-image-tor-window.json — statement, unsplit; no Mathlib match. An abstract Tor-window estimate for any scheme morphism with a supplied all-module-sheaf bound and bounded constructible output.
- dag/nodes/sec-smooth-purity/lem-pur-etale-finite-scalar-ctf-descent.json — statement, unsplit; no Mathlib match. Ordinary-etale preservation of bounded constructibility and a specified Tor interval for a finite ell-primary coefficient map on any qcqs scheme.
- report.md and citations.json — this review, exact old argument handoff and verbatim citations for every parent proof use. searches.jsonl is the unedited search-command log. returned-proof.json retains the returned eight steps, their sources and uses exactly as read.

## Attachments

None. The project declaration AlgebraicGeometry.Etale.finiteTor_directImage_coefficients in lean/Sheaf/Paper/EtaleFiniteTorDirectImageCoefficients.lean:102 has sorry at line 153. Searching lean/WeilConjectures for its exact blueprint tag and declaration found no replacement. The finite-ring direct-image result in WeilConjectures/SixFunctors/Etale/Derived/DirectImageTorAmplitude.lean:272 has the geometric 2d bound, not an arbitrary supplied c; ClosedSupportTorAmplitude.lean:73 has a supplied c but assumes a quasi-compact open immersion. The pro-etale ScalarExtension.lean concerns finite free coefficient maps, not arbitrary nonflat finite algebras on the ordinary etale site. None attaches either extracted statement.

## WANTED

None. All sources used are available in literature/.

## Returned fault and repair

The return requires spreading the 6849-character proof into at least two comparable independent jobs, each delivered statement-only, and leaving a parent assembly of at most 3000 characters. The sandbox initially contained only dispatcher marker files, no node, report or search log. I copied the current read-only repository node (the returned eight-step version) as the baseline. Its statement, statement dependencies, source and pre-existing metadata are retained. The current node's Lean statement is a sorry and is not evidence of completion. No unit or chapter file was changed.

Old Steps 4–5, 1567 characters, form the residue/projection Tor-window job. Old Steps 6–7, 2307 characters, form the scalar-preservation/descent job. Their statements introduce their own rings, schemes, categories, interval endpoints and hypotheses. They have proof=[], proof_deps=[], proof_origin=null, status=unsplit. They do not move the whole theorem to a single node. The parent still proves coefficient arithmetic, constructs the relative bound, obtains constructibility, checks the two jobs' hypotheses and proves the isomorphism and normalization of the specified B-linear counit mate. Its five steps total 2327 characters; none exceeds 2000 characters.

The two extracted statements have useful independent hypotheses: the first assumes bounded constructible Rh_*K and a bound c without any base field or finite-type morphism; the second concerns a single arbitrary qcqs scheme and arbitrary finite ell-primary rings, with no direct-image theorem or k-morphism. Thus neither is a restatement of the full item. Every part of the old argument is reproduced verbatim below, including its old uses and source place, so the future workers receive the actual argument rather than a shortened summary. The original assembly arguments occur below as well as in the shorter parent proof.

## Search record and blueprint

Before creating nodes I searched the whole DAG by the tag/source strings 0F10 and 6.7.17 and by scalar/finite/Tor/direct-image statements; I read the potentially overlapping statements named below. I ran tools/blueprint_refs.py search for 'Tor amplitude', 'finite local', 'scalar extension', 'residue', 'residue tensor direct image', 'scalar extension Tor', 'cohomological bound', and 'etale scalar'. The narrow searches found no exact blueprint statement; the broader ones identified the comparison/pro-etale and restricted-geometry results discussed below. The ancestor command reports blueprint.from.node=None: the launcher-created ancestry seed has no imported blueprint ancestor. I retained that null and prepended the item to the inherited via list; each from.place identifies the exact returned steps and the current blueprint paragraphs. same_as=[] for the two new nodes.

All Mathlib searches were run only with msearch.py, using Q106 and this item. Each new node has LeanFinder, valid Loogle, grep and LeanSearch records, and a second semantic phrasing. The log's actual query texts and returned declaration names are recorded. For the Tor-window job the initial quoted 'Tor' Loogle search returned irrelevant string/functor declarations, so I additionally ran the valid CategoryTheory.Tor search; it gives the ordinary left-derived tensor definition and projective-object vanishing, not the desired etale theorem. The semantic hits DerivedCategory.IsGE/IsLE and exists_iso_Q_obj_of_isGE_of_isLE construct bounded representatives but do not bound any direct image or detect Tor by the residue field. For the scalar job the Loogle hits are underived sheaf/module adjunctions; LeanSearch's ModuleCat.preservesFiniteLimits_extendScalars_of_flat has a flatness hypothesis and no constructibility, derived Tor interval or etale site comparison. The grep searches have zero hits for the combined properties. None is an exact match or a one-line specialization. The item's existing Mathlib searches have been retained, not re-invented or rerun.

## Not duplicates

lem-pur-etale-residue-direct-image-tor-window vs thm-sf-direct-image-tor-amplitude: existing theorem assumes an algebraically closed base field, separated finite-type morphism; the new supplied-bound argument is for any scheme morphism, with constructibility of the output a hypothesis, not a conclusion.
lem-pur-etale-residue-direct-image-tor-window vs lem-sf-direct-image-tor-amplitude-noetherian: existing theorem requires separated finite-type geometry and uses the 2d geometric bound; the new estimate uses arbitrary c for all module sheaves and no geometric dimension hypothesis.
lem-pur-etale-residue-direct-image-tor-window vs det-cor-sf-direct-image-ctf-open-tor: existing theorem is for an open immersion over a separably closed field; the new argument applies to any scheme morphism with the supplied bound and constructible output.
lem-pur-etale-residue-direct-image-tor-window vs lem-exc-residue-tor-test: existing statement detects Tor amplitude by residue tensor but says nothing about a derived direct image or its c-shifted interval.
lem-pur-etale-residue-direct-image-tor-window vs lem-sf-projection-finite-constant: existing statement is the derived projection isomorphism for finitely presented modules; the new argument combines it with the finite-rectangle derived bound and residue detection, concluding a Tor interval.
lem-pur-etale-finite-scalar-ctf-descent vs det-sp-scalar-extension-functor: existing theorem is on the pro-etale site; the new job proves boundedness and constructibility of the actual ordinary-etale extension before/after descent, including the exact interval. It cannot be cited as an etale assertion without the descent argument.
lem-pur-etale-finite-scalar-ctf-descent vs sk-def-sp-scalar-extension: existing node defines the pro-etale functor and refers to its preservation theorem; it does not prove the ordinary-etale statement.
lem-pur-etale-finite-scalar-ctf-descent vs det-pe-finite-tor-comparison-noetherian: existing equivalence only gives interval detection for already bounded constructible etale objects; it does not prove that the actual etale coefficient extension is bounded constructible.
lem-pur-etale-finite-scalar-ctf-descent vs lem-weil-pbc-derived-scalar-extension-local-systems: existing theorem gives abstract localized left adjoints and a site comparison, with no constructible or Tor-preservation conclusion. Identification with the K-flat change of rings still needs the derived coefficient adjunction and uniqueness of adjoints.
lem-pur-etale-finite-scalar-ctf-descent vs lem-pur-sheaf-ring-derived-coefficient-adjunction: existing adjunction is on any small site with no constructibility or interval conclusion.
lem-pur-etale-finite-scalar-ctf-descent vs lem-sfb-constant-realization-derived-scalar-extension: existing result identifies scalar extension of globally constant complexes; the new statement handles all bounded constructible complexes on qcqs schemes.
lem-pur-etale-finite-scalar-ctf-descent vs det-prop-scalar-six-ctf: existing theorem uses the standing separated finite-type positive-characteristic setting and pulled-back condensed coefficient modules; the new one uses arbitrary qcqs schemes and actual ordinary constant-ring module extension.
lem-pur-etale-finite-scalar-ctf-descent vs lem-sp-supported-scalar-tor-interval: existing theorem is an extension-by-zero comparison/vanishing statement for pro-etale supported objects, with no bounded-constructible ordinary-etale scalar-preservation conclusion.

## Review by Q106

I read delivery-errors B–E and checked the node files against the cited sources, rather than using their dependency lists as proofs. I read the current blueprint scalar-extension-functor proof, paragraphs (1)–(2), and reduction-exceptional proof, Locality and Charts; Bhatt–Scholze Section 6.7 (Theorem 6.7.1, Lemma 6.7.2 and Lemmas 6.7.16–17), and Stacks etale-cohomology.tex definition-cd-f (0F0Z) and lemma-finite-cd (0F10). Bhatt–Scholze supplies the projection/residue argument and finite-coefficient context, not an assertion that the base field has finite absolute cohomological dimension. The ordinary-etale scalar job follows the blueprint via the explicitly named site/adjunction comparisons, not via an SGA trace route. No SGA source is used.

Parent Step 1 uses the statements of lem-weil-l-adic-extension-integers-dvr (local DVR with finite residue, valuation extension and a uniformizer) and lem-weil-valued-dvr-finite-quotients (finite local quotient). The finite-set arguments for Noetherianity and finite presentation are written out, and ell lies in the uniformizer ideal because its extended absolute value is less than one. Thus ell^n annihilates A and every unital A-algebra B, while remaining invertible in k.

Parent Step 2 uses exactly clause (1) of lem-kun-0f10, then the definition def-kun-cd for relative all-torsion-sheaf vanishing. The statement of lem-sbc-canonical-restrict-scalars-functor-comparisons supplies the invertible derived comparison for Z to A on D+; a sheaf in degree zero is in that domain. def-pc-sheaf-restrict-scalars retains the same abelian sheaf and hence detects zero cohomology. No clause about absolute cd(k), algebraic closedness or separatedness has been assumed.

Parent Step 3 uses thm-dg-finite-type-constructibility precisely as stated: arbitrary field, finite ring killed by an invertible integer and no separatedness assumption. It then supplies bounded constructibility of F, A's Noetherianity and Step 2's uniform bound to the new residue-window statement. The latter explicitly concludes the exact [a,b+c_h] Tor interval and assumes no geometric hypotheses missing from h.

For that new node, I reread the old Step 4 dependencies: module-sheaves-grothendieck-abelian really states Grothendieck abelianness, module-direct-image-left-exact really states additive left exactness, and thm-sp-truncation-e2 states the R^r f_* H^q page and finite exhaustive separated abutment filtration. They justify a finite [0,c] by [a,b] rectangle, hence the derived cohomology window, not just termwise vanishing without convergence. In old Step 5, lem-sf-projection-finite-constant requires A Noetherian, K bounded above, kappa finitely presented and a bound for every A-module sheaf. Each is present; finite A makes kappa finitely presented. Its conclusion is an isomorphism of derived objects. lem-exc-residue-tor-test requires the exact quotient O_E/t^n and bounded constructible F, both in the new statement; it concludes the desired all-module-sheaf Tor interval. The future worker has these exact steps below. I did not add them as proof dependencies of the unsplit child.

Parent Step 4 uses lem-weil-pbc-finite-type-over-noetherian with the Noetherian field k, and the new scalar statement for W=U,V. Finite-type schemes over a field are Noetherian and qcqs. The finite ell-primary ring hypotheses for A and B were checked in Step 1; nonflatness of B causes no missing hypothesis.

For that new node, old Step 6 uses lem-pur-derived-change-of-rings to construct the actual B-action, def-kun-derived-tensor to identify the underlying A-complex, def-kun-tor-amplitude with B_W to bound its cohomology, and def-pc-sheaf-restrict-scalars to retain the same cohomology. This proves boundedness before invoking full faithfulness. Old Step 7 uses det-pe-finite-tor-comparison-noetherian only for qcqs W and finite, hence Noetherian, A and B. Its equivalence and interval-detection clauses are exactly what the step uses. det-sp-scalar-extension-functor clause (2) applies to the pro-etale constructible image and needs no flatness. I checked lem-pur-sheaf-ring-derived-coefficient-adjunction: its left adjoint really is the K-flat extension, so uniqueness of adjoints identifies the functors in lem-weil-pbc-derived-scalar-extension-local-systems with the actual extensions on both sites. That comparison is an isomorphism of derived objects, not per-degree assertions. Essential surjectivity gives an etale ctf J'; sk-prop-sf-comparison is fully faithful on D+, which contains both J' and J_B by old Step 6. It lifts the isomorphism and inverse, establishing constructibility of the actual J_B. Only then is the interval-detection equivalence applied to J_B. This preserves the earlier reviewer repair instead of reverting to an unsupported identification of the abstract adjoints.

Parent Step 5 cites lem-pur-etale-scalar-mate-projection for the very same counit transpose, after checking K, T_UK and T_VF are bounded below. Its statement supplies equality with the specified projection map, and does not itself assert invertibility. lem-sbc-canonical-restrict-scalars-functor-comparisons supplies d invertible on the bounded-below T_UK. lem-sf-projection-finite-constant supplies invertibility of PF with finitely presented B, bounded-above K and the all-module bound of Step 2. The cone has the same cohomology under exact restriction (def-pc-sheaf-restrict-scalars), so an isomorphism after restriction is an isomorphism of B-complexes. No arbitrary isomorphism is substituted for the canonical map.

Small cases: K=0 and empty schemes give zero complexes; negative endpoints and a=b do not change the finite-rectangle calculation; c=0 gives [a,b] rather than an extra shift; n=1 gives kappa=A; f=id has c=0. The scalar statement allows B=0, B=A, B=kappa and B=kappa[epsilon]/epsilon^2, so finite presentation is not being confused with flatness or finite projective dimension. A field of infinite absolute torsion cohomological dimension and nonseparated h are allowed throughout. Both new statements require r<=s or a<=b, avoiding an undefined empty-interval convention. The scalar node does not claim a finite-stratification comparison on non-qcqs W; qcqs is explicit. No parent statement correction or statement dispute is needed.

Citations.json contains a verbatim statement quote for each use in every parent step. The retained old proof and its dependency statements were read for C1/C4, and every old use is either still in the parent or listed in the handoff of the relevant extracted job. No new proof is marked elementary, no proof or proof sketch is hidden in an unsplit statement, and no source tag is used to define a notion. The new nodes have no edges to their parent, so they introduce no dependency cycle. All parent step source places are retained from the return. Existing off-unit uses still needed by the parent remain declared in split_report.tool_uses; pre-existing maintainer-owned tool_uses metadata is untouched.

## Exact returned argument: task allocation

The text below is deliberately the full returned argument, with no omissions. Old Steps 1–3 and 8 remain parent assembly work. Old Steps 4–5 are the first unsplit task; old Steps 6–7 are the second. The Noetherian finite-type reduction at the start of old Step 7 is performed in parent Step 4; the scalar child assumes only qcqs, exactly the comparison theorem's hypothesis. The old proofs' concrete O_E/t^n coefficients are a special case of the scalar child's finite ell-primary rings, and every subsequent sentence uses only finite rings and qcqs W.

### Returned Step 1: parent assembly

The valuation-ring theorem [lem-weil-l-adic-extension-integers-dvr] and finite-quotient theorem [lem-weil-valued-dvr-finite-quotients] make $A$ a finite local ring with residue field $\kappa=A/(t)$. Every ideal of a finite ring is generated by its finite set of elements, so $A$ is Noetherian. Every finite $A$-module is finitely presented: its elements give a finite free surjection and its kernel is a finite set, hence finitely generated. This applies to $\kappa$ and to the underlying $A$-module of any finite $A$-algebra $B$. Since the valuation extends the $\ell$-adic valuation, $|\ell|_E<1$, so $\ell\in(t)$ and $\ell^n\in(t^n)$. Thus $\ell^nA=0$, and also $\ell^nB=0$. The integer $\ell^n$ is invertible in $k$.

Uses: lem-weil-l-adic-extension-integers-dvr, lem-weil-valued-dvr-finite-quotients.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf — Section 6.7 coefficient hypotheses, before Theorem 6.7.1; elementary coefficient arithmetic from the cited DVR statements.

### Returned Step 2: parent assembly

Apply [lem-kun-0f10], clause (1), to the given morphism $h$ of finite-type $k$-schemes. By [def-kun-cd] this supplies a nonnegative integer $c_h$ annihilating all higher direct images of torsion abelian sheaves above $c_h$. An $A$-module sheaf is killed by $\ell^n$, hence is such a torsion sheaf. Apply [lem-sbc-canonical-restrict-scalars-functor-comparisons] to $\mathbf Z\to A$ and to this sheaf in degree zero. It identifies the underlying abelian higher direct image of the module-sheaf direct image with the abelian-sheaf higher direct image. Exact scalar restriction detects a zero module sheaf, because it retains its underlying abelian sheaf [def-pc-sheaf-restrict-scalars]. Therefore $R^qh_{*,A}M=0$ for $q>c_h$, for every $M$. Only the relative clause (1) of 0F10 is used; no assertion about $\operatorname{cd}(k)$ is needed.

Uses: lem-kun-0f10, def-kun-cd, lem-sbc-canonical-restrict-scalars-functor-comparisons, def-pc-sheaf-restrict-scalars.

Source: literature/stacks-project/etale-cohomology.tex — Tag 0F10, lemma-finite-cd (1); Tag 0F0Z, definition-cd-f; module comparison: sites-cohomology.tex Tag 03FD.

### Returned Step 3: parent assembly

Put $F=Rh_{*,A}K$. The coefficient ring is finite and killed by the integer $\ell^n$ invertible in $k$, and $U,V$ are finite type over this field. The input $K$ is bounded constructible. Thus [thm-dg-finite-type-constructibility] gives $F\in D^b_c(V,A)$. Its statement explicitly allows nonseparated $h$ and an arbitrary field.

Uses: thm-dg-finite-type-constructibility.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf — Theorem 6.7.1 and Lemma 6.7.2, finite-coefficient constructibility input; arbitrary-field ordinary-etale version in the cited existing node.

### Returned Step 4: lem-pur-etale-residue-direct-image-tor-window

Let $L=K\otimes_A^L\kappa_U$. The Tor hypothesis [def-kun-tor-amplitude] gives $\mathcal H^q(L)=0$ outside $[a,b]$. The source and target module-sheaf categories are Grothendieck abelian by [lem-weil-pbc-module-sheaves-grothendieck-abelian], and $h_*$ is additive and left exact by [lem-weil-pbc-module-direct-image-left-exact]. Apply [thm-sp-truncation-e2] to a bounded-below representative of $L$. Its page is $E_2^{r,q}=R^rh_*\mathcal H^q(L)$, with $r\geq0$; Step 2 makes it zero for $r>c_h$, and the Tor hypothesis makes it zero for $q\notin[a,b]$. Thus the page is supported in $[0,c_h]\times[a,b]$. All later pages have the same support, so in total degree outside $[a,b+c_h]$ every graded quotient of the finite abutment filtration supplied by that theorem is zero. Successively using $F^r/F^{r+1}=0$ and the zero final term of that finite filtration gives $\mathcal H^i(Rh_*L)=0$ for $i\notin[a,b+c_h]$.

Uses: def-kun-tor-amplitude, lem-weil-pbc-module-sheaves-grothendieck-abelian, lem-weil-pbc-module-direct-image-left-exact, thm-sp-truncation-e2.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf — Lemma 6.7.17, residue-tensor argument made explicit using the finite rectangle of the existing truncation spectral sequence.

### Returned Step 5: lem-pur-etale-residue-direct-image-tor-window

Apply [lem-sf-projection-finite-constant] with $M=\kappa$, $N=c_h$ and the bounded-above complex $K$. Step 1 checks Noetherianity and finite presentation, and Step 2 checks the uniform vanishing hypothesis for all module sheaves. It identifies $F\otimes_A^L\kappa_V$ with $Rh_*(K\otimes_A^L\kappa_U)=Rh_*L$ by the canonical projection map. Step 4 therefore gives residue-tensor vanishing outside $[a,b+c_h]$. Apply [lem-exc-residue-tor-test] to the bounded constructible object $F$ of Step 3, with exactly the coefficient ring $\mathcal O_E/t^n$ and its residue field. It gives Tor amplitude $[a,b+c_h]$ for $F$, proving its membership in $D^b_{ctf}(V,A)$.

Uses: lem-sf-projection-finite-constant, lem-exc-residue-tor-test.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf — Lemma 6.7.17, finite-constant projection; residue test expanded in the cited DAG node.

### Returned Step 6: lem-pur-etale-finite-scalar-ctf-descent

For either $W=U$ or $V$, and $J\in D^b_{ctf}(W,A)$ with Tor interval $[r,s]$, form the actual $B$-linear derived extension $J_B=T_WJ$ using [lem-pur-derived-change-of-rings]. A K-flat representative $P$ gives $P\otimes_{A_W}B_W$ with the $B_W$-action through the second factor. Its underlying $A$-complex is precisely $J\otimes_A^LB_W$, by the K-flat definition [def-kun-derived-tensor]. Hence its underlying cohomology vanishes outside $[r,s]$, by [def-kun-tor-amplitude]. Restriction changes no cohomology groups [def-pc-sheaf-restrict-scalars], so $J_B$ is already bounded as a $B$-complex. This observation does not assert constructibility yet.

Uses: lem-pur-derived-change-of-rings, def-kun-derived-tensor, def-kun-tor-amplitude, def-pc-sheaf-restrict-scalars.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-def-sp-scalar-extension/sk-def-sp-scalar-extension-functor.proof.md — Paragraphs (1) and (2), derived extension and cohomological boundedness on its finite-Tor domain.

### Returned Step 7: lem-pur-etale-finite-scalar-ctf-descent

We now establish constructibility and the full $B$-Tor interval of $J_B$. Finite-type schemes over a field are Noetherian by [lem-weil-pbc-finite-type-over-noetherian], and in particular qcqs, so [det-pe-finite-tor-comparison-noetherian] applies to $W$ and the finite Noetherian rings $A,B$. It takes $J$ to a pro-etale constructible complex of Tor amplitude $[r,s]$. By [det-sp-scalar-extension-functor], clause (2), its pro-etale scalar extension is constructible of $B$-Tor amplitude $[r,s]$. By [lem-pur-sheaf-ring-derived-coefficient-adjunction], for $A_W\to B_W$ on $W_{\mathrm{et}}$ and on $W_{\mathrm{proet}}$, the K-flat extension $J\mapsto J_B$ and the pro-etale $(-)_B$ (K-flat, clause (1)) are left adjoint to derived restriction of scalars. The global functors $T,S$ of [lem-weil-pbc-derived-scalar-extension-local-systems] are left adjoints of the same functors, so uniqueness of adjoints gives $T\cong(-)_B$ and $S\cong(-)_B$, and its comparison $S\nu_W^*\cong\nu_W^*T$ identifies $(\nu_W^*J)_B$ with $\nu_W^*J_B$. Essential surjectivity of the $B$-coefficient equivalence in [det-pe-finite-tor-comparison-noetherian] supplies $J'\in D^b_{ctf}(W_{\mathrm{et}},B)$ and $\nu_W^*J'\simeq\nu_W^*J_B$. Both $J'$ and $J_B$ are bounded below (Step 6). Full faithfulness of $\nu_W^*$ on $D^+$ in [sk-prop-sf-comparison] lifts this isomorphism and its inverse, giving $J'\simeq J_B$. Consequently $J_B$ is bounded constructible. The interval equivalence in [det-pe-finite-tor-comparison-noetherian] now gives its $B$-Tor interval $[r,s]$ from that of $\nu_W^*J_B$. This works for every finite $A$-algebra $B$, without flatness, and for both schemes $W$.

Uses: lem-weil-pbc-finite-type-over-noetherian, det-pe-finite-tor-comparison-noetherian, det-sp-scalar-extension-functor, lem-pur-sheaf-ring-derived-coefficient-adjunction, lem-weil-pbc-derived-scalar-extension-local-systems, sk-prop-sf-comparison.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-def-sp-scalar-extension/sk-def-sp-scalar-extension-functor.proof.md — Paragraph (2), scalar preservation, transferred to the ordinary etale site by the existing coefficient and finite-Tor comparison theorems.

### Returned Step 8: parent assembly

Let $\beta_K:T_VF\to Rh_{*,B}T_UK$ be the specified counit transpose. Steps 5--7 imply $T_UK$ and $T_VF$ are bounded, so the domain requirements of [lem-pur-etale-scalar-mate-projection] hold. Its statement identifies the restricted map, followed by $d: \operatorname{Res}Rh_{*,B}\xrightarrow{\sim}Rh_{*,A}\operatorname{Res}$, with $\mathrm{PF}_h(K,B_V[0])$. The isomorphism $d$ is exactly [lem-sbc-canonical-restrict-scalars-functor-comparisons]. Apply [lem-sf-projection-finite-constant] with the finitely presented underlying $A$-module $B$ from Step 1, the bounded-above $K$, and the bound $c_h$ from Step 2. It says that this projection morphism is invertible. Thus $d\circ\operatorname{Res}(\beta_K)$ is invertible, and so is $\operatorname{Res}(\beta_K)$. Exact restriction of scalars reflects isomorphisms: its cone has the same underlying cohomology sheaves before and after restriction [def-pc-sheaf-restrict-scalars]. Hence $\beta_K$ is a $B$-linear isomorphism. This also proves the claimed normalization of the map, rather than merely the existence of an unspecified isomorphism.

Uses: lem-pur-etale-scalar-mate-projection, lem-sbc-canonical-restrict-scalars-functor-comparisons, lem-sf-projection-finite-constant, def-pc-sheaf-restrict-scalars.

Source: literature/stacks-project/more-etale.tex — Tag 0GL6, remark-Rf-lower-shriek-change-of-rings, scalar/projection interpretation; arbitrary ordinary direct-image counit normalization supplied by the cited mate node.

## Unfinished work

No part of the repair remains unfinished locally. The two extracted statements are intentionally unsplit proof jobs for other workers; their complete original arguments and the relevant hypotheses are handed off above. Required server dry-run and delivery results are appended below when available.
