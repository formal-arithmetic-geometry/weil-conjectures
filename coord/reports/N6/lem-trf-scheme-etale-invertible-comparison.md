# Worker report: repair of lem-trf-scheme-etale-invertible-comparison

## Files written

- dag/nodes/sec-trace-formula/lem-trf-scheme-etale-invertible-comparison.json: statement unchanged; short assembly proof.
- dag/nodes/sec-trace-formula/lem-trf-etale-line-sections-normalized-comparisons.json: statement, unsplit; no Mathlib match after the logged semantic, Loogle and source searches.
- dag/nodes/sec-trace-formula/lem-trf-etale-line-frame-transition-units.json: statement, unsplit; no Mathlib match after the logged semantic, Loogle and source searches.
- dag/nodes/sec-trace-formula/lem-trf-etale-framed-line-effective-gluing.json: statement, unsplit; no Mathlib match after the logged semantic, Loogle and source searches.

## Attachments

None. The project declaration AlgebraicGeometry.Scheme.scheme_etale_invertible_comparison at lean/Sheaf/SixFunctors/TraceFormula/SchemeEtaleInvertibleComparison.lean:200 ends in sorry. Searches under lean/WeilConjectures for the blueprint tag and the invertible/etale notions found no declaration proving the whole item. EtaleOpenQuasiCoherentIdentification only covers open restriction of additive quasi-coherent sheaves, not the full equivalence or the module-level arbitrary-etale coherence.

## WANTED

None. All mathematical sources are present.

## Fault and repair

The released repair order requires spreading the 7415-character proof, at least two comparable new tasks, statement-only leaves, and a parent proof below 3000 characters. Three tasks now carry the normalized section construction and coherence (old 1–3), frame-to-cocycle extraction (old 5), and ordinary effective descent plus site gluing (old 6–7). Old 4 is already the final Hom-bijection assertion of lem-trf-etale-extension-free-presentations-hom; it is reused, not duplicated. Old 8 is the elementary inverse-functor assembly retained in the parent. This distribution is specifically the human's re-split order, rather than a claim that the formerly elementary-labelled 1000-character calculations are single-line elementary steps. No statement correction. No SGA source.

## Review by N6

I read Descent Tag 03DX, proposition-equivalence-quasi-coherent, including the fully faithful associated functor, formation of overlap descent data, its omitted cocycle verification, effective fpqc descent, and the final gluing of local isomorphisms. I read 05VG, lemma-equivalence-quasi-coherent-properties, where finite local freeness is preserved/reflected (the exception for unrestricted locally free modules does not apply to rank one). I read 03LC, proposition-equivalence-quasi-coherent-functorial (1), whose reference is remark-change-topologies-ringed-sites. The new normalized-comparisons statement asks for the tensor-section realization of this pullback comparison, with its units and explicit coherence, not a second equivalence theorem. The frame-transition statement isolates the cocycle verification omitted in 03DX. The framed-gluing statement asks for the effective descent and the actual global isomorphism with its prescribed local maps, not merely an isomorphism class. All new nodes introduce X, the site, ring sheaf, modules, cover, and maps themselves. Their proofs and proof dependencies are empty.

Step 1 quotes the normalized-comparisons node for exactly its functor, unit, local-line, and coherence conclusions. Step 2 quotes the existing etale-extension-free-presentations-hom statement, including its canonical section identification and final Hom bijection, and the invertible-module definition for quasi-coherence. Both use all module maps. Its dependency closure was read computationally and does not reach the item, so this reuse introduces no cycle. Step 3 quotes the transition-unit node for the explicit multiplication relation, triple cocycle and diagonal, then the framed-gluing node whose hypotheses are these exact assertions. The two orientations agree: t_b=t_a g_ab and lambda_a=g_ab lambda_b give t_a A(lambda_a)=t_b A(lambda_b). Step 4 is the explicit elementary construction of a quasi-inverse from the preceding Hom bijection and chosen isomorphisms; its inverse maps, functor laws, counit, unit and triangle identities remain written out. No non-elementary source assertion is hidden in this final assembly.

For the first new task I checked invertibility of pullbacks on pulled-back Zariski frames; no surjectivity is needed for v. Its identity equation uses the tensor identity isomorphism and its composite equation uses the inverse-normalized restriction comparison followed by c_(z,v), so all objects have the same base. The frame statement deliberately asserts g_aa=1 only after diagonal pullback; a nonmonomorphic etale chart can have nontrivial self-overlap transitions away from the diagonal. In the third task the cover is arbitrary and jointly surjective, hence the existing fpqc-finer-than-etale assertion applies; the existing fpqc-descent statement (3) supplies precisely an ordinary invertible L and compatible lambda_a. I checked the literal statements of these old inputs, and preserved their arguments below so the next workers have the original route. The sheaf gluing is on W times_X U_a, not on an unjustified factorization through an image. No affineness of pairwise intersections, Noetherianity, quasi-compactness, or separation is used.

Small cases: X empty admits the empty cover and unique module; all equalizer formulas still give the unique section. The identity cover with one frame gives g=1 on its diagonal, the trivial bundle, and the specified frame map. For repeated or nonmonomorphic etale members the pairwise/triple fibre products retain both projections. Zero module morphisms are included in the Hom statement. Tensor identity and triple composition reduce on local generators respectively to insertion/removal of 1 and multiplication of scalars in their original order. This also checks that the new tasks do not silently demand literal equality of different pullback objects.

I compared the item against the released current repository node and the read-only stage-2 Lean statement. The sandbox was empty at resumption, so there was no earlier report/search work to discard. Its original statement, metadata and recorded searches were retained; the delivery tool overlays only authorized split fields on the current head. The new claims have no exact blueprint counterpart: whole-blueprint searches for 03DX, 03LC, 05VG, line modules, tensor sections, invertible and frame were read, followed by all-DAG keyword/source searches. The scheme quasi-coherent equivalence itself depends on this item and cannot be cited back. The pre-existing free-presentation Hom node is used instead of a fourth new node.

## Original arguments and allocation

The following are the complete returned proof steps, retained verbatim as handoff material, not as proofs in the statement-only nodes. They record every argument rather than replacing them with summaries.

### Returned step 1: normalized-comparisons task

For invertible $L$, quasi-coherence is part of [def-sc-invertible-module], so [lem-sc-etale-qcoherent-descent] supplies the sheaf underlying $A_X(L)$. Its restrictions are semilinear and compose by [lem-sc-etale-qcoherent-presheaf-functorial]; thus its sectionwise scalar action makes it a module sheaf. For $h:L\to K$, naturality of the pullback adjunction [lem-pc-module-pullback-adjunction] gives $g^*(u^*h(s))=g^*u^*h(g^*s)$, and naturality of the composition comparison in [def-pc-module-pullback] gives $\rho_g(u^*h(s))=u'^*h(\rho_g(s))$. Therefore the stated components define $A_X(h)$. Pullback and global sections preserve identities and compositions, proving the functor laws. For the structure module, $u^*\mathcal O_X\simeq\mathcal O_U$ is the tensor map $a\otimes b\mapsto a\,u^\sharp(b)$ with inverse $a\mapsto a\otimes1$. It identifies the restrictions with the ring restrictions, proving $A_X(\mathcal O_X)\simeq\mathcal O_{X_{\mathrm{et}}}$, including its module action.

Inputs: def-sc-invertible-module, lem-sc-etale-qcoherent-descent, lem-sc-etale-qcoherent-presheaf-functorial, lem-pc-module-pullback-adjunction, def-pc-module-pullback

### Returned step 2: normalized-comparisons task

For etale $v:Y\to X$ and $w:W\to Y$, the component of the restriction comparison is $\Gamma(W,(v\circ w)^*L)\simeq\Gamma(W,w^*v^*L)$ from [def-pc-module-pullback]. The composition is etale: apply [lem-weil-pbc-etale-covering-composition] to the covering $\{v,\mathrm{id}_X\}$ and, over its $Y$ member, $\{w,\mathrm{id}_Y\}$ (use the identity covering over its $X$ member). Compatibility with restrictions and with $h$ follows from the unit-normalized composition comparison of [lem-sc-etale-qcoherent-presheaf-functorial]. Explicitly its tensor formula multiplies the intermediate scalar into the final scalar; the inverse inserts $1$ in the intermediate factor. For three successive pullbacks, both composites on local tensor generators multiply the three scalars in their original order, so associativity makes them equal; identity comparisons insert or remove $1$. Since tensor generators locally generate the pullback sheaves, these are equalities of the module maps. This proves the identity, composition and morphism compatibilities claimed in the item.

Inputs: def-pc-module-pullback, lem-weil-pbc-etale-covering-composition, lem-sc-etale-qcoherent-presheaf-functorial

### Returned step 3: normalized-comparisons task

Choose a Zariski trivializing cover $V_i\subseteq X$ for $L$, using [def-sc-invertible-module]. These are objects and a covering of $X_{\mathrm{et}}$ by [lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites]. Pullback along an open immersion is restriction by [lem-weil-pbc-open-immersion-module-pullback-restriction], so $L|_{V_i}\simeq\mathcal O_{V_i}$ identifies $v_i^*L$ with the structure module. Step 2 and the structure comparison of Step 1 now identify $A_X(L)$ on each $(V_i)_{\mathrm{et}}$ with its structure module. Thus the functor takes values in the stated line modules.

Inputs: def-sc-invertible-module, lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites, lem-weil-pbc-open-immersion-module-pullback-restriction

### Returned step 4: existing etale-extension-free-presentations-hom task (general case)

Given a module-sheaf map $\alpha:A_X(L)\to A_X(K)$, evaluate it on every open immersion $j:V\hookrightarrow X$. Via the natural, unit-compatible restriction identification in [lem-weil-pbc-open-immersion-module-pullback-restriction], these components are $\mathcal O_X(V)$-linear maps $L(V)\to K(V)$ commuting with restriction to smaller opens. They therefore define an ordinary module map $h:L\to K$, by the definition [def-weil-sheaf-of-modules-category]. For a general etale $u:U\to X$, cover $X$ by opens $V_i$ with frames $e_i$ of $L$ and cover $U$ by $U_i=U\times_XV_i$. The first cover is etale by [lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites]; its pullback is a cover by [def-weil-pbc-sites-and-cohomology](1). Naturality of $\alpha$ along $U_i\to V_i$ gives $\alpha_{U_i}(u^*e_i)=u^*(h(e_i))$ using Step 2. Every section on $U_i$ is $b\,u^*e_i$, so linearity gives $\alpha_{U_i}=\Gamma(U_i,u^*h)$. For any $s\in A_X(L)(U)$ the two images in $A_X(K)(U)$ agree on all $U_i$, and hence agree by separatedness. Thus $\alpha=A_X(h)$. Evaluation on opens also shows that $A_X(h)=A_X(h')$ implies $h=h'$, proving the Hom bijection for all module morphisms.

Inputs: lem-weil-pbc-open-immersion-module-pullback-restriction, def-weil-sheaf-of-modules-category, def-sc-invertible-module, lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites, def-weil-pbc-sites-and-cohomology

### Returned step 5: frame-transition-units task

Let $G$ be a line module and choose its trivializing etale family $u_a:U_a\to X$ and frames $t_a:\mathcal O_{(U_a)_{\mathrm{et}}}\xrightarrow{\sim}G|_{(U_a)_{\mathrm{et}}}$. Put $R_{ab}=U_a\times_XU_b$. These are objects of the site by [def-weil-pbc-etale-site]. On its localized site set $\beta_{ab}=t_a^{-1}t_b$. A module endomorphism $\beta$ of this structure sheaf is multiplication by its value $g=\beta_{R_{ab}}(1)$: for $q:W\to R_{ab}$, naturality gives $\beta_W(1)=q^\sharp(g)$, and linearity gives $\beta_W(b)=bq^\sharp(g)$. Applying this to the inverse makes $g_{ab}=\beta_{ab}(1)$ a unit. On triple products the identity $(t_a^{-1}t_b)(t_b^{-1}t_c)=t_a^{-1}t_c$ evaluated at $1$ gives $g_{ab}g_{bc}=g_{ac}$, with the functions pulled back to the triple product. On the diagonal it gives $g_{aa}=1$ after diagonal pullback. Thus multiplication by $g_{ab}$ gives ordinary module gluing maps $\mathcal O_{U_b}|_{R_{ab}}\to\mathcal O_{U_a}|_{R_{ab}}$ satisfying exactly the descent cocycle. Here pullbacks of the structure modules use the tensor unit comparison of Step 1. This is a calculation in frames, requiring no general theorem identifying the two categories of modules.

Inputs: def-weil-pbc-etale-site, def-weil-sheaf-of-modules-category

### Returned step 6: framed-line-effective-gluing task

The jointly surjective etale family $(u_a)_a$ is fpqc by [lem-weil-pbc-fpqc-finer-than-etale]. Apply the invertible-module descent assertion (3) of [lem-pc-fpqc-descent] to the ordinary structure modules $\mathcal O_{U_a}$ and the gluing maps of Step 5. It supplies an ordinary invertible module $L$ and isomorphisms $\lambda_a:u_a^*L\xrightarrow{\sim}\mathcal O_{U_a}$ compatible with those maps. With our orientation this compatibility reads $\lambda_a=g_{ab}\lambda_b$ on $R_{ab}$ after the canonical pullback comparisons. Consequently $t_aA(\lambda_a)=t_bA(\lambda_b)$ there, because $t_b=t_a\,g_{ab}$. Steps 1 and 2 identify the domains of these local maps with $A_X(L)$ restricted to $R_{ab}$. All covers here are arbitrary set-indexed covers in the universes of [def-weil-size-convention]; no quasi-compactness or separatedness of $X$ was imposed.

Inputs: lem-weil-pbc-fpqc-finer-than-etale, lem-pc-fpqc-descent, def-weil-size-convention

### Returned step 7: framed-line-effective-gluing task

Write $e_a=t_aA(\lambda_a)$. For an object $W\to X$ and $s\in A_X(L)(W)$, restrict to $W_a=W\times_XU_a$ and apply $e_a$ to obtain $r_a\in G(W_a)$. The family $(W_a\to W)_a$ is a covering by [def-weil-pbc-sites-and-cohomology](1), and Step 6 makes $r_a$ agree on $W_a\times_WW_b$. Its sheaf equalizer axiom therefore gives a unique $r\in G(W)$; define $e_W(s)=r$. Restriction along $W'\to W$, addition and multiplication by $b\in\mathcal O(W)$ commute with this rule because both resulting sections have the same restrictions to all $W'_a$ or $W_a$. Hence $e$ is a module-sheaf map. The inverses $e_a^{-1}$ agree on overlaps as well; the identical gluing rule constructs its inverse. Their composites are identities since they are identities on each $W_a$ and sections are separated. Thus $G\simeq A_X(L)$, proving essential surjectivity.

Inputs: def-weil-pbc-sites-and-cohomology, def-weil-sheaf-of-modules-category

### Returned step 8: parent assembly step 4

Finally choose for each line module $G$ a pair $(L_G,e_G:A_X(L_G)\xrightarrow{\sim}G)$ from Steps 6 and 7. For $f:G\to H$, define its inverse-functor image as the unique ordinary module map with $A_X$-image $e_H^{-1}fe_G$, using Step 4. Uniqueness gives the identity and composition laws. The maps $e_G$ form a natural counit isomorphism. For ordinary $L$, lift $e_{A_X(L)}$ by the same Hom bijection to $L_{A_X(L)}\to L$; lifting its inverse proves this is an isomorphism. Its naturality and the triangle identities follow by applying the faithful $A_X$ and cancelling the $e_G$. This gives an equivalence with the specified functor $A_X$. Steps 1 and 2 already provide its natural structure-module and etale-restriction identifications.

Inputs: 

## Not duplicates

lem-trf-etale-framed-line-effective-gluing vs lem-trf-fpqc-cartier-ideal-reflection: The existing statement starts with an already given closed immersion and its ideal, identifies its flat pullbacks with the fibre ideals, and reflects the effective Cartier property. The new statement starts with a framed small-etale module G and its transition units, constructs an ordinary invertible L, and gives the prescribed sectionwise isomorphism A_X(L) to G. It assumes no ideal inclusion and cannot be obtained from Cartier reflection.

lem-trf-etale-line-sections-normalized-comparisons vs lem-sfb-scheme-etale-module-exact-finiteness-comparison: The existing statement gives exactness and preservation/reflection of finite type and finite presentation, assuming the full quasi-coherent equivalence. The new statement constructs the line section functor and its tensor-unit and etale-restriction comparisons with explicit identity and composition equations. Exactness or finite presentation does not supply those equations, and the existing statement depends on the quasi-coherent equivalence which uses this parent.

lem-trf-etale-line-sections-normalized-comparisons vs lem-trf-zariski-etale-functor-comparison-square: That statement compares ringed-site adjoints and quasi-coherent direct images; it does not assert the explicit tensor-section identity/composition equations, frame cocycle or effective framed gluing.

lem-trf-etale-line-sections-normalized-comparisons vs lem-trf-scheme-zariski-etale-quasi-coherent-equivalence: That statement gives the entire quasi-coherent equivalence including direct images and depends on the item; it is not an independent lemma for this task.

lem-trf-etale-line-sections-normalized-comparisons vs lem-trf-etale-presented-module-effective-recovery: That statement starts with arbitrary site-quasi-coherent presentations and tensor pullback L_T; it does not state prescribed unit-valued frames, ordinary invertible descent trivializations, or the sectionwise framed inverse formulas.

lem-trf-etale-line-sections-normalized-comparisons vs lem-trf-scheme-etale-invertible-comparison: The parent asserts the whole equivalence with all Hom maps and coherent restrictions; this task supplies only the indicated technical construction.

lem-trf-etale-line-sections-normalized-comparisons vs lem-trf-algebraic-space-invertible-descent: That statement descends line modules on an algebraic space across an atlas and uses this scheme comparison; it does not provide this independent scheme calculation.

lem-trf-etale-line-sections-normalized-comparisons vs def-trf-space-module-scheme-restriction: That node defines restriction of space modules to schemes; it proves none of the three assertions.

lem-trf-etale-line-frame-transition-units vs lem-trf-scheme-zariski-etale-quasi-coherent-equivalence: That statement gives the entire quasi-coherent equivalence including direct images and depends on the item; it is not an independent lemma for this task.

lem-trf-etale-line-frame-transition-units vs lem-trf-etale-presented-module-effective-recovery: That statement starts with arbitrary site-quasi-coherent presentations and tensor pullback L_T; it does not state prescribed unit-valued frames, ordinary invertible descent trivializations, or the sectionwise framed inverse formulas.

lem-trf-etale-line-frame-transition-units vs lem-trf-scheme-etale-invertible-comparison: The parent asserts the whole equivalence with all Hom maps and coherent restrictions; this task supplies only the indicated technical construction.

lem-trf-etale-line-frame-transition-units vs def-trf-space-module-scheme-restriction: That node defines restriction of space modules to schemes; it proves none of the three assertions.

lem-trf-etale-framed-line-effective-gluing vs lem-trf-two-term-determinant-affine-descent: The existing node concerns descent of determinant-functor systems with exterior, zero and evaluation data; this task concerns one ordinary invertible module and a prescribed comparison with a framed etale module, with no determinant data.

lem-trf-etale-framed-line-effective-gluing vs lem-trf-scheme-zariski-etale-quasi-coherent-equivalence: That statement gives the entire quasi-coherent equivalence including direct images and depends on the item; it is not an independent lemma for this task.

lem-trf-etale-framed-line-effective-gluing vs lem-trf-etale-presented-module-effective-recovery: That statement starts with arbitrary site-quasi-coherent presentations and tensor pullback L_T; it does not state prescribed unit-valued frames, ordinary invertible descent trivializations, or the sectionwise framed inverse formulas.

lem-trf-etale-framed-line-effective-gluing vs lem-trf-scheme-etale-invertible-comparison: The parent asserts the whole equivalence with all Hom maps and coherent restrictions; this task supplies only the indicated technical construction.

lem-trf-etale-framed-line-effective-gluing vs lem-trf-algebraic-space-invertible-descent: That statement descends line modules on an algebraic space across an atlas and uses this scheme comparison; it does not provide this independent scheme calculation.

lem-trf-etale-framed-line-effective-gluing vs def-trf-space-module-scheme-restriction: That node defines restriction of space modules to schemes; it proves none of the three assertions.

lem-trf-etale-framed-line-effective-gluing vs lem-pd-degree-picard-sheaf-fpqc-existence: Existing scope: Existence of an fpqc amalgamation. That statement is about classes or sheafified relative Picard sections under hypotheses on a curve or its universal structure-sheaf direct image. This task has no such hypotheses and constructs a particular ordinary module and an actual isomorphism of etale module sheaves preserving the prescribed frames.

lem-trf-etale-framed-line-effective-gluing vs lem-pd-degree-picard-sheaf-fpqc-uniqueness: Existing scope: Uniqueness of an fpqc amalgamation. That statement is about classes or sheafified relative Picard sections under hypotheses on a curve or its universal structure-sheaf direct image. This task has no such hypotheses and constructs a particular ordinary module and an actual isomorphism of etale module sheaves preserving the prescribed frames.

lem-trf-etale-framed-line-effective-gluing vs lem-pd-normalized-picard-fpqc: Existing scope: Normalized Picard classes satisfy fpqc descent. That statement is about classes or sheafified relative Picard sections under hypotheses on a curve or its universal structure-sheaf direct image. This task has no such hypotheses and constructs a particular ordinary module and an actual isomorphism of etale module sheaves preserving the prescribed frames.

lem-trf-etale-framed-line-effective-gluing vs lem-pd-picard-fpqc-separated: Existing scope: Fpqc separatedness of the relative Picard sheaf. That statement is about classes or sheafified relative Picard sections under hypotheses on a curve or its universal structure-sheaf direct image. This task has no such hypotheses and constructs a particular ordinary module and an actual isomorphism of etale module sheaves preserving the prescribed frames.

lem-trf-etale-framed-line-effective-gluing vs lem-pd-picard-fpqc-local-equality: Existing scope: Fpqc-local equality of Picard classes determines their relative class. That statement is about classes or sheafified relative Picard sections under hypotheses on a curve or its universal structure-sheaf direct image. This task has no such hypotheses and constructs a particular ordinary module and an actual isomorphism of etale module sheaves preserving the prescribed frames.

lem-trf-etale-framed-line-effective-gluing vs lem-pd-degree-picard-sheaf-fpqc: Existing scope: The degree part of the Picard functor is an fpqc sheaf. That statement is about classes or sheafified relative Picard sections under hypotheses on a curve or its universal structure-sheaf direct image. This task has no such hypotheses and constructs a particular ordinary module and an actual isomorphism of etale module sheaves preserving the prescribed frames.

lem-trf-etale-framed-line-effective-gluing vs lem-pc-fpqc-descent: The existing node supplies ordinary invertible L and its compatible trivializations (the first part of this task). It does not start with the given etale module G or construct the prescribed e:A_X(L)≃G and its sectionwise inverse. The new task includes that separate site-gluing argument; its future proof uses the existing descent node, rather than replacing it.

lem-trf-etale-framed-line-effective-gluing vs lem-pd-picard-sheaf-fpqc: Existing scope: The relative Picard sheaf of a curve is an fpqc sheaf. That statement is about classes or sheafified relative Picard sections under hypotheses on a curve or its universal structure-sheaf direct image. This task has no such hypotheses and constructs a particular ordinary module and an actual isomorphism of etale module sheaves preserving the prescribed frames.

lem-trf-etale-framed-line-effective-gluing vs lem-sc-etale-qcoherent-descent-fpqc-sections: The existing node glues sections of the pullback of an already given quasi-coherent module. Here the ordinary invertible L must first be constructed, and G is only a given framed etale module; the new conclusion is an isomorphism to G, with specified local maps and inverse.

lem-trf-etale-framed-line-effective-gluing vs lem-sc-etale-hom-sheaf: The existing node asserts the sheaf property of Hom between two ordinary quasi-coherent modules pulled to etale charts. Here the target G is a site module not yet identified with an ordinary pullback; the new conclusion constructs that identification and its prescribed inverse.

Additional comparisons: lem-trf-etale-extension-free-presentations-hom supplies the existing Hom bijection and canonical functor but does not state the normalized identity and triple-composition tensor formulas demanded by the first task. lem-trf-zariski-etale-tensor-sections identifies ringed-site pullback with a sheafification for arbitrary modules; it does not prove these normalized equations or the line property. lem-sc-glue-component-transition-cocycle is Zariski-open gluing, whereas the new third task handles arbitrary etale covers and a prescribed etale module isomorphism. lem-sc-closed-cover-frame-transitions concerns a finite closed cover of a reduced scheme with discrete intersections, and lem-pc-twist-cocycle only the specific Proj transition functions (x_i/x_j)^d. None supplies the new frame extraction or framed effective etale gluing statement.

## Unfinished work

The three new lemmas are deliberately statement-only and unsplit, as ordered; future workers prove them. No Lean was written or compiled. Delivery verification follows below.

## Verification

The required server dry run exited successfully: preflight passed, OK (not pushed), commit 1b899eb5f23. The final report expands the same-tag distinctions after reading all corresponding statements, including Tag 023T and the ringed-site change-of-topology remark in descent.tex. A further dry run checks this final report before direct delivery. The parent proof has 1977 characters and no step longer than 2000 characters; all three new nodes have empty proof arrays and proof dependency lists, and four genuine logged searches each.


## Repair of the returned landing (2026-10-22)

The return at coord/returns/N6.md names returned head c1de88aa34b and says the reader approved the mathematics, but landing refused the side completion because it had not been promoted to the live DAG. This is a rebase repair of that delivery, not a new split and not a claim that the old completion has landed. L retains responsibility for promotion into the live DAG.

I resumed the retained delivered node files, report, citations and searches. Compared with the current read-only repository, the parent differs only in proof, proof_deps and split_report; its statement, statement dependencies, blueprint ancestry, Lean record and maintainer metadata agree. None of the three added nodes is present in the current repository. The released stage-1 repair note is still present, keeps the statement and plan, requires at least two statement-only tasks, and permits this re-split despite the older reviewed record. The three retained tasks satisfy that order. The delivery command builds on current origin/sheaf-dag and preserves its maintainer metadata, so the new branch is rebased rather than re-pushing the returned commit.

I re-read every current statement cited by the parent, including both existing inputs rather than assuming that their old wording survived. Step 1 uses the retained normalized-comparisons statement for the functor, unit, line property and all comparison equations. Step 2 uses lem-trf-etale-extension-free-presentations-hom, whose current statement explicitly identifies L_TF(v) with Gamma(V,v^*F), with scalar action and module maps, and ends with the Hom bijection for every pair of quasi-coherent F,H. The current def-sc-invertible-module still defines invertible modules to be quasi-coherent and Zariski locally free of rank one. Thus the specialization has exactly the needed hypotheses and covers noninvertible morphisms too. Step 3 uses the retained transition statement and framed-gluing statement; the former supplies every overlap, triple-product and diagonal condition required by the latter. Step 4 only assembles the already obtained full faithfulness and essential surjectivity. I corrected its subject-verb typo; its construction and proof are retained.

I re-read descent.tex at Tags 03DX, 05VG, 03LC, the change-of-topologies ringed-site remark, and 023T. They still give the recorded construction, finite locally free descent, pullback compatibility and effective descent route. The checks on nonmonomorphic covers and their diagonals, empty schemes, arbitrary small covers, and the transition orientation in the original review remain valid. I re-read the logged Mathlib search results and their verdicts; neither the statements nor the search questions changed, so no search was repeated and no search record was invented. All five proof citations have literal quotes in citations.json. The initial required dry run after resumption exited 0 with preflight passed, OK (not pushed), commit b633b40d729. A final dry run checks this amended report and split_report before pushing.


## Current returned-head repair (2026-10-23)

The current return entry names head 8edd03a4974 (2026-10-22 16:15 UTC), with the same landing refusal concerning unpromoted side completion. I resumed all four retained node files, report, five citation quotes and twelve logged new-node searches. The initial dry run in this repair exited 1 before pushing: it identified two newly present same-tag nodes, lem-trf-fpqc-cartier-ideal-reflection (023T) and lem-sfb-scheme-etale-module-exact-finiteness-comparison (05VG). I read both complete statements and their dependencies; neither duplicates a retained task. The two pairwise distinctions now appear under Not duplicates. This is a repair on the current DAG rather than an unchanged re-push of the returned head. The required delivery command prepares its own worktree on the current base; no worker git command or repository write was used.

I re-read all five cited statements. Step 1 still takes exactly the normalized functor, tensor unit, line property, and restriction coherence from the first task. Step 2 still has the needed quasi-coherence hypotheses from def-sc-invertible-module and the existing comparison's explicit canonical section identification, compatibility with module maps, and final full Hom bijection. I clarified the assembly text: conjugation by these canonical identifications takes that bijection to precisely h mapped to the family Gamma(U,u^*h), so the proof establishes full faithfulness for the specified functor and includes noninvertible morphisms. Step 3's two tasks still have identical overlap orientations and the same triple and diagonal conditions. Step 4 retains the explicit quasi-inverse construction. The literal citation quotes remain valid for every cited node.

I re-read descent.tex at 03DX (the proof and omitted overlap cocycle verification), 023T (effective descent and full faithfulness), 05VG (finite local freeness), 03LC (pullback comparison), and the ringed-site change-of-topology remark. The parent statement and all new statements are unchanged; the normalized-comparison identity and composition equations have the correct source and target, and the framed gluing uses the cover of each W by its actual fibre products. Empty X, zero morphisms, repeated charts and nonmonomorphic self-overlaps still satisfy these statements, with g_aa normalized only on the diagonal. The source calculations remain fully preserved in Original arguments and allocation. The JSON-decoded TeX and every citation quote have single backslashes; no TeX edit was necessary.

The current repository parent differs from the retained split only in its proof, proof_deps and split_report; no statement, statement dependency, Lean record, blueprint ancestry or maintainer metadata is replaced. None of the three task ids is currently present in the read clone. The released stage-1 re-split order still keeps this plan and requires at least two tasks; the three retained statement-only tasks satisfy it. Searches in lean/WeilConjectures by the item tag and etale/invertible concepts give no declaration proving the whole item: GmPicard concerns isomorphism classes and torsors, not this equivalence of module categories with all maps and coherent restriction comparisons. I read the retained searches.jsonl results and the node verdicts; their statements and search questions did not change, so I reused them without repeating or inventing searches. Final server preflight and direct delivery follow this amended report.
