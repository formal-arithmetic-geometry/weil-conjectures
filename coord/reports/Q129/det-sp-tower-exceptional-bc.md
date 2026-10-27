# Stage-1 re-split: det-sp-tower-exceptional-bc

## Files written

- `dag/nodes/sec-smooth-purity/det-sp-tower-exceptional-bc.json`: item, same statement and statement dependencies, five-step assembly (2271 characters).
- `dag/nodes/sec-smooth-purity/lem-sp-ctf-tower-pullback-reconstruction.json`: statement, unsplit; no Mathlib match. Uniform tower domains, quotient reduction and actual reconstruction counit, for arbitrary scheme morphisms in the finite-type setting.
- `dag/nodes/sec-smooth-purity/lem-sp-tower-mate-evaluation-reduction.json`: statement, unsplit; no Mathlib match. Finite evaluation and explicit mixed reduction square of an already constructed tower transpose; does not assert exceptional invertibility.
- `dag/nodes/sec-smooth-purity/lem-sp-integral-exceptional-mate-transport.json`: statement, unsplit; no Mathlib match. Counit-preserving right-adjoint identification and transpose transport for an arbitrary supplied tower arrow; does not assert exceptional base-change invertibility.
- `citations.json`: one verbatim supporting statement excerpt for every assembly step/node pair.

There are three new nodes and zero Mathlib leaves. Search-plan, full search responses, searches.jsonl, and original-item.json are retained as sandbox evidence, along with the scripts which wrote the delivery. Only the four DAG files and this report are delivery content.

## Attachments

None. I searched the live project root WeilConjectures by blueprint id and by exceptional base change, tower adjunction, normalized tower and reconstruction. No project declaration states the whole item. The ordinary finite/small-etale normalized-tower realization results do not state the varying-coefficient pro-etale compact-support and exceptional square, with integral counit normalization. Mathlib declarations are not project attachments.

## WANTED

None. The source and dependency statements needed for this re-split are available locally. This is an agent-written refinement of the blueprint, not a new claim to have read an independent proof in Stacks. No SGA source is used.

## What was wrong; repair order

The live proof was already accepted on 2026-10-17, but the released stage-1 repair note dated 2026-10-22 expressly reopens it with keep_plan=true. Its seven arguments were too much work for one node. The order requires at least two separate statement-only nodes, comparable in size, and at most 3000 characters of assembly, retaining every old argument. I created three tasks, separating geometric pullback/reconstruction, finite tower mate compatibility, and integral transpose transport. They are not restated clauses: the first has no exceptional functor at all, the second deliberately leaves invertibility open, and the third handles arbitrary tower morphisms without asserting their invertibility. The assembly still has to invoke finite exceptional invertibility and conservativity, propagate normalization, and apply the transported transpose identity.

The route note's Q107 sandbox does not exist on this machine. The Q129 sandbox initially contained only dispatcher brief markers, with no interrupted delivery or search log. I retained the current live node (including all prior metadata and recorded searches) instead of reconstructing an obsolete Q107 attempt. No live repository, launcher, Lean source, compiler or Lake/build tool was written or run.

There is no new statement dispute. The earlier correction of the imported unbound context and the reviewer normalization of beta_Zl remain verbatim. The old statement-correction record remains. The item is not the unit key node, so the unit realization record is not changed.

## Argument allocation

- Old step 1: finite-type Noetherian domains, finite etale origin, ordinary-tower boundedness, exact pullback bounds, tensor/pullback comparison and normalization are the first new task. The geometric pullback compactification and smooth relative dimension remain explicit assembly citations.
- Old step 2: the existing actual compactification exchange remains an assembly application. Its ctf restriction and finite evaluations are explicitly in the second task, with the original argument retained below.
- Old step 3: actual transpose formula, naturality and finite evaluation go to the second task. Finite canonical exceptional invertibility, the identity ell=unit*varpi^e, and derived evaluation conservativity remain in the assembly. No inference that an arbitrary mate is invertible is used.
- Old step 4: the two reduction formulas and both equalities, including the input transition r, are stated in full in the second task. The normalization argument remains in assembly step 4, with G preserving normalized towers and exact pullback preserving them.
- Old step 5: both adjunctions have the same compact-support functor and the unique counit-preserving identification delta in the third task. The original unique-right-adjoint proof citation and all hypotheses are retained below for that worker.
- Old step 6: pullback is the total limit of the single strict quotient complex and its actual comparison is the reconstruction counit: first task. The composites a,b and conjugated unit/limit formula for an arbitrary t: third task. Functors sending inverse pairs to inverse pairs remains in the assembly.
- Old step 7: the coefficient-transported beta_I and the exact reduction-of-transpose equation for arbitrary t are the third task. Its consequence follows by full faithfulness on actual derived towers, not equality of evaluations; the complete argument is retained below. Applying it to the already constructed e remains in assembly step 5.

The next section preserves the complete seven arguments verbatim, including every old citation and source place, as the proof handoff for the statement-only tasks. Nothing is discarded by replacing the item's long proof.

## Retained complete argument handoff

### Previous step 1

Put $F_f=Rf_{!,\bullet}$ and $G_f=f^!_\bullet$. The pullback compactification $c'$ exists by [def-cbc-compact-support-square]; [lem-sbc-smooth-relative-dimension-permanence](1) makes $f'$ smooth of the same relative dimension $d$. All four schemes are Noetherian by [lem-weil-pbc-finite-type-over-noetherian], applied to their structure maps over the field $k$ (a field has only the ideals $0,(1)$). Their finite levels have etale-origin witnesses by [lem-weil-pbc-finite-ring-constructible-derived-origin], since $A_n$ is finite. Uniform cohomological bounds make each tower bounded below in the ordinary tower derived category, whose cohomology is levelwise [det-sp-coefficient-towers-abelian]. Pullback along $u,v$ preserves the finite constructible Tor interval by [lem-sf-pullback-tor-amplitude], and the cohomological interval by exactness [prop-weil-pbc-proetale-constant-exact]. Consequently it preserves the stated tower category. The tensor-pullback isomorphism [lem-weil-pbc-ringed-topoi-derived-tensor-pullback], applied to the coefficient quotient, identifies pullback of $C_n\otimes^L_{A_n}A_m\to C_m$ with the reduction map of the pulled-back tower. These identifications are natural in the quotient, so pullback also preserves normalized towers.

Uses: def-cbc-compact-support-square, lem-sbc-smooth-relative-dimension-permanence, lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-finite-ring-constructible-derived-origin, det-sp-coefficient-towers-abelian, lem-sf-pullback-tor-amplitude, prop-weil-pbc-proetale-constant-exact, lem-weil-pbc-ringed-topoi-derived-tensor-pullback.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-tower.proof.md, (1)–(3): geometric and coefficient domains.

### Previous step 2

Use the specified actual tower exchange of [det-sp-tower-shriek-levels](2b), constructed from the proper counit mate and open extension for $c,c'$. Step 1 supplies its bounded-below input and an etale-origin witness at every finite level; compatible choices of these witnesses are unnecessary. This gives the isomorphism $\beta_{f,\bullet}:v^*_\bullet F_f\xrightarrow{\sim}F_{f'}u^*_\bullet$, whose evaluations are the finite compact-support exchanges. The same statement's clause (1) identifies $F_f$ and $F_{f'}$ with the compactification operations used in [det-sp-tower-gluing]. That adjunction makes these functors defined on the tower ctf categories. Thus the ambient exchange restricts to the functors in clause (1) of the item.

Uses: det-sp-tower-shriek-levels, det-sp-tower-gluing.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-tower.proof.md, (1): compactification exchange and its finite evaluations.

### Previous step 3

For a tower $K$ on $Y$, define $q_K=v^*_\bullet(\varepsilon_{f,K})\,\beta_{f,\bullet}(G_fK)^{-1}:F_{f'}u^*_\bullet G_fK\to v^*_\bullet K$. Its unique transpose under $F_{f'}\dashv G_{f'}$ of [det-sp-tower-gluing] is $e_K$, and explicitly $e_K=G_{f'}(q_K)\eta_{f',u^*G_fK}$. Naturality of $\beta$, the counit, and the unit makes this family natural. The evaluation comparisons in [det-sp-tower-gluing](3) and [det-sp-tower-shriek-levels](1),(2) carry this formula to $G_{f',n}(v_n^*\varepsilon_{f,n}\,\beta_{f,n}^{-1})\eta_{f',n}$; this is the finite counit transpose, with the adjunction normalization in the item. Its invertibility is [lem-pur-smb-extraordinary], applied at $A_n=\mathcal O_E/\varpi_E^{en}$, where $\ell$ is a unit times $\varpi_E^e$. It applies to $K_n$ in the finite ctf category, the same global field and smooth morphism, and arbitrary $v$. Hence each evaluation of the already constructed tower map $e_K$ is invertible. Clause (3) of [det-sp-tower-shriek-levels] implies $e_K$ is invertible. This uses evaluation conservativity only after constructing $e_K$ by an actual tower adjunction.

Uses: det-sp-tower-gluing, det-sp-tower-shriek-levels, lem-pur-smb-extraordinary.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-tower.proof.md, (2): transpose construction, evaluation and invertibility.

### Previous step 4

Write $T_{nm}=-\otimes^L_{A_n}A_m$, $r=r^K_{n,m}:T_{nm}K_n\to K_m$ and $P=u^*G_fK$, $Q=G_{f'}v^*K$. By [det-sp-tower-gluing](3), their reductions are $r^P_{n,m}=u_m^*G_{f,m}(r)\,u_m^*c^f_{n,m}(K_n)$ and $r^Q_{n,m}=G_{f',m}(v_m^*r)\,c^{f'}_{n,m}(v_n^*K_n)$, after the pullback/tensor identifications of Step 1. Apply the second identity of [det-sp-mixed-base-change] to the actual, possibly nonflat quotient $A_n\to A_m$. Composing that identity with $G_{f',m}(v_m^*r)$ and using naturality of $e_{f,m}$ gives
$$\begin{aligned}
r^Q_{n,m}\,T_{nm}(e_{f,n}(K_n))
&=G_{f',m}(v_m^*r)\,e_{f,m}(T_{nm}K_n)\,u_m^*c^f_{n,m}(K_n)\\
&=e_{f,m}(K_m)\,u_m^*G_{f,m}(r)\,u_m^*c^f_{n,m}(K_n)
=e_{f,m}(K_m)\,r^P_{n,m}.
\end{aligned}$$
This is the claimed reduction square; no equality of derived tower maps is inferred from equality of their evaluations. For normalized input $K$, [det-sp-tower-gamma](3) makes $G_fK$ normalized, and Step 1 makes $P$ normalized. The square just proved and the invertibility of both horizontal maps make each reduction of $Q$ invertible. The ctf bounds of $Q$ already follow from Step 1 and the tower adjunction.

Uses: det-sp-tower-gluing, det-sp-mixed-base-change, det-sp-tower-gamma.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-tower.proof.md, (2): explicit mixed reduction square and normalized subcategory.

### Previous step 5

Now put $E=\mathbf Q_\ell$, write $r_T=\operatorname{red}_T$ and $L_T=R\varprojlim$, and use the equivalence [det-sp-normalized-equivalence]. Its Noetherian hypothesis holds by Step 1. For $K\in\Dbc(Y,\mathbf Z_\ell)$, [det-sp-integral-adjunction-bijection] gives the normalized tower $G_fr_YK$, the integral object $H_fK=L_XG_fr_YK$, the comparison $r_XH_fK\simeq G_fr_YK$, and $Rf_{!,\mathbf Z_\ell}\dashv H_f$ with its unit and counit transported from the tower adjunction. The right adjoint $f^!_{\mathbf Z_\ell}$ of [prop-coef-integral-exceptional-adjoint] is for the same compact-support functor: [det-sp-integral-direct-image-tower](2) identifies that functor with $L_YF_fr_X$. Thus [det-sp-unique-right-adjoint] gives the unique counit-preserving identification $f^!_{\mathbf Z_\ell}\simeq H_f$, and likewise for $f'$. Use these identifications throughout the remaining calculation; they transport the adjunctions, not merely their objects.

Uses: det-sp-normalized-equivalence, det-sp-integral-adjunction-bijection, prop-coef-integral-exceptional-adjoint, det-sp-integral-direct-image-tower, det-sp-unique-right-adjoint.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-tower.proof.md, (3): integral adjunction and its counit-preserving normalization.

### Previous step 6

For a morphism $h:U\to V$, put $C_K=h_\bullet^*r_VK$. Step 1 shows that $C_K$ is a normalized constructible tower for $K\in\Dbc(V,\mathbf Z_\ell)$, using [det-sp-normalized-equivalence] for $r_VK$. By the definition [def-pur-integral-derived-operations], completed pullback is $h^*_{\mathbf Z_\ell}K=L_UC_K$: apply termwise finite pullback to the single reduction complex and then take total derived inverse limit, with its quotient transitions. The reconstruction equivalence therefore shows directly that this pullback is constructible and gives an isomorphism of actual derived towers
$$r_Uh^*_{\mathbf Z_\ell}K=r_UL_UC_K\xrightarrow{\epsilon^{r,L}_{C_K}}C_K=h_\bullet^*r_VK.$$
This is the counit of [det-sp-normalized-equivalence], natural in the entire tower, rather than a lift inferred from individual reductions. Together with Step 5, for $h=u,v$ this supplies
$$a_K:r_{X'}(u_{\mathbf Z_\ell}^*f^!_{\mathbf Z_\ell}K)\xrightarrow{\sim}u_\bullet^*G_fr_YK=P_K,\qquad b_K:r_{X'}((f')^!_{\mathbf Z_\ell}v_{\mathbf Z_\ell}^*K)\xrightarrow{\sim}G_{f'}v_\bullet^*r_YK=Q_K.$$
Apply $L_{X'}$ to $e_{r_YK}:P_K\xrightarrow{\sim}Q_K$ and conjugate by these isomorphisms and the reconstruction units. This constructs a natural integral isomorphism $E_K$ with $r_{X'}E_K=b_K^{-1}e_{r_YK}a_K$. A functor takes an inverse pair to an inverse pair, so $E_K$ is invertible. This is precisely $R\varprojlim e_{f,\bullet}(r_YK)$ under the specified reconstruction identifications.

Uses: def-pur-integral-derived-operations, det-sp-normalized-equivalence.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-tower.proof.md, (3): pullback reductions and reconstruction of the isomorphism.

### Previous step 7

Identify its transpose without commuting a Hom set with an infinite limit. For $M\in\Dbc(X,\mathbf Z_\ell)$, [det-sp-integral-direct-image-tower](2) and Step 6 identify the reductions of $v_{\mathbf Z_\ell}^*Rf_{!,\mathbf Z_\ell}M$ and $R(f')_{!,\mathbf Z_\ell}u_{\mathbf Z_\ell}^*M$ with $v_\bullet^*F_fr_XM$ and $F_{f'}u_\bullet^*r_XM$. Both towers are normalized by [det-sp-tower-gamma](3) and Step 1. By the item's statement, $\beta_{f,\mathbf Z_\ell}(M)$ is the reconstruction of $\beta_{f,\bullet}(r_XM)$ through the equivalence [det-sp-normalized-equivalence], under these identifications: full faithfulness of $r_{Y'}$ on $\Dbc(Y',\mathbf Z_\ell)$ gives a unique integral arrow with that reduction, and it is invertible because $\beta_{f,\bullet}$ is (Step 2). This is the coefficient transport by which the source's proof, paragraph (3), reads the integral compact-support exchange. The Hom bijections of [det-sp-integral-adjunction-bijection] send an integral arrow to its reduced arrow with these operation comparisons inserted, and send the integral counit to the tower counit. Consequently reduction of the integral transpose $\varepsilon_{f',v^*K}\,R(f')_!(E_K)$ is exactly
$$\varepsilon_{f',\bullet}\,F_{f'}(e_{r_YK})=v_\bullet^*(\varepsilon_{f,\bullet})\,\beta_{f,\bullet}(G_fr_YK)^{-1},$$
by the defining transpose equation of Step 3. The right side is the reduction of $v_{\mathbf Z_\ell}^*(\varepsilon_{f,\mathbf Z_\ell})\,\beta_{f,\mathbf Z_\ell}(f^!_{\mathbf Z_\ell}K)^{-1}$ by Step 5 and the just specified reconstruction of $\beta$. Faithfulness of $r_{Y'}$ in [det-sp-normalized-equivalence] proves equality of these integral arrows. Thus $E_K$ is exactly the exceptional base-change counit transpose, proving clause (3) with its stated normalization.

Uses: det-sp-integral-direct-image-tower, det-sp-tower-gamma, det-sp-normalized-equivalence, det-sp-integral-adjunction-bijection.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-tower.proof.md, (3): explicit reduction of the transpose, using full faithfulness rather than levelwise faithfulness.

## Not duplicates

lem-sp-ctf-tower-pullback-reconstruction vs det-sp-normalized-equivalence: the latter supplies reduction/limit adjunction, not the arbitrary scheme-pullback domain and actual completed-pullback reconstruction comparison.
lem-sp-ctf-tower-pullback-reconstruction vs lem-pur-integral-operations-preserve-constructible: individual reduction isomorphisms and integral preservation do not state the actual whole varying-coefficient tower comparison, its normalization and uniform intervals.
lem-sp-ctf-tower-pullback-reconstruction vs lem-sf-exact-pullback-tower-counit-comparison: that statement treats towers over one fixed ring and the universal left-derived counit, not coefficient quotient systems, constructibility/Tor bounds or the reduction/total-limit counit.
lem-sp-ctf-tower-pullback-reconstruction vs lem-fd-whole-tower-integral-pullback-comparison: that compares two framework pullbacks for scheme isomorphisms; this gives arbitrary morphism pullback, uniform tower domains and reconstruction counit in the specific tower model.
lem-sp-ctf-tower-pullback-reconstruction vs lem-pod-integral-pullback-system-comparison: the latter concerns the independently specified coherent-system calculus with a representative-level scalar adjoint; this task is about the ordinary strict-tower derived category in the retained route and additionally uniform domain and quotient-tensor assertions. No unproved identification of the two coherent models is made.
lem-sp-tower-mate-evaluation-reduction vs det-sp-tower-gluing: the latter gives evaluation of a single exceptional adjoint and its transitions, not the base-change mate and its mixed reduction square including r^K.
lem-sp-tower-mate-evaluation-reduction vs det-sp-mixed-base-change: that is a two-ring finite identity, not construction/evaluation of an actual tower mate and its full reduction square.
lem-sp-tower-mate-evaluation-reduction vs lem-sp-coefficient-tower-shriek-calculus: that supplies compact-support composition and direct-image transitions, not exceptional base-change transpose evaluation/reduction.
lem-sp-tower-mate-evaluation-reduction vs lem-pur-brown-tower-finite-site-comparison: that compares an etale Brown adjoint with pro-etale finite evaluations on its stated normalized domain, not an arbitrary unnormalized ctf tower square and its base-change transpose identity.
lem-sp-integral-exceptional-mate-transport vs det-sp-integral-adjunction-bijection: that constructs one integral adjunction and H; the new task compares both right-adjoint normalizations in a square and computes the transpose of an arbitrary reconstructed map.
lem-sp-integral-exceptional-mate-transport vs det-sp-unique-adjoint-coefficients: that treats a finite coefficient-extension functor between two stages, not reconstruction through four reduction/limit equivalences and completed scheme pullbacks.
lem-sp-integral-exceptional-mate-transport vs lem-sp-completion-mate-comparison: that is the ordinary inverse-image/direct-image mate for constant coefficient completion; this is the exceptional compact-support adjunction in completed coefficient sheaves with the beta_I defined by transport.
lem-sp-integral-exceptional-mate-transport vs lem-pur-point-trace-reconstruction: the latter has point target and coefficient-unit pairing, not arbitrary base-change square and arbitrary K/t.
lem-sp-integral-exceptional-mate-transport vs lem-pur-transport-integral-counit-realization: that compares condensed purity representing adjunctions and trace transports; this computes the specific completed ordinary-module arbitrary-arrow transpose under a four-corner coefficient reconstruction. It does not assume a condensed comparison.

The whole imported blueprint was searched using blueprint_refs for reconstruction, pullback reduction, integral pullback, tower mate, mate, counit-preserving, normalized constructible, reduction maps and exceptional base change. All DAG statements were searched for the reconstruction counit, mixed identity, evaluation comparisons and transpose language. Searches by the three proposed ids found none. The item's broad clauses are not duplicate replacement lemmas: the new claims are subsidiary comparison identities with invertibility excluded as stated above. There are no newly cited Stacks tags, hence no same-tag pairs requiring a further distinction. The source places point directly at the blueprint's three proof paragraphs.

## Mathlib search reading

Each new node has five actual searches: LeanFinder, LeanSearch, Loogle, grep, and a second LeanFinder phrasing. The exact tools and query strings are in its mathlib_searches, matching searches.jsonl; full responses are adjacent *.searchN.txt. All services answered. The pullback search returned SheafOfModules.pullback and pullbackPushforwardAdjunction: I read PullbackContinuous.lean, including the construction and adjunction (lines 49–61) and pullbackIso. These are underived sheaf functors, without uniform normalized derived towers. The pro-etale grep hits in Sites/Proetale.lean and Sites/ElladicCohomology.lean only define the site and ell-adic coefficient/cohomology, not this comparison. The mate query returned Adjunction.homEquiv and its unit/counit formulas; I read Adjunction/Basic.lean at 160–190. They provide the formal transpose but no geometric tower transition/evaluation theorem. The integral query returned Equivalence.toAdjunction and Adjunction.map_restrictFullyFaithful_counit_app: general equivalence and restriction normalization do not construct or identify the compact-support, completed pullback and exceptional functors in this statement, so they are not a one-line specialization of the new geometric claim. The other hits concern ideal completion, normalization of schemes, condensed modules or unrelated coefficient extension, not an exact match. A further msearch grep recorded the relevant general declarations. No new Mathlib leaf is asserted.

## Review by Q129

I read the current tower lemma and its proof paragraphs (1)–(3) in literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/, together with its unit _section and chapter record. The chapter's finite diagonal/DNC route is retained. The source for all three extracted tasks is that same tower proof, expanded by the accepted seven-step argument preserved above; I do not represent the blueprint as a human-authored independent proof.

For assembly step 1 I opened the entire statements of the first new task, def-cbc-compact-support-square and lem-sbc-smooth-relative-dimension-permanence. They give respectively the uniform domains and actual quotient comparisons, the pullback compactification, and smoothness with unchanged d for arbitrary v. The standing finite-type hypotheses make all schemes Noetherian; finite rings A_n supply the etale-origin witnesses needed below. No compatible choices of origin witnesses are assumed.

For assembly step 2 I read det-sp-tower-shriek-levels (1), (2b) and (3), and det-sp-tower-gluing (2), (3). The exchange is an actual map on bounded-below towers whose evaluations have etale origin, precisely the first task's output. The second task explicitly states restriction to ctf and the finite exchange; gluing supplies the adjunction on those categories. Merely knowing finite isomorphisms would not construct a derived-tower morphism, so the construction remains before evaluation.

For assembly step 3 the second task's displayed evaluation is literally the finite transpose with its unit and counit, rather than an arbitrary finite map. I checked lem-pur-smb-extraordinary's smoothness and relative dimension hypotheses and arbitrary horizontal v, and the coefficient convention A_n=O_E/varpi_E^(en). The finite comparison is the one in the unchanged item normalization. Conservativity is exactly det-sp-tower-shriek-levels (3), which explicitly does not assert faithfulness or arbitrary lifts. It is applied only after constructing e.

For assembly step 4 I recomputed the two reductions in the second task from gluing (3). For r:T_nm K_n→K_m, the mixed identity first gives G'v*r e_m(TK_n) u*c; naturality of e_m moves r to give e_m(K_m) u*G(r) u*c. This is the displayed r^Q T(e_n)=e_m r^P square, with a possibly nonflat quotient. The normalization proof uses det-sp-tower-gamma (3), whose statement explicitly preserves normalized constructible towers. With source reduction and both horizontal maps invertible, the target reduction is invertible by composing inverses. Ctf membership is already supplied by the first task and tower adjunctions.

For assembly step 5 I read det-sp-normalized-equivalence, det-sp-integral-adjunction-bijection, det-sp-integral-direct-image-tower, prop-coef-integral-exceptional-adjoint, det-sp-unique-right-adjoint and the completed-pullback definition in full. The two right adjoints are for the identical integral compact-support composite after its canonical limit comparison. The third task retains this as a counit-preserving delta, not an object-only identification. The first task's alpha is the reconstruction counit on the actual pulled-back quotient tower; the third task inserts it in a,b, and states the formula with reconstruction units. Its transpose identity is stated for an arbitrary t, making the proof obligation independent of exceptional invertibility. It computes the integral counit after full reduction, where the tower transpose equation holds, and uses faithfulness of the whole reduction equivalence. It never swaps Hom with an infinite limit. The beta_I used here is exactly the coefficient transport fixed in the item's existing statement, with no claimed comparison to def-cbc-completed-exchange-map.

I tested the extracted statements at K=0 and empty schemes: reductions, counits and the asserted maps have zero source/target as required. For identity horizontal v, the reduction equations reduce to the identity square and the reconstruction transpose equation reduces to the ordinary adjunction. The n=m case gives T_nn=id and c_nn=id, hence the same map on both sides; for n>m the quotient need not be flat and all formulas retain derived tensor. In relative dimension zero the argument uses the finite etale-style adjunction without a positive-dimensional shift. Non-normalized K is allowed in the second task; normalization is invoked only after imposing it. The third task accepts t=0 and does not incorrectly force invertibility. These checks rule out the common overstrong variants of the extracted lemmas.

I checked B–E of delivery-errors against the written files. New statements introduce all schemes, rings, categories, functors and comparisons, carry no proof steps or proof_deps, and each notion is cited or defined inline. The statement-only tasks carry equations, not proof sketches. No elementary two-line fact was promoted in isolation: each task combines substantial domain/evaluation/normalization data, as the explicit repair order requires. The retained report contains every previous argument. The assembly is below 3000 characters and no step exceeds 2000. Every uses entry has a verbatim quote in citations.json checked as a substring of the cited statement; proof_deps is their exact union. All new statements depend only on prior nodes and the first task, not on the item, so no new cycle is introduced. The previous accepted tool_uses metadata is preserved; the new proof cites the existing smooth-relative-dimension tool and otherwise stays on its unit route. No statement, definition, target, chapter or unit route was changed.

## Unfinished work

The three new nodes are intentionally unsplit proof tasks for subsequent workers, as the released human repair order requires. No mathematical argument of the prior item was left without either an extracted statement obligation or explicit assembly use. Mechanical server validation and push results are recorded below after completion.
