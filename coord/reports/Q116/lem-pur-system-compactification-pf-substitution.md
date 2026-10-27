# Stage 1 repair: lem-pur-system-compactification-pf-substitution

1. Files written: the unchanged-statement item, now a short assembly; lem-pur-system-refinement-constructible-domain (statement, unsplit, no Mathlib match); lem-pur-refinement-inverse-mate-comparisons (statement, unsplit, no Mathlib match); citations.json.
2. Attachments: none. The upstream finite-ring refinement declarations do not state an equality for varying-coefficient systems. The local Sheaf module has sorry in refinementGamma_isIso, system_compactification_pf_substitution and system_compactification_refinement_coherence.
3. WANTED: none.
4. The released repair note requires distributing the nine-step proof, whose length was 7363 characters, without weakening its statement. The sandbox initially had no node, report or search log; I copied the current live node. It carries the returned nine-step proof and the old independent review. The new proof changes no statement or Lean record and no unit or chapter.
5. Nothing mathematical remains unfinished in the assembly. Both new nodes are intentionally statement-only for other workers.

## Review by Q116

I read the stage-1 brief, delivery-errors B-E (both copies), the chapter and compatibility unit, the released repair note, and the current item. The relevant blueprint ancestor says coherence is transported as compatible finite-level systems; it does not supply faithfulness of derived evaluation. I read its current main-20261015 proof, and the finite-Tor tensor proof (i),(ii). I read Stacks more-etale.tex lemma-shriek-proper-and-open (0F7B), its vertical-pasting lemma (0F7C), and lemma-shriek-composition (0F7J), sites-cohomology.tex equation-projection-formula-map (0B56) and lemma-derived-pushforward-composition (0D6E), and flat.tex lemma-compactifications-cofiltered (0ATU), including its equalizer construction. The new domain node is an agent deduction from these sources and the actual semilinear models, not a claim that Stacks already proves varying-ring assertions. The new comparison node is an abstract agent extraction of the inverse/compositor and cancellation arguments, with the exact pointwise domain hypothesis. Neither node contains proof steps or a proof disguised as its statement.

Step 1 uses the new domain node for closure, invertibility and its finite normalization, and semilinear-derived-sections for actual operations before evaluation. The new domain node preserves both the finite-level Tor intervals and actual transition-adjoint formulas of old Step 2. Old Step 3 uses a constant auxiliary tower at one fixed A_n, never the varying-ring tower in the fixed-ring calculus: etale-origin witnesses exist by constructible-origin (ii), the fixed-ring proper/open theorem supplies invertibility, varying-ring pasting identifies the evaluated mate, and joint conservativity detects an isomorphism, not equality of maps. Each of those cited statements was opened and read. Normalization of direct images is not required.

Step 2 uses compactification/refinement equations and properness implying finite type, finite-type composition and preservation of Noetherianity, then quasi-compactness of opens in a Noetherian scheme. These are precisely the clauses in the cited statements. Applying the clopen tensor identity to (j1,j2,id_X,u), H=M and Q=P_p2 N gives the displayed equation, with both sides K2 tensor P_p2 N to R_u j1! T. No Cartesian refinement square is assumed: an extra clopen component is allowed.

Step 3 uses the existing ringed projection-composition theorem, which includes naturality and its counit definition. Its input category is the module category of the ringed topos of semilinear systems, as explicitly stated in semilinear-derived-sections. Ambient setting (b) identifies the compositors with the conjugate canonical ones and gives tensor/composition coherence. Thus this is a direct application of an existing general node, not a new duplicate. The common transpose calculation from old Step 5 is retained below for its future worker.

Step 4 is the explicit substitution: invert both gamma maps, apply R_p2, precompose by the proper projection and compositor, use naturality of c and pi. The quoted canonical compositor theorem supplies naturality, and the projection theorem supplies naturality in both arguments. This produces the original two composites without evaluating them.

Step 5 uses the new inverse-mate lemma only after checking its hypotheses: full levelwise bounded constructible domain; every refinement gamma invertible by Step 1; actual vertical-pasting and identity equations from varying-ring pasting; associative unital compositors from ambient setting (b); cofilteredness with parallel-arrow equalizers from compactifiable-cofiltered. These citations give their stated equations and both cofilteredness clauses. Unlike the existing formal staircase theorem, the new lemma needs invertibility only for refinement mates evaluated on this one source domain; it assumes no invertibility for all proper/open squares on every ambient derived category and no compatible binary or triple towers. That distinction avoids imposing unstated preservation hypotheses. It retains the exact inverse-compositor formula and parallel-arrow and span cancellation arguments, shown below.

Small cases checked: identity u (all units reduce to identity), empty X (zero extension), a compactification with an extra clopen component (projector is (1,0), so no Cartesian assumption), distinct parallel arrows (must equalize before cancelling), and Tor intervals growing with n (every assertion remains levelwise). The comparison node also works when gamma is not invertible outside the supplied full subcategory. No target or statement was changed; no SGA source, compiler, Lake, Lean-writing, repository-writing or manual git command was used. The assembly has 2176 characters; no non-elementary step exceeds 2000 characters.

## Original arguments and their destinations

These are the exact original step texts, retained so no shortened assembly conceals lost work. They are future-worker guidance in this report, not proof fields in the unsplit nodes.
### Original step 1 -> assembly Steps 1-4 and existing projection/clopen nodes

Work in the simultaneous enhanced section models for $D(\mathscr S_W)$. The counit transpose defining $\pi_u$, the open tensor comparison $\delta_j$, and their composites are specified transformations in these models. Evaluation preserves these constructions and their composition, but is not used to detect equality of morphisms. Naturality of $\pi$ follows from its unit/counit formula and naturality of the tensor comparison; $\delta$ is the natural open-adjunction comparison. All subsequent tensor symbols denote derived tensor.

Uses: lem-coef-semilinear-derived-sections, def-exchange-projection, lem-sf-open-tensor-normalization

Source: {"document": "literature/stacks-project/sites-cohomology.tex", "place": "Tag 0B56 (equation-projection-formula-map), the displayed counit transpose; agent application to the simultaneous section models"}

### Original step 2 -> lem-pur-system-refinement-constructible-domain

Put $T=M\otimes^LP_fN$. At each $n$, pullback preservation gives $(P_fN)_n\in D^b_{ctf}(X,A_n)$, with the same Tor interval as $N_n$. Tensor preservation then gives $T_n\in D^b_{ctf}(X,A_n)$, with the sum of the two level-$n$ Tor intervals. The normalized-system closure lemma applies to the ring systems $B_{n,X}=f^{-1}B_{n,Y}$: the actual transition-adjoint of $P_fN$ is $f^{-1}\alpha^N_{m,n}$, and that of $T$ is the strong monoidal scalar-extension comparison followed by $\alpha^M_{m,n}\otimes\alpha^{P_fN}_{m,n}$. Both are invertible. Thus $M$ and $T$ have the domain properties needed below. All bounds here are chosen separately at each $n$. No assertion about normalization of $R_pj_!M$ is needed, since the operations and projection transformations are defined in the ambient unbounded system categories.

Uses: lem-sf-pullback-tor-amplitude, lem-sf-tensor-ctf, lem-pur-system-normalized-tensor-closure, lem-coef-semilinear-derived-sections

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-biduality-general/lem-sf-tensor-ctf.proof.md", "place": "Clauses (i) and (ii); agent domain check combining this finite-level result with lem-sf-pullback-tor-amplitude and the transition-adjoint formulas of lem-pur-system-normalized-tensor-closure. There is no blueprint strict-system domain-check paragraph."}

### Original step 3 -> lem-pur-system-refinement-constructible-domain

Let $K$ be any system with bounded constructible levels, including $M$ and $T$. For each $n$, constructible origin supplies $L_n\in D^b_c(X_{\mathrm{et}},A_n)$ and $\nu_X^*L_n\simeq K_n$. Apply the fixed-ring proper/open calculus only with $B=A_n$, to the constant-in-the-tower-index system with value $K_n$ and identity transitions. Its finite-origin hypothesis holds with $\Lambda_m=A_n$ and $L_m=L_n$ at every auxiliary tower index $m$. Hence its evaluated refinement mate is an isomorphism, normalized as the finite proper/open comparison. Separately, the varying-ring pasting lemma with $R_n=A_n$ constructs the actual semilinear mate $\gamma_u$ and identifies its evaluation with this constant-$A_n$ mate. Evaluation detects equivalences in the semilinear section category, so $\gamma_{u,K}$ is invertible. Evaluation of $R_{p_2}(\gamma_{u,K}^{-1})c_{p_2,u}$ is exactly the finite comparison of the refinement-comparison definition, with the witness just chosen. This proves the finite normalization without asserting that derived evaluation is faithful on morphisms.

Uses: lem-sf-proetale-constructible-origin, lem-cbc-strict-tower-proper-open-calculus, lem-sp-varying-ring-proper-open-pasting, lem-coef-semilinear-derived-sections, def-sf-refinement-comparison-isomorphism

Source: {"document": "literature/stacks-project/more-etale.tex", "place": "Tags 0F7B (lemma-shriek-proper-and-open) and 0F7J (lemma-shriek-composition); agent separation of fixed-A_n invertibility from the varying-ring construction and equivalence detection"}

### Original step 4 -> assembly Steps 1-4 and existing projection/clopen nodes

Apply the strict-system clopen tensor-mate identity to $(k_1,i,r,p_1)=(j_1,j_2,1_X,u)$ and $Q=P_{p_2}N$. The refinement definition supplies $uj_1=j_2$ and $p_2u=p_1$, and all schemes are separated finite-type over $k$. The compactification spaces are Noetherian: $p_i$ is proper, hence finite-type, and finite-type composition over the Noetherian scheme $\operatorname{Spec}k$ gives this by the cited Noetherian lemma. Each inverse image of an affine chart under $j_i$ is an open subscheme of that Noetherian chart, hence quasi-compact by the cited open-subscheme lemma. Thus $j_i$ is quasi-compact. The identity-left projection is the identity under the unit identifications. Write $K_i=j_{i!}M$ and $d_i=\delta_{j_i;M,P_{p_i}N}$. After the canonical pullback identifications the cited identity is
$$\gamma_{u,T}d_2=R_u(d_1)\pi_{u;K_1,P_{p_2}N}(\gamma_{u,M}\otimes1).$$
Its source is $K_2\otimes P_{p_2}N$, and its target is $R_uj_{1!}T$. This is already an equality in the derived category of varying-coefficient systems.

Uses: lem-pur-system-clopen-tensor-compatibility, def-weil-compactifications-refinements, def-weil-proper-morphism, lem-sfb-finite-type-composition-base-change, lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-noetherian-open-subscheme-noetherian

Source: {"document": "literature/stacks-project/more-etale.tex", "place": "Tag 0F7B (lemma-shriek-proper-and-open), refinement square; agent specialization of lem-pur-system-clopen-tensor-compatibility"}

### Original step 5 -> assembly Steps 1-4 and existing projection/clopen nodes

Use the ambient system compositor and tensor/composition coherence in setting (b) of the cited pasting lemma. For $H\in D(\mathscr S_{\overline X_1})$ and $Q\in D(\mathscr S_Y)$, put $H'=H\otimes P_{p_1}Q$. The typed projection-composition identity is
$$c_{p_2,u,H'}\pi_{p_1;H,Q}
=R_{p_2}(\pi_{u;H,P_{p_2}Q})\pi_{p_2;R_uH,Q}(c_{p_2,u,H}\otimes1_Q).$$
Indeed, transpose under $P_uP_{p_2}\dashv R_{p_2}R_u$. On both sides, the tensor/composition identity first splits the tensor pullback; the counit on its first factor is
$$P_uP_{p_2}R_{p_2}R_uH\xrightarrow{P_u\varepsilon_{p_2,R_uH}}P_uR_uH\xrightarrow{\varepsilon_{u,H}}H.$$
The second factor is unchanged. The composite-adjunction counit and mate-pasting statements therefore give equal transposes, hence equal maps. This calculation takes place in the same section models.

Uses: lem-sf-ambient-proper-open-pasting, lem-weil-pbc-ringed-topoi-derived-pushforward-composition, lem-weil-pbc-mate-pasting, def-exchange-projection

Source: {"document": "literature/stacks-project/sites-cohomology.tex", "place": "Tags 0B56 (equation-projection-formula-map) and 0D6E (lemma-derived-pushforward-composition); explicit agent transpose calculation using the cited system tensor/composition coherence"}

### Original step 6 -> assembly Steps 1-4 and existing projection/clopen nodes

Since both refinement mates in Step 4 are invertible by Step 3, that equation gives
$$\gamma_{u,T}^{-1}R_u(d_1)\pi_{u;K_1,P_{p_2}N}
=d_2(\gamma_{u,M}^{-1}\otimes1).$$
Apply $R_{p_2}$ and precompose with $\pi_{p_2;R_uK_1,N}(c_{p_2,u,K_1}\otimes1_N)$. On the left, naturality of $c$ and Step 5 identify the result with $\theta_{u,T}R_{p_1}(d_1)\pi_{p_1;K_1,N}$. On the right use the explicit naturality equation
$$R_{p_2}(\gamma_{u,M}^{-1}\otimes1)\pi_{p_2;R_uK_1,N}
=\pi_{p_2;K_2,N}(R_{p_2}(\gamma_{u,M}^{-1})\otimes1).$$
The result is $R_{p_2}(d_2)\pi_{p_2;K_2,N}(\theta_{u,M}\otimes1_N)$. By the specified definitions these are exactly the two required projection/refinement composites, with common source $F_1M\otimes N$ and target $F_2T$.

Uses: def-exchange-projection, lem-weil-pbc-ringed-topoi-derived-pushforward-composition

Source: {"document": "literature/stacks-project/sites-cohomology.tex", "place": "Tag 0B56 (equation-projection-formula-map); agent substitution of the clopen tensor identity into the typed projection-composition equation"}

### Original step 7 -> lem-pur-refinement-inverse-mate-comparisons

Let $u:c_1\to c_2$ and $v:c_2\to c_3$. The varying-ring vertical-pasting statement gives the typed equation
$$c_{v,u,j_{1!}}\gamma_{vu}=R_v(\gamma_u)\gamma_v:j_{3!}\longrightarrow R_vR_uj_{1!}.$$
The ambient system compositors are associative, so the two maps from $R_{p_1}$ to $R_{p_3}R_vR_u$ satisfy
$$R_{p_3}(c_{v,u})c_{p_3,vu}=(c_{p_3,v}R_u)c_{p_2,u},\qquad p_2=p_3v.$$
Inverting the first equation and using the second rewrites the definition of $\theta_{vu}$ as
$$R_{p_3}(\gamma_v^{-1})\,R_{p_3}R_v(\gamma_u^{-1})\,c_{p_3,v,R_uj_{1!}}\,c_{p_2,u,j_{1!}}.$$
Here the third factor means $c_{p_3,v,R_uj_{1!}}:R_{p_2}R_uj_{1!}\to R_{p_3}R_vR_uj_{1!}$. Naturality of $c_{p_3,v}$ moves $\gamma_u^{-1}:R_uj_{1!}\to j_{2!}$ across that factor, giving precisely $\theta_v\theta_u$. Identity squares and unital compositors give $\gamma_1=1$ and $\theta_1=1$. Inverses are used on systems with bounded constructible levels, as justified in Step 3.

Uses: lem-sp-varying-ring-proper-open-pasting, lem-sf-ambient-proper-open-pasting, def-weil-compactifications-refinements

Source: {"document": "literature/stacks-project/more-etale.tex", "place": "Tags 0F7C (lemma-shriek-proper-and-open-compose) and 0F7J (lemma-shriek-composition); agent typed system compositor calculation"}

### Original step 8 -> lem-pur-refinement-inverse-mate-comparisons

The compactification category is nonempty since $c_1$ is supplied. By compactifiable cofilteredness, for parallel refinements $a,b:d\to c$ there is a refinement $e:d'\to d$ with $ae=be$. Step 7 gives
$$\theta_a\theta_e=\theta_{ae}=\theta_{be}=\theta_b\theta_e.$$
Since $\theta_e$ is invertible on the same domain, cancellation gives $\theta_a=\theta_b$. This proves independence of the arrow, which does not follow merely from the existence of common refinement objects. The argument is an equality of strict-system natural transformations.

Uses: lem-cbc-compactifiable-cofiltered

Source: {"document": "literature/stacks-project/flat.tex", "place": "Tag 0ATU (lemma-compactifications-cofiltered), proof (a), condition (3), equalizer of two parallel compactification maps; explicit cancellation after Step 7"}

### Original step 9 -> lem-pur-refinement-inverse-mate-comparisons

For a common refinement $a:d\to c_1$, $b:d\to c_2$, define $C_{12}=\theta_b\theta_a^{-1}$. Another span $a':d'\to c_1$, $b':d'\to c_2$ has a common refinement $h:e\to d$, $h':e\to d'$. By Step 8, $\theta_{ah}=\theta_{a'h'}$ and $\theta_{bh}=\theta_{b'h'}$. By Step 7,
$$\theta_b\theta_a^{-1}=\theta_{bh}\theta_{ah}^{-1}
=\theta_{b'h'}\theta_{a'h'}^{-1}=\theta_{b'}\theta_{a'}^{-1}.$$
Thus the comparison is independent both of the common object and of its chosen arrows. For three compactifications choose one common refinement, obtained by applying pairwise cofilteredness twice, with arrows $a_i$. Then
$$C_{23}C_{12}=(\theta_{a_3}\theta_{a_2}^{-1})(\theta_{a_2}\theta_{a_1}^{-1})
=\theta_{a_3}\theta_{a_1}^{-1}=C_{13}.$$
The identity, composition, independence and cocycle equations therefore hold before evaluation; their finite normalization was established in Step 3.

Uses: lem-cbc-compactifiable-cofiltered

Source: {"document": "literature/stacks-project/more-etale.tex", "place": "Tag 0F7J (lemma-shriek-composition), independence-of-choices paragraphs invoking flat.tex Tag 0ATU (lemma-compactifications-cofiltered); explicit span comparison and cancellation"}


## Not duplicates

lem-pur-system-refinement-constructible-domain vs lem-pur-system-compactification-pf-substitution: the parent proves the PF/refinement equation and coherence; this node proves its constructible-domain and finite-normalization prerequisites without any PF assertion.

lem-pur-system-refinement-constructible-domain vs lem-weil-pbc-etale-open-proper-interchange: bounded-below constant finite-ring etale Cartesian interchange, versus varying-ring systems, non-Cartesian refinements, normalized tensor closure and finite evaluation normalization.

lem-pur-system-refinement-constructible-domain vs lem-sfb-exact-compactification-unit-composition: exact finite-ring etale functor units for a composition, versus constructible-domain inversion of semilinear refinement mates.

lem-pur-system-refinement-constructible-domain vs lem-sfb-exact-compactification-unit-refinement: an exact sheaf functor with two section-normalized factorizations, versus arbitrary derived semilinear inputs with levelwise constructibility and finite-origin witnesses.

lem-pur-system-refinement-constructible-domain vs lem-sfb-proper-open-tower-derived-unit: K-injective chain representatives of a finite-ring etale tower compositor, versus inversion and normalization of varying-ring refinement mates.

lem-pur-system-refinement-constructible-domain vs lem-sfb-proper-open-tower-single-unit-formula: single total-derived-unit expression at chosen complexes, versus constructible domain and evaluated refinement isomorphisms.

lem-pur-system-refinement-constructible-domain vs lem-sfb-proper-open-tower-successive-unit-formula: successive total-derived-unit expression under a representative hypothesis, versus bounded-constructible semilinear refinement invertibility.

lem-pur-system-refinement-constructible-domain vs def-coef-semilinear-proper-open-mate: defines the actual mate and explicitly asserts no invertibility; this node proves invertibility on a specified domain and normalizes its inverse.

lem-pur-system-refinement-constructible-domain vs def-sf-etale-support-compositor: defines the finite-ring etale composition map and asserts no coherence; this node concerns constructible varying-ring refinement inverses.

lem-pur-system-refinement-constructible-domain vs def-sf-semilinear-proper-open-comparisons: defines the section-normalized comparison data for arbitrary inputs; it does not prove constructible invertibility or normalized finite-Tor domain closure.

lem-pur-system-refinement-constructible-domain vs lem-sf-ambient-clopen-restriction-uniqueness: abelian clopen restriction equivalence and uniqueness, versus derived varying-ring mate inversion on levelwise constructible inputs.

lem-pur-system-refinement-constructible-domain vs lem-sf-ambient-exact-clopen-comparison-localization: identifies exact localization with the specified derived mate and explicitly excludes invertibility; this node gives constructible inversion and finite normalization.

lem-pur-system-refinement-constructible-domain vs lem-sf-clopen-comparison-tensor-square: a clopen inverse-image tensor square, versus constructible inverse mates and normalized finite-Tor domain.

lem-pur-system-refinement-constructible-domain vs lem-sf-projection-refinement-descent: states the PF equality, with a local system identity; does not supply arbitrary levelwise constructible system mate invertibility and witness-independent finite normalization.

lem-pur-system-refinement-constructible-domain vs lem-sf-unbounded-compact-support-proper-composition: proper-factor compact-support composition, versus constructible inversion of refinement mates with varying coefficients.

lem-pur-system-refinement-constructible-domain vs lem-sf-ambient-proper-open-pasting: unbounded ambient compositor and pasting identities explicitly assert no invertibility; this node supplies constructible inversion with finite normalization.

lem-pur-system-refinement-constructible-domain vs lem-sf-native-weil-open-proper-interchange: native proper/open interchange comparison, versus varying-ring normalized finite-Tor domain and finite-witness normalization.

lem-pur-system-refinement-constructible-domain vs lem-sf-semilinear-proper-open-mate-pasting: intrinsic semilinear mate pasting and finite evaluated normalization, versus actual system invertibility and normalized finite-Tor domain closure.

lem-pur-system-refinement-constructible-domain vs lem-sf-composition-projection-mate: composition of compact-support projection maps, versus constructible inverse refinement mates and their finite evaluation.

lem-pur-system-refinement-constructible-domain vs lem-sf-proper-open-projection-mate: tensor compatibility of a proper/open mate, without inversion; this node proves inverse-domain and finite-normalization assertions.

lem-pur-system-refinement-constructible-domain vs lem-sp-compactification-refinement-coherence: formal coherence assumes invertible comparison data; this node supplies the actual pointwise constructible inverses.

lem-pur-system-refinement-constructible-domain vs lem-cbc-strict-tower-proper-open-calculus: fixed coefficient B at every auxiliary tower index, versus changing rings A_n; applying it requires a separate constant-A_n tower at each n and semilinear conservativity.

lem-pur-system-refinement-constructible-domain vs lem-pur-system-normalized-tensor-closure: general transition-adjoint tensor/pullback normalization, versus bounded finite-Tor constructible closure together with geometric mate inversion and finite witness normalization.

lem-pur-refinement-inverse-mate-comparisons vs lem-pur-system-compactification-pf-substitution: the parent is a geometric PF assertion with a coherence clause; this node is the abstract inverse-compositor and cofiltered-span argument with no tensor or PF.

lem-pur-refinement-inverse-mate-comparisons vs lem-cbc-compactifiable-cofiltered: geometric existence of common refinements and equalizers, versus natural isomorphism equations for supplied categorical data assuming cofilteredness.

lem-pur-refinement-inverse-mate-comparisons vs lem-sf-ambient-proper-open-pasting: constructs ambient compositors and mate pasting, explicitly without invertibility; this node derives inverse refinement comparisons and cancellation on a pointwise domain.

lem-pur-refinement-inverse-mate-comparisons vs lem-sf-semilinear-proper-open-mate-pasting: actual semilinear mate identities, versus a coefficient-independent inverse-compositor/cancellation theorem assuming those identities only for refinement squares.

lem-pur-refinement-inverse-mate-comparisons vs lem-sf-composition-projection-mate: compact-support projection composition and tensor, versus refinement inverse natural transformations and common-span cancellation without tensor.

lem-pur-refinement-inverse-mate-comparisons vs lem-sf-proper-open-projection-mate: proper/open tensor compatibility, versus inverse-compositor coherence and parallel-arrow cancellation.

lem-pur-refinement-inverse-mate-comparisons vs lem-sf-ambient-underived-clopen-pasting: abelian clopen map pasting before deriving, versus inverse mates and canonical common-refinement isomorphisms on a full source subcategory.

lem-pur-refinement-inverse-mate-comparisons vs def-cbc-finite-constant-coefficient-transport: defines finite-origin scalar transport, versus formal inverse/compositor and cofiltered cancellation identities.

lem-pur-refinement-inverse-mate-comparisons vs def-cbc-strict-constant-tower-operations: defines fixed-ring derived operations and comparators, versus coherence of inverse mates in arbitrary categories.

lem-pur-refinement-inverse-mate-comparisons vs def-cbc-strict-tower-composition-maps: defines actual constant-tower refinement and staircase transformations and asserts no choice independence, versus abstract refinement inverse independence and cocycle.

lem-pur-refinement-inverse-mate-comparisons vs def-cbc-strict-tower-open-extension: defines exact open extension and its adjunction, versus inverse refinement coherence in arbitrary categories.

lem-pur-refinement-inverse-mate-comparisons vs def-cbc-strict-tower-proper-open-arrows: defines fixed-ring open and proper mates, versus identities and span independence of their pointwise inverses.

lem-pur-refinement-inverse-mate-comparisons vs lem-cbc-normalized-proper-open-pasting: finite-ring derived horizontal pasting under sheaf normalization hypotheses, versus inverse refinement functoriality and cofiltered-span independence.

lem-pur-refinement-inverse-mate-comparisons vs lem-cbc-complete-proetale-composition-pasting-coherence: constant-B binary tower composition and base-change interchange, versus no towers and arbitrary category-valued refinement data with pointwise inverses.

lem-pur-refinement-inverse-mate-comparisons vs lem-sp-ordinary-vertical-pasting-transport: transports a supplied cell equality through comparison functors, versus proving inverse-compositor coherence and equalizing parallel arrows.

lem-pur-refinement-inverse-mate-comparisons vs lem-amb-unbounded-proper-open-interchange: constructs finite constant-ring etale proper/open isomorphisms and pasting, versus abstract pointwise inverse refinement comparisons and span cancellation.

lem-pur-refinement-inverse-mate-comparisons vs lem-sp-compactification-refinement-coherence: requires every proper/open comparison to be a natural isomorphism on the whole supplied categories and compatible binary/triple staircases; the new lemma assumes only refinement mates invertible after restriction to one source subcategory, and requires no tower data.

## Search results checked

For the domain node the semantic searches returned sheaf finite presentations, condensed-module constructors, affine-limit sections and semilinear linear equivalences, none of which asserts constructible inversion of this derived geometric mate. Loogle returned sheafification, pullback-of-unit and presentation isomorphisms. For inverse-mate coherence the semantic searches returned profinite locally constant functions, cofilteredness definitions and pseudofunctor compositor components; Loogle returned eventually constant limit-cone isomorphisms, which require a cone and do not give this pointwise-mate construction. The grep searches returned no semilinear geometric mate matches, and only generic cofiltered-limit references for the comparison node. The separate projection search returned Adjunction.comp_counit, whose component formula I read at Mathlib/CategoryTheory/Adjunction/Basic.lean:580; it is a generic ingredient and not either new statement. All recorded queries are actual msearch.py entries, including a second semantic phrasing for both new nodes. Existing item searches were retained unchanged.
