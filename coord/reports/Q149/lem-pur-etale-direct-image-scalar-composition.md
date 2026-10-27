# Q149 repair report

## Files written

- lem-pur-etale-direct-image-scalar-composition: existing statement unchanged; three-step assembly, 1475 characters.
- lem-pur-scalar-composite-mate-adjunct: new statement, unsplit; no exact Mathlib match.
- lem-pur-scalar-iterated-mates-adjunct: new statement, unsplit; no exact Mathlib match.
- lem-pur-etale-scalar-pullback-identity-normalization: new statement, unsplit; no exact Mathlib match.
- citations.json: a verbatim statement quotation for every citation in every parent step.

## Attachments

None. The two declarations in lean/Sheaf/Paper/EtaleDirectImageScalarComposition.lean have sorry bodies (lines 84 and 109). The project-source keyword/tag searches give no finished declaration covering this item. No Lean was written or compiled.

## WANTED

None: the Stacks source and current blueprint are present.

## What was wrong and repair of every returned point

The returned seven-step argument is 5286 characters. The initial required dry run found that the supplied sandbox actually had no node files or report (only dispatcher brief markers), so I copied the current repository item, which contains precisely that returned proof. There was no earlier local search log to discard; its recorded 2026-10-21 Mathlib searches remain intact in the parent. This is a substantive re-split, not an unchanged re-push. The parent statement, hypotheses, source, blueprint ancestry, import fields and existing Lean records are retained.

The first two new nodes are independently assignable computations, not the composition or identity clauses of the parent. One compares the outer mate to an explicit counit expression through the actual K-injective compositor and scalar/pullback cocycle. The other compares the successive mates to that expression using two counit identities and naturality. Neither asserts F=G or the identity clause. They have comparable proof obligations, carrying old steps 1/2/4 (with the mate characterization) and old steps 3/5/6 respectively. These two and the identity normalization lemma are delivered statement-only: proof=[], proof_deps=[], proof_origin=null, status=unsplit. The geometric/scalar identity normalization is also extracted, into lem-pur-etale-scalar-pullback-identity-normalization; the parent keeps only its identity-transpose assembly. Its total proof is below 3000 characters; no individual step exceeds 2000. All seven old arguments are reproduced below with their destinations.

## Unfinished work

The three new lemmas intentionally remain unsplit for parallel future workers. The parent assembly is complete relative to their exact statements. The corrected quotation dry run passed server preflight at b5b37cc7c7b. The final dry run below also includes an explicit introduction of the identity-step pullback compositor; no proof argument changed.

## Review by Q149

I read Stacks sites-cohomology.tex at remark-compose-base-change (Tag 0E46) for the item and all three new nodes. It asserts pasting of the actual maps but explicitly omits the verification. I also read lemma-derived-pullback-composition (0D6D), lemma-adjoint (07A6), and lemma-derived-pushforward-composition (0D6E): these use unbounded derived categories and adjoint uniqueness. This is why the parent retains proof_origin=agent rather than attributing its explicit calculation to a printed Stacks proof. The current blueprint cor-pur-vector-bundle-purity.proof.md, second paragraph, requires coefficient reduction to commute with composition before transposing; the repair serves precisely that route, with no SGA reference.

For parent step 1 I read the first new statement: F is defined with the same Q(kappa_A inverse), the same kappa_B and chi_sr as here, and the conclusion gives exactly Adj_B(F)=T. For step 2 I read the second statement: G has precisely R_sB(chi_r) after chi_s and the same U, V and T. I checked the domain of both adjuncts is P_rB P_sB Q_Z V and their target Q_X M. The quoted def-kun-projection-formula-map supplies the actual unbounded Hom bijections, not an invertibility theorem; lem-sfb-ringed-derived-monoidal-comparisons explicitly identifies their composite counit, with the same K-injective kappa. Equality of adjuncts therefore implies equality of arrows, and only Q(kappa_A) is cancelled.

For final parent step 3 I read the new identity-normalization statement: its explicit equation Q(i_A) after lambda_id = i_B is exactly lambda_id=1 under the two canonical comparisons. lem-sfb-ringed-derived-monoidal-comparisons explicitly identifies the geometric identity adjunction, including its counit; def-pur-etale-scalar-mate then gives the claimed identity transpose. The work formerly inline is now the independently assignable identity-normalization node: it must compute the actual identity-identity compositor on flat-term K-flat representatives (lem-sfb-ringed-derived-monoidal-comparisons and lem-pc-kflat-resolution), specialize the scalar cocycle of lem-sf-scalar-pullback-composition, and cancel the invertible scalarPullbackIso of def-pur-etale-scalar-pullback-iso. Its conclusion is an equality of pullback/scalar comparisons, not the parent's identity assertion about chi. This is the canonical-representative normalization argument, rather than a new lemma for the final one-line identity transpose. The full former argument is retained below.

For the arguments assigned to the new nodes I opened prop-weil-pbc-inverse-image-modules-exact: its clauses (2)/(3) identify exact constant-ring inverse image with module pullback and its adjunction. I read the full adjunction-compatible clause of lem-sfb-ringed-derived-monoidal-comparisons, the exact scalar cocycle of lem-sf-scalar-pullback-composition, the representative normalization in def-pur-etale-scalar-pullback-iso, the transpose in def-pur-etale-scalar-mate, and the iff/counit formula of lem-weil-pbc-adjunct-counit-identity. These support the old arguments retained below without using proofs of dependency nodes. The new statements define their own objects and composite adjunct, cite its definition, and place all equalities in the ordinary derived categories; they make no per-degree substitute for a derived equality.

Hypotheses and small cases: schemes and their maps are arbitrary; all sites use the small representatives already required by the canonical functors. No properness, Noetherian condition, boundedness, coefficient flatness, or invertibility of chi is used. The zero object, empty scheme and zero coefficient ring give zero morphisms with the same formulas. For r or s identity the formulas reduce to the corresponding one-counit formula, and for both identity to the identity calculation. For the nonflat coefficient map Z/4 -> Z/2 all scalar operations remain derived; the proof never replaces them by ordinary tensor or assumes restriction preserves K-injectives. Typed each factor of T: P_rB P_sB Q_Z V -> P_rB Q_Y P_sA V -> Q_X P_rA P_sA V -> Q_X P_rA U -> Q_X M. The two new obligations are substantial independent normal-form computations, while the final equality and cancellation remain elementary assembly.

I checked delivery-errors B--E: both new nodes are self-contained statement-only records with real source tags, ancestor/via fields and logged searches; no elementary lemma was added merely to pad the split; no existing generic mate theorem or nearby coefficient comparison was recreated as if it were new; no item clause was renamed. citations.json quotations were asserted to be verbatim substrings of the cited statements. No source or statement dispute was found. The only correction is the requested distribution of the existing argument plus the now-direct citation of the scalar mate definition in the identity step.

## Searches and comparison with existing work

Before creating nodes I searched the whole DAG by tag 0E46, by scalar/adjunct/counit terminology, the whole blueprint with tools/blueprint_refs.py (ancestor and searches scalar, adjunct, counit, scalar mate, transported adjunct, iterated scalar), and the live WeilConjectures source by notion and blueprint tag. The only blueprint hit for 'scalar mate' is lem-finite-compact-support-scalar-transport, which concerns bounded-below intrinsic compact-support realization with Noetherian proper compactification, rather than either unbounded normal-form calculation here. The old parent Lean declarations are sorry statements, not attachments.

For each new node I ran leanfinder, leansearch, loogle and Mathlib grep through the mandated msearch.py command and read the hits. Two distinct natural-language phrasings address each calculation; exact query texts and returned metadata are retained in both nodes and searches.jsonl. Mathlib Adjunction/Basic.lean:580 gives the composite counit formula and Adjunction/Mates.lean:209 gives mateEquiv_hcomp. I read both. They do not identify the canonical geometric K-injective compositor with the composite adjunction or prove the K-flat scalar comparison cocycle. For the iterated calculation, mateEquiv_hcomp gives another mate, and its adjunct still requires the counit characterization and expansion of the pasted left square; it is not the asserted explicit specialized normal form in one line. Thus neither new node is a Mathlib leaf. The existing generic mate-pasting node remains available and is not duplicated.

## Retained argument and assignment of work

### Old step 1: lem-pur-scalar-composite-mate-adjunct

Put $P_{u,R}=u_R^*$ and $R_{u,R}=Ru_{*,R}$. The exact constant-ring inverse image is the module pullback, so the canonical ringed-topos comparisons apply to these functors. Write $a_R:P_{sr,R}\xrightarrow{\sim}P_{r,R}P_{s,R}$. The adjunction-compatibility assertion of [lem-sfb-ringed-derived-monoidal-comparisons], with constant ring $R=A$ or $B$, identifies the specified K-injective-normalized $\kappa_R$ with the right-adjoint comparison for $a_R$. Thus, when $P_{sr,R}$ and $R_{sr,R}$ are written as $P_{r,R}P_{s,R}$ and $R_{s,R}R_{r,R}$ using these comparisons, the counit is exactly
$$\varepsilon_{r,R,M}\circ P_{r,R}(\varepsilon_{s,R,R_{r,R}M}).$$
This uses the actual canonical adjunction of the item. The cited theorem also identifies the identity pullback/direct-image adjunction with the identity adjunction. All sites are taken in the small representatives used by the derived categories; there is no assumption on the schemes or on the complexes beyond those in the item.

Original citations: prop-weil-pbc-inverse-image-modules-exact, lem-sfb-ringed-derived-monoidal-comparisons.

### Old step 2: lem-pur-scalar-composite-mate-adjunct

Apply [lem-sf-scalar-pullback-composition] to $j_1=r$, $v=s$, $j_2=sr$. Its scalarPullbackIso is exactly the K-flat-normalized $\lambda$ specified in [def-pur-etale-scalar-pullback-iso]. For every $N\in D_A(Z)$ the result is
$$\lambda_{r,P_{s,A}N}\circ P_{r,B}(\lambda_{s,N})\circ a_{B,Q_ZN}
 =Q_X(a_{A,N})\circ\lambda_{sr,N}.$$
In particular, after the comparisons in Step 1, the scalar map for the composite is the pasted left square $\lambda_{r,P_{s,A}N}\circ P_{r,B}(\lambda_{s,N})$. The cited result explicitly allows arbitrary commutative rings, morphisms and unbounded complexes, so it applies also when $B$ is not flat over $A$.

Original citations: lem-sf-scalar-pullback-composition, def-pur-etale-scalar-pullback-iso.

### Old step 3: both new nodes (the defining transpose; explicitly expanded for lem-pur-scalar-iterated-mates-adjunct)

By the adjunction Hom bijection of [def-kun-projection-formula-map] and the counit characterization [lem-weil-pbc-adjunct-counit-identity], the definition of $\chi$ gives, for $u=r,s,sr$ and every $E$,
$$\varepsilon_{u,B,Q_WE}\circ P_{u,B}(\chi_{u,E})
 =Q_W(\varepsilon_{u,A,E})\circ\lambda_{u,R_{u,A}E},$$
where $u:W\to T$. Adjuncts are unique because this is a Hom bijection. Only this equality will be used about $\chi$; no invertibility of $\chi$ is required.

Original citations: def-kun-projection-formula-map, lem-weil-pbc-adjunct-counit-identity.

### Old step 4: lem-pur-scalar-composite-mate-adjunct

Fix $M\in D_A(X)$, put $U=R_{r,A}M$ and $V=R_{s,A}U$, and transport the source of the desired equation along $Q_Z(\kappa_{A,M})$. The two arrows now have source $Q_ZV$ and target $R_{s,B}R_{r,B}Q_XM$. They are
$$F=\kappa_{B,Q_XM}\circ\chi_{sr,M}\circ Q_Z(\kappa_{A,M})^{-1},\qquad
G=R_{s,B}(\chi_{r,M})\circ\chi_{s,U}.$$
Under the composite adjunction of Step 1, the adjunct of $F$, by the defining equation of Step 3 and the scalar equation of Step 2, is
$$T=Q_X(\varepsilon_{r,A,M})\circ Q_X(P_{r,A}(\varepsilon_{s,A,U}))\circ
\lambda_{r,P_{s,A}V}\circ P_{r,B}(\lambda_{s,V}).$$
Naturality of $\lambda_{sr}$ at $\kappa_{A,M}^{-1}$ moves the source inverse through the scalar comparison; the counit normalization in Step 1 then replaces the composite counit by its two factors. Here the source is $P_{r,B}P_{s,B}Q_ZV$ and the target is $Q_XM$. The inverse in $F$ is legitimate because $Q_Z$ is a functor and $\kappa_A$ is an isomorphism.

Original citations: .

### Old step 5: lem-pur-scalar-iterated-mates-adjunct

Expand the adjunct of $G$ using the same composite counit. It is
$$\varepsilon_{r,B,Q_XM}\circ P_{r,B}(\varepsilon_{s,B,R_{r,B}Q_XM})\circ P_{r,B}P_{s,B}\bigl(R_{s,B}(\chi_{r,M})\circ\chi_{s,U}\bigr).$$
Naturality of $\varepsilon_{s,B}$ at the arrow $\chi_{r,M}:Q_YU\to R_{r,B}Q_XM$ reads
$$\varepsilon_{s,B,R_{r,B}Q_XM}\circ P_{s,B}R_{s,B}(\chi_{r,M})
=\chi_{r,M}\circ\varepsilon_{s,B,Q_YU}.$$
Substitution, followed by functoriality of $P_{r,B}$, rewrites the expanded adjunct as
$$\varepsilon_{r,B,Q_XM}\circ P_{r,B}(\chi_{r,M})\circ
P_{r,B}\bigl(\varepsilon_{s,B,Q_YU}\circ P_{s,B}(\chi_{s,U})\bigr).$$

Original citations: .

### Old step 6: lem-pur-scalar-iterated-mates-adjunct (final injectivity/cancellation retained in parent step 2)

Use the Step-3 equations first for $s,U$ and then for $r,M$. The last expression becomes
$$Q_X(\varepsilon_{r,A,M})\circ\lambda_{r,U}\circ
P_{r,B}\bigl(Q_Y(\varepsilon_{s,A,U})\circ\lambda_{s,V}\bigr).$$
Naturality of $\lambda_r$ at $\varepsilon_{s,A,U}:P_{s,A}V\to U$ says
$$\lambda_{r,U}\circ P_{r,B}Q_Y(\varepsilon_{s,A,U})
=Q_XP_{r,A}(\varepsilon_{s,A,U})\circ\lambda_{r,P_{s,A}V}.$$
After this substitution and functoriality, the expression is exactly $T$ from Step 4. Consequently the adjuncts of $F$ and $G$ coincide. Injectivity of the composite Hom bijection gives $F=G$, and precomposing with $Q_Z(\kappa_{A,M})$ gives precisely the displayed equation of the item.

Original citations: .

### Old step 7: lem-pur-etale-scalar-pullback-identity-normalization (geometric/scalar normalization); parent step 3 (last identity transpose)

For the identity clause, use the identity comparisons of Step 1. The comparison $a_R$ when $r=s=\mathrm{id}$ is the identity: the cited canonical composition comparison is computed by ordinary pullback composition on K-flat representatives, where the two identity pullbacks insert no scalar and give the identity chain map. Every derived object admits such a representative by [lem-pc-kflat-resolution], so the equality holds at every object. Applying Step 2 with both maps the identity therefore gives $\lambda_{\mathrm{id}}\circ\lambda_{\mathrm{id}}=\lambda_{\mathrm{id}}$. Since $\lambda_{\mathrm{id}}$ is an isomorphism by [def-pur-etale-scalar-pullback-iso], cancellation yields $\lambda_{\mathrm{id}}=1$. The identity adjunction has identity counit by [lem-sfb-ringed-derived-monoidal-comparisons]; the Step-3 characterization now reads $\chi_{\mathrm{id},E}=Q_T(1_E)\circ1=1_{Q_TE}$. This proves the identity assertion without deducing any invertibility for nonidentity $\chi$.

Original citations: lem-sfb-ringed-derived-monoidal-comparisons, lem-sf-scalar-pullback-composition, def-pur-etale-scalar-pullback-iso, lem-pc-kflat-resolution.

## Not duplicates

lem-pur-scalar-composite-mate-adjunct vs lem-weil-pbc-derived-square-iso-pasting: the existing node concerns bounded-below abelian square isomorphisms, not unbounded module scalar adjuncts.

lem-pur-scalar-composite-mate-adjunct vs lem-weil-pbc-mate-pasting: the existing node is generic mate pasting; neither specialized equation with the canonical geometric derived comparisons and explicit counit normal form is its statement.

lem-pur-scalar-composite-mate-adjunct vs lem-weil-pbc-ordinary-ringed-exchange-coherence: the existing node concerns completed adic coefficient exchange in Cartesian squares, not finite constant-ring scalar mates or these explicit adjunct formulas.

lem-pur-scalar-composite-mate-adjunct vs lem-weil-pbc-square-iso-pasting: the existing node concerns abelian inverse-image square isomorphisms at a fixed coefficient, not the derived scalar/direct-image adjunct.

lem-pur-scalar-composite-mate-adjunct vs sk-thm-geo-generic-open: the existing node concerns generic-open constructibility and pro-etale base change, not an unbounded small-etale scalar adjunct.

lem-pur-scalar-composite-mate-adjunct vs lem-pur-etale-direct-image-scalar-composition: the parent asserts equality of the two direct-image maps and the identity clause; the new node computes only one map's adjunct against an explicit four-factor normal form and does not assert either parent clause.

lem-pur-scalar-composite-mate-adjunct vs lem-pur-etale-open-scalar-composition: the existing node concerns open extension by zero and its unit, not ordinary right derived direct image and the two counit calculations.

lem-pur-scalar-composite-mate-adjunct vs def-trf-oriented-hypercover-descent-datum: the existing node defines oriented nearby-cycle descent data; it proves neither scalar adjunct equation.

lem-pur-scalar-composite-mate-adjunct vs lem-trf-total-site-augmentation-spectral-sequence: the existing node concerns total-site spectral sequences and component restriction, not finite coefficient mates for two arbitrary scheme maps.

lem-pur-scalar-iterated-mates-adjunct vs lem-weil-pbc-derived-square-iso-pasting: the existing node concerns bounded-below abelian square isomorphisms, not unbounded module scalar adjuncts.

lem-pur-scalar-iterated-mates-adjunct vs lem-weil-pbc-mate-pasting: the existing node is generic mate pasting; neither specialized equation with the canonical geometric derived comparisons and explicit counit normal form is its statement.

lem-pur-scalar-iterated-mates-adjunct vs lem-weil-pbc-ordinary-ringed-exchange-coherence: the existing node concerns completed adic coefficient exchange in Cartesian squares, not finite constant-ring scalar mates or these explicit adjunct formulas.

lem-pur-scalar-iterated-mates-adjunct vs lem-weil-pbc-square-iso-pasting: the existing node concerns abelian inverse-image square isomorphisms at a fixed coefficient, not the derived scalar/direct-image adjunct.

lem-pur-scalar-iterated-mates-adjunct vs sk-thm-geo-generic-open: the existing node concerns generic-open constructibility and pro-etale base change, not an unbounded small-etale scalar adjunct.

lem-pur-scalar-iterated-mates-adjunct vs lem-pur-etale-direct-image-scalar-composition: the parent asserts equality of the two direct-image maps and the identity clause; the new node computes only one map's adjunct against an explicit four-factor normal form and does not assert either parent clause.

lem-pur-scalar-iterated-mates-adjunct vs lem-pur-etale-open-scalar-composition: the existing node concerns open extension by zero and its unit, not ordinary right derived direct image and the two counit calculations.

lem-pur-scalar-iterated-mates-adjunct vs def-trf-oriented-hypercover-descent-datum: the existing node defines oriented nearby-cycle descent data; it proves neither scalar adjunct equation.

lem-pur-scalar-iterated-mates-adjunct vs lem-trf-total-site-augmentation-spectral-sequence: the existing node concerns total-site spectral sequences and component restriction, not finite coefficient mates for two arbitrary scheme maps.

lem-pur-scalar-composite-mate-adjunct vs lem-pur-scalar-iterated-mates-adjunct: the former computes Adj_B of the transported outer mate using both canonical compositors; the latter computes Adj_B of two successive mates using counit naturality. They have different left sides and neither proves their equality alone.

lem-pur-etale-scalar-pullback-identity-normalization vs lem-weil-pbc-derived-square-iso-pasting: the existing node concerns bounded-below abelian square isomorphisms, not unbounded module scalar adjuncts.

lem-pur-etale-scalar-pullback-identity-normalization vs lem-weil-pbc-mate-pasting: the existing node is generic mate pasting; neither specialized equation with the canonical geometric derived comparisons and explicit counit normal form is its statement.

lem-pur-etale-scalar-pullback-identity-normalization vs lem-weil-pbc-ordinary-ringed-exchange-coherence: the existing node concerns completed adic coefficient exchange in Cartesian squares, not finite constant-ring scalar mates or these explicit adjunct formulas.

lem-pur-etale-scalar-pullback-identity-normalization vs lem-weil-pbc-square-iso-pasting: the existing node concerns abelian inverse-image square isomorphisms at a fixed coefficient, not the derived scalar/direct-image adjunct.

lem-pur-etale-scalar-pullback-identity-normalization vs sk-thm-geo-generic-open: the existing node concerns generic-open constructibility and pro-etale base change, not an unbounded small-etale scalar adjunct.

lem-pur-etale-scalar-pullback-identity-normalization vs lem-pur-etale-direct-image-scalar-composition: the parent asserts equality of the two direct-image maps and the identity clause; the new node normalizes the identity geometric compositor and lambda_id, not the scalar direct-image mate chi_id.

lem-pur-etale-scalar-pullback-identity-normalization vs lem-pur-etale-open-scalar-composition: the existing node concerns open extension by zero and its unit, not ordinary right derived direct image and the two counit calculations.

lem-pur-etale-scalar-pullback-identity-normalization vs def-trf-oriented-hypercover-descent-datum: the existing node defines oriented nearby-cycle descent data; it proves neither scalar adjunct equation.

lem-pur-etale-scalar-pullback-identity-normalization vs lem-trf-total-site-augmentation-spectral-sequence: the existing node concerns total-site spectral sequences and component restriction, not finite coefficient mates for two arbitrary scheme maps.

lem-pur-etale-scalar-pullback-identity-normalization vs lem-pur-scalar-composite-mate-adjunct: geometric/scalar identity comparisons, rather than the adjunct of the composite mate for two arbitrary maps.

lem-pur-etale-scalar-pullback-identity-normalization vs lem-pur-scalar-iterated-mates-adjunct: geometric/scalar identity comparisons, rather than the adjunct of two successive direct-image mates.

## Validation

The initial empty-sandbox dry run failed before creating a delivery. After writing the repair, the citation gate required longer quotations for the two new equations and the scalar isomorphism; those quotations now include the complete formulas. The next dry run exited 0 with OK (not pushed) at b5b37cc7c7b. Final self-review introduced a_R explicitly in the shortened identity step and extended its statement quotation to cover the K-flat compositor normalization as well as the identity adjunction. The final dry run and push use these files. No local DAG checker, preflight script, Lean compiler or build tool was run.

## Final extraction of the identity normalization

The dry run at 9c365c458d8 also passed. Before pushing, I applied the return literally to every substantive old argument: the identity-identity pullback compositor and scalar identity comparison now have a third statement-only node. The parent retains only the last identity-adjunction transpose. The third node states the normalized geometric identity compositor and lambda identity equations, not chi_id=1. The two main adjunct computations remain of comparable size and independently assignable. All original step-7 arguments now have the new identity node as their destination, apart from that final one-line assembly.

For this third node, blueprint searches 'scalar pullback identity' and 'scalarPullbackIso' gave no blueprint match. DAG and Lean searches found the original item and nearby pro-etale/integral or coefficient-identity statements, not this geometric-identity normalization. I opened lem-pur-inverse-image-scalar-unit-normalization, lem-pur-etale-scalar-pullback-uniqueness, lem-pur-inverse-image-scalar-comparison, lem-sp-constant-pullback-scalar, lem-pur-scalar-tensor-unit, lem-pod-pullback-identities-scalar-extension, lem-sfb-derived-scalar-mate-composition and lem-sp-open-scalar-coefficient-coherence. Their comparisons, coefficients or sites differ: in particular identity coefficient maps are not identity geometric morphisms. The pro-etale derived-scalar-mate composition theorem does not supply this fixed small-etale K-flat identity lambda. The new statement is meaningful on zero objects, the zero coefficient ring, the empty scheme and nonflat Z/4 -> Z/2, and its equations have precisely the same source P_R E or P_B Q N on both sides. I read the Mathlib hits Scheme.Modules.pullbackId at Modules/Sheaf.lean:219 (ordinary structure-sheaf modules) and Functor.leftDerivedNatTrans_id at Functor/Derived/LeftDerived.lean:115 (deriving an already identified identity transformation); neither identifies this specified scalar comparison. msearch.py recorded leanfinder, leansearch, grep and Loogle calls, including the failed NatIso query and its successful leftUnitor replacement, without hiding the invalid query.












