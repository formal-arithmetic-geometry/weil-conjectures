# Repair report: lem-fd-local-weil-model-trace-independence

## Files written

- Item: dag/nodes/sec-fourier-transform/lem-fd-local-weil-model-trace-independence.json; statement unchanged, four-step assembly.
- lem-fd-local-frobenius-weil-morphism-naturality: statement, unsplit, no Mathlib match.
- lem-fd-local-frobenius-coefficient-extension: statement, unsplit, no Mathlib match.
- citations.json contains a literal statement excerpt for each assembly-step citation.

## Attachments

None. The live Sheaf.Paper.LocalWeilModelTraceIndependence theorem at line 151 ends with sorry (line 185). The project-source search under lean/WeilConjectures by the blueprint id and local Frobenius concept found no finished declaration stating the item or either new comparison lemma. Existing helpers in the Sheaf module construct b and the comparison isomorphisms; they do not prove their operator identities.

## WANTED

None. These are agent-extracted comparison arguments from the existing proof; neither the blueprint nor Stacks is claimed to state them verbatim.

## Return repaired

The human requested at least two comparable, separately provable statement-only tasks and an assembly of at most 3000 characters. The sandbox initially held only dispatcher .brief files, with no node, report or searches.jsonl to retain. I read the current live node (including its reviewed previous proof and Lean signature) as the repair baseline. I preserved its statement exactly, its provenance, audit and import fields, and its existing search record. Its source is main-20261015 def-fd-trace-function.md, displayed formula (order 3033). The local operator definition was also read in the new snapshot. The new tasks split the actual arguments, not the original conclusion: one handles arbitrary pair morphisms at one coefficient field, the other one pair under coefficient extension. Neither asserts comparison of two coefficient models or equality of their degreewise traces. They are independent of each other and of the item. Their proof/proof_deps are empty and proof_origin null.

The assembly has 2058 proof-text characters. Every old argument is retained below for the next workers; nothing was erased by shortening the assembly. Old steps 2,3,4 belong to the naturality node; old steps 1,5,6 belong to the coefficient-extension node. Old steps 7,8,9 remain assembly steps 2,3,4, respectively, with the first half of old step 7 now supplied by assembly step 1. No Lean, compiler, Lake or build tool was used.

## Not duplicates

- lem-fd-local-frobenius-weil-morphism-naturality vs lem-fd-local-weil-model-trace-independence: the existing item compares two models after a common extension and their traces; this new node isolates only arbitrary pair morphisms at one fixed field. It is an extracted prerequisite, with no dependency on the item.
- lem-fd-local-frobenius-weil-morphism-naturality vs lem-weil-local-frobenius-conjugacy-class: that lemma changes a residue-field embedding for one pair; this task keeps the geometric point fixed.
- lem-fd-local-frobenius-weil-morphism-naturality vs lem-trf-local-frobenius-conjugacy: that lemma changes a closed-point lift at finite quotient coefficients; this task concerns rational constructible pairs and fixed point comparisons.
- lem-fd-local-frobenius-weil-morphism-naturality vs lem-rp-local-frobenius-models-agree: that lemma compares an integral finite-Tor lattice realization with the rational model at one field; this task has no such lattice or finite-Tor hypothesis.
- lem-fd-local-frobenius-weil-morphism-naturality vs lem-wf-adic-local-frobenius-model-conjugacy: that lemma concludes conjugacy after passing to a coefficient closure and canonical small models at closed points; it does not state these specified finite-field complex-level naturality/scalar identities.
- lem-fd-local-frobenius-weil-morphism-naturality vs prop-trf-karoubi-independence: that theorem concerns trace values on transported perfect complexes/summands; this task proves the actual point-complex operator identity, including its specified intermediate comparisons.
- lem-fd-local-frobenius-weil-morphism-naturality vs thm-trf-finite-coefficient-map: that theorem concerns finite rings and finite-Tor objects; it does not provide this rational full-constructible comparison.
- lem-fd-local-frobenius-weil-morphism-naturality vs lem-trf-integral-pullback-comparison-realization: that lemma specifies comparison coherence but does not state the iterated local Frobenius identities.
- lem-fd-local-frobenius-weil-morphism-naturality vs lem-weil-frobenius-point-transport-natural: that lemma gives one-step transport naturality and scalar compatibility, not the iterated point return and Weil-structure comparison.
- lem-fd-local-frobenius-weil-morphism-naturality vs lem-trf-iterated-weil-cocycle: that lemma is a finite-coefficient iterate cocycle, not this rational local-operator comparison.
- lem-fd-local-frobenius-coefficient-extension vs lem-fd-local-weil-model-trace-independence: the existing item compares two models after a common extension and their traces; this new node isolates only one pair under one coefficient extension. It is an extracted prerequisite, with no dependency on the item.
- lem-fd-local-frobenius-coefficient-extension vs lem-weil-local-frobenius-conjugacy-class: that lemma changes a residue-field embedding for one pair; this task keeps the geometric point fixed.
- lem-fd-local-frobenius-coefficient-extension vs lem-trf-local-frobenius-conjugacy: that lemma changes a closed-point lift at finite quotient coefficients; this task concerns rational constructible pairs and fixed point comparisons.
- lem-fd-local-frobenius-coefficient-extension vs lem-rp-local-frobenius-models-agree: that lemma compares an integral finite-Tor lattice realization with the rational model at one field; this task has no such lattice or finite-Tor hypothesis.
- lem-fd-local-frobenius-coefficient-extension vs lem-wf-adic-local-frobenius-model-conjugacy: that lemma concludes conjugacy after passing to a coefficient closure and canonical small models at closed points; it does not state these specified finite-field complex-level naturality/scalar identities.
- lem-fd-local-frobenius-coefficient-extension vs prop-trf-karoubi-independence: that theorem concerns trace values on transported perfect complexes/summands; this task proves the actual point-complex operator identity, including its specified intermediate comparisons.
- lem-fd-local-frobenius-coefficient-extension vs thm-trf-finite-coefficient-map: that theorem concerns finite rings and finite-Tor objects; it does not provide this rational full-constructible comparison.
- lem-fd-local-frobenius-coefficient-extension vs lem-trf-integral-pullback-comparison-realization: that lemma specifies comparison coherence but does not state the iterated local Frobenius identities.
- lem-fd-local-frobenius-coefficient-extension vs lem-weil-frobenius-point-transport-natural: that lemma gives one-step transport naturality and scalar compatibility, not the iterated point return and Weil-structure comparison.
- lem-fd-local-frobenius-coefficient-extension vs lem-trf-iterated-weil-cocycle: that lemma is a finite-coefficient iterate cocycle, not this rational local-operator comparison.

The whole DAG was searched by id, local Frobenius/naturality/scalar-extension concepts, and the source place; whole-blueprint searches used blueprint_refs.py for local Frobenius, local operator, point transport, iterated Weil, Frobenius natural, and local Frobenius scalar. No existing node states either task. The new statements cite the actual comparison infrastructure; no new Stacks-tag lemma is introduced. The two nodes have distinct content: one changes a pair morphism, one changes coefficients. They share setup and comparisons, not conclusions.

## Mathlib search results read

For each new task I ran LeanFinder, Loogle, grep and LeanSearch through msearch.py, with a second natural-language phrasing and corrected Loogle names. searches.jsonl is retained as generated. The first compound Loogle queries reported unknown identifiers (Endofunctor.IsoAlgebra and NatIso); I recorded that result and then searched the valid NatTrans.naturality and Functor.map_comp names. LeanFinder returned Witt-vector isocrystals; LeanSearch returned ring Frobenius and ordinary ModuleCat scalar extension, which do not act on the project's constructible Weil-pair point complexes. I read NatTrans.naturality in Mathlib/CategoryTheory/NatTrans.lean:59, Functor.map_comp in Mathlib/CategoryTheory/Functor/Basic.lean:49, and WittVector.IsocrystalHom.frob_equivariant / IsocrystalEquiv.frob_equivariant in Mathlib/RingTheory/WittVector/Isocrystal.lean:134,141. These are basic category axioms or a different Frobenius category, not one-line specializations of the new tasks. The grep algEquivIsoAlgebraIso hit is an algebra-category equivalence at Algebra/Category/AlgCat/Basic.lean:243, not the project's category of fixed pairs. No service was unavailable. The item's historical searches were preserved, not invented or repeated.

## Review by Q128

I read the chapter sec-fourier-transform, unit sk-def-trace, GOAL.md, SETUP.md's three levels, the stage-1 contract and delivery-errors B-E. The source main-20261015 sk-def-trace/def-fd-trace-function.md gives the numerical trace formula; the precise construction of its local operator is in the full live statement of def-weil-local-frobenius-trace. I checked the live raw rationalization and Weil-pair definition: a morphism must obey v alpha = beta G(v), while the underlying rational map need not have a stable integral lattice. The new nodes cite those definitions directly and introduce all fields, schemes, functors, point returns and iterates. They carry statements only, not proof sketches.

For the naturality task I read lem-weil-frobenius-point-transport-natural (2), which states the one-step natural transformation, and lem-trf-integral-pullback-comparison-realization, which states natural, associative composition comparisons compatible with equality of scheme maps and finite iterations, also after raw rationalization. Those are precisely the inputs of old steps 2-4, retained below: the induction on the pair equation, the induction on I, and naturality of rho and R. I made the conclusions for I, rho, R and the iterated Weil map explicit in the new statement, so none of those arguments disappears. The return is g_X^n xbar = xbar g_s^n, not g_X^n xbar = xbar.

For the coefficient task I read the full statements of lem-weil-point-sections-scalar-extension, lem-pur-integral-operations-scalar-extension, lem-trf-integral-pullback-comparison-realization and point-transport naturality (2). The first points its phi from sections of the extended object to extended sections, hence b uses phi inverse; the second points a from extended pullback to pullback of the extension; the third states the composition/scalar equation, equality-of-scheme-map compatibility and rationalization with no finite-Tor assumption. The point-transport lemma includes finite-field scalar compatibility. The new statement retains naturality of b for all rational morphisms, scalar extension of every iterated Weil map, and the precise R comparison before the final b F identity. Old steps 1,5,6 below specify the nontrivial linear extension and finite-pasting argument for its future worker. Since all schemes are over characteristic p and ell differs from p, the required invertibility holds; all objects are constructible. No unmentioned smoothness, properness, integral Weil lattice or finite-reduction Tor bound is used.

Assembly step 1 uses exactly the final displayed operator equation and the specified b from the coefficient task twice. Its hypotheses F subset L, n positive, fixed rational point and constructible Weil pair are precisely the item's hypotheses. Step 2 uses the arbitrary pair-morphism equation in the naturality task at F=L; the given u is a morphism of Weil pairs, not just an underlying isomorphism. The cancellation displayed there is elementary, with inverse b^{-1} U^{-1} b'. Neither step invokes the new nodes' eventual proofs.

Assembly step 3 uses lem-weil-cohomology-commutes-scalar-extension, whose statement explicitly supplies natural scalar/cohomology isomorphisms. The local-operator definition explicitly states bounded finite-dimensional point cohomology. Thus H^j of the conjugacy has the claimed conjugating map for every integer j. Step 4 uses the current statement of prop-trf-trace-formal-laws, which explicitly extends the signed dual-frame construction to any commutative coefficient ring, and def-weil-endomorphism-trace, which identifies the degree-zero field trace and its basis invariance. I checked the actual statement rather than relying on the finite-quotient Lean signature: the latter's categorical formal-law declarations are not being asserted to already instantiate at E. Ordinary field trace invariance and base change also follow from the displayed diagonal sum, agreeing with the existing Lean docstring. The field inclusions E -> L -> Qbar and E' -> L -> Qbar are the fixed ones.

I checked n=1 (all inductions have their specified first comparison), F=L (unit b and a), identity and zero pair morphisms for naturality, a rank-one structure with scalar lambda (iterate lambda^n), nontrivial Jordan blocks (no semisimplicity assumed), zero complexes and degrees outside cohomological support, and an empty rational-point set (vacuous). Each equation is correctly typed; in particular D_L(a_n) follows b_{G_n M}, whose target still contains T_X G_n M. New tasks contain no trace claim, do not restate the whole item, and are comparable workloads: naturality has two inductions plus return naturality, coefficient extension has the scalar induction plus transport/return pasting. I corrected the original overlarge split by extracting those arguments rather than compressing them. Every assembly step is below 2000 characters. No source statement was disputed or target changed.

## Preserved arguments for the next workers

The following is the old proof text, verbatim, with ownership labels. It is report material only: neither new node has proof steps or proof dependencies. These arguments explain what each independent task must eventually formalize.

### Previous step 1: lem-fd-local-frobenius-coefficient-extension

Fix $n,x$ as in the statement, put $s=\operatorname{Spec}k$, and write $P_F=L\bar x_F^*$, $Q_F=\operatorname{Fib}_{s,F}$, $D_F=Q_FP_F$, $G_{F,r}=L(g_X^r)_F^*$ and $S_{F,r}=L(g_s^r)_F^*$. A superscript $T$ denotes extension from $F\in\{E,E'\}$ to $L$. The point-sections comparison and the pullback/scalar comparison give the natural isomorphism $b_M:D_F(M)\otimes_F L\to D_L(M^T)$ specified in the statement. Naturality holds for rationalized morphisms as well: the integral naturality equation extends linearly to Hom groups tensored with $F$. All objects used here are in the constructible categories. Since $\ell\ne p$, $\ell$ is invertible on $X,s$. Thus both cited comparisons apply to $\bar x,g_X^r,g_s^r$, without restrictions on finite-reduction Tor-amplitude.

Cited inputs: lem-weil-point-sections-scalar-extension, lem-pur-integral-operations-scalar-extension, lem-trf-integral-pullback-comparison-realization

### Previous step 2: lem-fd-local-frobenius-weil-morphism-naturality

Put $A=M_E^T$, $B=(M'_{E'})^T$ with their extended Weil maps $\alpha,\beta$, and write $G_r=G_{L,r}$. In the specified composition identifications, the Weil-pair equation implies $u\alpha^{[r]}=\beta^{[r]}G_r(u)$ for every $r\geq1$. The base case is the assumed equation. If it holds for $r$, then
$$u\alpha^{[r+1]}=\beta^{[r]}G_r(u)G_r(\alpha)=\beta^{[r]}G_r(u\alpha)=\beta^{[r]}G_r(\beta)G_rG_1(u)=\beta^{[r+1]}G_{r+1}(u).$$
The last equality uses naturality of the composition comparison; its associativity makes these the iterates in the local-operator definition. This is an induction on the given intertwining equation, not an assertion that an arbitrary underlying isomorphism is equivariant.

Cited inputs: def-weil-weil-sheaf-complex, def-weil-local-frobenius-trace, lem-trf-integral-pullback-comparison-realization

### Previous step 3: lem-fd-local-frobenius-weil-morphism-naturality

For any coefficient field $F$ in use and any morphism $v:N\to N'$ on $s$, naturality of $\iota$ implies
$$Q_F(S_{F,r}v)I_N^{[r]}=I_{N'}^{[r]}Q_F(v).$$
Indeed, before replacing repeated pullbacks by $S_{F,r}$, set $J_1(N)=\iota_N$ and $J_{r+1}(N)=\iota_{(Lg_s^*)^rN}J_r(N)$. The cited naturality equation, applied to $(Lg_s^*)^rv$, and the inductive equation for $J_r$ give the equation for $J_{r+1}$. Apply the natural pullback-composition comparison to obtain the displayed formula for $I^{[r]}$. This induction applies to $N=P_LA$, $N'=P_LB$ and $v=P_Lu$.

Cited inputs: lem-weil-frobenius-point-transport-natural, def-weil-local-frobenius-trace, lem-trf-integral-pullback-comparison-realization

### Previous step 4: lem-fd-local-frobenius-weil-morphism-naturality

For $r=n$ let $\rho_{F,M}:S_{F,n}P_FM\xrightarrow{\sim}P_FG_{F,n}M$ be the return comparison from $g_X^n\bar x=\bar xg_s^n$. It is a composite of natural pullback-composition comparisons and the identification for this equality of scheme maps. Consequently $P_FG_{F,n}(v)\rho_{F,M}=\rho_{F,M'}S_{F,n}P_F(v)$. Define $R_F(M)=Q_F(\rho_{F,M})I_{P_FM}^{[n]}$. Step 3 and this equation give $D_F(G_{F,n}v)R_F(M)=R_F(M')D_F(v)$. The defining local operator is $\mathcal F_F(M,\theta)=D_F(\theta^{[n]})R_F(M)$. Hence steps 2 and 3 give, for $U=D_L(u)$,
$$U\mathcal F_L(A,\alpha)=D_L(u\alpha^{[n]})R_L(A)=D_L(\beta^{[n]})R_L(B)U=\mathcal F_L(B,\beta)U.$$
Here the return comparison uses the semilinear equality of maps displayed above; it does not identify $g_X^n\bar x$ with $\bar x$.

Cited inputs: def-weil-local-frobenius-trace, lem-trf-integral-pullback-comparison-realization

### Previous step 5: lem-fd-local-frobenius-coefficient-extension

For $F=E$ or $E'$, let $a_{r,M}:(G_{F,r}M)^T\xrightarrow{\sim}G_{L,r}(M^T)$ be the specified scalar comparison. If $\theta_L$ is the extended Weil map, its definition says $\theta_La_{1,M}=(\theta)^T$. Inductively,
$$\theta_L^{[r]}a_{r,M}=(\theta^{[r]})^T.$$
To check the induction, the composition/scalar equation identifies $a_{r+1,M}$, after the composition identifications, with $G_{L,r}(a_{1,M})a_{r,G_{F,1}M}$. Naturality of $a_r$ for $\theta:G_{F,1}M\to M$ gives
$$G_{L,r}(\theta^T)a_{r,G_{F,1}M}=a_{r,M}(G_{F,r}\theta)^T.$$
Substitute this and $\theta_La_{1,M}=\theta^T$ into $\theta_L^{[r]}G_{L,r}(\theta_L)a_{r+1,M}$. The result is $(\theta^{[r]})^T(G_{F,r}\theta)^T=(\theta^{[r+1]})^T$. Thus the scalar-extended iterated Weil map is precisely the one in the local-operator definition.

Cited inputs: def-weil-weil-sheaf-complex, def-weil-local-frobenius-trace, lem-trf-integral-pullback-comparison-realization

### Previous step 6: lem-fd-local-frobenius-coefficient-extension

The scalar compatibility in point-transport naturality (2) commutes each factor $\iota$ with the point-sections and pullback/scalar comparisons. Compose these squares for the $n$ factors defining $J_n$ in step 3; each intermediate comparison cancels with its inverse. The composition/scalar equation identifies the remaining repeated-pullback comparison with that for $g_s^n$. Apply the same equation to the two composites $g_X^n\bar x$ and $\bar xg_s^n$; its compatibility with equality of scheme maps identifies their comparison squares. This gives, with $a=a_{n,M}$,
$$D_L(a)b_{G_{F,n}M}(R_F(M)\otimes_F L)=R_L(M^T)b_M.$$
Naturality of $b$ for $\theta^{[n]}$ and step 5 now yield
$$b_M(\mathcal F_F(M,\theta)\otimes_F L)=D_L((\theta^{[n]})^T)b_{G_{F,n}M}(R_F(M)\otimes_F L)=\mathcal F_L(M^T,\theta_L)b_M.$$
These are finite pastings of the cited squares, using the specified comparisons; no choice of an integral Weil-stable lattice is involved. Apply the equation separately to $V_E$ and $V'_{E'}$.

Cited inputs: lem-weil-frobenius-point-transport-natural, lem-weil-point-sections-scalar-extension, lem-trf-integral-pullback-comparison-realization, def-weil-local-frobenius-trace

### Previous step 7: item assembly

Write $b=b_{M_E}$, $b'=b_{M'_{E'}}$, $f=F^{(n)}_{E,x}\otimes_E L$ and $f'=F'^{(n)}_{E',x}\otimes_{E'}L$. Step 6 says $bf=\mathcal F_L(A,\alpha)b$ and $b'f'=\mathcal F_L(B,\beta)b'$. Using step 4 and $\widetilde u_x=(b')^{-1}Ub$ gives
$$\widetilde u_x f=(b')^{-1}U\mathcal F_L(A,\alpha)b=(b')^{-1}\mathcal F_L(B,\beta)Ub=f'\widetilde u_x.$$
All three factors defining $\widetilde u_x$ are isomorphisms, and their inverse composite is $b^{-1}U^{-1}b'$. This proves the claimed conjugacy with exactly the isomorphism in the statement.

Cited inputs: 

### Previous step 8: item assembly

For every $j$, apply $H^j$ to the equality in step 7. Use the natural scalar-cohomology isomorphisms $h_{F,j}:H^j(C_{F,x})\otimes_F L\xrightarrow{\sim}H^j(C_{F,x}\otimes_F L)$. Naturality identifies $H^j(F^{(n)}_{F,x}\otimes_F L)$ with $H^j(F^{(n)}_{F,x})\otimes_F L$ through $h_{F,j}$. Thus $(h_{E',j})^{-1}H^j(\widetilde u_x)h_{E,j}$ is an $L$-linear isomorphism intertwining the two scalar-extended cohomology endomorphisms. The spaces are finite dimensional by the point-complex assertion of the local-operator definition.

Cited inputs: lem-weil-cohomology-commutes-scalar-extension, def-weil-local-frobenius-trace

### Previous step 9: item assembly

Regard each finite-dimensional cohomology space as a perfect complex concentrated in degree zero. Formal trace law (4) identifies its categorical trace with its ordinary linear trace. Laws (1) and (3), applied to the conjugacy of step 8 and to $E\hookrightarrow L$, $E'\hookrightarrow L$, therefore give
$$\operatorname{incl}_{E,L}\operatorname{Tr}_E(H^j(F^{(n)}_{E,x}))=\operatorname{Tr}_L(H^j(F^{(n)}_{E,x})\otimes_E L)=\operatorname{Tr}_L(H^j(F'^{(n)}_{E',x})\otimes_{E'}L)=\operatorname{incl}_{E',L}\operatorname{Tr}_{E'}(H^j(F'^{(n)}_{E',x})).$$
These laws allow any commutative coefficient ring, hence in particular the finite extension fields here. Compose with $L\hookrightarrow\Qlb$; both composites are the fixed inclusions in the statement. The assertion holds degree by degree, including the zero cohomology spaces.

Cited inputs: prop-trf-trace-formal-laws, def-weil-endomorphism-trace

## Unfinished work

Only the two new nodes' proofs remain for other workers, deliberately as requested. No issue prevents the stage-1 repair. Delivery validation is recorded after the required server dry run.

## Validation

The required deliver.py --no-push exited successfully: OK (not pushed) at 1757705a1fb, server preflight passed. I then expanded the trace-law citation into literal clauses (1), (3), and (4); the final dry run checks that complete delivery before pushing. Local read-only comparison also confirms that the item statement is identical to current main, its proof has 2058 characters, and the two new nodes are unsplit with empty proofs and five actual logged searches each.
