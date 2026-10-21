## Worker report

This is the human-requested stage-1 re-split of thm-pur-general-admissibility, not a replacement of its statement or its already recorded Lean declaration. The sandbox was initially empty of node files. I read the current shared item and its blueprint_update, the original master theorem/proof, the main-20261015 theorem/proof, the chapter and preservation-unit records, and the stage-1 contract. The delivered statement is byte-for-byte equal to the live item's statement. In particular the separate cohomological and finite-Tor conclusions, nonnegative chart constants, arbitrary finite-type k-schemes (not necessarily separated over k), and empty-chart convention are retained.

Files written:

- dag/nodes/sec-six-functors/thm-pur-general-admissibility.json: existing statement, four-step assembly, 2229 proof-text characters.
- dag/nodes/sec-six-functors/lem-pur-affine-chart-exceptional-identification.json: statement; unsplit, no Mathlib match. Independent argument about the domain and witnesses of adjunctions, base-open restriction, and chart comparison. It has no complement-condition or preservation hypothesis.
- dag/nodes/sec-six-functors/lem-pur-closed-etale-transport-bounds.json: statement; unsplit, no Mathlib match. Independent argument transporting ordinary etale closed-support bounds and their exact intervals to intrinsic pro-etale coefficients. It involves neither an affine-space projection nor a cover.
- dag/nodes/sec-six-functors/lem-pur-finite-open-interval-descent.json: statement; unsplit, no Mathlib match. Independent descent argument for an arbitrary ambient complex, with separate cohomology and Tor implications; no exceptional functor occurs.
- citations.json: verbatim statement excerpts for every citation of each of the four parent steps.
- searches.jsonl: search-command records; prepare.py: sandbox-only JSON preparation helper. Neither is a project-source change.

Attachments: none. I searched WeilConjectures by the item tag and by exceptional/preservation names and read Etale/Derived/PurityPreservation.lean and ProEtale/FiniteCoefficient/Derived/UpperShriekPreservation.lean. The former's preservationClauses_of_charts is on the ordinary etale category. The latter's exists_preservationClauses gives existential constants and does not assert this item's bounds for an arbitrary specified cover and its specified complement constants. The recorded exact local statement WeilConjectures.PurityFiniteSetting.general_admissibility in Sheaf/Paper/PurityGeneralAdmissibility.lean still ends in sorry. These are not an exact finished attachment under the brief. No Lean was written or compiled.

WANTED: none.

The previous proof is mathematically usable but carried adjunction domain verification, two Hom chains, comparison reflection, stratification disjointification and arbitrary-sheaf tensor descent in one node. This delivery distributes those arguments, rather than deleting them. The current blueprint's base-open displayed formula suppresses the source restriction and is ill-typed literally; I retain the already repaired formula Lh* Rf! L = Rf_V! Lg* L on X_V. No new statement dispute or statement change is introduced. No work is left in the assembly; the three newly exposed statements deliberately remain unsplit for independent workers.

## Sources and searches

The source for all three extracted arguments is literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-et-proet/thm-pur-general-admissibility.proof.md, Steps 1–4. Each new node's source.place and blueprint.from.place specifies the corresponding sentences and the previous DAG step allocation. All have blueprint.from.node thm-pur-general-admissibility, via [], same_as []. I ran blueprint_refs ancestor and whole-blueprint searches for chart adjoint, closed comparison, finite cover constructible, origin adjunction, constructible interval, bounded below origin, chart exceptional, closed proetale, open interval descent, adjoint bounded, closed amplitude and cohomology locality. The returned neighbouring blueprint statements were read; none states the complete new interface.

I searched all DAG statements and titles by adjunction/origin, closed/interval, open/cohomology/interval, and finite-open/chart/locality vocabulary, and read the specific near matches distinguished below. Source-library searches covered both the tag and the concepts. No other node files are edited. The item remains in its recorded chapter and unit; the current blueprint places it in smooth purity, but changing the maintainer-owned classification is not this delivery's work. The route remains open restriction, smooth affine-space purity, closed support, then finite-cover descent. No SGA source is used.

I also opened the actual local Stacks statements and proofs: 09AK, proetale.tex, lemma-compare-constructible; 04JC, sites-modules.tex, lemma-flat-pullback-exact; 095F, etale-cohomology.tex, lemma-constructible-local; 07A4, sites-cohomology.tex, lemma-pullback-tensor-product. 09AK is a sheaf comparison, not a statement of either closed exceptional bound. 04JC justifies exact constant-coefficient inverse image, not a Tor-interval conclusion by itself. 095F is sheaf constructibility locality, requiring a further complex and tensor argument here. 07A4 allows both tensor factors to be arbitrary ambient derived objects, essential for the last Tor tests. The original reviewed nine steps are reproduced below with their dependency lists, so no argument or citation disappears from the handoff.

Every new node has searches actually run with msearch.py, using its own mathematical statement in mind. I read the returned hits, tried a second semantic phrasing, and recorded the exact queries. Loogle's rightAdjointUniq and Mathlib/CategoryTheory/Adjunction/Unique.lean:102 give abstract uniqueness, not the existence and closure hypotheses for this chart comparison. I read that declaration and its counit formula. The other chart hits are affine scheme restriction identities and ordinary structure-sheaf module pseudofunctors. The closed-support searches returned ring-theoretic etaleness, exact-functor criteria and t-structure localization results, none a closed-support comparison or bound. The locality hits are DerivedCategory.isGE_iff / isLE_iff and Topology.IsLocallyConstructible.of_isOpenCover (Mathlib/Topology/Constructible.lean:504, read through :538). The latter concerns a subset of a topological space, not an intrinsic constructible sheaf or its tensor cohomology. The grep searches for exceptional operations and for proetale/Tor names in the relevant Mathlib directories had no relevant matches. Thus none of the new nodes is a one-line specialization of a returned Mathlib theorem. Searches not recorded as run are not claimed.

## Not duplicates

lem-pur-affine-chart-exceptional-identification vs thm-sf-ambient-adjoint-class: the existing theorem supplies a relative Hom bijection and bounded-below transported values at a compactification; it does not give an actual lift of both functors to the witnessed categories together with the source/base-open and closed/projection chart identifications.

lem-pur-affine-chart-exceptional-identification vs thm-sf-comp-composition: the existing theorem concerns left compact-support functors and their domains, not the right-functor chart comparison with explicit witnesses.

lem-pur-affine-chart-exceptional-identification vs lem-sf-etale-chart-adjoint-comparison: that lemma is an ordinary-etale Hom comparison against bounded-below test objects, with neither representing value assumed bounded below. The new statement establishes the bounded-below witnessed pro-etale domain, its adjunctions, and the resulting actual functor isomorphisms. This is not obtained by forgetting an assumption or by a one-line specialization.

lem-pur-affine-chart-exceptional-identification vs cor-exc-base-change-open-immersion-general: the latter supplies just the Cartesian base-open comparison on its specified classes; it does not include chart-source restriction, closed/projection composition, or the witnessed adjunction domain verification.

lem-pur-affine-chart-exceptional-identification vs lem-exc-relative-adjoint-open-origin: the latter is for a proper f, and only constructs two bounded-below origin witnesses; its statement explicitly does not identify them. Here f is any separated finite-type morphism and the required chart isomorphisms are conclusions.

lem-pur-affine-chart-exceptional-identification vs lem-sf-kv-affine-locality: its comparison concerns K in Dctf and also a Kunneth transpose. Here the chart comparison holds on the bounded-below etale-origin domain, and the base-open application includes bounded constructible inputs of infinite Tor dimension.

lem-pur-closed-etale-transport-bounds vs lem-exc-closed-amplitude: the existing lemma gives an ordinary-etale cohomological bound, not its intrinsic pro-etale transport or the separate Tor bound and arbitrary pro-etale sheaf tests.

lem-pur-closed-etale-transport-bounds vs prop-exc-closed-tor: the existing proposition gives an ordinary-etale finite-Tor bound; it does not cover the independent cohomological assertion without Tor assumptions, or transport to all pro-etale module tests.

lem-pur-closed-etale-transport-bounds vs lem-sf-comparison-tor-amplitude: that statement transfers Tor amplitude between sites but gives no exceptional closed-support calculation or complement-dependent c+1 increment.

lem-pur-closed-etale-transport-bounds vs lem-coef-finite-closed-shriek: that lemma compares changes of coefficient ring for finite-Tor inputs, with separated schemes; it does not give the cohomology-only clause or either explicit bound from a specified complement constant.

lem-pur-closed-etale-transport-bounds vs lem-weil-finite-duality-locally-closed-comparison: that statement normalizes ordinary/pro-etale ambient locally closed adjunction counits on separated schemes; it does not assert the two interval bounds under the specified complement hypothesis.

lem-pur-closed-etale-transport-bounds vs lem-sfb-finite-field-closed-support: its coefficient ring must be a finite field, and it supplies no specified interval from c. Here A may be a nonreduced finite valuation-ring quotient, and the first clause does not require finite Tor amplitude.

lem-pur-finite-open-interval-descent vs lem-sf-finite-cover-ctf-locality: the existing lemma assumes a uniform local Tor interval even for its constructibility conclusion. The new first implication must apply without any finite-Tor hypothesis; its second implication separately applies without constructibility or boundedness. Neither independent implication may be replaced by a simultaneous assumption of both.

lem-pur-finite-open-interval-descent vs lem-sfb-noetherian-global-constructibility: that statement is about one sheaf and finitely presented values. It is a useful ingredient but does not state fixed derived cohomological intervals, arbitrary ambient complexes, the independent full-sheaf Tor implication, or the empty-site assertion.

lem-pur-finite-open-interval-descent vs lem-sf-noetherian-constructible-open-local: that lemma concerns sheaves on the ordinary etale site, not either complex-level pro-etale implication.

lem-pur-finite-open-interval-descent vs lem-sfb-tor-interval-local-detection: its clause (i) is an existing stronger tool for the second implication. It supplies no constructible-cohomology implication without a Tor hypothesis; the new node records the full independent descent interface needed by both clauses of this assembly, rather than creating a separate redundant Tor node.

lem-pur-finite-open-interval-descent vs lem-sf-affine-chart-factorization-gluing: that lemma uses ordinary etale coefficients, assumes both local cohomology and Tor intervals together, and assumes separated schemes over k. The new independent cohomology assertion is pro-etale and needs neither local Tor bounds nor separatedness over k.

None of the three new statements restates the item's conclusion or a clause of it: the first has no preservation assertion, the second is a single closed-support comparison with no chart cover or global morphism f, and the third is a locality assertion for arbitrary F with no exceptional operation.

## Review by Q69

I checked B–E with the node statements and the sources open. For the item I used the main-20261015 proof and the old repaired proof, with the preservation-unit paragraph (iv) and its closed and smooth cases (ii), (iii). The statement is unchanged, and each new statement introduces its field, coefficients, schemes, functors, intervals and covering data rather than inheriting unnamed objects from the parent. All three are statement-only unsplit nodes: no proof steps or proof dependencies are placed on them, and the argument handoff is below. Their definition references are statement dependencies. The first never asserts an unrestricted pro-etale right adjoint; the second names the etale complement condition; the third tests Tor against all ordinary pro-etale module sheaves.

Parent Step 1 uses the new chart lemma's two displayed isomorphisms, with the source of Lh* Rf! and target of G_fV Lg* both X_V. Its G_i G_pi formula is on U. I checked that the new statement includes the witnessed bounded-below domain, so uniqueness of adjoints can be applied without assuming the preservation being proved. I separately reopened prop-exc-open-adjoint: it identifies the open exceptional functor with inverse image on the whole ordinary derived category. I reopened thm-exc-explicit-preservation: it preserves constructible intervals and Tor intervals, so both uses on Lg* are licensed. A constructible cohomological input need not have finite Tor dimension.

Parent Step 2 uses sbc-lem-affine-space-smooth for relative dimension d, and cor-pur-smooth-admissibility for both distinct conclusions with shift -2d. I read the corollary's statement: it allows finite-type k-schemes not necessarily separated over k, but requires the morphism separated; this is verified by the polynomial diagonal equations written in the parent. The new closed lemma applies with r=a-2d and s=b-2d. Its statement gives exactly c_U+1 on the upper endpoint, preserves bounded constructibility in its Tor clause, and assumes precisely the given ordinary-etale complement condition. This step keeps the cohomology calculation separate from the Tor calculation; it never uses the false inference that bounded constructibility implies finite Tor dimension over A.

Parent Step 3 is interval arithmetic, not an omitted geometric argument: I checked both endpoint inequalities and the dependence of c on D-d_U. The two cited definitions explicitly characterize the needed vanishings, so enlarging the interval is immediate for both. The empty-chart branch cites the new descent lemma's explicit zero-object clause, not a maximum of an empty set. No non-elementary fact is hidden in this elementary step.

Parent Step 4 uses exactly the first and second implications of the new descent statement. Its first implication is independent of Tor. Its second tests arbitrary degree-zero sheaves, including those without etale origin; I checked that this is in the new statement and not merely in its intended proof. The extra use of conclusion 1 with an input cohomological interval establishes bounded constructibility for the Tor input. This use is not an induction or a circular assumption: conclusion 1 is already proved before the Tor implication is applied. Every citation in Steps 1–4 has a copied statement excerpt in citations.json; no excerpt is taken from a dependency's proof.

For the chart lemma I read the statements of all former Steps 1–3 dependencies: finite type over a Noetherian base; locally Noetherian quasi-separatedness; Nagata compactification; finite dimension over a field; the bounded-class adjoint theorem and discharge; intrinsic constructible etale origin; the exceptional transport definition; the witnessed-category definition; compact-support comparison and composition; base-open comparison; the open adjoint; explicit open preservation; right-adjoint composition; and the comparison-site definition. Nagata is applied over qcqs targets, not just arbitrary targets. Proper compactification factors are finite type over k, hence of finite dimension. Comparison makes both functors land in the witnessed bounded-below categories. Both Hom chains from the old proof remain part of this node's argument allocation below. Merely citing abstract right-adjoint uniqueness would not verify these geometric and domain hypotheses, which is why the chart statement is not a Mathlib leaf or an elementary-node creation.

For the closed-transfer lemma I read the ordinary closed adjoint, closed-amplitude and closed-Tor statements, both clauses of comparison-tor-amplitude, exact comparison pullback, full faithfulness/unit of the site comparison, intrinsic constructible origin, and the exceptional transport formula. The witness B_e is bounded constructible in both applications; faithful exact comparison reflects its cohomological interval; comparison-tor-amplitude(ii) reflects its Tor interval. The given complement is quasi-compact and supplies both all-sheaf vanishing and constructible direct images. The etale closed theorems therefore apply before pullback, and comparison-tor-amplitude(i) returns the Tor conclusion with arbitrary pro-etale tests. No smooth purity is needed to prove this new node.

For the descent lemma I read the finite-cover locality, noetherian global constructibility and Tor-detection near matches as well as the old proof. The new first implication is necessary when A has nontrivial nilpotents: finite modules need not have finite Tor dimension. I checked exact open restriction from prop-weil-pbc-proetale-constant-exact, and the ambient finite-level clause of lem-pur-derived-pullback-tensor-iso; neither is only an etale-origin assertion. Finite-type k-schemes are Noetherian even when not separated over k; hence the finite disjointification of local locally closed constructible strata stays constructible. Exact restriction identifies cohomology and restrictions of cohomology, and the sheaf axiom detects zero from the opens pulled back to each site object. These are the actual local cohomology and arbitrary-sheaf tensor arguments, retained below for the next worker, not replaced by a vague claim of gluing.

Small cases checked: d=0 (projection is the identity); i the identity and W empty (the c+1 bound is a valid overestimate); Z empty (closed pullback is zero); c=0; a=b and zero input; a nonreduced A such as O_E/varpi_E^2 (cohomological constructibility must not assume perfectness); empty X/empty chart family (no use of a nonempty maximum); Y empty (then X empty); repeated or overlapping opens (ordered disjointification still partitions X); and finite-type schemes nonseparated over k (no absolute separatedness hypothesis was added). The definition dependencies were checked against their actual notions. The original corrected typed base-open formula is retained. No long parent non-elementary step exceeds 2000 characters; the nontrivial arguments were extracted instead of compressed into long assembly steps.

This is direct delivery: there is no second worker or independent lead review to claim. The signature above is Q69's own reading and repairs; the maintainer's review is still independent.

## Complete argument allocation from the previous split

The following preserves the full previous argument, including its citations, for the three statement-only workers. The current parent retains the smooth-projection paragraph and endpoint arithmetic. Allocation: old Steps 1–3 belong to lem-pur-affine-chart-exceptional-identification; old Steps 5–6 to lem-pur-closed-etale-transport-bounds; old Steps 8–9 and the empty-cover argument in Step 7 to lem-pur-finite-open-interval-descent. Step 4 and the nonempty arithmetic in Step 7 remain in the parent. Thus none of the 9820-character argument is silently discarded, and no new node contains the whole theorem.

### Previous Step 1

All exceptional functors in this argument are the transported etale adjoints, not unrestricted pro-etale adjoints. All these finite-type $k$-schemes are Noetherian by [lem-weil-pbc-finite-type-over-noetherian], applied to the spectrum of the field $k$; they are quasi-separated by [lem-weil-pbc-locally-noetherian-quasi-separated]. (A field is Noetherian because its only ideals are $0$ and the unit ideal.) A separated finite-type morphism between the finite-type $k$-schemes in the argument has a compactification by [thm-nagata-compactification]; its proper factor is finite type over $k$ and has finite dimension by [lem-kun-dimension-finite-type]. Thus [thm-sf-ambient-adjoint-class](2) supplies the adjunction on bounded-below objects of etale origin, with the canonical comparisons of its clause (3), as summarized in [cor-sf-ambient-adjoint-discharge]. By [lem-sf-proetale-constructible-origin](ii), bounded constructible inputs have etale-origin witnesses. The formula in [def-weil-exceptional-inverse-image] identifies the functor on such an input $\nu_Y^*G$ with $\nu_X^*f^\times G$. Only this construction and the bounded-below adjunction are used at this stage; preservation of bounded constructibility is proved below. More explicitly, work in the categories $\mathcal C(T)=\mathcal D^+_{\mathrm{et}}(T,A)$ of complexes with an etale-origin witness [def-sf-etale-origin-subcategory]. The comparison [lem-sf-class-compact-support-comparison] gives $Rf_!\nu_X^*G\cong\nu_Y^*(Rf_!^{\mathrm{et}}G)$, so compact support preserves these categories. The transported right functor also takes values in them: its witness is $f^\times R\nu_{Y,*}L$, bounded below by the construction above. Thus the displayed Hom bijection restricts to an actual adjunction $\mathcal C(X)\rightleftarrows\mathcal C(Y)$, before any constructible-preservation assertion is used.

Cited statements: lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-locally-noetherian-quasi-separated, thm-nagata-compactification, lem-kun-dimension-finite-type, thm-sf-ambient-adjoint-class, cor-sf-ambient-adjoint-discharge, lem-sf-proetale-constructible-origin, def-weil-exceptional-inverse-image, def-sf-etale-origin-subcategory, lem-sf-class-compact-support-comparison.

### Previous Step 2

For an affine base open $g:V\hookrightarrow Y$, put $X_V=f^{-1}(V)$, $h:X_V\hookrightarrow X$, and $f_V:X_V\to V$. The class-restricted clause of [cor-exc-base-change-open-immersion-general] gives the correctly typed isomorphism
$$
 Lh^*Rf^!L\cong Rf_V^!Lg^*L.
$$
Here both sides are objects on $X_V$. By [prop-exc-open-adjoint], the exceptional adjoint for $g$ is $Lg^*$; hence [thm-exc-explicit-preservation] for $g$ shows that $Lg^*L$ has the same constructible interval as $L$, and that $Lg^*K$ has the same Tor interval as $K$. The comparison is used only on bounded constructible inputs, exactly the unconditional class specified by the cited base-change statement.

Cited statements: cor-exc-base-change-open-immersion-general, prop-exc-open-adjoint, thm-exc-explicit-preservation.

### Previous Step 3

Fix one chart and let $u':U\hookrightarrow X_V$, $u=hu':U\hookrightarrow X$. Write $d=d_U$, $T=T_U$, $i=i_U$, and $\pi=\pi_U$, so $f_Vu'=\pi i$. Open restriction preserves the categories $\mathcal C$ of Step 1: the inclusion defining the comparison morphism [def-weil-pbc-site-comparison-morphism], restricted to objects over $U$, is the inclusion for $U$ itself; hence $L(u')^*\nu_{X_V}^*G\cong\nu_U^*(G|_U)$, with witness $G|_U$. By [prop-exc-open-adjoint], the restriction of $L(u')^*$ is right adjoint to $R(u')_!$ on these categories.

For $M\in\mathcal C(U)$ and $N\in\mathcal C(V)$, Step 1 and [thm-sf-comp-composition] give the natural bijections
$$
\begin{aligned}
\operatorname{Hom}(M,Ri^!R\pi^!N)
&\cong\operatorname{Hom}(Ri_!M,R\pi^!N)\\
&\cong\operatorname{Hom}(R\pi_!Ri_!M,N)\\
&\cong\operatorname{Hom}(R(\pi i)_!M,N),\\
\operatorname{Hom}(M,L(u')^*Rf_V^!N)
&\cong\operatorname{Hom}(R(u')_!M,Rf_V^!N)\\
&\cong\operatorname{Hom}(Rf_{V,!}R(u')_!M,N)\\
&\cong\operatorname{Hom}(R(f_Vu')_!M,N).
\end{aligned}
$$
Since $f_Vu'=\pi i$, [lem-cat-right-adjoint-composition] identifies both right adjoints with $R(f_Vu')^!$ and gives
$$
L(u')^*Rf_V^!\cong R(f_Vu')^!\cong Ri^!R\pi^!.
$$
Consequently, for $N=Lg^*L$, Step 2 and composition of open restrictions give
$$
Lu^*Rf^!L\cong Ri^!R\pi^!N.
$$
All Hom calculations take place on the bounded-below etale-origin categories, where both compact support and its right adjoint are defined by Step 1; none assumes the preservation being proved.

Cited statements: thm-sf-comp-composition, lem-cat-right-adjoint-composition, prop-exc-open-adjoint, def-weil-pbc-site-comparison-morphism.

### Previous Step 4

The affine-space projection $\pi:T\to V$ is smooth of pure relative dimension $d$ by [sbc-lem-affine-space-smooth]; over the affine $V=\operatorname{Spec}R$ it is separated, since its diagonal is defined in $\operatorname{Spec}R[x_1,\ldots,x_d,y_1,\ldots,y_d]$ by the equations $x_j-y_j=0$. Apply [cor-pur-smooth-admissibility] to obtain
$$
 B=R\pi^!N\in D_c^{[a-2d,b-2d]}(T,A)
$$
when $N\in D_c^{[a,b]}(V,A)$. If instead $N$ is bounded constructible with Tor amplitude $[a,b]$, the same corollary gives that $B$ is bounded constructible with Tor amplitude $[a-2d,b-2d]$. These are separate applications: the cohomological-interval assertion is not restricted to finite-Tor inputs.

Cited statements: sbc-lem-affine-space-smooth, cor-pur-smooth-admissibility.

### Previous Step 5

To apply the closed-immersion bounds, pass explicitly to the etale site. By [lem-sf-proetale-constructible-origin](ii) choose $B'\in D^b_c(T_{\mathrm{et}},A)$ with $B\cong\nu_T^*B'$. Exactness and the cohomology formula of [lem-sf-comparison-pullback-exact], together with full faithfulness in [thm-weil-pbc-site-comparison], show that $B'$ has the same cohomological interval as $B$: a cohomology sheaf with zero comparison pullback is zero because that pullback is faithful. For the Tor application, [lem-sf-comparison-tor-amplitude](ii) gives the same Tor interval for $B'$. The defining transport formula [def-weil-exceptional-inverse-image], using the unit isomorphism of [thm-weil-pbc-site-comparison], identifies
$$
 Ri^!B\cong\nu_U^*i_{\mathrm{et}}^!B'.
$$
Thus the following closed-immersion calculation concerns ordinary etale adjoints and the etale complement condition, on the same coefficient ring $A$.

Cited statements: lem-sf-proetale-constructible-origin, lem-sf-comparison-pullback-exact, thm-weil-pbc-site-comparison, lem-sf-comparison-tor-amplitude, def-weil-exceptional-inverse-image.

### Previous Step 6

By [def-exc-open-complement-bound], the assumed constant $c_U$ gives both $R^qj_*M=0$ for all etale $A$-module sheaves $M$ and $q>c_U$, and constructibility of every $R^qj_*F$ for constructible $F$, where $j:W_U\hookrightarrow T$. The ordinary etale closed adjoint is supplied by [lem-exc-closed-ambient]. Apply the constructible clause of [lem-exc-closed-amplitude] to $B'$ in the cohomological-interval application. In the Tor application apply [prop-exc-closed-tor] to the bounded constructible $B'$ of Step 5. The open $j$ is quasi-compact as required by the assumed open-complement condition. The resulting interval in either application is
$$
 [a-2d,b-2d+c_U+1].
$$
In both cases the result is bounded constructible. Pullback by $\nu_U^*$ preserves this constructibility by [lem-sf-proetale-constructible-origin](ii), and preserves its cohomological interval by [lem-sf-comparison-pullback-exact]. In the Tor application it preserves the Tor interval by [lem-sf-comparison-tor-amplitude](i). Combining with Steps 2–5 gives the claimed chartwise bounds for $Lu^*Rf^!$.

Cited statements: def-exc-open-complement-bound, lem-exc-closed-ambient, lem-exc-closed-amplitude, prop-exc-closed-tor, lem-sf-proetale-constructible-origin, lem-sf-comparison-pullback-exact, lem-sf-comparison-tor-amplitude.

### Previous Step 7

Suppose the chart family is nonempty and put $I=[a-2D,b-2D+c]$. For each chart $d_U\leq D$, so $a-2D\leq a-2d_U$. Also $c\geq c_U+1+2(D-d_U)$ gives $b-2d_U+c_U+1\leq b-2D+c$. Hence every chartwise interval of Step 6 is contained in $I$. Vanishing outside a smaller interval implies vanishing outside $I$, for ordinary cohomology and for every tensor test defining Tor amplitude. If there are no charts, $X$ is empty; sheaves on its small pro-etale site are zero by the sheaf condition for the empty covering, so both conclusions hold with $D=c=0$.

Cited statements: def-weil-constructible-intervals, def-weil-finite-tor-amplitude.

### Previous Step 8

Let $F=Rf^!L$ in the cohomological-interval application. Open restriction on constant-$A$ pro-etale module sheaves is exact by [prop-weil-pbc-proetale-constant-exact], so $\mathcal H^r(F)|_U=\mathcal H^r(F|_U)$: apply restriction to the kernel/image quotient defining cohomology. The latter vanishes for $r\notin I$ by Step 7. A sheaf zero on every $U$ is zero, since for any site object $P\to X$ its inverse images $P\times_XU$ cover it and every section restricting to zero is zero by the sheaf axiom. For $r\in I$, glue the finite constructible stratifications of the finitely many $\mathcal H^r(F)|_{U_i}$ as follows. Order the opens and replace the strata in $U_i$ by their intersections with $U_i\setminus\bigcup_{j<i}U_j$. These are finitely many locally closed constructible strata in $X$ (the opens here are quasi-compact, and the displayed difference is closed in $U_i$); they partition $X$. Pulling each local constant trivialization back to an intersection gives a local constant trivialization there with the same finite module, so the restrictions remain locally constant with finite stalks. This is precisely [def-weil-finite-torsion-constructibility]. Thus $F\in D_c^I(X,A)$ by [def-weil-constructible-intervals]. For any bounded constructible $K$, choose integers $a_0\leq b_0$ containing its finitely many nonzero cohomology degrees (choose $a_0=b_0=0$ when $K=0$). The first conclusion just proved, applied with $[a_0,b_0]$, gives bounded constructibility of $Rf^!K$.

Cited statements: prop-weil-pbc-proetale-constant-exact, def-weil-finite-torsion-constructibility, def-weil-constructible-intervals.

### Previous Step 9

Finally let $K\in D^b_{ctf}(Y,A)$ have Tor amplitude $[a,b]$, and put $F=Rf^!K$, which is bounded constructible by Step 8. For an arbitrary pro-etale $A$-module sheaf $M$ on $X$, the ambient finite-level tensor comparison of [lem-pur-derived-pullback-tensor-iso] gives
$$
 Lu^*(F\otimes_A^LM)\cong Lu^*F\otimes_A^L u^*M.
$$
The use of a sheaf $u^*M$ in degree zero is justified by [prop-weil-pbc-proetale-constant-exact]. The right side has no cohomology outside $I$ by the chartwise Tor bound of Steps 6–7. Exact restriction commutes with the kernel/image quotient defining cohomology. For $r\notin I$, every section of $\mathcal H^r(F\otimes_A^LM)$ over a site object $P\to X$ restricts to zero on all $P\times_XU$; these form a covering, so the sheaf axiom makes the section zero. Hence $\mathcal H^r(F\otimes_A^LM)=0$ for $r\notin I$. This is the Tor-amplitude condition of [def-weil-finite-tor-amplitude] for every $M$, including sheaves not of etale origin. Bounded constructibility of $F$ and this finite interval prove the second assertion and the stated $D^b_{ctf}$ preservation.

Cited statements: lem-pur-derived-pullback-tensor-iso, prop-weil-pbc-proetale-constant-exact, def-weil-finite-tor-amplitude.
