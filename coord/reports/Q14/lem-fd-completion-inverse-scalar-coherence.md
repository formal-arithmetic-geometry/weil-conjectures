# Worker report

1. Files written: dag/nodes/sec-fourier-transform/lem-fd-completion-inverse-scalar-coherence.json (existing statement unchanged; 1551-character assembly), and the following three statement-only nodes, all status unsplit, no proof steps, no Mathlib match:

- lem-fd-normalized-integral-completion-comparison: integral restriction, fixed quotient transport, descent normalization and exact shifts (old steps 1–3).
- lem-fd-integral-inverse-scalar-cocycle: normalization against the chosen associators, inverse cocycle, completeness/multiplication units (old steps 4–6).
- lem-fd-raw-localization-scalar-coherence: semilinear rationalization and both four-field contractions, including unit degeneracies (old steps 7–8).

2. Attachments: none. Read lean/Sheaf/Paper/FdCompletionInverseScalarCoherence.lean: WeilConjectures.fdCompletionInverseScalarCoherence ends in sorry. The project-wide upstream searches by blueprint tag and completion/inverse/scalar terminology found no finished declaration stating the item or a new task. Its FdCompletionIntegralComparison structure only defines data; it is not an existence theorem.

3. WANTED: none. The source is the available current blueprint, not SGA. Its trace definition supplies the final PBC coefficient-category sentence, not a proof of this auxiliary comparison. All auxiliary arguments are explicitly agent-written.

4. Returned fault repaired: the released 2026-10-22 keep_plan repair note reopens this previously reviewed node. Its 6571-character proof was too large. I retained its statement, statement dependencies and route and distributed the whole argument into three comparable tasks, rather than replacing it by a summary. Each new statement introduces its own fields, scheme, categories, maps and hypotheses. The original proof text is preserved below, with the assigned task and the exact old citations; no proof sketch is put into a new node's statement. No task restates the whole item: the first establishes only integral normalization/exactness; the second assumes the restricted comparisons and establishes only the integral associator/inverse/unit argument; the third assumes that integral data and establishes only its raw localization and four-field equations.

5. Unfinished work: the three new statements deliberately remain unsplit, for separate workers as ordered. No Lean was written or compiled. Required dry-run and push results are recorded by the delivery command.

## Not duplicates

lem-fd-normalized-integral-completion-comparison vs lem-weil-finite-free-completed-scalar-comparison: the existing ambient result supplies chi, not restriction to the two identified constructible categories together with exactness for their specified shifts and the coefficient-datum transport normalization.
lem-fd-normalized-integral-completion-comparison vs lem-weil-point-completed-scalar-shift: the existing result supplies the ambient cone shift equation, not the normalized exact integral restriction and presentation transport.
lem-fd-integral-inverse-scalar-cocycle vs lem-fix-scalar-completion-associator: the existing result supplies the forward ambient associator law and its pentagon; the new task identifies the chosen framework and PBC presentations and derives the inverse comparison law with normalized multiplication/completeness unit squares.
lem-fd-integral-inverse-scalar-cocycle vs lem-pur-completed-line-tensor-coherence: the existing statement concerns signed powers of an extra line and their tensor/evaluation comparisons; the new statement is about inverses of the coefficient completion maps between the two scalar systems and their chosen associators, without any extra line.
lem-fd-raw-localization-scalar-coherence vs lem-pur-semilinear-scalar-localization: the existing statement is generic extension through localization, not identification of the actual rational coefficient functors and specified lifts or the explicit two contractions of three successive comparison components.
lem-fd-raw-localization-scalar-coherence vs lem-weil-derived-field-scalar-extension-tower: that statement concerns derived vector spaces over fields, without completed coefficient sheaves or two distinct adic scalar systems.
All three new nodes vs lem-fd-rational-coefficient-category-comparison: that parent establishes the finite and common-stage equivalences and geometric pullback compatibility; these are the three internal arguments extracted under its existing completion-comparison child, and citing the parent would make a cycle.
All three new nodes vs lem-fd-whole-tower-integral-pullback-comparison: that sibling compares scheme pullbacks and whole-tower counits, assuming the scalar inverses; these nodes construct and organize only those scalar comparisons.

No new Stacks tag is asserted: these are extractions of the previously reviewed agent argument. Whole-DAG and blueprint searches were made for completion inverse, scalar comparison, four-field, quotient-map, inverse cocycle, semilinear and completion comparison. The blueprint hits defining Frobenius/Tate data do not state these auxiliary arguments. The PBC scalar-extension proposition is reused, not duplicated. The new ids were absent in the DAG before writing.

## Review by Q14

I read the current blueprint main-20261015 sec-fourier-transform/sk-def-trace/def-fd-trace-function.md, the chapter and unit records, the released repair note, and the entire retained eight-step proof and its reviewed Lean statement. The unit defines a trace with a PBC coefficient category; this extraction stays below that definition and keeps the original coefficient-comparison route. The blueprint does not furnish an independent literature proof, so the item's proof_origin remains agent and each new source explicitly identifies the old steps being extracted. I read the statements of every old proof input; the audit below records their exact uses. No Stacks section number or forbidden SGA route has been introduced.

Assembly step 1 uses exactly the first new task: its conclusion states restriction of chi and its inverse, generator-fixed transport, quotient coordinates, independence of representatives and exactness for the specified shifts. Its prime, finite coefficient extensions, noetherian finite-dimensional scheme and invertibility hypotheses are precisely those of the item. The integral identities are inputs in both statements, not newly asserted equivalences. The first task keeps the flat-term K-flat and actual cone-coordinate normalization, including zero shifted coordinate.

Assembly step 2 uses exactly the second task's inverse cocycle and normalized units. Its input b is the actual comparison of step 1. The normalized associator hypothesis is the item's hypothesis, and ordinary tensor transport fixes its PBC balancing. I read lem-fix-scalar-completion-associator: its statement supplies the actual quotient-cocone forward equality, resolution independence, pentagon and unit equations on any scheme. I read prop-weil-pbc-scalar-extension: its statement supplies ordinary integral balancing, its specified rational associator, shifts, unit equations and pentagon on the allowed scheme. These are the two generic tool citations in this assembly step, retained in split_report.tool_uses. No off-unit route is substituted.

Assembly step 3 uses exactly the third task. Its hypotheses on b, shifts and normalized lift come from step 1; its inverse equation and chosen associator identifications come from step 2; the associator pentagon/unit hypotheses were explicitly supplied in step 2. Its J is the given raw identity on objects and tensor morphisms, and its Q_L(b inverse) has the displayed source J_L S and target P J_E. It gives both four-field contractions, not merely an existence of a coherent replacement. The citations.json entries quote verbatim statement text, one for every cited node of every assembly step.

For small cases I checked K=0, empty T, shifts 0 and +1/-1, the base coefficient field, all three fields equal, and each repeated adjacent field alongside a proper extension. Zero and empty cases have the unique maps; the cone sign fixes the zero shifted coordinate at every integer shift; identity extension uses tensor multiplication and the completeness unit, not an unjustified literal equality U_E/E=id. The cocycle is well typed: both sides map U_M/L U_L/E K to C_M/E K. The four-field D maps J_3 S_32 S_21 S_10 to P_32 P_21 P_10 J_0, and both contractions end at P_30 J_0. Nonzero image of the source uniformizer becomes invertible in the final coefficient field, so semilinear localization applies. No extra constructibility or Tor hypothesis was added.

I checked B–E of delivery-errors.md: new nodes are statement-only, self-contained and sourced; all definitions are linked to existing nodes; searches are actual logged calls with second semantic phrasings; no statement was weakened; proof dependencies equal the assembly uses; citations use statements, not proofs. Each of the three assembly steps is below 2000 characters. Existing maintainer-owned fields are preserved. The first generated draft had a TeX newline replacement and a mistaken dependency extracted from K[m]; I corrected both before validation. No mathematical dispute was found.

Mathlib candidates were read in source: AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean:328) and AdicCompletion.map_exact concern ordinary finite modules, not the strict quotient tower in derived sheaves. NatTrans.CommShift.of_iso_inv (Mathlib/CategoryTheory/Shift/CommShift.lean:389) and Functor.isTriangulated_iff_of_iso (Mathlib/CategoryTheory/Triangulated/Functor.lean:265) handle a generic portion of the first argument, not the entire task. MonoidalCategory.associator_naturality (Mathlib/CategoryTheory/Monoidal/Category.lean:181) does not identify the two specified scalar associators. Loogle's initial localization query reported an unknown identifier; I retained that actual diagnostic and searched again for Functor.IsLocalization, which concerns generic categorical localization. The semantic searches returned adic modules, tensor associativity and module localization, none a one-line specialization of these tasks.

## Original arguments retained for the new workers

These are verbatim original step texts and their citations. They are handoff material in the report, not proof steps of the statement-only nodes. The allocation is exhaustive and non-overlapping: first task steps 1–3 (2628 characters), second task steps 4–6 (1980 characters), third task steps 7–8 (1963 characters).

### Original step 1 — lem-fd-normalized-integral-completion-comparison

Use the integral identity identifications in the hypothesis throughout. Write $C_{L/E}(K)=K\otimes^L_{R_E}R_L$ for ordinary extension and $U_{L/E}$ for framework strict-tower extension. The stratified-perfect characterization identifies both integral categories as the same full subcategory of $D(R_E)$. Finite-free constructible scalar transport puts $C_{L/E}K$ in the common category over $L$. Every such $K$ is derived complete, so the finite-free completed comparison supplies a natural isomorphism $b_{L/E,K}=\chi_{L/E,K}:C_{L/E}K\to U_{L/E}K$. Its target is in the same full category because it is isomorphic to $C_{L/E}K$. Thus $b$ and its inverse restrict to the integral categories; their naturality is the ambient derived naturality, not just naturality on chain maps.

Cited statements and hypothesis audit:

- lem-weil-pbc-integral-stratified-perfect-characterization (literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Definition 6.5.1; Proposition 6.6.11; Proposition 6.8.11(1),(3). Adapted to the explicitly retained compatible etale-origin witnesses and uniform reduction bounds of the DAG; those clauses must be verified, not identified by notation.):

Use the coefficient conventions of [def-weil-l-adic-coefficient-extension] and schemes of [def-pc-scheme]. Let $\ell$ be prime, let $E/\mathbf Q_\ell$ be finite with valuation ring $A=\mathcal O_E$ and uniformizer $\varpi$, and let $T$ be a noetherian finite-dimensional scheme on which $\ell$ is invertible. Here noetherian means that $T$ has a finite affine cover by spectra of noetherian rings, finite-dimensional means a finite bound on the lengths of strict chains of irreducible closed subsets, and invertible means that $\ell\cdot1$ is a unit in each local ring. Put $A_T=\varprojlim_n(A/\varpi^n)_T$ as in [def-weil-pbc-adic-coefficient-datum]. For $K\in D(\operatorname{Mod}(A_T))$ [def-weil-abstract-derived-category], the following conditions are equivalent: (i) $K$ belongs to [def-weil-pbc-bounded-constructible-complete], including its compatible etale-origin witnesses; (ii) there is a finite stratification [def-constructible-stratification] such that on each stratum $K$ is pro-etale locally isomorphic to $A_T\otimes_A^L P$ for a perfect $A$-complex $P$, meaning a bounded complex of finite projective $A$-modules; (iii) $K$ is bounded and every cohomology sheaf, after a finite stratification, is pro-etale locally $A_T\otimes_A N$ for a finitely presented $A$-module $N$. These conditions also describe exactly the category of [def-weil-derived-complete-integral-detailed] whenever that notation is used over such a $T$, with the same completed ring sheaf and reduction functors. This full subcategory is closed under shifts, cones, standard truncations and cohomology sheaves placed in degree zero.

- lem-weil-pbc-finite-free-constructible-scalar-transport (literature/blueprint/main-20261015/blueprint/sec-proper-base-change/sk-thm-properbasechange/prop-weil-pbc-scalar-extension.md, Exactness of T_{E'/E} (first display); the membership argument of the reviewed base proof step 1, through the stratified perfect characterization (ii) <=> (i). Agent lemma.):

Let $\ell$ be prime, let $E\subset E'$ be finite extensions of $\mathbf Q_\ell$ with valuation rings $A=\mathcal O_E\subset B=\mathcal O_{E'}$ and uniformizers $t=\varpi_E$, $v=\varpi_{E'}$ [def-weil-l-adic-coefficient-extension], and let $T$ be a noetherian finite-dimensional scheme on which $\ell$ is invertible [def-pc-scheme, def-weil-pbc-noetherian-ring], with its small pro-etale site [def-weil-pbc-proetale-site]. Put $R_T=\varprojlim_n(A/t^n)_T$ and $S_T=\varprojlim_m(B/v^m)_T$, the completed coefficient sheaves of [def-weil-pbc-adic-coefficient-datum], with the canonical ring map $R_T\to S_T$ induced by $A\subset B$. Let $\Dbc(T_{\Proet},A)\subset D(\operatorname{Mod}(R_T))$ and $\Dbc(T_{\Proet},B)\subset D(\operatorname{Mod}(S_T))$ be the full subcategories of [def-weil-pbc-bounded-constructible-complete] (derived completeness, uniformly bounded constructible reduction towers with common local models, and compatible etale-origin witnesses), and let $C(K)=K\otimes^L_{R_T}S_T$ be derived change of rings [lem-pur-derived-change-of-rings].

Then $C$ carries $\Dbc(T_{\Proet},A)$ into $\Dbc(T_{\Proet},B)$. More precisely, let $(T_k)$ be a finite stratification of $T$ [def-constructible-stratification] such that, on each stratum $T_k$ and pro-etale locally on it, $K$ is isomorphic to $R\otimes^L_AP$ for a bounded complex $P$ of finite projective $A$-modules (here $R$ is the completed sheaf of $A$ on that stratum). Then on the same strata and the same pro-etale localizations $C(K)$ is isomorphic to $S\otimes^L_B(B\otimes_AP)$, where $B\otimes_AP$ is a bounded complex of finite projective $B$-modules with the same amplitude as $P$; the isomorphism is the image under $C$ of the given one, composed with the balancing $(R\otimes_AP)\otimes_RS\cong S\otimes_B(B\otimes_AP)$.

- lem-weil-finite-free-completed-scalar-comparison (literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Lemma 6.8.2(1), pp. 58-59 (completed coefficient sheaves); Definition 3.4.10 and Lemma 3.4.12, pp. 22-23 (completed tensor and derived completeness); Proposition 3.5.1, p. 24 (completion as derived inverse limit). The finite-free coefficient-extension comparison is a consequence of these constructions, not a verbatim numbered lemma. Reduction of completed constant coefficients is Stacks Tag 093M, sites-modules.tex, lemma-completion-flat.):

Let $\ell$ be a prime, let $E\subset L$ be finite extensions of $\mathbf Q_\ell$ with valuation rings $\mathcal O_E\subset\mathcal O_L$ and uniformizers $t=\varpi_E$, $v=\varpi_L$ [def-weil-l-adic-coefficient-extension], and let $Y$ be any scheme. Work on its small pro-etale site [def-weil-pbc-proetale-site]. Write $R=\widehat{\mathcal O}_{E,Y}=\varprojlim_n(\mathcal O_E/t^n)_Y$ and $S=\widehat{\mathcal O}_{L,Y}=\varprojlim_m(\mathcal O_L/v^m)_Y$ for the completed coefficient sheaves [def-weil-completed-integral-coefficients], where $(-)_Y$ is the constant sheaf [def-weil-pbc-constant-sheaf]. The inclusions of valuation rings give a canonical map $R\to S$. The $R$-module sheaf $S$ is finite free of rank $[L:E]$.

For $T=R,S$, write $D(T)$ for the derived category of sheaves of $T$-modules [def-weil-sheaf-of-modules-category, def-weil-abstract-derived-category]. Let $K\in D(R)$ be derived $t$-complete [def-weil-derived-complete]. Form ordinary derived change of rings $K\otimes_R^L S$ [lem-pur-derived-change-of-rings]. The reductions $S\to(\mathcal O_L/v^m)_Y$ induce the canonical completion map
$$
 \chi_{L/E,K}:K\otimes_R^L S\longrightarrow
 R\varprojlim_m\operatorname{Res}^L_m\bigl(K\otimes_R^L(\mathcal O_L/v^m)_Y\bigr)
 =K\otimes_{\mathcal O_E}\mathcal O_L,
$$
Here $m\geq1$, $\operatorname{Res}^L_m$ is restriction of scalars along $S\to(\mathcal O_L/v^m)_Y$ [def-pc-sheaf-restrict-scalars], and $R\varprojlim$ denotes the strict-tower cone model specified in [def-weil-integral-scalar-extension], a derived limit [def-weil-derived-limit]. More explicitly, on a K-flat resolution $P\to K$ [def-pc-kflat-complex] the compatible quotient maps $P\otimes_R S\to\operatorname{Res}^L_m(P\otimes_R(\mathcal O_L/v^m)_Y)$ define a map to the product killed strictly by $1-s$; the induced map to $\operatorname{Cone}(1-s)[-1]$ has zero component in the shifted product. The map $\chi_{L/E,K}$ is the resulting morphism in $D(S)$, independent of the resolution. The last functor is exactly the strict-tower integral scalar extension of [def-weil-integral-scalar-extension], and the right side is interpreted as its derived-limit realization [lem-weil-integral-scalar-extension-well-defined]. This map is an isomorphism, natural in $K$, and $K\otimes_R^L S$ is derived $v$-complete. For $L=E$ it is the natural derived-completeness map $K\to R\varprojlim_n K\otimes_R^L(\mathcal O_E/t^n)_Y$, after the multiplication isomorphism $K\otimes_R^L R\cong K$.


### Original step 2 — lem-fd-normalized-integral-completion-comparison

Retain the specified map, rather than choose an isomorphism between its source and target. For a flat-term K-flat representative $P$, its $m$th quotient coordinate sends $p\otimes s$ to $p\otimes\bar s$ and its shifted-product coordinate is zero. Ordinary change of coefficient presentation sends each tensor generator to that same generator under the identity ring identifications. Hence its transport is the prescribed ordinary tensor transport, and the comparison with derived localization is exactly the quotient-completion map with the canonical resolving comparisons. The descent lemma applies with $R=\widehat{\mathcal O}_{E,T}$, $S=\widehat{\mathcal O}_{L,T}$ and $B_n=(\mathcal O_L/\varpi_L^n)_T$: these are commutative $S$-algebras with $S$-linear transitions, and countable products of $S$-module sheaves on the pro-etale site are exact by the countable-products lemma. It makes this equation independent of $P$. This verifies the integral-lift normalization requested by the definition of comparison datum; no existence assertion is being taken from that definition.

Cited statements and hypothesis audit:

- lem-weil-finite-free-completed-scalar-comparison (literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Lemma 6.8.2(1), pp. 58-59 (completed coefficient sheaves); Definition 3.4.10 and Lemma 3.4.12, pp. 22-23 (completed tensor and derived completeness); Proposition 3.5.1, p. 24 (completion as derived inverse limit). The finite-free coefficient-extension comparison is a consequence of these constructions, not a verbatim numbered lemma. Reduction of completed constant coefficients is Stacks Tag 093M, sites-modules.tex, lemma-completion-flat.):

Let $\ell$ be a prime, let $E\subset L$ be finite extensions of $\mathbf Q_\ell$ with valuation rings $\mathcal O_E\subset\mathcal O_L$ and uniformizers $t=\varpi_E$, $v=\varpi_L$ [def-weil-l-adic-coefficient-extension], and let $Y$ be any scheme. Work on its small pro-etale site [def-weil-pbc-proetale-site]. Write $R=\widehat{\mathcal O}_{E,Y}=\varprojlim_n(\mathcal O_E/t^n)_Y$ and $S=\widehat{\mathcal O}_{L,Y}=\varprojlim_m(\mathcal O_L/v^m)_Y$ for the completed coefficient sheaves [def-weil-completed-integral-coefficients], where $(-)_Y$ is the constant sheaf [def-weil-pbc-constant-sheaf]. The inclusions of valuation rings give a canonical map $R\to S$. The $R$-module sheaf $S$ is finite free of rank $[L:E]$.

For $T=R,S$, write $D(T)$ for the derived category of sheaves of $T$-modules [def-weil-sheaf-of-modules-category, def-weil-abstract-derived-category]. Let $K\in D(R)$ be derived $t$-complete [def-weil-derived-complete]. Form ordinary derived change of rings $K\otimes_R^L S$ [lem-pur-derived-change-of-rings]. The reductions $S\to(\mathcal O_L/v^m)_Y$ induce the canonical completion map
$$
 \chi_{L/E,K}:K\otimes_R^L S\longrightarrow
 R\varprojlim_m\operatorname{Res}^L_m\bigl(K\otimes_R^L(\mathcal O_L/v^m)_Y\bigr)
 =K\otimes_{\mathcal O_E}\mathcal O_L,
$$
Here $m\geq1$, $\operatorname{Res}^L_m$ is restriction of scalars along $S\to(\mathcal O_L/v^m)_Y$ [def-pc-sheaf-restrict-scalars], and $R\varprojlim$ denotes the strict-tower cone model specified in [def-weil-integral-scalar-extension], a derived limit [def-weil-derived-limit]. More explicitly, on a K-flat resolution $P\to K$ [def-pc-kflat-complex] the compatible quotient maps $P\otimes_R S\to\operatorname{Res}^L_m(P\otimes_R(\mathcal O_L/v^m)_Y)$ define a map to the product killed strictly by $1-s$; the induced map to $\operatorname{Cone}(1-s)[-1]$ has zero component in the shifted product. The map $\chi_{L/E,K}$ is the resulting morphism in $D(S)$, independent of the resolution. The last functor is exactly the strict-tower integral scalar extension of [def-weil-integral-scalar-extension], and the right side is interpreted as its derived-limit realization [lem-weil-integral-scalar-extension-well-defined]. This map is an isomorphism, natural in $K$, and $K\otimes_R^L S$ is derived $v$-complete. For $L=E$ it is the natural derived-completeness map $K\to R\varprojlim_n K\otimes_R^L(\mathcal O_E/t^n)_Y$, after the multiplication isomorphism $K\otimes_R^L R\cong K$.

- lem-pur-quotient-scalar-comparison-descent (literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Definition 3.4.10 and Proposition 3.5.1, pp. 22,24: completion via derived reduction towers. Explicit scalar augmentation and resolving-class descent are expanded here; not a verbatim assertion of the source.):

Let $R\to S$ be a map of commutative ring sheaves on a small site. Let $(B_n)_{n\geq1}$ be a strict inverse sequence of commutative $S$-algebras with $S$-linear transition maps, and assume countable products of $S$-module sheaves are exact. For a complex $P$ of $R$-modules put $F(P)=P\otimes_R S$ and $G(P)=\operatorname{Cone}(1-s:\prod_n\operatorname{Res}^S_{B_n}(P\otimes_R B_n)\to\prod_n\operatorname{Res}^S_{B_n}(P\otimes_R B_n))[-1]$, using restriction of scalars [def-pc-sheaf-restrict-scalars] and module-derived categories [def-weil-sheaf-of-modules-category, def-weil-abstract-derived-category]. There is a unique chain natural transformation $\beta:F\to G$ whose product projections send $p\otimes s$ to $p\otimes\bar s$ and whose shifted-product component is zero. The notation $\bar s$ means the image of $s$ in $B_n$, without a surjectivity assumption. On flat-term K-flat representatives [def-pc-kflat-complex], $F,G$ compute their everywhere-defined left derived functors $LF,LG$, and $\beta$ descends uniquely to $\chi:LF\to LG$ normalized by their universal comparison isomorphisms on those representatives. Thus $\chi$ is natural on the entire derived category and independent of the representative. For $S=R$ and $B_n=R/a^nR$, multiplication $P\otimes_R R\cong P$ identifies $\beta_P$ with the quotient unit having zero shifted-product component. All tensor products of module sheaves are sheafified tensor products [def-pur-sheaf-tensor-product], applied termwise to complexes when an ordinary tensor is written.

- lem-weil-proetale-countable-products-exact (literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Proposition 3.1.9 (countable products are exact in a replete topos), Proposition 3.2.3(1) (a locally weakly contractible topos is replete), Proposition 4.2.8 ($\Shv(X_{\mathrm{proet}})$ is locally weakly contractible); for modules over $\mathcal R$, products and surjectivity are those of the underlying abelian sheaves):

Let $Y$ be a scheme and $\mathcal R$ a sheaf of commutative rings on the small pro-etale site $Y_{\mathrm{proet}}$ [def-weil-pbc-proetale-site] (for instance a constant sheaf $A_Y$, or the completed coefficient sheaf $\widehat{\mathcal O}_{E,Y}$). Countable products exist in the category of sheaves of $\mathcal R$-modules on $Y_{\mathrm{proet}}$, are computed sectionwise, $(\prod_nF_n)(U)=\prod_nF_n(U)$, and are exact: if $F_n\to G_n$ is a surjection of sheaves of $\mathcal R$-modules for every $n\in\mathbf Z_{\geq1}$, then $\prod_nF_n\to\prod_nG_n$ is surjective.

- def-fd-coefficient-comparison-datum (literature/blueprint/main-20261015/blueprint/sec-fourier-transform/sk-def-trace/def-fd-trace-function.md, Final sentence: local Frobenius operators computed in the coefficient category def-weil-pbc-qbar-category; comparison with the framework finite stages used to define those operators):

Fix a prime $\ell$ and an algebraic closure $\Omega/\mathbf Q_\ell$. Let $T$ be noetherian, finite dimensional, with $\ell$ invertible. A coefficient comparison datum on $T$ means the following tuple; it asserts no existence. For every finite $E\subset\Omega$, it supplies equivalences of the integral full categories identified by [lem-weil-pbc-integral-stratified-perfect-characterization] and of their raw rationalizations [def-weil-rationalization-karoubi], [def-weil-pbc-rational-category]. The integral underlying functor is restriction along the quotient-normalized completed-coefficient isomorphism. The rational equivalence fixes integral objects and sends each pure tensor $e\otimes f$ to the same scalar and integral map; it is additive and exact in both directions, and its shift comparison is the localization of the canonical exact restriction-of-scalars shift. For every inclusion $E\subset L$, there is an ordinary tensor transport fixed on all tensor generators and an integral scalar comparison whose complex-localization equation is the specified quotient-map completion chain map of [lem-weil-finite-free-completed-scalar-comparison], with zero shifted-product component and the canonical derived counits. Its rationalization is a coherent morphism of the actual scalar systems [lem-weil-scalar-extension-composition], [prop-weil-pbc-scalar-extension]; its inverse is the scalar comparison $j$. The morphism satisfies the scalar associator cocycle, including identity inclusions, and commutes with shifts. Finally the datum contains an additive exact equivalence, exact also in the reverse direction, from the literal pair category [def-weil-algebraically-closed-coefficients] to [def-weil-pbc-qbar-category]. Its functor is the functor of this stage-system morphism: it preserves the field label, applies the finite equivalence, and conjugates a common-stage map by the two scalar comparisons. Its shift components are those induced by the finite-stage components. On every common-field representative it preserves multiplication by every element of that field, viewed in $\Omega$. No Karoubi completion occurs.


### Original step 3 — lem-fd-normalized-integral-completion-comparison

Ordinary derived change of rings is exact. The common integral category has the inherited distinguished triangles, so its restriction $C_{L/E}$ is exact. The completed-scalar shift lemma gives $\sigma^U_{m,K}b_{K[m]}=b_K[m]\sigma^C_{m,K}$ for every integer $m$ with the specified shifts. In its reordered cone the comparison is $(x,y)\mapsto(x,(-1)^m y)$; applying it to $(c(z),0)$ gives $(c(z),0)$, which is why no sign appears in the completion map itself. Consequently $\sigma^C_{m,K}b_{K[m]}^{-1}=b_K^{-1}[m]\sigma^U_{m,K}$. A triangle and its image under $U$ are identified by $b$ with its distinguished image under $C$, including the last arrow by this shift equation. Thus $U$ is exact with its specified shifts, and $b$ and $b^{-1}$ are exact natural isomorphisms.

Cited statements and hypothesis audit:

- lem-pur-derived-change-of-rings (literature/stacks-project/sites-cohomology.tex, Section 'Flat resolutions' (Tag 06YL): Lemma Tag 06YT (sites-cohomology-lemma-derived-tor-quasi-isomorphism-other-side) with $\mathcal F^\bullet=\mathcal O'$ in degree 0 for (1), and the construction before Definition Tag 06YU; Section 'Derived pullback' (Tag 06YV): Lemma Tag 06YY (sites-cohomology-lemma-derived-base-change) for the morphism of ringed topoi $(\Sh(\mathcal C),\mathcal O')\to(\Sh(\mathcal C),\mathcal O)$ given by the identity of $\Sh(\mathcal C)$ and $\varphi$, whose pullback $f^*$ is $-\otimes_{\mathcal O}\mathcal O'$, using literature/stacks-project/derived.tex, Lemma Tag 06XN (derived-lemma-find-existence-computes) for (2)):

Let $\mathcal C$ be a site and $\varphi:\mathcal O\to\mathcal O'$ a morphism of sheaves of commutative rings on $\mathcal C$; let $D(\mathcal O)$, $D(\mathcal O')$ be the derived categories [def-weil-abstract-derived-category] of the abelian categories of sheaves of $\mathcal O$-modules and of $\mathcal O'$-modules [def-weil-sheaf-of-modules-category]. For a complex $\mathcal P^\bullet$ of $\mathcal O$-modules write $\mathcal P^\bullet\otimes_{\mathcal O}\mathcal O'$ for the complex of $\mathcal O'$-modules obtained by applying the change of rings $-\otimes_{\mathcal O}\mathcal O'$ [def-pur-sheaf-tensor-product] termwise. Then: (1) if $\alpha:\mathcal P^\bullet\to\mathcal Q^\bullet$ is a quasi-isomorphism [def-pc-quasi-iso-modules] between K-flat complexes of $\mathcal O$-modules [def-pc-kflat-complex], the induced map $\alpha\otimes1:\mathcal P^\bullet\otimes_{\mathcal O}\mathcal O'\to\mathcal Q^\bullet\otimes_{\mathcal O}\mathcal O'$ is a quasi-isomorphism of complexes of $\mathcal O'$-modules; (2) consequently there is an exact functor of triangulated categories $L\varphi^*=-\otimes^{\mathbf L}_{\mathcal O}\mathcal O':D(\mathcal O)\to D(\mathcal O')$, the left derived functor of the termwise change of rings $K(\mathcal O)\to D(\mathcal O')$, $\mathcal G^\bullet\mapsto\mathcal G^\bullet\otimes_{\mathcal O}\mathcal O'$, which is everywhere defined and computed by K-flat complexes: for every K-flat resolution $\mathcal P^\bullet\to\mathcal G^\bullet$ [def-pc-kflat-complex, lem-pc-kflat-resolution] the canonical map $L\varphi^*\mathcal G^\bullet\to\mathcal P^\bullet\otimes_{\mathcal O}\mathcal O'$ (inverse of the map induced by the resolution) is an isomorphism in $D(\mathcal O')$, and for two K-flat resolutions $\mathcal P^\bullet\to\mathcal G^\bullet$, $\mathcal P'^\bullet\to\mathcal G^\bullet$ the resulting isomorphism $\mathcal P^\bullet\otimes_{\mathcal O}\mathcal O'\cong\mathcal P'^\bullet\otimes_{\mathcal O}\mathcal O'$ in $D(\mathcal O')$ is canonical (compatible with composition for a third resolution).

- lem-weil-integral-constructible-triangulated (literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Section 6.5, the sentence after Definition 6.5.1 ('It is immediate that D_cons(X_proet, R^) is a triangulated subcategory'), for the variant of the definition used in def-weil-derived-complete-integral-detailed; the derived-complete part is Stacks Project, the paragraph after the definition of derived completeness on a ringed site, Tag 0999 (literature/stacks-project/algebraization.tex lines 919-925); the blueprint states it inside the definition (literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/def-weil-derived-complete-integral-detailed.md)):

Fix a prime $\ell\neq p$, a finite extension $E/\Ql$ with valuation ring $\mathcal O_E$ and uniformizer $\varpi_E$, and a scheme $Y$. The full subcategory $D^b_c(Y,\mathcal O_E)$ of $D(Y_{\mathrm{proet}},\mathcal O_E)$ [def-weil-derived-complete-integral-detailed] is a triangulated subcategory: it contains a zero object, it is closed under isomorphisms and under the shifts $[m]$, $m\in\mathbf Z$, and for every distinguished triangle $K'\to K\to K''\to K'[1]$ of $D(Y_{\mathrm{proet}},\mathcal O_E)$ [def-weil-triangulated-category] with $K'$ and $K''$ in $D^b_c(Y,\mathcal O_E)$, also $K$ is in $D^b_c(Y,\mathcal O_E)$. Hence $D^b_c(Y,\mathcal O_E)$, with the shift and the distinguished triangles of $D(Y_{\mathrm{proet}},\mathcal O_E)$ lying in it, is a triangulated category and its inclusion is an exact functor.

- lem-weil-point-completed-scalar-shift (literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-admissible/def-weil-finite-coefficient-point.md, Final equivalence display: shift compatibility needed in its common-stage passage, made explicit by the retained item proof. Coefficient sheaves: Bhatt-Scholze Lemma 6.8.2(1), pp.58-59; strict tower model as in Stacks Tag 070M (derived.tex, lemma-difficulty-K-injectives). The asserted compatibility and sign formula are the extracted agent argument, not assertions of Bhatt-Scholze Lemma 6.8.2.):

Let $\ell$ be a prime and $E\subseteq L$ finite extensions of $\mathbf Q_\ell$ with valuation rings $\mathcal O_E\subseteq\mathcal O_L$ and uniformizers $t=\varpi_E$, $v=\varpi_L$ [def-weil-l-adic-coefficient-extension]. Let $Y$ be a scheme, with small pro-etale site [def-weil-pbc-proetale-site]. Write $R_F=\widehat{\mathcal O}_{F,Y}=\varprojlim_{j\geq1}(\mathcal O_F/\varpi_F^j)_Y$, $F=E,L$, for its completed coefficient sheaves [def-weil-completed-integral-coefficients], with the canonical map $R_E\to R_L$. Let $K\in D(R_E)$ be a derived $t$-complete complex of module sheaves [def-weil-abstract-derived-category, def-weil-sheaf-of-modules-category, def-weil-derived-complete]. Write $T_{L/E}K=K\otimes_{\mathcal O_E}\mathcal O_L$ for the strict-tower integral scalar extension [def-weil-integral-scalar-extension] and
$$
 \chi_K:K\otimes^L_{R_E}R_L\longrightarrow T_{L/E}K
$$
for the canonical quotient-map completion comparison of [lem-weil-finite-free-completed-scalar-comparison]. For every $m\in\mathbf Z$, this natural transformation commutes with cochain shift $[m]$.

More precisely, take a K-flat resolution $P\to K$ with flat terms [lem-pc-kflat-resolution], put $D(P)=\prod_{j\geq1}\operatorname{Res}^L_j(P\otimes_{R_E}(\mathcal O_L/v^j)_Y)$, and let $h_P=1-s_P$ where $s_P$ is induced by the quotient transitions. Here $\operatorname{Res}^L_j$ is restriction along $R_L\to(\mathcal O_L/v^j)_Y$ [def-pc-sheaf-restrict-scalars]. In the reordered cone $C(P)=\operatorname{Cone}(h_P)[-1]$ with $C(P)^r=D(P)^r\oplus D(P)^{r-1}$ and differential $(x,y)\mapsto(dx,-dy-h_Px)$, let $c:P\otimes_{R_E}R_L\to D(P)$ be the quotient maps, so that $\chi_P(z)=(c(z),0)$. The map
$$
 \alpha_{m,P}:C(P[m])\xrightarrow{\sim}C(P)[m],\qquad (x,y)\longmapsto(x,(-1)^m y)
$$
is a natural chain isomorphism, compatible with the standard zero-shift and successive-shift identifications, and satisfies $\alpha_{m,P}\chi_{P[m]}=\chi_P[m]$ after identifying $(P[m])\otimes_{R_E}R_L=(P\otimes_{R_E}R_L)[m]$. This identity descends to the stated shift compatibility of $\chi_K$ in $D(R_L)$, independently of the K-flat resolution.


### Original step 4 — lem-fd-integral-inverse-scalar-cocycle

Let $A^C_{M,L,E}:C_{M/L}C_{L/E}\to C_{M/E}$ be ordinary tensor associativity and $A^U$ the specified integral framework associator. The scalar-completion associator lemma gives
$$A^U_K\,U_{M/L}(b_{L/E,K})\,b_{M/L,C_{L/E}K}=b_{M/E,K}\,A^C_K.$$
Its maps use the actual quotient cocones and are resolution independent. The normalization in the hypothesis, as specified in the integral realization node, identifies this $A^U$ with the framework associator used here: it is the conjugate of this same $A^C$ by these same maps $b$. Thus the displayed equality holds for the chosen associator, not merely for some associator. Ordinary tensor transport in step 2 identifies $A^C$ with the integral balancing whose rationalization is the specified PBC associator.

Cited statements and hypothesis audit:

- lem-fix-scalar-completion-associator (literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-pf-reduction/lem-fix-operation-reduction.proof.md, Paragraph 3: transport to field stages by the specified scalar extensions; original split step 8, finite-free tensor/product-cone interchange and three-field tensor formula. Completion universal property: Stacks Tag 099B (algebraization.tex, lemma-derived-completion). Landing-return revalidation: def-weil-integral-scalar-extension, coefficient maps rho_m and explicit termwise Cone(1-s)[-1] construction; lem-weil-integral-scalar-extension-well-defined, resolution-independent functor.):

Fix a prime $\ell$, finite extensions $E\subset L\subset M$ of $\mathbf Q_\ell$, chosen uniformizers $t_F$ of their valuation rings $\mathcal O_F$, and a scheme $W$ [def-weil-l-adic-coefficient-extension, def-weil-pbc-proetale-site]. Put $R_F=\varprojlim_{n\ge1}(\mathcal O_F/t_F^n)_W$ [def-weil-completed-integral-coefficients]. On the unbounded derived categories of module sheaves [def-weil-sheaf-of-modules-category, def-weil-abstract-derived-category] write $C_{G/F}(K)=K\otimes^L_{R_F}R_G$ [lem-pur-derived-change-of-rings], and let
$$I_{G/F}(K)=R\varprojlim_n\operatorname{Res}^G_n(K\otimes^L_{R_F}(\mathcal O_G/t_G^n)_W)$$
be the specified product-cone scalar functor of [def-weil-integral-scalar-extension]. Explicitly, write $B_{G,n}=(\mathcal O_G/t_G^n)_W$. The coefficient map $\rho^{G/F}_n:R_F\to B_{G,n}$ is the projection to $(\mathcal O_F/t_F^n)_W$ followed by the constant-sheaf map induced by $\mathcal O_F\subset\mathcal O_G$. For a flat-term K-flat representative $P$ of $K$ [def-pc-kflat-complex, def-pc-flat-sheaf-modules], put $T_n=\operatorname{Res}^G_n(P\otimes_{R_F}B_{G,n})$, with transitions induced by $B_{G,n+1}\to B_{G,n}$ and restriction along $R_G\to B_{G,n}$ [def-pc-sheaf-restrict-scalars]. The chosen realization of $I_{G/F}(K)$ is $\operatorname{Cone}(1-s:\prod_nT_n\to\prod_nT_n)[-1]$ on termwise products, where $s((x_n)_n)=(t_n(x_{n+1}))_n$. Its resolution-independent functorial interpretation is [lem-weil-integral-scalar-extension-well-defined]. Let $\chi_{G/F}:C_{G/F}\to I_{G/F}$ be the actual quotient-cocone map with zero shifted-product component of [lem-weil-finite-free-completed-scalar-comparison]. Use derived completeness in the quotient-tower sense [def-weil-derived-complete].

On derived-complete inputs there are natural scalar associators
$$a^I_{M,L,E}:I_{M/L}I_{L/E}\xrightarrow{\sim}I_{M/E}.$$
They are the comparisons from termwise balanced tensor reassociation on the strict quotient systems, finite-free tensor/product-cone interchange, and cofinal replacement of uniformizer powers; in particular they use the actual quotient cocones defining $I$, rather than chosen isomorphisms of their values. With $a^C:C_{M/L}C_{L/E}\xrightarrow{\sim}C_{M/E}$ the ordinary balanced tensor associator, their normalization is the equality in $D(R_M)$
$$a^I_K\circ I_{M/L}(\chi_{L/E,K})\circ\chi_{M/L,C_{L/E}K}
=\chi_{M/E,K}\circ a^C_K.$$
These associators are independent of K-flat representatives and of cofinal exponent choices. They satisfy the pentagon for four nested fields and the unit equations under the multiplication and completeness identifications for $I_{F/F}$. No constructibility, cohomological bound, dimension or Noetherian hypothesis on $W$ is required.

- lem-trf-integral-pullback-comparison-realization (literature/stacks-project/proetale.tex, Tag 099N, lemma-pushforward-Noetherian-case (2),(5), completed pullback and quotient realization; with Tag 0D6D, sites-cohomology.tex, lemma-derived-pullback-composition. The simultaneous integral scalar/composition coherence is an extracted construction, not a verbatim assertion of either tag; blueprint prop-trf-karoubi-independence.proof.md, last sentence.):

Fix a prime $\ell$ and finite extensions $E\subset L$ of $\mathbf Q_\ell$ inside a fixed algebraic closure, with valuation rings $\mathcal O_F$, uniformizers $\varpi_F$ and $A_{F,n}=\mathcal O_F/\varpi_F^n$ for $F=E,L$ and $n\geq1$ [def-weil-l-adic-coefficient-extension]. Let $h:Z\to W$ and $k:W\to V$ be scheme morphisms, with $\ell$ invertible on these schemes [def-weil-scheme-morphism-properties]. Use the small pro-etale sites [def-weil-pbc-proetale-site], the completed coefficient sheaves $R_{F,U}=\varprojlim_n(A_{F,n})_U$ [def-weil-completed-integral-coefficients], the derived-complete constructible categories $\mathcal C_F(U)=D^b_c(U,\mathcal O_F)$ [def-weil-derived-complete-integral-detailed], the completed pullbacks $F_{f,F}=Lf_F^*$ [def-pur-integral-derived-operations], and the strict-tower scalar extensions $T_U=T_{L/E,U}$ [def-weil-integral-scalar-extension]. The finite module pullbacks use the canonical constant-coefficient identifications and the termwise composition maps $c_{h,k,n}$ of [lem-weil-pbc-proetale-derived-pullback-composition]. Realization means the functor $R\lim$ on the derived category of strict towers, or its $\operatorname{Cone}(1-s)[-1]$ model on the quotient complexes [lem-weil-pbc-ringed-strict-tower-homotopy-limit, def-pur-integral-derived-operations].

The following construction specifies comparison families, including the identifications used in their realization. For $K\in\mathcal C_E(V)$ take a flat-term K-flat representative $P\to K$ [lem-pc-kflat-resolution] and its simultaneous quotients $P_{F,n}=P\otimes_{R_{E,V}}(A_{F,n})_V$. For any such scheme map $f:U\to U'$ use the same notation for a representative $P$ on its target $U'$, and set
$$Q_{f,F}(P)_n=f^*P_{F,n},\qquad Q_{h,k,E}(P)_n=h^*k^*P_{E,n}.$$
Transitions are induced by the actual quotient maps, and restriction of scalars to the relevant completed coefficient sheaf is implicit. There are natural comparison isomorphisms
$$\eta_{h,k,K}:F_{h,E}F_{k,E}K\xrightarrow{\sim}R\lim Q_{h,k,E}(P),$$
$$\lambda_{f,K}:T_UF_{f,E}K\xrightarrow{\sim}R\lim Q_{f,L}(P),\qquad
\mu_{f,K}:F_{f,L}T_VK\xrightarrow{\sim}R\lim Q_{f,L}(P).$$
These comparisons use the derived-limit counit of the entire tower, with the following precise normalization. Write $\Delta$ for the constant-tower functor. For a strict tower complex $C_\bullet$, take a K-injective tower resolution $C_\bullet\to I_\bullet$ [def-pur-kinjective-complex] and define
$$\epsilon_C:\Delta R\lim C_\bullet\longrightarrow C_\bullet\quad\text{in }D(\operatorname{Tow}(\operatorname{Mod}(R)))$$
by the ordinary limit-cone map $\Delta\lim I_\bullet\to I_\bullet$, transported through that resolution. Here $R$ is the completed coefficient sheaf at the relevant scheme; this specifies the counit without discarding tower homotopies. Apply derived change of rings levelwise to this counit, then the quotient-module action maps (the counits of extension/restriction of scalars) and the tensor associators [lem-pur-derived-change-of-rings]. The resulting arrows are taken in the derived category of the whole quotient diagram. In detail, $\eta$ is the realization of $h^*$ applied to the resulting arrow from the $A_{E,\bullet}$-reduction tower of $F_{k,E}K$ to $k^*P_{E,\bullet}$; $\lambda$ is realization of the resulting arrow from the $A_{L,\bullet}$-coefficient tower of $F_{f,E}K$ to $f^*P_{L,\bullet}$, using $(f^*P_{E,n})\otimes^L_{A_{E,n}}A_{L,n}\cong f^*P_{L,n}$; $\mu$ is realization of $f^*$ applied to the resulting arrow from the $A_{L,\bullet}$-reduction tower of $T_VK$ to $P_{L,\bullet}$. The reduction and scalar towers here are precisely those of [def-pur-integral-derived-operations, def-weil-integral-scalar-extension]. The initial completion map from an uncompleted K-flat representative to its quotient cone has the quotient-map component in the unshifted product and zero component in the shifted product. The counit construction, rather than arbitrary individual reduction isomorphisms, supplies all iterated identifications. These constructions descend independently of the tower resolutions, K-flat representatives and common refinements, and the displayed $\eta,\lambda,\mu$ are isomorphisms. Put
$$c^E_{h,k,K}=\eta_{h,k,K}^{-1}\circ R\lim(c_{h,k,\bullet}):F_{kh,E}K\longrightarrow F_{h,E}F_{k,E}K,$$
$$a_{f,K}=\mu_{f,K}^{-1}\circ\lambda_{f,K}:T_UF_{f,E}K\longrightarrow F_{f,L}T_VK.$$
The source in the first formula is identified with $R\lim Q_{kh,E}(P)$ by the defining pullback construction. These formulas give natural isomorphisms and specify the choices of the integral composition and pullback scalar comparisons whose existence is asserted in [lem-pod-integral-pullback-composition, lem-pur-integral-operations-scalar-extension]. The analogous formula defines $c^L$.

With these specified families the composition/scalar equation is
$$F_{h,L}(a_{k,K})\circ a_{h,F_{k,E}K}\circ T_Z(c^E_{h,k,K})
=c^L_{h,k,T_VK}\circ a_{kh,K}.$$
The composition maps are associative and unital, and these equations respect equality of scheme morphisms and arbitrary finite iterations. For $E=L$ the scalar comparison is the identity under multiplication and completeness. For $E\subset L\subset M$, the comparisons respect the integral scalar associator obtained by conjugating the ordinary derived tensor associator by the specified completion maps $\chi$ of [lem-weil-finite-free-completed-scalar-comparison]. All the asserted equations are equalities of the transformations of simultaneous quotient diagrams before realization, transported by the displayed comparison maps. Their rationalizations give the same equations in the raw rationalized constructible categories [def-weil-rationalization-karoubi]. No finite Tor-amplitude hypothesis on the finite reductions is imposed.

- prop-weil-pbc-scalar-extension (literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/prop-weil-pbc-scalar-extension.md, node prop-weil-pbc-scalar-extension, order 1307):

Let $\ell$ be prime, let $E\subset E'$ be finite extensions of $\mathbf Q_\ell$, and let $T$ be a noetherian finite-dimensional scheme on which $\ell$ is invertible. Use the completed integral coefficient categories and their raw rationalizations $\Dbc(T,E)$ of [def-weil-pbc-rational-category], with no Karoubi envelope. Derived scalar extension means integral change of completed coefficient rings followed by scalar localization. Then it defines an exact functor
$$T_{E'/E}=E'\otimes_E^L-:\Dbc(T,E)\longrightarrow\Dbc(T,E').$$
Choose $T_{E/E}=\operatorname{id}$ literally. For $E\subset E'\subset E''$, balancing of derived tensor specifies an exact natural isomorphism
$$a_{E'',E',E}:T_{E''/E'}T_{E'/E}\xrightarrow{\sim}T_{E''/E}.$$
The associators satisfy the unit equations and the pentagon for four nested fields. There are canonical natural shift comparisons
$$\sigma_{E'/E,K}:T_{E'/E}(K[1])\xrightarrow{\sim}(T_{E'/E}K)[1]$$
commuting with these associators.

Write $C_{E'/E,T}(K)=K\otimes^L_{\widehat{\mathcal O}_{E,T}}\widehat{\mathcal O}_{E',T}$ for the integral ambient scalar-extension functor; its constructible restriction and rationalization is $T_{E'/E,T}$. For morphisms $f:X\to Y$ and $g:Y'\to Y$ between schemes satisfying the same scheme hypotheses, there are coherent comparisons on ambient derived-complete integral categories
$$C_{E'/E,Y}Rf_{*,\mathcal O_E}\xrightarrow{\sim}Rf_{*,\mathcal O_{E'}}C_{E'/E,X},\qquad
C_{E'/E,Y'}Lg^*_{\mathrm{comp},\mathcal O_E}\xrightarrow{\sim}Lg^*_{\mathrm{comp},\mathcal O_{E'}}C_{E'/E,Y}.$$
Their restrictions and rationalizations are comparisons on $\Dbc$ whenever the displayed operations preserve those constructible categories; no preservation assertion for arbitrary $f$ is implicit. Here ordinary direct image is the ringed-topos derived direct image, and completed pullback is [def-weil-pbc-completed-pullback]. For a cartesian square $(f,f',g,g')$ whose four schemes satisfy the stated hypotheses, the exchange is the canonical ambient ringed-topos mate of [def-weil-pbc-ambient-ringed-exchange], followed by derived completion and the direct-image/completion comparison, and then rationalization. Under the displayed comparisons, scalar extension of this $E$-exchange is this $E'$-exchange. The comparisons respect identity morphisms, composition, successive coefficient extensions and shifts.


### Original step 5 — lem-fd-integral-inverse-scalar-cocycle

Naturality of $b_{M/L}$ at $b_{L/E,K}$ rewrites the middle factors in step 4 as
$$U_{M/L}(b_{L/E,K})\,b_{M/L,C_{L/E}K}=b_{M/L,U_{L/E}K}\,C_{M/L}(b_{L/E,K}).$$
Insert this equality in step 4, multiply on the left by $b_{M/E,K}^{-1}$, and on the right by $C_{M/L}(b_{L/E,K}^{-1})\,b_{M/L,U_{L/E}K}^{-1}$. The result is precisely
$$A^C_K\,C_{M/L}(b_{L/E,K}^{-1})\,b_{M/L,U_{L/E}K}^{-1}=b_{M/E,K}^{-1}\,A^U_K.$$
Here functoriality sends $b^{-1}$ to the inverse of the image of $b$; all adjacent pairs cancel. This is the integral inverse-comparison cocycle, with the direction of every arrow fixed.

Cited statements and hypothesis audit:


### Original step 6 — lem-fd-integral-inverse-scalar-cocycle

For $L=E$, multiplication identifies $C_{E/E}$ with the identity, and the finite-free completed comparison identifies $b_{E/E}$ with the natural completeness unit $K\to U_{E/E}K$. Thus $b_{E/E}^{-1}$ is exactly the normalized unit $U_{E/E}\to\mathrm{id}$. The scalar-completion associator lemma supplies the unit equations with these multiplication/completeness identifications. Setting $L=E$ or $M=L$ in step 5 therefore gives the two unit comparison squares; with all fields equal it gives the identity square. This also covers a repeated field adjacent to a strict extension: no strict-inclusion hypothesis was used in steps 1–5.

Cited statements and hypothesis audit:

- lem-weil-finite-free-completed-scalar-comparison (literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Lemma 6.8.2(1), pp. 58-59 (completed coefficient sheaves); Definition 3.4.10 and Lemma 3.4.12, pp. 22-23 (completed tensor and derived completeness); Proposition 3.5.1, p. 24 (completion as derived inverse limit). The finite-free coefficient-extension comparison is a consequence of these constructions, not a verbatim numbered lemma. Reduction of completed constant coefficients is Stacks Tag 093M, sites-modules.tex, lemma-completion-flat.):

Let $\ell$ be a prime, let $E\subset L$ be finite extensions of $\mathbf Q_\ell$ with valuation rings $\mathcal O_E\subset\mathcal O_L$ and uniformizers $t=\varpi_E$, $v=\varpi_L$ [def-weil-l-adic-coefficient-extension], and let $Y$ be any scheme. Work on its small pro-etale site [def-weil-pbc-proetale-site]. Write $R=\widehat{\mathcal O}_{E,Y}=\varprojlim_n(\mathcal O_E/t^n)_Y$ and $S=\widehat{\mathcal O}_{L,Y}=\varprojlim_m(\mathcal O_L/v^m)_Y$ for the completed coefficient sheaves [def-weil-completed-integral-coefficients], where $(-)_Y$ is the constant sheaf [def-weil-pbc-constant-sheaf]. The inclusions of valuation rings give a canonical map $R\to S$. The $R$-module sheaf $S$ is finite free of rank $[L:E]$.

For $T=R,S$, write $D(T)$ for the derived category of sheaves of $T$-modules [def-weil-sheaf-of-modules-category, def-weil-abstract-derived-category]. Let $K\in D(R)$ be derived $t$-complete [def-weil-derived-complete]. Form ordinary derived change of rings $K\otimes_R^L S$ [lem-pur-derived-change-of-rings]. The reductions $S\to(\mathcal O_L/v^m)_Y$ induce the canonical completion map
$$
 \chi_{L/E,K}:K\otimes_R^L S\longrightarrow
 R\varprojlim_m\operatorname{Res}^L_m\bigl(K\otimes_R^L(\mathcal O_L/v^m)_Y\bigr)
 =K\otimes_{\mathcal O_E}\mathcal O_L,
$$
Here $m\geq1$, $\operatorname{Res}^L_m$ is restriction of scalars along $S\to(\mathcal O_L/v^m)_Y$ [def-pc-sheaf-restrict-scalars], and $R\varprojlim$ denotes the strict-tower cone model specified in [def-weil-integral-scalar-extension], a derived limit [def-weil-derived-limit]. More explicitly, on a K-flat resolution $P\to K$ [def-pc-kflat-complex] the compatible quotient maps $P\otimes_R S\to\operatorname{Res}^L_m(P\otimes_R(\mathcal O_L/v^m)_Y)$ define a map to the product killed strictly by $1-s$; the induced map to $\operatorname{Cone}(1-s)[-1]$ has zero component in the shifted product. The map $\chi_{L/E,K}$ is the resulting morphism in $D(S)$, independent of the resolution. The last functor is exactly the strict-tower integral scalar extension of [def-weil-integral-scalar-extension], and the right side is interpreted as its derived-limit realization [lem-weil-integral-scalar-extension-well-defined]. This map is an isomorphism, natural in $K$, and $K\otimes_R^L S$ is derived $v$-complete. For $L=E$ it is the natural derived-completeness map $K\to R\varprojlim_n K\otimes_R^L(\mathcal O_E/t^n)_Y$, after the multiplication isomorphism $K\otimes_R^L R\cong K$.

- lem-fix-scalar-completion-associator (literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-pf-reduction/lem-fix-operation-reduction.proof.md, Paragraph 3: transport to field stages by the specified scalar extensions; original split step 8, finite-free tensor/product-cone interchange and three-field tensor formula. Completion universal property: Stacks Tag 099B (algebraization.tex, lemma-derived-completion). Landing-return revalidation: def-weil-integral-scalar-extension, coefficient maps rho_m and explicit termwise Cone(1-s)[-1] construction; lem-weil-integral-scalar-extension-well-defined, resolution-independent functor.):

Fix a prime $\ell$, finite extensions $E\subset L\subset M$ of $\mathbf Q_\ell$, chosen uniformizers $t_F$ of their valuation rings $\mathcal O_F$, and a scheme $W$ [def-weil-l-adic-coefficient-extension, def-weil-pbc-proetale-site]. Put $R_F=\varprojlim_{n\ge1}(\mathcal O_F/t_F^n)_W$ [def-weil-completed-integral-coefficients]. On the unbounded derived categories of module sheaves [def-weil-sheaf-of-modules-category, def-weil-abstract-derived-category] write $C_{G/F}(K)=K\otimes^L_{R_F}R_G$ [lem-pur-derived-change-of-rings], and let
$$I_{G/F}(K)=R\varprojlim_n\operatorname{Res}^G_n(K\otimes^L_{R_F}(\mathcal O_G/t_G^n)_W)$$
be the specified product-cone scalar functor of [def-weil-integral-scalar-extension]. Explicitly, write $B_{G,n}=(\mathcal O_G/t_G^n)_W$. The coefficient map $\rho^{G/F}_n:R_F\to B_{G,n}$ is the projection to $(\mathcal O_F/t_F^n)_W$ followed by the constant-sheaf map induced by $\mathcal O_F\subset\mathcal O_G$. For a flat-term K-flat representative $P$ of $K$ [def-pc-kflat-complex, def-pc-flat-sheaf-modules], put $T_n=\operatorname{Res}^G_n(P\otimes_{R_F}B_{G,n})$, with transitions induced by $B_{G,n+1}\to B_{G,n}$ and restriction along $R_G\to B_{G,n}$ [def-pc-sheaf-restrict-scalars]. The chosen realization of $I_{G/F}(K)$ is $\operatorname{Cone}(1-s:\prod_nT_n\to\prod_nT_n)[-1]$ on termwise products, where $s((x_n)_n)=(t_n(x_{n+1}))_n$. Its resolution-independent functorial interpretation is [lem-weil-integral-scalar-extension-well-defined]. Let $\chi_{G/F}:C_{G/F}\to I_{G/F}$ be the actual quotient-cocone map with zero shifted-product component of [lem-weil-finite-free-completed-scalar-comparison]. Use derived completeness in the quotient-tower sense [def-weil-derived-complete].

On derived-complete inputs there are natural scalar associators
$$a^I_{M,L,E}:I_{M/L}I_{L/E}\xrightarrow{\sim}I_{M/E}.$$
They are the comparisons from termwise balanced tensor reassociation on the strict quotient systems, finite-free tensor/product-cone interchange, and cofinal replacement of uniformizer powers; in particular they use the actual quotient cocones defining $I$, rather than chosen isomorphisms of their values. With $a^C:C_{M/L}C_{L/E}\xrightarrow{\sim}C_{M/E}$ the ordinary balanced tensor associator, their normalization is the equality in $D(R_M)$
$$a^I_K\circ I_{M/L}(\chi_{L/E,K})\circ\chi_{M/L,C_{L/E}K}
=\chi_{M/E,K}\circ a^C_K.$$
These associators are independent of K-flat representatives and of cofinal exponent choices. They satisfy the pentagon for four nested fields and the unit equations under the multiplication and completeness identifications for $I_{F/F}$. No constructibility, cohomological bound, dimension or Noetherian hypothesis on $W$ is required.


### Original step 7 — lem-fd-raw-localization-scalar-coherence

Localize $b^{-1}$ over the final field, defining $j_{T,L/E}=Q_L(b_{L/E}^{-1})$. The raw rationalizations have the same objects and tensor-localized Hom groups. Their identity equivalences send each integral map and each scalar to itself, so the source is exactly $J_{T,L}S_{L/E}$ and the target is $P_{L/E}J_{T,E}$. Semilinear localization applies: the image of $\varpi_E$ is nonzero in $L=\mathcal O_L[1/\varpi_L]$, hence invertible. Both scalar functors are semilinear by coefficient multiplication on tensors; the comparison components are $R_L$-linear. The localization lemma preserves exact transformations, inverses, composition and whiskering. It therefore sends the inverse equation of step 5 to the displayed $a^p\,P(j)\,j=j\,J(a^s)$, and preserves the shift and unit equations. In particular the integral lift retained in step 2 is still the specified lift, not a newly chosen map.

Cited statements and hypothesis audit:

- def-weil-rationalization-karoubi (literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/def-weil-rationalization-karoubi.md, node def-weil-rationalization-karoubi, order 1460):

For the global finite-field datum [def-weil-finite-field-fiber], fix a prime
$\ell\neq p$, a finite extension $E/\Ql$ [def-weil-l-adic-coefficient-extension], a scheme $Y$, and a uniformizer
$\varpi_E$ of its valuation ring $\mathcal O_E$. The derived-complete
integral category [def-weil-derived-complete-integral-detailed] is
$D^b_c(Y,\mathcal O_E)$, built from the finite-torsion coefficients
[def-weil-finite-torsion-constructibility] $A_{E,n}=\mathcal
O_E/\varpi_E^n$; it is an $\mathcal O_E$-linear triangulated category with $\mathcal O_E$-linear shift [lem-weil-integral-constructible-triangulated, lem-weil-integral-constructible-linear]. If $\mathcal C$ is an $\mathcal O_E$-linear triangulated
category, its rationalization $\mathcal C[1/\varpi_E]$ is its scalar localization at $\varpi_E$ [def-weil-linear-scalar-localization]: it has the same objects
and, for $K,L\in\mathcal C$,

$$
 \Hom_{\mathcal C[1/\varpi_E]}(K,L)
 =\Hom_{\mathcal C}(K,L)\otimes_{\mathcal O_E}E,
$$

with the induced shift, and with distinguished triangles those isomorphic to images of distinguished triangles of $\mathcal C$; this makes $\mathcal C[1/\varpi_E]$ a triangulated category and $\mathcal C\to\mathcal C[1/\varpi_E]$ an exact functor [lem-weil-linear-scalar-localization-triangulated]. Set

$$
 D^b_c(Y,E)=
 D^b_c(Y,\mathcal O_E)[1/\varpi_E].
$$

No Karoubi (idempotent) completion is taken in this definition: the notation
$\mathcal C[1/\varpi_E]$ denotes the raw scalar localization displayed above,
in which no idempotent is formally adjoined. For $E=\Ql$, this uses $\mathcal
O_E=\Zl$ and $\varpi_E=\ell$.

If $E\subset L$ is a finite extension, the scalar-extension functor is

$$
 -\otimes_E L:D^b_c(Y,E)\longrightarrow D^b_c(Y,L),
$$

defined on integral representatives by the integral scalar extension
$K\mapsto K\otimes_{\mathcal O_E}\mathcal O_L$ [def-weil-integral-scalar-extension] (completed derived tensor product with $\mathcal O_L$, levelwise modulo powers of the
two uniformizers), which carries $D^b_c(Y,\mathcal O_E)$ into $D^b_c(Y,\mathcal O_L)$ [lem-weil-integral-scalar-extension-constructible], followed by rationalization: on objects $K\mapsto K\otimes_{\mathcal O_E}\mathcal O_L$, and on morphisms $f\otimes a\mapsto(f\otimes_{\mathcal O_E}\mathcal O_L)\otimes a$ for $f\in\Hom(K,M)$, $a\in E\subset L$, which is well defined because integral scalar extension is $\mathcal O_E$-linear.

- def-weil-pbc-rational-category (literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/def-weil-pbc-rational-category.md, node def-weil-pbc-rational-category, order 1305):

Let $T$ be a noetherian finite-dimensional scheme on which the torsion orders are invertible, as required for [def-weil-pbc-bounded-constructible-complete], and let $E/\Ql$ be finite, let $\mathcal O_E$ be its ring of integers, and let
$\varpi$ be a uniformizer. Define
$$
 \Dbc(T,E)=
 \Dbc(T,\mathcal O_E)[1/\varpi],
$$
the *rationalization* (raw scalar localization) of the integral category
[def-weil-pbc-bounded-constructible-complete]: it has the same objects as
$\Dbc(T,\mathcal O_E)$, and morphisms
$$
 \Hom(K,L)[1/\varpi]
 =\Hom_{\Dbc(T,\mathcal O_E)}(K,L)\otimes_{\mathcal O_E}E.
$$
No Karoubi envelope is taken in this definition. That the category is
idempotent complete, and that the canonical functor into the Karoubi
envelope is consequently an exact equivalence, is recorded with the other
properties of this construction.

- lem-weil-l-adic-integers-localization-uniformizer (literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/def-weil-rationalization-karoubi.md, node def-weil-rationalization-karoubi, the identification Hom ⊗_{O_E} E of the rationalization (implicit: O_E[1/ϖ_E]=E)):

Let $E/\Ql$ be a finite extension with valuation ring $\mathcal O_E$ and uniformizer $\varpi_E$ [def-weil-l-adic-coefficient-extension]. Then the inclusion $\mathcal O_E\subset E$ makes $E$ a localization of $\mathcal O_E$ at $\varpi_E$ [def-weil-ring-localization-away]: the induced ring map $\mathcal O_E[1/\varpi_E]\to E$, $x/\varpi_E^n\mapsto x\varpi_E^{-n}$, is an isomorphism. Consequently, for every $\mathcal O_E$-module $M$, $M\otimes_{\mathcal O_E}\mathcal O_E[1/\varpi_E]\cong M\otimes_{\mathcal O_E}E$ as $E$-modules. Here tensor products are tensor products of modules [def-weil-pbc-module-tensor-product], and the left-hand side has its $E$-module structure transported through the displayed ring isomorphism.

- lem-pur-semilinear-scalar-localization (literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-field-extension/prop-pur-rational-purity-transitivity-summands.proof.md, Proof, finite-extension sentence: scalar transport between different valuation rings; generic semilinear localization lemma extracted from old Step 3):

Let $R,S$ be commutative rings, $t\in R$, $u\in S$, and $\phi:R\to S$ a unital ring homomorphism such that the image of $\phi(t)$ is invertible in $S[1/u]$. Let $\mathcal C$ be an $R$-linear category and $\mathcal D$ an $S$-linear category [def-weil-linear-category], and use their raw scalar localizations and localization functors $Q_R,Q_S$ of [def-weil-linear-scalar-localization]. Call an additive functor $F:\mathcal C\to\mathcal D$ $\phi$-semilinear when $F(rf)=\phi(r)F(f)$ for every scalar $r$ and morphism $f$.

Every such $F$ has a unique additive extension $\overline F:\mathcal C[1/t]\to\mathcal D[1/u]$, with the same object map, agreeing with $Q_SF$ on integral arrows and semilinear for the induced map $R[1/t]\to S[1/u]$. On fractions it is
$$\overline F(f/t^n)=\phi(t)^{-n}Q_S(F(f)).$$
For two such functors $F,G$ every natural transformation $\eta:F\Rightarrow G$ extends uniquely with components $Q_S(\eta_K)$. Natural isomorphisms extend to natural isomorphisms. These extensions preserve identity transformations, vertical composition and whiskering by composable semilinear functors (with compatible coefficient homomorphisms and inverted elements); consequently every well-typed equation of such composites remains true. In particular, unit, associator, shift and comparison-square equations on integral functors remain equations after scalar localization.

If the categories carry linear triangulated structures [def-weil-triangulated-category], their localizations have the induced shifts and distinguished triangles isomorphic to localized integral distinguished triangles as in [lem-weil-linear-scalar-localization-triangulated], and $F$ is exact with a specified linear shift comparison, then $\overline F$ is exact with the localized shift comparison. The same assertion applies to exact natural comparison isomorphisms.


### Original step 8 — lem-fd-raw-localization-scalar-coherence

Finally take $E_0\subseteq E_1\subseteq E_2\subseteq E_3$ and abbreviate $S_{ba}=S_{E_b/E_a}$, $P_{ba}=P_{E_b/E_a}$, $J_b=J_{T,E_b}$ and $j_{ba}=j_{T,E_b/E_a}$. Suppressing component subscripts, the comparison from $J_3S_{32}S_{21}S_{10}$ to $P_{32}P_{21}P_{10}J_0$ is
$$D=(P_{32}P_{21}j_{10})(P_{32}j_{21}S_{10})(j_{32}S_{21}S_{10}).$$
Twice applying the cocycle of step 7, and moving the inner $j$ past an associator by naturality, identifies the two contractions of $D$ with
$$j_{30}J_3\bigl(a^s_{3,2,0}\,S_{32}(a^s_{2,1,0})\bigr),\qquad
j_{30}J_3\bigl(a^s_{3,1,0}\,(a^s_{3,2,1}S_{10})\bigr).$$
The scalar-completion associator law makes these equal, and localization preserves that law. The PBC associators have the corresponding coherence by their scalar-extension proposition. These are exactly the four-field compatibility diagram for the specified comparisons. The same substitutions with units give its degeneracies, since step 6 included equal fields. All manipulations here are substitution, naturality and cancellation of already supplied natural isomorphisms.

Cited statements and hypothesis audit:

- lem-fix-scalar-completion-associator (literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-pf-reduction/lem-fix-operation-reduction.proof.md, Paragraph 3: transport to field stages by the specified scalar extensions; original split step 8, finite-free tensor/product-cone interchange and three-field tensor formula. Completion universal property: Stacks Tag 099B (algebraization.tex, lemma-derived-completion). Landing-return revalidation: def-weil-integral-scalar-extension, coefficient maps rho_m and explicit termwise Cone(1-s)[-1] construction; lem-weil-integral-scalar-extension-well-defined, resolution-independent functor.):

Fix a prime $\ell$, finite extensions $E\subset L\subset M$ of $\mathbf Q_\ell$, chosen uniformizers $t_F$ of their valuation rings $\mathcal O_F$, and a scheme $W$ [def-weil-l-adic-coefficient-extension, def-weil-pbc-proetale-site]. Put $R_F=\varprojlim_{n\ge1}(\mathcal O_F/t_F^n)_W$ [def-weil-completed-integral-coefficients]. On the unbounded derived categories of module sheaves [def-weil-sheaf-of-modules-category, def-weil-abstract-derived-category] write $C_{G/F}(K)=K\otimes^L_{R_F}R_G$ [lem-pur-derived-change-of-rings], and let
$$I_{G/F}(K)=R\varprojlim_n\operatorname{Res}^G_n(K\otimes^L_{R_F}(\mathcal O_G/t_G^n)_W)$$
be the specified product-cone scalar functor of [def-weil-integral-scalar-extension]. Explicitly, write $B_{G,n}=(\mathcal O_G/t_G^n)_W$. The coefficient map $\rho^{G/F}_n:R_F\to B_{G,n}$ is the projection to $(\mathcal O_F/t_F^n)_W$ followed by the constant-sheaf map induced by $\mathcal O_F\subset\mathcal O_G$. For a flat-term K-flat representative $P$ of $K$ [def-pc-kflat-complex, def-pc-flat-sheaf-modules], put $T_n=\operatorname{Res}^G_n(P\otimes_{R_F}B_{G,n})$, with transitions induced by $B_{G,n+1}\to B_{G,n}$ and restriction along $R_G\to B_{G,n}$ [def-pc-sheaf-restrict-scalars]. The chosen realization of $I_{G/F}(K)$ is $\operatorname{Cone}(1-s:\prod_nT_n\to\prod_nT_n)[-1]$ on termwise products, where $s((x_n)_n)=(t_n(x_{n+1}))_n$. Its resolution-independent functorial interpretation is [lem-weil-integral-scalar-extension-well-defined]. Let $\chi_{G/F}:C_{G/F}\to I_{G/F}$ be the actual quotient-cocone map with zero shifted-product component of [lem-weil-finite-free-completed-scalar-comparison]. Use derived completeness in the quotient-tower sense [def-weil-derived-complete].

On derived-complete inputs there are natural scalar associators
$$a^I_{M,L,E}:I_{M/L}I_{L/E}\xrightarrow{\sim}I_{M/E}.$$
They are the comparisons from termwise balanced tensor reassociation on the strict quotient systems, finite-free tensor/product-cone interchange, and cofinal replacement of uniformizer powers; in particular they use the actual quotient cocones defining $I$, rather than chosen isomorphisms of their values. With $a^C:C_{M/L}C_{L/E}\xrightarrow{\sim}C_{M/E}$ the ordinary balanced tensor associator, their normalization is the equality in $D(R_M)$
$$a^I_K\circ I_{M/L}(\chi_{L/E,K})\circ\chi_{M/L,C_{L/E}K}
=\chi_{M/E,K}\circ a^C_K.$$
These associators are independent of K-flat representatives and of cofinal exponent choices. They satisfy the pentagon for four nested fields and the unit equations under the multiplication and completeness identifications for $I_{F/F}$. No constructibility, cohomological bound, dimension or Noetherian hypothesis on $W$ is required.

- prop-weil-pbc-scalar-extension (literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/prop-weil-pbc-scalar-extension.md, node prop-weil-pbc-scalar-extension, order 1307):

Let $\ell$ be prime, let $E\subset E'$ be finite extensions of $\mathbf Q_\ell$, and let $T$ be a noetherian finite-dimensional scheme on which $\ell$ is invertible. Use the completed integral coefficient categories and their raw rationalizations $\Dbc(T,E)$ of [def-weil-pbc-rational-category], with no Karoubi envelope. Derived scalar extension means integral change of completed coefficient rings followed by scalar localization. Then it defines an exact functor
$$T_{E'/E}=E'\otimes_E^L-:\Dbc(T,E)\longrightarrow\Dbc(T,E').$$
Choose $T_{E/E}=\operatorname{id}$ literally. For $E\subset E'\subset E''$, balancing of derived tensor specifies an exact natural isomorphism
$$a_{E'',E',E}:T_{E''/E'}T_{E'/E}\xrightarrow{\sim}T_{E''/E}.$$
The associators satisfy the unit equations and the pentagon for four nested fields. There are canonical natural shift comparisons
$$\sigma_{E'/E,K}:T_{E'/E}(K[1])\xrightarrow{\sim}(T_{E'/E}K)[1]$$
commuting with these associators.

Write $C_{E'/E,T}(K)=K\otimes^L_{\widehat{\mathcal O}_{E,T}}\widehat{\mathcal O}_{E',T}$ for the integral ambient scalar-extension functor; its constructible restriction and rationalization is $T_{E'/E,T}$. For morphisms $f:X\to Y$ and $g:Y'\to Y$ between schemes satisfying the same scheme hypotheses, there are coherent comparisons on ambient derived-complete integral categories
$$C_{E'/E,Y}Rf_{*,\mathcal O_E}\xrightarrow{\sim}Rf_{*,\mathcal O_{E'}}C_{E'/E,X},\qquad
C_{E'/E,Y'}Lg^*_{\mathrm{comp},\mathcal O_E}\xrightarrow{\sim}Lg^*_{\mathrm{comp},\mathcal O_{E'}}C_{E'/E,Y}.$$
Their restrictions and rationalizations are comparisons on $\Dbc$ whenever the displayed operations preserve those constructible categories; no preservation assertion for arbitrary $f$ is implicit. Here ordinary direct image is the ringed-topos derived direct image, and completed pullback is [def-weil-pbc-completed-pullback]. For a cartesian square $(f,f',g,g')$ whose four schemes satisfy the stated hypotheses, the exchange is the canonical ambient ringed-topos mate of [def-weil-pbc-ambient-ringed-exchange], followed by derived completion and the direct-image/completion comparison, and then rationalization. Under the displayed comparisons, scalar extension of this $E$-exchange is this $E'$-exchange. The comparisons respect identity morphisms, composition, successive coefficient extensions and shifts.

- lem-pur-semilinear-scalar-localization (literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-field-extension/prop-pur-rational-purity-transitivity-summands.proof.md, Proof, finite-extension sentence: scalar transport between different valuation rings; generic semilinear localization lemma extracted from old Step 3):

Let $R,S$ be commutative rings, $t\in R$, $u\in S$, and $\phi:R\to S$ a unital ring homomorphism such that the image of $\phi(t)$ is invertible in $S[1/u]$. Let $\mathcal C$ be an $R$-linear category and $\mathcal D$ an $S$-linear category [def-weil-linear-category], and use their raw scalar localizations and localization functors $Q_R,Q_S$ of [def-weil-linear-scalar-localization]. Call an additive functor $F:\mathcal C\to\mathcal D$ $\phi$-semilinear when $F(rf)=\phi(r)F(f)$ for every scalar $r$ and morphism $f$.

Every such $F$ has a unique additive extension $\overline F:\mathcal C[1/t]\to\mathcal D[1/u]$, with the same object map, agreeing with $Q_SF$ on integral arrows and semilinear for the induced map $R[1/t]\to S[1/u]$. On fractions it is
$$\overline F(f/t^n)=\phi(t)^{-n}Q_S(F(f)).$$
For two such functors $F,G$ every natural transformation $\eta:F\Rightarrow G$ extends uniquely with components $Q_S(\eta_K)$. Natural isomorphisms extend to natural isomorphisms. These extensions preserve identity transformations, vertical composition and whiskering by composable semilinear functors (with compatible coefficient homomorphisms and inverted elements); consequently every well-typed equation of such composites remains true. In particular, unit, associator, shift and comparison-square equations on integral functors remain equations after scalar localization.

If the categories carry linear triangulated structures [def-weil-triangulated-category], their localizations have the induced shifts and distinguished triangles isomorphic to localized integral distinguished triangles as in [lem-weil-linear-scalar-localization-triangulated], and $F$ is exact with a specified linear shift comparison, then $\overline F$ is exact with the localized shift comparison. The same assertion applies to exact natural comparison isomorphisms.


## Original-step hypothesis audit

Original step 1: The characterization explicitly says the detailed/framework and PBC conditions describe the same full subcategory. Scalar transport gives preservation by ordinary tensor; finite-free chi is natural on derived-complete inputs. These are the allowed T and complete K in the task.

Original step 2: Quotient descent explicitly requires exact countable products; on the small pro-etale site the cited product theorem supplies this for R_L-module sheaves. B_n are commutative R_L-algebras with linear transitions. The datum is used only to specify a normalization, never as an existence theorem.

Original step 3: Derived change of rings gives an exact functor; the integral subcategory inherits triangles and is replete. The shift statement explicitly gives the signed reordered cone and its equality on chi, hence on its inverse. This identifies the last triangle arrow and justifies exactness.

Original step 4: The scalar associator statement supplies precisely the displayed equality; the realization statement explicitly specifies conjugation by the same chi. The PBC proposition states that its rational associator is integral balancing. No unspecified associator is substituted.

Original step 5: This is naturality and cancellation of the given natural isomorphisms. I checked the domain/codomain of the inner component and the order of inverse factors; functoriality preserves inverses.

Original step 6: The finite-free statement explicitly identifies equal-field chi with completeness after tensor multiplication. The associator statement supplies the unit equations, so both substitutions and the all-equal case are legitimate.

Original step 7: The rationalization definitions give the same objects and localized Hom groups. The uniformizer localization theorem identifies O_L[1/varpi_L] with L. Its nonzero source uniformizer image is invertible there; ordinary and completed tensor are semilinear and b is target-linear. The semilinear lemma states preservation of exact transformations, identities, inverses, vertical composition, whiskering and shift/comparison equations.

Original step 8: The two contractions are obtained by two uses of the inverse cocycle and naturality; the existing scalar associator pentagons equate them, and semilinear localization preserves that equation. Unit substitutions from step 6 cover repeated fields. No additional mathematical input is hidden.


## Dry-run repair

The first substantive preflight flagged the phrase “The item's” in assembly step 2 under B2. I replaced that phrase by the explicit assumed framework-associator normalization; all objects and hypotheses are introduced in the statement. The assembly remains below 3000 characters.
