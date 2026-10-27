# Worker report: Q136 / lem-sf-proper-open-projection-mate

## Files written

- Item: unchanged statement and Lean attachments; three assembly steps, 1764 characters total.
- lem-sf-clopen-comparison-tensor-square: statement, unsplit; Mathlib has generic mates and ordinary pullback statements, not the three mixed-action equalities.
- lem-sf-tensor-square-mate-transfer: statement, unsplit; Mathlib has mate/counit formulae but not this mixed action transfer with the stated common transpose.
- citations.json: exact statement excerpts for every citation in the assembly.

## Attachments

None. No matching project declaration was found under lean/WeilConjectures by item tag or concept. The actual item declarations in lean/Sheaf/SixFunctors/ProperOpenProjectionMate.lean:322 and :377 have sorry at :340 and :408. The upstream ProjectionMapCompat.rightAdjointProjectionMap_mate concerns full colax tensor comparisons on U,V; our new transfer uses mixed action maps JH tensor N and KM tensor V, so it is not an attachment or one-line specialization. No Lean was changed or compiled.

## WANTED

None.

## Return repaired

The sandbox initially contained only dispatcher marker files, no earlier report, node or searches. I recovered the returned eight-step argument from the current shared repository, matching all eight lengths and the 7224-character return. No repository git command or write was used. The parent statement is byte-for-byte unchanged as a JSON string. The two new nodes are strictly smaller tasks: one proves the tensor square before mates, the other takes that square as hypothesis and proves the categorical transfer by two transposes. Both have empty proof and proof_deps and status unsplit. They are comparable proof tasks (old steps 1–3 versus old steps 4–6); neither is a clause of the parent stated without an intermediate hypothesis. The system identification already has an existing more general node, so it is reused rather than duplicated. Its dependency closure was checked and does not reach this item. The existing lem-pur-system-clopen-tensor-compatibility and lem-sf-proper-open-tensor-compatibility instead depend on this item and were not cited.

## Argument ownership and preserved returned proof

New tensor-square node owns all of steps 1–3: geometric factorization and open normalizations, the beta tensor square reduced by full faithfulness, the (1,0) clopen calculation, agreement of composite-open deltas, and their alpha equation. New mate-transfer node owns steps 4–6: the left transpose via naturality of alpha, the right transpose via naturality of mu and delta, equality with K(c) alpha Pp(delta_i), injectivity of the Hom bijection, naturality, and absence of boundedness or Tor conditions. Existing lem-sf-semilinear-proper-open-mate-pasting owns step 7's intrinsic open restriction normalization, including the triangle identity. Step 8 is the application of these same results on the ringed sequence sites, now assembly step 3; it is not an evaluated equality argument. The original detailed arguments follow verbatim for future workers; they are not proof sketches hidden in the new statements.

### Returned step 1

Use [lem-cbc-strict-tower-proper-open-calculus] for the geometry of the square: $s=(k,r):A\to B_C$ is clopen, $bs=k$, $qs=r$, and $\alpha$ is exactly the specified base-change map followed by projection onto $s(A)$. This geometric assertion has no hypothesis on an input complex. Write $J=i_!$, $K=k_!$, $E=R_rM$, $X=P_iN$, $Y=P_pN$, and $T=P_rX=P_kY$. All tensors below are derived; canonical pullback/tensor identifications are understood. For an open $j$ write $\delta_j(U,V):j_!U\otimes V\to j_!(U\otimes P_jV)$. The normalizations in [lem-sf-open-tensor-normalization] make these maps and the open base-change map identities after restriction and the open units.

### Returned step 2

First check the tensor square for the base-change factor $\beta:P_pJ\to b_!P_q$. For arbitrary $H$ on $C$, its two routes have source $P_p(JH\otimes N)$ and target $b_!(P_qH\otimes P_bY)$: one applies $P_p\delta_i$, then $\beta_{H\otimes X}$ and the pullback tensor comparison; the other applies $\mu_p$, then $\beta_H\otimes1_Y$ and $\delta_b$. Both source and target lie in the image of $b_!$: use $\beta_H$ and the open tensor isomorphism to identify the source with $b_!(P_qH\otimes P_bY)$. Thus full faithfulness of $b_!$ reduces equality to restriction by $P_b$. Under the open units, $P_b\beta$ and $P_i\delta_i$ are identities. The remaining maps on both routes are the canonical pullback/tensor comparison on $P_qH\otimes P_bY$, using $P_bP_p=P_qP_i$. Hence the square commutes. Here the comparison is the canonical one for the commutative ringed pullback square, as in [lem-weil-pbc-ringed-exchange-tensor-coherence].

### Returned step 3

The clopen-projection factor also respects tensor: in $B_C=s(A)\amalg(B_C\setminus s(A))$, $\pi_s$ acts by $(1,0)$. Tensoring it with $P_bY$ still acts by $(1,0)$ on the two components. The open tensor comparison for $s$ restricts to the identity on $s(A)$; on the complementary component its target is zero. Consequently projection before tensor and projection after tensor agree, followed by $\delta_s$. This is an identity of the given termwise clopen projections on complexes and hence of their derived classes, using the canonical tensor comparisons. The comparisons for the composite open $bs=k$ agree with $\delta_k$: both are maps between objects in the image of $k_!$, and after restriction to $k$ they are identities, so full faithfulness gives equality. Combining this calculation with Step 2 gives, for every $H$ on $C$, the explicit identity
$$K(\mu_r)\,\alpha_{H\otimes X}\,P_p(\delta_i)=\delta_k\,(\alpha_H\otimes1_Y)\,\mu_p.$$
Both sides run from $P_p(JH\otimes N)$ to $K(P_rH\otimes T)$.

### Returned step 4

Put $Z=M\otimes T$ and $a_r=(\varepsilon_{r,M}\otimes1_T)\mu_r:P_r(E\otimes X)\to Z$. The counit definition of $\pi_r$ gives $\varepsilon_{r,Z}P_r(\pi_r)=a_r$. The mate definition of $\gamma$ gives $\varepsilon_{p,KW}P_p(\gamma_W)=K(\varepsilon_{r,W})\alpha_{R_rW}$ for every $W$. Therefore the transpose under $P_p\dashv R_p$ of the left side of the claimed identity is
$$K(\varepsilon_{r,Z})\,\alpha_{R_rZ}\,P_pJ(\pi_r)\,P_p\delta_i
=K(\varepsilon_{r,Z}P_r\pi_r)\,\alpha_{E\otimes X}\,P_p\delta_i
=K(a_r)\,\alpha_{E\otimes X}\,P_p\delta_i.$$
The middle equality is naturality of $\alpha$ for the arrow $\pi_r:E\otimes X\to R_rZ$.

### Returned step 5

Transpose the right side under the same adjunction. Naturality of $\varepsilon_p$ first moves $R_p\delta_k$ out of the transpose; the defining adjunct equation of $\pi_p$ then gives
$$\delta_k\,(\varepsilon_{p,KM}\otimes1_Y)\,\mu_p\,P_p(\gamma_M\otimes1_N).$$
Naturality of $\mu_p$ replaces this by
$$\delta_k\,((\varepsilon_{p,KM}P_p\gamma_M)\otimes1_Y)\,\mu_p
=\delta_k\,((K\varepsilon_{r,M}\,\alpha_E)\otimes1_Y)\,\mu_p.$$
Now apply naturality of $\delta_k$ to $\varepsilon_{r,M}:P_rE\to M$, and then the identity of Step 3 with $H=E$. The result is
$$K(\varepsilon_{r,M}\otimes1_T)\,K(\mu_r)\,\alpha_{E\otimes X}\,P_p\delta_i
=K(a_r)\,\alpha_{E\otimes X}\,P_p\delta_i,$$
which is the transpose computed in Step 4. The adjunction Hom bijection is injective, so the original maps agree. All substitutions are natural in $M,N$.

### Returned step 6

These calculations use arbitrary inputs in the unbounded ringed-site derived categories. In particular [lem-weil-pbc-ringed-projection-mate-exact] supplies the counit-defined map for arbitrary sheaves of commutative rings and all objects, so the use of its formula does not specialize the finite ring $\Lambda$ to a quotient DVR or impose invertibility of its order. [lem-sf-open-tensor-normalization] also has no boundedness or Tor hypothesis. We never invert $\pi_p$, $\pi_r$ or $\gamma$, nor invoke a proper projection formula or proper base-change isomorphism on these inputs. This proves precisely the finite constant-coefficient identity claimed.

### Returned step 7

We identify the stipulated system $\Gamma_Q$ intrinsically, rather than from its finite evaluations. Let $\widetilde\gamma$ be the proper-adjunction mate of the clopen $\alpha$. The realization node characterizes $\Gamma_Q$ by $\lambda_QP_i\Gamma_Q=1$ under the open unit, where $\lambda_Q:P_iS_pJ_k\cong S_r$ is obtained by open restriction, $k=bs$, $J_s=S_s$ for the clopen $s$, and direct-image composition. Make exactly those identifications in $P_i\widetilde\gamma$. Mate pasting identifies the restricted unit/counit maps with the unit/counit of $P_r\dashv S_r$; the restricted open base-change map is the identity by open normalization, and the clopen projection acts as identity on $J_sM$. Thus the composite $\lambda_QP_i\widetilde\gamma$ is $S_r\varepsilon_r\circ\eta_rS_r=1_{S_r}$ by the triangle identity. Since $J_i\dashv P_i$ gives a bijection on the relevant Hom sets, its adjunct characterization implies $\widetilde\gamma=\Gamma_Q$. This argument uses only the intrinsic open-restriction characterization and canonical composite adjunctions, and is independent of the total-limit comparisons or the finite evaluated arrows.

### Returned step 8

For the system assertion, apply Steps 1--5 inside the unbounded derived module categories of the ringed diagram sites themselves. [lem-pur-coefficient-system-derived-comparison] supplies the exact system inverse images and their derived adjunctions on these unbounded categories. [lem-sf-open-tensor-normalization] explicitly supplies the same open-unit, tensor and base-change normalization on the diagram topoi. The operations and intrinsic $\Gamma_Q$ are the simultaneous ringed-diagram constructions stipulated in [lem-sf-integral-compactification-system-realization]; Step 7 identifies $\Gamma_Q$ with the proper mate of the same clopen-projection $\alpha$. Thus the system analogue of the mate equation in Step 4 is an equation in the system category. On system complexes the clopen projection in Step 3 is literally identity on the open component and zero on its complement; these are morphisms of systems, compatible with every coefficient transition. Steps 4--5 now compare the two system maps by the single system adjunction Hom bijection and the displayed common transpose, before applying any evaluation. The generic ringed tensor/projection nodes apply to these small ringed diagram sites without change. Only the unbounded operations and intrinsic-map clauses of the realization node are used; no total-limit realization or constructible-domain claim is needed.

## Review by Q136

I read the unchanged statement, all eight returned steps, the chapter sec-six-functors and summary unit sk-rem-sf-pf-done (which has no proof steps), and the current main-20261015 fix-prop-projection-formula.proof.md sentence on composition/refinement/exchange/proper coincidence. The source context is more-etale.tex Tag 0F7B (lemma-shriek-proper-and-open) and 0F7C/0F7D for pasting; those are etale interchange statements, not quotations of our tensor or semilinear refinements. I also read sites-cohomology.tex Tag 07A4 (lemma-pullback-tensor-product), 0GL1 (lemma-j-shriek-and-tensor), 0B56 (equation-projection-formula-map), 07A7 (remark-base-change), and categories.tex 0DV0/0B65 with their labels. The parent correctly retains agent proof provenance; both new statements identify their extra tensor calculation as agent-formulated.

Assembly step 1 uses exactly new node 1 equation (3). Its finite ring sheaves are the constant-ring specialization of that node; open ring restrictions give the right coefficient sheaves, and neither a Cartesian hypothesis nor a field-base hypothesis was added. Equations (1) and (2) in the new statement expose the two formerly inline obligations: the supported beta square and the clopen (1,0) comparison, plus composite-open normalization. Its generic ringed form includes the vertical sequence realization of systems explicitly, and each of its notions has an inline explanation or a statement dependency. The old proof of full faithfulness is not reclassified as elementary.

Assembly step 2 uses exactly new node 2's equal transposes and resulting equality. I checked the four functor domains: Pr:C to A, Pp:D to B, J:C to D and K:A to B. The common transpose has source Pp(J(Rr M) tensor N) and target K(M tensor Pr Pi N). The square's tensor hypothesis is supplied by step 1. The pi definition is a counit transpose, not an assumed projection isomorphism, and the g convention is the mate formula of def-weil-pbc-adjunction-mate. Arbitrary bifunctors and mixed action maps make this independent of extra monoidal structure on J,K; thus the upstream full-tensor square theorems are not matches. Specializing to the ringed derived categories uses precisely lem-weil-pbc-ringed-projection-mate-exact, whose statement gives the counit-defined map for arbitrary small ringed sites and all objects.

Assembly step 3 uses the unbounded-operation and intrinsic-map paragraphs of lem-sf-integral-compactification-system-realization, read in full. The restriction to normalized constructible systems is needed for that node's total-limit comparison, which is not used here; its operations and intrinsic Gamma are stated on D(S). I opened lem-sf-semilinear-proper-open-mate-pasting and checked that it gives the proper mate of precisely beta followed by the clopen projection, and that its open adjunct is lambda inverse. This and the realization node's identical open-adjunct characterization identify the two maps by adjunction uniqueness. This reuses all of old step 7, rather than assuming derived evaluations faithful. Applying the two new lemmas on the ringed sequence sites proves the system equality itself and supplies old step 8. The varying coefficient rings are the specified A_{E,n} tower; no flatness of coefficient transitions is used. The diagram sites are small in the fixed universe; generic ringed tensor results therefore apply.

For B1–B9 I checked the new files: statements alone, no proof sketch or proof dependencies, objects and all domains introduced, ring maps and open localizations specified, correct labels in the local sources, all four search methods actually run with a second semantic phrasing, actual results logged, no Mathlib match claimed. I read the candidate Mathlib mateEquiv_counit (Mates.lean:123) and frobeniusMorphism_mate (Closed/Functor.lean:139); these give a mate component equation and a Cartesian-closed Frobenius comparison, not our tensor squares. The monoidal counit compatibility (Monoidal/Functor.lean:1036) likewise does not give mixed action transfer. The searches for the unchanged item are retained verbatim from the returned node; new-node searches are taken from the present searches.jsonl, never invented.

For C1–C8 every assembly use has a verbatim quote in citations.json; I checked each excerpt against its statement, not a proof. The new nodes cite the existing definition/foundation interfaces in stmt_deps and remain independent (neither cites the parent or the other). Off-unit generic tools used by the assembly are declared in split_report.tool_uses; the unit route is unchanged. No step is longer than 2000 characters and the total assembly is below 3000. The old long steps remain as explicit new proof tasks, not shortened claims of obviousness.

For E I tested identity squares (rho=1, beta and deltas normalize to identity), Cartesian squares (s=identity), zero input objects and zero coefficient ring, and the empty A case (alpha=zero). For a genuine noncartesian test, B=D disjoint union D, C=D, p the finite fold, A one component, and i=r=identity: s selects one component, alpha is the corresponding (1,0) projection, and the tensor square and its mate select the same summand on both sides. In the abstract transfer the comparisons may be noninvertible; its derivation uses no inverses. These checks catch the missing-complement error and the incorrect assumption that the square is Cartesian. No source statement needs correction and no target or parent statement changed.

## Not duplicates

lem-sf-clopen-comparison-tensor-square vs cor-pur-smooth-admissibility: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Smooth morphisms satisfy the preservation clauses. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs cor-weil-boundary-duality-discharge: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is The finite-stage boundary input is a consequence. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-asd-compact-support-graph-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is The specified sheaf and unbounded derived graph comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-cbc-finite-constant-coefficient-transport: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized finite scalar and etale-origin transport to constant coefficient modules. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-cbc-signed-koszul-completion-model: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is The pure-tensor-normalized signed Koszul completion model. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-cbc-strict-constant-tower-operations: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Strict constant-coefficient towers and normalized inverse/direct-image operations. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-cbc-strict-tower-composition-maps: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical strict-tower composition comparison maps. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-cbc-strict-tower-open-extension: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized exact open extension on strict constant-coefficient towers. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-cbc-strict-tower-proper-open-arrows: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Unit-normalized proper and open arrows on strict towers. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-coef-ringed-tensor-hom-model: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical closed tensor-Hom representative model on a ringed site. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-coef-semilinear-derived-calculus: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Ordinary derived semilinear calculus interfaces. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-coef-semilinear-geometry-base: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Geometry base fields for coefficient linear operations. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-coef-semilinear-geometry-derived: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Derived geometric system operations and normalization. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-coef-semilinear-geometry-ops: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical geometric mate and projection words. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-coef-semilinear-proper-open-mate: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical semilinear proper/open adjunction mate. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-coef-semilinear-system-models: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Generic strict semilinear system constructions and representative normalization. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-fix-proper-etale-origin-scalar-data: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical scalar, tensor and direct-image comparisons at etale origins. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-kun-constant-projection-morphism: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical constant-coefficient derived projection morphism. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-kun-projection-formula-map: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is The projection-formula morphism. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-pd-section-derived-realization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical derived section-module realization. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-pd-section-derived-tensor-data: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical derived section-module tensor data. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-pur-adic-site-strict-quotient-interface: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Small-site adic strict quotient interface and canonical normalizations. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-pur-cochain-coefficient-arrows: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical scalar-association and transition arrows on cochain sheaves. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-pur-cochain-coefficient-universe-transport: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical common-universe transport of ring and module sheaves. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-pur-cochain-tensor-coherence-data: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical cochain ringed-pullback and coherence data. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-pur-completed-pullback-tensor-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical completed, rational and common-stage tensor pullback comparisons. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-pur-etale-scalar-pullback-iso: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical derived scalar and pullback isomorphism. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-pur-exceptional-coefficient-tensor-maps: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical tensor and unit transport maps for exceptional coefficient comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-pur-finite-pullback-tensor-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical finite derived pullback tensor comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-pur-integral-line-reduction-data: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Signed integral line reduction and restriction data. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-pur-open-coefficient-normalizations: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Exact-pullback and open-unit coefficient normalizations. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-pur-scalar-pullback-representative-data: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical scalar/pullback representative data. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-pur-smooth-pullback-exchange: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Smooth pullback exchange for exceptional inverse image. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-pur-system-tensor-mate-arrows: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical tensor and proper/open arrows for varying coefficient systems. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sf-etale-support-compositor: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical unbounded etale compact-support compositor. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sf-finite-coefficient-site-chain-tensor: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical finite coefficient site comparison on total tensor complexes. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sf-finite-coefficient-site-hom-arrow: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical finite coefficient site internal-Hom arrow. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sf-finite-coefficient-site-scalar-arrow: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical finite coefficient site scalar comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sf-finite-open-tensor-operations: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical finite open tensor and pullback operations. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sf-integral-open-reduction-comparison-data: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized integral open tensor and reduction comparison data. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sf-open-normalization-data: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Geometric and operation data for open tensor normalization. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sf-open-semilinear-tensor-model-data: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Simultaneous semilinear open tensor model data. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sf-point-evaluation-derived-compatibility: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Representative-normalized derived point comparisons. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sf-point-evaluation-scalar-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Tensor square for balanced point scalar data. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sf-point-evaluation-scalar-data: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Balanced scalar comparison for point sections. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sf-point-evaluation-tensor-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Signed tensor coherence for point sections. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sf-point-evaluation-tensor-data: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized tensor presentation for point sections. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sf-point-fibre-tensor-common-stage: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical common-stage point tensor and coefficient unit. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sf-point-fibre-tensor-finite-models: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical finite point tensor normalization on K-flat representatives. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sf-point-fibre-tensor-models: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical integral representative normalization. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sf-point-fibre-tensor-rational-compatibility: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical rational point tensor, unit, and scalar compatibility. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sf-point-fibre-tensor-reduction: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical module scalar tensor data and finite reduction squares. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sf-point-fibre-tensor-system: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Strong symmetric tensor comparison data for the point fibres. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sf-point-finite-source-constraints: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is The finite point source uses the recorded tensor constraints. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sf-point-integral-scalar-square: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is The integral point completion commutes with scalar extension. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sf-semilinear-proper-open-comparisons: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical semilinear proper/open compositors and intrinsic clopen comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sfb-internal-scalar-tensor-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Scalar-unit normalized tensor comparison for internal modules. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sfb-proetale-trace-coefficient-interfaces: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical internal-module trace coefficient interfaces. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sfb-ringed-derived-comparison-data: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Data of normalized derived monoidal comparisons of ringed topoi. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sfb-ringed-projection-coherence-data: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Recorded data for tensor projection coherence. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sfb-ringed-slice-comparison-model: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized ringed slice comparison data. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sfb-scalar-hom-comparison-data: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Actual scalar-adjunction and normalized tensor-Hom comparison data. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sp-open-coefficient-adjunction-data: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Intrinsic open coefficient adjunction data. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sp-open-scalar-operations: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Constant-ring pro-etale scalar and open operations and their canonical comparisons. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sp-open-scalar-tensor-data: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Open scalar tensor normalization data. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sp-proetale-scalar-mate-identifications: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized pro-etale scalar-to-tensor and coefficient-pullback identifications. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sp-semilinear-constant-ring-operations: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Constant-ring semilinear system operations and normalized evaluation mates. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sp-varying-ring-clopen-arrow-factors: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Separate the cartesian lift and clopen section factors before taking mates. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-sp-varying-ring-proper-open-arrows: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Intrinsic varying-ring clopen proper/open arrows. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-weil-pbc-four-corners: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Four finite-level corners. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-weil-pbc-level-map-corners: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Four finite-level rectangle corners. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-weil-pbc-normalized-origin-scalar-comparisons: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical quotient scalar-extension unit and associator. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-weil-pbc-projection-formula-map: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Projection-formula map. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-weil-pbc-ringed-projection-restriction-data: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized ringed projection and slice comparison data. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-weil-pbc-ringed-tensor-square-presentation: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Representative presentation of a commutative ringed tensor square. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs def-weil-pbc-witness-compatibility: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Witness compatibility condition. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs det-cor-sf-direct-image-ctf-open-tor: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Scalar projection formula and the Tor bound for an open immersion. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs det-pe-finite-tor-comparison-noetherian: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Tor amplitude under comparison for Noetherian coefficients. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs det-prop-sfb-cartesian-coefficients-twists: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Inverse image of Tate twists. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs det-sp-integral-direct-image-tower: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Tower description of the integral compactly supported direct image. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs det-sp-purity-bc-factors: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Base change of the orientation and of the tensor map. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs det-sp-reduction-compatibilities: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Coefficient comparisons: units, composition and purity. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs det-thm-sf-pf-field-localizing: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is The proper projection formula on the rational localizing categories. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs det-thm-sfb-proper-base-change-rational: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Proper direct image, base change and projection formula for $E$ and $\overline{\mathbf Q}_\ell$. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs fix-prop-projection-formula: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Compact-support projection formula at all coefficient stages. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-a1-adic-compactification-section-realization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Adic compactification cohomology and extension-by-zero sections. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-a1-finite-pullback-strict-tower-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Natural finite pullback comparison of strict reduction towers. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-ag-uniform-complete-tensor: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Completed tensor preserves compatible uniform constructible complexes. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-amb-compact-support-open-source-composition: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Compact-support composition with a source open. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-amb-compactification-projection-composition: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Projection maps respect the explicit proper/open compactification tower. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-amb-etale-adjoint-locality: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Etale localization of the ambient adjoint. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-amb-etale-compact-comparisons: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is The etale compact-support comparisons. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-amb-open-projection-composition: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Composition of the canonical derived open tensor isomorphisms. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-amb-shriek-open-exchange-adjoint: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Open compact-support exchange is the extension-composition mate. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-amb-shriek-open-tower-counit: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Open compact-support composition on the pullback tower. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-amb-shriek-tensor-composition: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Tensor projection maps respect compact-support composition. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-amb-tensor-projection-adjunct: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Adjoint of a tensor-projected morphism. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-amb-unbounded-compact-support-comparisons: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Unbounded ordinary etale compact-support comparisons. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-amb-unbounded-proper-open-adjunction-normalization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Adjunction normalization of unbounded proper/open interchange. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-amb-unbounded-proper-open-interchange: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Unbounded torsion-coefficient proper/open interchange with its canonical maps. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-asd-compact-projection-exchange: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Compact-support projection maps commute with etale exchange. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-asd-compact-support-finite-graph-isomorphism: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is The specified graph comparison for finite etale morphisms. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-asd-compact-support-graph-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Base-change, proper-refinement and identity equations for the graph map. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-asd-compact-support-graph-derived-isomorphism: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Invertibility of the specified graph map on unbounded complexes. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-asd-compact-support-graph-geometric-base-change: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is The specified forward graph comparison at a geometric base change. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-asd-compact-support-graph-sheaf-normalization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Graph comparison agrees with the canonical map into direct image. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-asd-compact-support-graph-sheaf-normalization-transpose: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Transpose of graph comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-asd-etale-compact-support-normalization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalization of compactified etale support and its exchange. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-asd-etale-finite-twist-pullback: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Finite Tate lines on the small etale site and their pullback. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-asd-etale-finite-twist-pullback-rest: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Finite Tate pullback derived and exponent coherence. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-asd-internal-adjunction-evaluation: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Evaluation formula for the canonical internal compact-support adjunction. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-asd-open-projection-exchange: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Ordinary etale open tensor comparison commutes with base change. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-asd-proper-open-refinement-adjoint-projection: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Adjoint of the unbounded proper-open refinement comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-asd-tensor-mate-etale-precomp: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical tensor mate is compatible with etale precomposition. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-cbc-complete-proetale-refinement-exchange-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Refinement Exchange Coherence. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-cbc-completed-extension-zero-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Completed extension-by-zero base change. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-cbc-etale-local-compact-support-extension: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Zariski-local extension of etale compact-support functors and exchange morphisms. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-cbc-normalized-proper-open-geometric-normalization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Refinement and base change for fixed normalized proper/open comparisons. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-cbc-normalized-proper-open-pasting: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Horizontal pasting for fixed normalized proper/open comparisons. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-cbc-open-extended-injective-proper-acyclic: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Open extension of an injective sheaf is acyclic for the proper right-hand map. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-cbc-proper-open-interchange-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Proper/open interchange and its base-change and composition equations. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-cbc-ringed-open-strict-reduction: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Augmented strict adic reduction under ringed open extension. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-cbc-strict-tower-proper-open-calculus: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized proper/open calculus on strict pro-etale towers. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-cbc-tower-composition-refinement: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Compatible-tower composition commutes with proper refinements. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-coef-derived-system-evaluation-calculus: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Coherent derived reduction, limit adjunction and fiberwise evaluation. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-coef-enriched-sequence-projection-formula: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Uncurried finite projections of the enriched sequence adjunction. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-coef-etale-hom-thick-locus: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Triangulated compatibility of the evaluation-defined scalar Hom comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-coef-etale-tensor-model-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Unique flat-model normalization of the étale scalar tensor comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-coef-finite-etale-descent: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Étale recovery of the closed exceptional quotient comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-coef-integral-finite-extension: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Integral duality and a finite extension of coefficient fields. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-coef-ringed-pullback-hom-evaluation-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Evaluation-defined Hom comparison for ringed pullback. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-coef-semilinear-operations-existence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Geometric and coefficient operations on a fixed semilinear system calculus. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-coef-semilinear-system-existence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Ordinary semilinear system calculus and cartesian internal Hom. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-derived-right-exact-tensor-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized tensor comparison for a right exact strong monoidal functor. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-exc-cartesian-open-finite-stage-hypercohomology-model: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Finite-stage hypercohomology model for a Cartesian open extension. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-exc-etale-origin-proper-open-interchange: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Site transport preserves the canonical Cartesian proper/open interchange. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-exc-proetale-cartesian-open-injective-acyclic: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Proper acyclicity of injectives extended from an arbitrary Cartesian open. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-exc-proetale-constant-support-projection: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Constant-coefficient projection for compact support. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-exc-proetale-finite-cd-proper-open-interchange: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Deriving proper/open support under all-sheaf finite cohomological dimension. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-exc-proetale-proper-open-sheaf-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Proper/open comparison for pro-etale module sheaves. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-exc-support-scalar-projection-normalization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalization of support scalar mate as a projection arrow. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-fd-base-change: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Base change of the transform. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-fix-compact-support-coefficient-change: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Change of finite coefficients for compact support. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-fix-compactification-completed-realization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Completed proper/open realization and its projection normalization without a Tor bound. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-fix-etale-proper-coefficient-tensor-unit: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Proper direct image preserves a universal finite-coefficient tensor unit. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-fix-open-scalar-exchange: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Scalar extension respects the open base-change comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-fix-open-scalar-tensor-normalization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Open scalar comparison with unit, tensor and composition normalization. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-fix-proetale-scalar-mate-normalization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Pro-etale scalar mate restricts to the specified projection arrow. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-fix-projection-compactification-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Projection transformations of two compactifications agree under the refinement comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-fix-reduction-open-etale-origin: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Bounded etale witnesses for finite reduction and open extension. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-fix-ringed-scalar-tensor-monoidal: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized strong monoidality of derived scalar extension in independent universes. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-fix-site-perfect-scalar-hom: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Evaluation-normalized scalar Hom comparison for a site-perfect first variable. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-fix-tensor-pullback-square: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Tensor inverse-image comparisons commute around an open square. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-geo-cartier-coeff-extension: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Derived scalar extension of a closed supported constant sheaf. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-kun-0f0f: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Projection formula, integer coefficients. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-kun-bc-kunneth-compat: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Cohomology of the base change map through the Kunneth identification. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-kun-derived-pullback-composition-monoidal: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical derived etale inverse-image composition is monoidal. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-kun-geometric-point-projection-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Geometric-point projection morphism agrees with the constant-section projection morphism. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-kun-geometric-point-pullback-tensor-normalization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Tensor normalization of the pullback/stalk evaluation comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-kun-inverse-image-monoidal: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Monoidality of the derived inverse image. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-kun-kunneth-map-agrees: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Compatibility of the Kunneth map with Leray, proper base change and the projection formula. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-kun-kunneth-map-natural: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Naturality of the Kunneth map. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-kun-kunneth-via-0f1n: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Compatibility of the Kunneth map with the projection-formula variant. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-kun-proj-formula-natural: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Naturality of the projection formula. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pd-module-ringed-topos-derived-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Module-object and ringed-topos derived tensor comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pd-section-derived-tensor-normalization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Derived tensor and actual pullback tensor arrows under section equivalence. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pe-constructible-comparison-tensor-test-reflection: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Reflection of a single comparison tensor test. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-per-noetherian-supported-product-calculus: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Supported products and Cartier interchange on ordinary etale sites. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-per-rational-pullback-composition-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Scheme composition coherence of normalized rational pullback. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pod-frobenius-cup-transport: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Finite-coefficient Frobenius transport commutes with mixed-support cup product. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pod-integral-pullback-composition: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Composition isomorphism for integral derived pullbacks. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pod-point-duality-coefficient-compatibility: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Point dualizing identification is compatible with coefficient change. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-adic-projection-shift-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Shift compatibility of the compact-support projection and trace transpose. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-algebra-diagram-pullback-extension-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Derived scalar-extension/pullback comparison agrees with the ambient strict-diagram tensor map. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-canonical-coefficient-system-geometry: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Geometric realization on the literal constant finite coefficient tower. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-closed-supported-cup-vanishing: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Restriction to a closed support detects the zero action on supported cohomology. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-co-smooth-pf-exchange-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Projection/exchange coherence for compact support. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-cochain-comparison-monoidal-equations: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Monoidal equations for the canonical cochain pullback comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-cochain-pullback-tensor-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Signed tensor comparison and composition on cochain sheaf pullbacks. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-common-stage-tensor-line-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Natural associativity and regular right unit for common-stage tensor. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-compact-support-integral-coefficient-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Integral compact support under finite free coefficient extension. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-compact-support-strict-scalar-refinement: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Scalar mate compatibility with strict compactification refinements. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-completed-line-tensor-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Completed scalar extension commutes coherently with compatible coefficient lines. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-completed-open-tensor-system-realization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Strict open-tensor systems realize the completion-unit-normalized open map. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-completed-operation-tower-substitution: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Coherent substitution of normalized systems into completed operations. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-composite-left-projection-action: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Pasting two forward left-coefficient tensor actions. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-composite-relative-tensor-action: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Composition preserves relative tensor-action identities. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-condensed-tate-realization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Realization of the reconstructed Tate tower in the condensed coefficient category. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-constant-native-pullback-monoidal: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical native derived tensor comparison for constant coefficients. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-coprojection-composition-mate: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Co-projection composition is the mate of projection associativity. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-derived-pullback-tensor-iso: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Derived pullback commutes with derived tensor product on the constructible categories. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-dualizing-unit-composite: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Dualizing unit and composite tensor identifications. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-etale-closed-chart-exceptional-preservation: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Exceptional inverse image on a closed affine-space chart. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-etale-exceptional-constant-tensor: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Constant-coefficient tensor calculus for the finite etale exceptional adjoint. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-etale-horizontal-support-tower: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Etale compact-support composition on a pullback compactification tower. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-etale-kflat-support-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is K-flat comparison of the actual support sequences. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-etale-open-derived-tensor: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Open extension by zero and unbounded derived tensor on ordinary etale sites. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-etale-open-scalar-composition: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Open scalar balancing respects composition of ordinary etale open extensions. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-etale-scalar-mate-projection: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Restriction of the derived coefficient mate equals the projection morphism. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-etale-scalar-pullback-existence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Existence of normalized derived scalar/pullback comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-etale-scalar-pullback-uniqueness: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Uniqueness of normalized derived scalar/pullback comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-exact-pullback-signed-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Exact ringed pullback identifies the canonical signed derived tensor comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-exceptional-coefficient-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Counit-transpose coefficient comparison and tensor coherence. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-external-evaluation-transpose-natural: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Naturality and open restriction of the external evaluation transpose. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-finite-forward-product-symmetry: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Symmetry of the finite forward compact-support external product. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-finite-free-scalar-projection: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Finite-free scalar extension preserves the specified proper, open and compact projection maps on both sites. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-finite-open-product-swap: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Finite open external-tensor comparison and signed factor swap. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-finite-projection-action-laws: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Tensor-action and open-counit identities for finite-level projection maps. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-finite-ring-site-tensor-transpose: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Etale/pro-etale transport of compact-support projection maps and their transposes over an arbitrary finite ring. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-finite-site-counit-projection-transport: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Finite site comparison preserves counit and projection transposes. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-flat-term-kflat-tensor-native: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Total tensor of native flat-term K-flat complexes. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-geometric-scalar-association-cocycle: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Scalar-association cocycle from normalized inverse-image restriction squares. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-integral-ambient-operation-models: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Ambient completion presentations for integral pullback and tensor. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-integral-coherence-tower: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Coherence identities on normalized integral comparison towers. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-integral-line-derived-comparisons: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized derived signed-line reductions and support. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-integral-line-power-comparisons: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Signed power scalar comparisons and evaluations. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-integral-line-reduction-restriction: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Signed line reductions and restriction to the derived-complete integral category. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-integral-line-restrictions: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Completeness and normalized restricted line equivalences. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-integral-operations-scalar-extension: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Integral derived operations commute with finite scalar extension. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-integral-tensor-reduction-tower-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Strict tensor comparison for finite coefficient-reduction towers. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-integral-tensor-transition-compatibility: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Quotient compatibility of the normalized total tensor comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-integral-tower-limit-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Derived limit of the strict integral comparison tower. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-kflat-total-tensor-model: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is K-flat total tensor model for flat-term resolutions. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-lifted-external-evaluation-chain-model: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Lifted external evaluation chain models with common shifted targets. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-line-zero-class-exchange: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized exchange and geometric-fibre identification of the zero-section compact class. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-module-tensor-coefficient-equations: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Ordinary module tensor equations for coefficient change. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-module-tensor-composition-equation: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Ordinary tensor square for composite module pullback. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-normalized-operation-system-models: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalization and simultaneous models for finite coefficient-system operations. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-normalized-pullback-composition-transport: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Transport of normalized pullback composition through coherent realization. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-normalized-scalar-comparison-realization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized realization of scalar comparisons on quotient systems. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-normalized-tensor-constraint-transport: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Transport of normalized tensor constraints through coherent realization. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-open-left-projection-action: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Left-coefficient action laws from normalized open restriction. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-open-projection-site-transport: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Site transport of the normalized open tensor projection and its inverse. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-ordinary-kunneth-finite-ring: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Ordinary Kunneth at a finite coefficient ring. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-ordinary-line-derived-scalar-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Ordinary unbounded derived scalar extension intertwines signed line tensor and evaluation. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-perfect-quotient-exchange-normalization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Perfect quotient coefficient exchange with augmentation and completion-unit normalization. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-proetale-restricted-tensor-finite-local-constancy: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Finite local constancy of a restricted tensor with bounded-above inputs. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-projection-comparison-etale-origin: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Etale-origin comparison intertwines compact-support projection maps. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-projection-formula-coefficient-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Unit and coefficient associativity of compact-support projection maps. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-quotient-diagram-projection-evaluation: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Finite-coefficient evaluation of the quotient-diagram projection mate. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-quotient-expression-kflat-normalization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Simultaneous K-flat normalization of strict quotient expressions. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-scalar-extension-tower-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Coherent quotient towers for integral scalar extension. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-scalar-hom-comparison-tower: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Evaluation-defined scalar Hom maps respect coefficient towers. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-scalar-tensor-pullback-normalization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Scalar/tensor pullback normalization on a K-flat representative. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-scalar-tensor-unit: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Scalar action unitor for a normalized signed tensor comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-shifted-tensor-morphism-calculus: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Signed calculus of shifted derived tensor morphisms on ringed sites. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-signed-line-derived-base-change: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Signed line comparisons and their unbounded derived tensor action. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-strict-coefficient-comparison-calculus: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Simultaneous strict coefficient comparisons on ring-sheaf towers. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-support-site-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Etale-proetale comparison for supported sections and their exterior products. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-supported-cup-functoriality: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Pullback and symmetry of supported Kummer cup products. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-system-clopen-tensor-compatibility: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Proper/open tensor-mate interchange on varying-coefficient systems. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-system-compactification-pf-substitution: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Refinement comparisons intertwine strict-system projection maps. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-system-level-projection-formula-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Strict-system projection formula composition coherence. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-system-normalized-tensor-closure: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized semilinear systems are closed under tensor and inverse image. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-system-tensor-reduction-formula: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Tensor formula for actual semilinear reduction adjoints. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-unit-adjunct-tensor-action: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Tensor action and counit equations for a unit-defined left-adjoint projection. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-varying-ring-tensor-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized tensor comparison for one varying-ring inverse image. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-varying-ring-tensor-support: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Tensor support for canonical varying-ring extension. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-vector-integration-site-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Finite-level site comparison of normalized vector-bundle integration. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-pur-weil-tate-datum-transport: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Transport of the Tate source datum. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-affine-chart-factorization-gluing: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Finite affine chart factorization and interval gluing. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-ambient-proper-open-pasting: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized proper/open pasting on ambient pro-etale and semilinear-system categories. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-canonical-open-restriction-model: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical open restriction on augmented quotient models. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-cbc-coefficient-linear-projection-descent: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Coefficient-linear derived projection from a specified ordinary slice comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-cbc-constant-tower-direct-image-normalization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Constant strict towers and normalized derived direct image. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-cbc-localized-strict-tensor-descent: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is K-flat normalized descent of localized extension tensor comparisons to strict coefficient towers. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-closed-support-tor-bound: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Closed support triangle adds one to the Tor upper bound. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-compact-coefficient-composition: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Finite coefficient comparison respects compact-support composition. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-compact-support-proper-image-tower: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is The proper-image reduction tower of open extension equals the compact-support tower. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-comparison-open-tensor-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Etale/pro-etale comparison respects the canonical open tensor map. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-completed-tensor-rational-naturality: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Naturality and rationalization of a completed tensor comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-composition-projection-mate: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized compact-support composition satisfies the projection mate identity. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-constant-semilinear-generator-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Scalar restriction identifies the single proper and open reduction generators. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-constructible-exceptional-coefficient-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Coherence of constructible exceptional coefficient comparisons. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-derived-weil-compact-projection-formula: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Compact projection formula for actual derived Weil complexes. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-derived-weil-tensor-hom-adjunction: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Native derived-Weil tensor preserves bounded constructible complexes. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-etale-generic-immersion-projection: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Projection formula for an immersion extension by zero. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-etale-local-dual-interval: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Uniform local models and Tor interval for a twisted coefficient dual. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-etale-smooth-stratified-ctf: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Smooth-stratum finite-Tor devissage over an arbitrary algebraically closed field. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-exceptional-product-direct-image-compatibility: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Exceptional external product is compatible with immersion direct images. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-finite-comparisons-existence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Section preserving finite comparisons exist. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-finite-compatibility-transport: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Pinned finite comparisons preserve canonical open arrows. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-finite-cover-ctf-locality: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Finite-cover locality of bounded constructibility and a fixed Tor interval. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-finite-exchange-projection-commshift: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Finite geometric exchange and projection commute with shifts. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-finite-operation-comparisons: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Prescribed finite realizations admit pinned operation comparisons. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-framework-theta-shift-compatibility: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Framework completed pullback scalar comparison commutes with shifts. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-generator-reduction-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Basic generator coefficient squares in semilinear systems. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-integral-compactification-comparison-bridge: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Constant-tower and semilinear-counit normalizations of integral compactification composition agree. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-integral-line-tensor-comparison-representative: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is K-flat line tensor models and finite balancing. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-integral-open-product-diagram-normalization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Strict-diagram normalization of integral open product comparisons. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-integral-open-reduction-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Strict reduction and normalized realization of completed open extension. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-locally-finite-adic-compact-support-realization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Actual compact supports commute with ordinary constructible coefficient realization. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-native-weil-open-proper-interchange: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Proper/open interchange for native bounded constructible Weil complexes. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-open-external-tensor-normalization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized finite open external-tensor comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-open-operation-models: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Open operation comparisons with fixed tensor models and right square. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-open-projection-roos-completion: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Completing the augmented open projection square with its actual units. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-open-reduction-adjunction-transport: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Open restriction and adjunction transport through actual completion units. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-open-restriction-completeness: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Completeness and the actual completion unit after ordinary open restriction. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-open-roos-unit-adjunction: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Roos completeness, actual open completion units and the complete adjunction. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-open-semilinear-tensor-model: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Simultaneous semilinear open tensor comparison on flat K-flat models. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-open-tensor-normalization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Open-extension unit normalization for derived tensor and base change. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-open-tensor-quotient-augmentation: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Open reduction towers and the strict augmented tensor square. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-open-tensor-support: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Derived tensor preserves open support in either factor. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-open-tensor-support-aux: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is The open tensor projection transpose is invertible. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-open-tor-bound-stalk-filtered-extension: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Finite constant-module tests detect etale Tor amplitude. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-package-compactified-tower-comparisons: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Compactified direct-image towers, reduction and composition. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-pf-open-factor-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Completed open restriction, constructibility and normalization of the open maps. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-point-fibre-derived-tensor: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is The point fibre functor preserves derived tensor at all coefficient stages. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-point-field-tensor-descent: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Rational and common-field point tensor descent. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-point-finite-tensor-comparisons: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Finite point tensor comparisons and all quotient squares. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-point-integral-completed-tensor-comparisons: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Completed integral point tensor and scalar squares. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-point-ringed-evaluation-model: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Ringed geometric-point evaluation with signed tensor and coefficient models. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-product-compactification-identity: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Product compactification identity for the exchange/projection composite. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-proper-open-comparison-site-normalization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalization of the proper/open comparison under the site comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-proper-open-projection-mate: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized proper/open interchange commutes with projection. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-rational-localization-triangle-orthogonality: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized rational localization triangles and cross-object orthogonality. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-rational-slice-completed-evaluation: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Restriction compatibility for completed rational evaluation. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-ringed-finite-free-hom-base-change: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Evaluation comparison for a finite free change of ring sheaves. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-ringed-finite-free-tensor-complex: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Actual scalar tensor comparison on complexes and K-flat preservation. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-ringed-finite-free-tensor-data: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Strong scalar tensor comparison for supplied normalized derived models. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-semilinear-alpha-pullback: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Pullback cube for the intrinsic semilinear alpha transformation. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-semilinear-proper-open-mate-pasting: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Intrinsic proper/open mates and pasting for varying coefficient systems. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-semilinear-scalar-ordinary-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Ordinary scalar restriction with section-normalized comparisons. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sf-unbounded-compact-support-proper-composition: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Unbounded ordinary etale compact supports composed with a proper direct image. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-coefficient-projection-square: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Coefficient compatibility square for the actual projection mate. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-coefficient-push-filtered-legs: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Flat coefficient push comparison from a bounded filtered module presentation. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-dc-hom-scalar-adjunction: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Derived internal Hom under restriction of coefficient scalars. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-dc-tensor-preserves: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is $\otimes^{\mathrm L}$ preserves bounded constructible complexes ($\ell$-adic $\Lambda$). Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-etale-derived-tensor-stalk: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Geometric etale stalks commute with unbounded derived tensor products. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-etale-proetale-cube-flat-model: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is One flat model computes all six etale/pro-etale scalar cube faces. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-etale-stalk-total-tensor-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical signed total tensor stalk comparison and chain naturality. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-exact-compactification-unit-composition: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Composition of normalized exact compact-support units. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-exact-compactification-unit-refinement: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized exact compactification units respect canonical refinements. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-exact-completed-koszul-pullback: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Exact product-preserving inverse image transports the actual Koszul unit. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-geometric-stalk-tensor-constant-single: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Geometric stalks commute with derived tensor against a constant module. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-hom-flat-evaluation-roof: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Flat scalar comparison is the evaluation-normalized resolution roof. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-hom-flat-scalar-evaluation-model: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Flat scalar evaluation on an arbitrary first complex and its derived coherence. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-integral-augmented-quotient-towers: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Generator-normalized augmented finite quotient pullback towers. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-integral-pullback-strict-roos-normalization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Strict Roos normalization of integral pullback and constant scalar restriction. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-integral-quotient-exchange-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Reduction of the actual unbounded integral exchange. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-integral-quotient-projection-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Reduction of the actual unbounded integral projection morphism. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-integral-quotient-pullback-face-model: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Common K-flat model for integral quotient pullback faces. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-internal-extension-monoidal: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Scalar-unit normalized strong monoidal extension of internal scalars. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-internal-extension-preserves-flat: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Extension of scalars preserves flat internal modules. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-internal-hom-dual-tor-amplitude: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Finite Tor amplitude of locally constant perfect duals. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-internal-inflation-graded-cup: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Monoidal derived inflation and graded cup composition. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-internal-scalar-mate-projection: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Restriction of an internal coefficient mate is the specified projection map. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-localized-direct-image-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Localization of coefficients commutes with bounded-below direct image. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-proetale-tor-local-global: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Local and global finite Tor dimension on a quasi-compact pro-étale site. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-projection-comparison-etale-proetale: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Etale-to-proetale comparison of the canonical direct-image projection morphism. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-proper-open-tower-derived-unit: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Derived-unit resolution calculation in a proper/open tower. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-proper-open-tower-single-unit-formula: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Single derived-unit formula in a proper/open tower. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-proper-open-tower-successive-unit-formula: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Successive derived-unit formula in a proper/open tower. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-quasifinite-compact-support-exact: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Quasi-finite compact support is exact and agrees with compactifications. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-quotient-section-tensor-normalization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized quotient scalar tensors and section-module realization. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-ringed-comparison-tensor-adjunction: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Tensor and adjunction compatibility of canonical ringed-topos path comparisons. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-ringed-derived-monoidal-comparisons: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Monoidal and adjunction normalization of derived ringed-topos comparisons. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-ringed-derived-tensor-diagrams: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Coherence equations for explicit canonical derived comparison maps. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-ringed-derived-tensor-lift: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Symmetric monoidal coherence of a canonical derived tensor lift. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-ringed-derived-two-iso-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Specified geometric 2-isomorphism comparison on derived modules. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-ringed-kunneth-factorizations: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Two factorizations of the ringed-topos external product comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-ringed-projection-first-shift: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is The ringed projection mate commutes with shifts in its direct-image input. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-ringed-projection-pullback-comparisons: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized identity, composition and section pullback comparisons. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-ringed-projection-tensor-compatibility: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Tensor constraints and compatibility of normalized comparisons. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-ringed-projection-tensor-structure: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical tensor structure in arbitrary recorded presentations. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-ringed-site-point-acyclic: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is A conservative point family detects acyclicity. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-ringed-site-point-tensor: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Signed total tensor comparison for normalized stalks. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-scalar-change-direct-image-unit: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Internal/sectionwise normalization of the scalar-change direct-image unit. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-scalar-hom-tensor-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Tensor coherence of the normalized scalar extension maps. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-scalar-internal-hom-tower-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Coefficient-tower and identity coherence for normalized internal Hom. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-scalar-tensor-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Derived scalar tensor comparison on all K-flat representatives. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-scalar-tensor-tower-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Simultaneous normalized scalar tensor comparisons with coefficient coherence. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-tame-pair-proper-generators: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Proper tame-pair generators for finite-field constructible complexes. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-tor-interval-local-detection: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Tor bounds detected on pro-etale covers and open-closed decompositions. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-trace-base-change-first: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Trace and base-change rearrangement before the first triangle. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sfb-trace-base-change-second: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Trace and base-change rearrangement before the second triangle. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-bounded-flat-coefficient-site-square: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Bounded-flat coefficient/site square with its canonical derived comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-canonical-open-scalar-tensor-models: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical scalar tensor models compatible with open inverse image. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-compact-projection-base-change: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Compact-support projection map commutes with base change (finite rings and coefficient towers). Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-completion-mate-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is The strict quotient-tower exchange realizes the completed-adjunction mate. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-direct-image-change-ring-transpose: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Restriction identifies the proper coefficient comparison with the pro-etale projection map. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-direct-image-etale-mate-isomorphism: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is The etale projection mate has the normalized pro-etale counit transpose. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-et-proet-coefficient-compatibility: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Finite coefficient compact-support comparison respects site transport, refinement and composition. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-etale-chart-comparison-isos: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical site comparisons for scalar and chart operations. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-finite-coefficient-input-models: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Finite coefficient and site extension on bounded flat input models. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-finite-compact-site-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Finite-ring compact-support site comparisons respect refinements and towers. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-finite-compact-support-domains: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Compact support and coefficient extension retain the finite-Tor domain. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-finite-ring-compact-support-projection: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Compact-support projection formula on pro-etale sites with arbitrary finite l-primary coefficients. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-finite-site-tower-paste: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Finite-site comparison of the proper/open compatible-tower word. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-flat-coefficient-chain-transpose: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Scalar extension of flat chain maps and their canonical derived transposes. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-intrinsic-open-projection-invertible: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Intrinsic open projection inverse is invertible. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-open-projection-scalar-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Scalar restriction of the normalized open projection. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-open-scalar-coefficient-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Coefficient coherence of scalar pullback. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-open-scalar-site-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Open extension scalar/site square on flat models. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-proetale-open-injective-proper-acyclic: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Open-extended injectives are proper-direct-image acyclic on pro-etale sites. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-proetale-proper-boundary-cohomology: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Boundary cohomology of an open-extended pro-etale injective on a proper scheme. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-proetale-scalar-tensor-normalization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Underlying tensor normalization of pro-etale scalar and inverse-image comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-proetale-tensor-coefficient-resolution-square: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Coefficient-resolution square for exact pro-etale tensor pullback. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-proper-open-coefficient-mate: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Coefficient and site squares for cartesian proper/open interchange. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-proper-open-coefficient-mate-transposed: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Transposed coefficient mate identity for proper/open interchange. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-proper-open-comparison-normalization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Structural normalization of explicit proper/open comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-proper-open-derived-support: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Proper pro-etale direct image preserves extension-by-zero support. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-proper-open-tower-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Open-adjunction normalization of proper/open interchange on strict coefficient towers. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-refinement-coefficient-mate: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Coefficient and site squares for the explicit refinement theta. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-supported-constructible-origin-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Supported constructible etale origin and its unbounded coefficient tensor comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-supported-etale-tensor-origin: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Bounded etale tensor origin for an open-supported finite-Tor complex. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-supported-scalar-tor-interval: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Supported scalar tensor interval and reflection to an arbitrary etale origin. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-tower-geometric-composition: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Geometric composition and exact etale sum-extension. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-varying-ring-cartesian-comparison-lift-relabelling: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is The cartesian open comparison on varying-ring systems relabels lifts. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-varying-ring-cartesian-lift-pullback-equivalence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Cartesian clopen lifts and equivalence of varying-ring inverse image. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-varying-ring-clopen-arrow-evaluation: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Compose the separately evaluated clopen arrow factors. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-varying-ring-clopen-section-evaluation: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized coefficient evaluation of the clopen section factor. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-varying-ring-open-base-change-evaluation: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized coefficient evaluation of cartesian open base change. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-varying-ring-ordinary-clopen-evaluation: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Ordinary coefficient evaluation preserves the single-square clopen arrow. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-sp-varying-ring-proper-open-pasting: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Clopen proper/open projections and pasting over a varying ring system. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-trf-compact-composition-proper-square-normalization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Compact-support composition along a proper square: closed and open normalizations. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-trf-compact-composition-tower-formula: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Computing finite pro-etale compact-support composition on a compatible tower. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-trf-compact-support-exchange-counit: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Compact-support exchange intertwines proper ordinary counits. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-trf-exceptional-tensor-open-restriction: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Open restriction of the counit-defined exceptional tensor map. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-trf-external-comparison-triangles: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Triangle compatibility of the external direct-image comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-trf-filtered-derived-operation-lifts: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Filtered lifts of sheaf-derived operations and their canonical adjunction maps. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-trf-finite-horizontal-shriek-mate: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Compact-support exchange as a mate along finite horizontal arrows. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-trf-finite-structural-maps-commshift: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical finite-coefficient structural maps commute with shifts. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-trf-fixed-stalk-identification-reduction: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Finite reduction of a fixed-point stalk identification. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-trf-integral-compact-transport-system-mate-pasting: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Typed Frobenius-power pasting for compactification exchange on systems. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-trf-kv-evaluation-formula: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Evaluation of the canonical Künneth–Verdier map. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-trf-nearby-compact-tensor-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Tensor and compact-support coherence before duality. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-trf-nearby-geometric-slice: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Geometric specialization slices of the vanishing topos. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-trf-open-exchange-section-adjunct: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Open dual exchange sends an adjoint section to its restricted adjoint. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-trf-open-hom-mate: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Exceptional internal-Hom exchange preserves the mate of an open-restricted morphism. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-trf-open-tensor: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Tensoring an extension by zero. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-trf-proetale-composition-tower-normalization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Pro-etale composition on a compatible tower has the open-adjoint normalization. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-trf-proper-composition-site-transport: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Site comparison preserves compact-support composition with a proper factor. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-trf-proper-open-site-transport: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Site comparison preserves finite proper/open interchange. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-trf-proper-unit-localization-composition: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Proper-endomorphism units commute with open and closed compact-support composition. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-trf-support-product-base-change: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Support-product comparison with base change along the other leg. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-trf-trace-map-from-external-duality: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Trace morphism from external duality. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-boundary-proetale-projection-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Proper compact-support and tensor comparisons identify etale and pro-etale projection maps. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-boundary-q-defining-composite-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Comparison of projection-inverse tensor composites before adjunction. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-closed-costalk-duality: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Exceptional restriction of a Verdier dual. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-etale-native-tensor-pullback: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Native unbounded derived tensor commutes with etale inverse image. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-adic-flat-iff-supplied-model-flat: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Ambient and supplied-model Padic cohomology flatness. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-augmented-cech-tensor-pullback: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Augmented Cech tensor actions commute with derived inverse image. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-augmented-diagram-projection-mate: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Projection mate for an augmented coefficient diagram before taking inverse limit. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-cochain-pullback-tensor-shift: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is The prescribed cochain pullback tensor comparison commutes with both signed shifts. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-compatible-finite-derived-trivializations: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Compatible trivializations of finite derived local systems. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-constant-derived-normalization-universal: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Constant derived realization preserves universal coefficient arrows. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-derived-adjunction-shift: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical derived ringed-topos adjunction is shift-compatible. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-derived-isomorphism-sheaf-wcontractible-evaluation: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Derived morphism sheaves evaluate on weakly contractible pro-etale affines. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-derived-scalar-extension-local-systems: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Coherent localized derived scalar extension and comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-etale-open-proper-interchange: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Open extension by zero and proper derived pushforward interchange. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-etale-shriek-qcqs-composition: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Composition of qcqs etale compact-support candidates. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-finite-reduction-pullback-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Finite reduction and the canonical pullback square. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-kflat-tensor-pullback-computation-universes: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Derived pullback computes K-flat tensor representatives. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-normalized-derived-isomorphism-section-reduction: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalization-compatible evaluation of actual local Isom sheaves. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-normalized-derived-isomorphism-transport: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Universal normalization and evaluation of source-site local Isom sheaves. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-normalized-etale-origin-witnesses: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Compatible etale-origin witnesses for normalized finite-coefficient towers. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-normalized-origin-comparison-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Comparison reduction respects canonical scalar units and composition. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-proper-open-identification-unit: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Unit normalization of the proper/open restriction identification. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-pullback-resolving-computation: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Derived pullback computes on resolving complexes with independent universes. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-pullback-tensor-canonical-shift-unit: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical shifts and action units of the derived pullback tensor comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-pulled-reduction-normalization-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Successive quotient normalizations under the pulled reduction comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-pulled-reduction-strict-model-descent: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Descent of the augmented pulled reduction model. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-reduction-pullback-derived-tower: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized derived pullback of a strict coefficient reduction tower. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-resolving-representative-whiskering: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Restriction to resolving representatives is fully faithful. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-ringed-equivalence-module-hom: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Module and closed Hom transport under a ringed equivalence. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-ringed-exchange-tensor-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Projection-formula coherence for a square of ringed topoi. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-ringed-projection-global-model: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Existence of the canonically normalized global projection package. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-ringed-projection-local-model: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Localization of a normalized global projection package. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-ringed-projection-mate-exact: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Exactness data for the ringed-topos projection mate. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-ringed-projection-restriction: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Localization comparisons for the ringed projection mate. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-ringed-projection-tensor-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Descent and signed shifts of the normalized pro-etale tensor comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-ringed-projection-tensor-shifts: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Signed shifts of an already normalized tensor comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-ringed-slice-comparisons-shift: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Shift normalization of canonical ringed-slice comparisons. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-ringed-slice-evaluation-transpose: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Slice restriction preserves evaluation for an arbitrary dualizing object. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-ringed-slice-koszul-coherence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Normalized slice restriction preserves Koszul exchange. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-ringed-slice-normalized-comparisons: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Existence of normalized slice tensor, Hom and Koszul comparisons. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-ringed-square-tensor-compatibility: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Tensor compatibility of a ringed square on flat K-flat representatives. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Derived tensor comparison for arbitrary ringed topoi. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-existence: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical tensor comparison unit existence. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-uniqueness: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Canonical tensor comparison unit uniqueness. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-slice-tensor-integer-shift-compatibility: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Integer-shift compatibility of the normalized slice tensor comparison. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-stratum-completion-unit-restriction: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Restriction and finite-stratum detection of the adic completion unit. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-pbc-tensor-comparison-descent-representatives: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Unique descent of tensor comparison from representatives. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-weil-stratum-ambient-hom: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Internal Hom from extension along a stratum. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-wf-constant-twist-coefficient-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Constant-line tensor and scalar Weil twist in the two coefficient models. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-wf-etale-cup-functoriality: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Functoriality of cup products in ordinary etale cohomology. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-zl-extension-by-zero-punctual: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Extension by zero is exact and preserves punctual weights. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-zl-immersion-weil-local-behavior: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Exact immersion operations and local Frobenius on Weil stalks. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lem-zl-rational-realization-tensor-comparison: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Tensor compatibility of the raw rational continuous realization. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lemma-weil-pbc-koszul-quotient-limit: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Koszul and quotient towers have the same limit. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lemma-weil-pbc-projection-formula-finite-free: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Finite-free projection formula. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lemma-weil-pbc-projection-formula-totalization: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Signed totalization of the perfect formula. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs lemma-weil-pbc-projection-formula-tower-compatibility: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Projection formulas form a coefficient tower. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs prop-asd-smooth-base-change: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Arbitrary base change for smooth ambient duality. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs prop-base-linear: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is P7: the transform is linear over the base. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs prop-exc-base-change-proper: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Base change for a proper morphism, against an open immersion. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs prop-sf-dualizable-hom: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Internal Hom through the coefficient dual. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs prop-weil-pbc-direct-image-limits: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Direct image, derived limits, and completeness. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs thm-amb-vector-bundle-purity: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Vector-bundle purity before smooth orientation. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs thm-cbc-complete-proetale: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Complete pro-etale compact-support base change. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs thm-pur-cohomological-smoothness: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Cohomological smoothness of smooth morphisms. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs thm-sf-hom-comparison-constructible: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Internal-Hom comparison for finite-Tor constructible inputs. Shared foundational tag is not equality of statements.

lem-sf-clopen-comparison-tensor-square vs thm-trf-internal-hom-pullback: the new node states the pre-mate beta, clopen and composite-open tensor squares for arbitrary ring sheaves on ordinary or sequence sites; the existing node is Internal Hom versus pullback for a site-perfect first variable. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs cor-weil-pbc-geometric-fiber-finite: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Finite-coefficient geometric-fiber formula. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-a1-lisse-section-evaluation: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical evaluation of ordinary common-stage sections at a geometric point. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-a1-proper-sections-germ-and-moving-point: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical proper compact rational germs and semilinear moving points. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-cbc-finite-constant-coefficient-transport: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Normalized finite scalar and etale-origin transport to constant coefficient modules. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-cbc-strict-constant-tower-operations: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Strict constant-coefficient towers and normalized inverse/direct-image operations. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-cbc-strict-tower-open-extension: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Normalized exact open extension on strict constant-coefficient towers. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-cbc-strict-tower-proper-open-arrows: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Unit-normalized proper and open arrows on strict towers. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-coef-semilinear-proper-open-mate: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical semilinear proper/open adjunction mate. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-fix-proper-etale-origin-scalar-data: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical scalar, tensor and direct-image comparisons at etale origins. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-kun-commutative-derived-exchange: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Derived exchange for an arbitrary commutative square of schemes. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-kun-commutative-exchange-raw-pullback: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical transport of represented raw classes through a commutative square. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-kun-constant-projection-morphism: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical constant-coefficient derived projection morphism. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-kun-projection-formula-map: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is The projection-formula morphism. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-pc-derived-base-change-map: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical derived base-change morphism. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-pd-proetale-section-module-functors: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Normalized tensor structures on existing pro-etale section-module functors. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-pd-section-derived-realization: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical derived section-module realization. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-pd-section-derived-tensor-data: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical derived section-module tensor data. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-pd-section-module-operations-data: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Existing section-module operations and pure-tensor data. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-pur-adic-site-strict-quotient-interface: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Small-site adic strict quotient interface and canonical normalizations. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-pur-etale-scalar-mate: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical derived etale scalar-change mate. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-pur-etale-scalar-pullback-iso: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical derived scalar and pullback isomorphism. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-pur-ringed-coefficient-projection-data: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Normalized coefficient projection interfaces. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-pur-scalar-pullback-representative-data: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical scalar/pullback representative data. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-pur-system-tensor-mate-arrows: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical tensor and proper/open arrows for varying coefficient systems. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-sbc-derived-localization-comparison-data: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical derived étale-localization comparisons. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-sf-semilinear-proper-open-comparisons: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical semilinear proper/open compositors and intrinsic clopen comparison. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-sfb-module-projection-section-arrows: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical module projection mate and section comparisons. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-sfb-module-projection-section-composites: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Unit-normalized forward section projection composite. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-sfb-module-projection-section-inverse: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Conditional inverse section projection composite. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-sfb-module-section-projection-arrow: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical section projection arrow. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-sfb-proetale-projection-exchange-maps: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical projection and exchange maps on internal pro-etale modules. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-sp-constant-quotient-projection: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is The canonical single-quotient reduction projection. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-sp-constant-reduction-models: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Coupled universal models for strict constant-coefficient reduction. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-sp-finite-free-direct-image-data: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Normalized scalar models and canonical coefficient comparison data. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-sp-varying-ring-proper-open-arrows: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Intrinsic varying-ring clopen proper/open arrows. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-trf-topos-derived-base-change-map: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Derived base-change map for a commutative square of ringed topoi. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-weil-pbc-adjunction-conjugate: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Conjugate transformations of adjoint functors. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-weil-pbc-adjunction-mate: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Mate of a transformation under two adjunctions. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-weil-pbc-ambient-ringed-exchange: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Ambient ringed exchange. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-weil-pbc-derived-exchange: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Derived exchange map. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-weil-pbc-derived-square-iso: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Square isomorphism on bounded below derived categories. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-weil-pbc-four-arrows: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Four finite-level arrows. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-weil-pbc-four-corners: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Four finite-level corners. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-weil-pbc-projection-formula-map: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Projection-formula map. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-weil-pbc-ringed-projection-restriction-data: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Normalized ringed projection and slice comparison data. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs def-weil-pbc-strict-tower-operations: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Specified derived operations and mate on strict pro-etale module towers. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs det-cor-sf-direct-image-ctf-open-tor: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Scalar projection formula and the Tor bound for an open immersion. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs det-prop-p1-adjunction-rational-triangle: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Triangle identities for the rational projective line. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs det-properbasechange-modules: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Étale proper base change for module coefficients. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs det-thm-sf-pf-field-localizing: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is The proper projection formula on the rational localizing categories. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs det-thm-sfb-proper-base-change-rational: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Proper direct image, base change and projection formula for $E$ and $\overline{\mathbf Q}_\ell$. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs fix-lem-exchanges: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Exchange functoriality: naturality, identities, and pasting. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs fix-prop-projection-formula: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Compact-support projection formula at all coefficient stages. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-a1-proper-sections-semilinear-germs: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Derived germs commute with semilinear transport on a proper geometric fibre. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-asd-compact-support-graph-coherence: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Base-change, proper-refinement and identity equations for the graph map. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-asd-ordinary-finite-p1-adjunction: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Ordinary etale projective-line adjunction with arbitrary finite invertible-exponent coefficients. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-asd-proper-finite-coefficient-extension: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical unbounded proper direct-image comparison for finite coefficient extension. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-asd-proper-finite-coefficient-extension-core: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Unbounded proper coefficient comparison and restricted projection identity. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-cbc-rational-compact-support-coefficient-coherence: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Coherent coefficient comparisons for rational compact-support exchange. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-cbc-strict-tower-direct-image-coherence: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Coherence of canonical strict-tower direct image and its square mates. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-cbc-strict-tower-proper-open-calculus: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Normalized proper/open calculus on strict pro-etale towers. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-cbc-strict-tower-pullback-square-pasting: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Pasting of normalized strict-tower inverse-image squares. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-coef-cartesian-section-adjoint-mates: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Adjoint mates on cartesian derived sections. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-coef-finite-adjunction-transition: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Finite-level adjunction transition compatibility. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-exc-support-scalar-projection-normalization: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Normalization of support scalar mate as a projection arrow. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-fin-module-exchange-composite-base-change: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is The module-valued exchange of a composite base change is the composite of the exchanges. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-finrepair-modification-extension-zero: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Extension by zero under a proper modification. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-fix-compactification-completed-realization: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Completed proper/open realization and its projection normalization without a Tor bound. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-fix-etale-origin-scalar-projection-square: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is The scalar restriction of the etale-origin projection square for a qcqs morphism. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-fix-etale-proper-coefficient-tensor-unit: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Proper direct image preserves a universal finite-coefficient tensor unit. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-fix-proetale-scalar-mate-normalization: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Pro-etale scalar mate restricts to the specified projection arrow. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-fix-proper-etale-origin-scalar-isomorphism: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Proper scalar comparison is invertible on bounded etale-origin inputs. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-kun-0f0f: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Projection formula, integer coefficients. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-kun-0f12: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Tensor product with a constant complex. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-kun-0f1j-prime-torsion-coefficient-reduction: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Prime-torsion coefficient reduction for the punctual tensor comparison. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-kun-bc-base-change: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Base change maps are compatible with further base change. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-kun-bc-map-on-cohomology: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Cohomology of a derived base-change map. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-kun-commutative-exchange-chart: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Commutative-square exchange agrees with cohomology pullback on etale charts. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-kun-commutative-exchange-class-compatibility: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is The exchange mate transports higher-image raw classes. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-kun-commutative-exchange-evaluation-compatibility: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Raw class evaluation commutes with geometric chart pullback. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-kun-derived-exchange-cube: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Derived exchange commutes around a commutative cube. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-kun-geometric-point-projection-comparison: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Geometric-point projection morphism agrees with the constant-section projection morphism. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-kun-higher-exchange-coefficient-cube: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Degreewise exchange compatibility with a morphism of squares and coefficients. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-kun-kunneth-map-agrees: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Compatibility of the Kunneth map with Leray, proper base change and the projection formula. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-kun-kunneth-via-0f1n: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Compatibility of the Kunneth map with the projection-formula variant. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-kun-proj-formula-natural: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Naturality of the projection formula. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-kun-proper-base-change-torsion-ring: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Unbounded proper base change over a torsion coefficient ring. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-kun-unbounded-abelian-exchange-comparison: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Unbounded coefficient forgetting identifies canonical etale exchange. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pd-module-ringed-topos-derived-comparison: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Module-object and ringed-topos derived tensor comparison. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pe-constant-exchange-encoding: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Constant scalar restriction identifies the ambient ringed exchange. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-per-excellent-etale-constant-projection: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Constant-coefficient projection formula for etale direct image over excellent schemes. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-per-field-exceptional-tensor: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Exceptional tensor comparison for coefficients pulled from a field. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-per-noetherian-affine-line-unit: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Ordinary finite-coefficient affine-line unit over a Noetherian base. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-per-regular-normal-crossings-constant-image: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Constant etale direct image across a regular normal crossings boundary. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pod-frobenius-cup-transport: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Finite-coefficient Frobenius transport commutes with mixed-support cup product. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pod-frobenius-exchange-degree-zero: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Degree-zero Frobenius exchange is the underived section-pullback mate. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-adic-projection-shift-coherence: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Shift compatibility of the compact-support projection and trace transpose. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-adjoint-left-projection-action: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Left-coefficient counit projection: transpose, unit and associativity. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-compact-support-completed-projection-coherence: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Completion coherence for the integral projection mate. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-compact-support-condensed-realization: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Compact-support comparison with completed and condensed coefficient realization. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-compact-support-integral-coefficient-comparison: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Integral compact support under finite free coefficient extension. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-compact-support-scalar-projection-identification: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Identification of scalar projection squares through completion. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-compact-support-scalar-shift-normalization: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical shifts of scalar proper/open mates and scalar limit maps. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-compact-support-strict-scalar-mate: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Finite scalar proper/open mate on strict reduction towers. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-composite-left-projection-action: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Pasting two forward left-coefficient tensor actions. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-composite-relative-tensor-action: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Composition preserves relative tensor-action identities. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-dualizing-unit-composite: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Dualizing unit and composite tensor identifications. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-etale-direct-image-scalar-exchange: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Scalar extension respects ordinary etale derived direct-image exchange. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-etale-exceptional-constant-tensor: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Constant-coefficient tensor calculus for the finite etale exceptional adjoint. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-etale-scalar-mate-projection: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Restriction of the derived coefficient mate equals the projection morphism. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-etale-scalar-pullback-existence: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Existence of normalized derived scalar/pullback comparison. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-etale-scalar-pullback-uniqueness: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Uniqueness of normalized derived scalar/pullback comparison. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-exceptional-coefficient-comparison: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Counit-transpose coefficient comparison and tensor coherence. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-finite-projection-action-laws: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Tensor-action and open-counit identities for finite-level projection maps. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-flag-local-comparison: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Coordinate Gysin composition and the supported cup product. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-flag-localized-product: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Forgetting a composite of subbundle divisor classes. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-ordinary-adjunction-scalar-compatibility: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Scalar compatibility of the ordinary completed adjunction. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-perfect-quotient-exchange-normalization: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Perfect quotient coefficient exchange with augmentation and completion-unit normalization. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-projection-formula-coefficient-coherence: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Unit and coefficient associativity of compact-support projection maps. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-quotient-diagram-projection-evaluation: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Finite-coefficient evaluation of the quotient-diagram projection mate. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-ringed-coefficient-projection-cocycle: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Coefficient projection cocycle for ordinary derived ringed diagrams. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-scalar-tensor-pullback-normalization: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Scalar/tensor pullback normalization on a K-flat representative. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-supported-constant-exchange-normalization: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical closed constant exchange and its underived comparison square. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-supported-triangle-mate-identification: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Counit identification of a scalar support-triangle comparison. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-system-clopen-tensor-compatibility: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Proper/open tensor-mate interchange on varying-coefficient systems. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-system-compactification-pf-substitution: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Refinement comparisons intertwine strict-system projection maps. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-system-level-projection-formula-coherence: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Strict-system projection formula composition coherence. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-system-projection-tensor-associativity: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Tensor-variable associativity of the specified system projection maps. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-system-tensor-transpose-composition: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Composition of the counit-defined tensor transposes on systems. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-pur-weil-basechange-semilinear-pasting: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Mixed geometric base-change and semilinear exchange pasting. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sbc-adic-finite-exchange-encoding: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Finite quotient realization preserves the actual smooth-exchange mate. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sbc-base-change-restrict-scalars-arrow: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Étale base-change arrows commute with restriction of coefficients. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sbc-base-change-restrict-scalars-comparison: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Coefficient comparison isomorphisms for the base-change source and target. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sbc-completed-operations-linear-natural-exchange: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Linearity and naturality of completed pullback, direct image, and exchange. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sbc-derived-base-change-arrow-localization: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Derived base-change arrow under etale localization. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sbc-integral-test-pushforward-arrow: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Integral pushforward identifies the two test-base comparison arrows. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sbc-reflector-square-mate-factorization: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Factorization of a reflected square mate through its ambient mate. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sbc-restrict-scalars-derived-adjunction-identities: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical coefficient comparisons preserve the derived adjunction. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sbc-restrict-scalars-derived-exchange: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical coefficient comparisons commute with derived exchange. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sbc-restrict-scalars-pullback-square-comparison: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical coefficient comparisons preserve inverse-image square transport. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sbc-ringed-topos-sheaf-slice-derived-comparison: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical unbounded derived adjunction comparisons on arbitrary sheaf slices. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sbc-unbounded-exact-adjunction-square: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Constant towers and evaluations preserve the unbounded derived adjunctions of a ringed morphism. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sf-adjunct-conjugate-open-factor: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Transport a mate through conjugation and cancel an open factor. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sf-ambient-proper-open-pasting: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Normalized proper/open pasting on ambient pro-etale and semilinear-system categories. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sf-cbc-constant-perfect-projection-models: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Constant finite-projective models and evaluated diagram projections. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sf-cbc-constant-tower-direct-image-normalization: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Constant strict towers and normalized derived direct image. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sf-cbc-direct-image-reduction-unit: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Strict direct-image reduction and its completion-unit normalization. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sf-constant-semilinear-generator-comparison: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Scalar restriction identifies the single proper and open reduction generators. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sf-exceptional-product-direct-image-compatibility: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Exceptional external product is compatible with immersion direct images. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sf-finite-exchange-projection-commshift: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Finite geometric exchange and projection commute with shifts. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sf-integral-open-product-diagram-normalization: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Strict-diagram normalization of integral open product comparisons. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sf-kunneth-coherence: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Coherence of the relative product. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sf-native-weil-open-proper-interchange: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Proper/open interchange for native bounded constructible Weil complexes. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sf-semilinear-proper-open-mate-pasting: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Intrinsic proper/open mates and pasting for varying coefficient systems. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sfb-base-change-identity-open-restriction: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is The canonical base-change mate is identity on an open isomorphism locus. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sfb-coefficient-push-filtered-legs: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Flat coefficient push comparison from a bounded filtered module presentation. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sfb-etale-proetale-scalar-counit-transposes: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Common counit transpose of the two site/scalar direct-image composites. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sfb-etale-proetale-scalar-mate: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Étale/pro-étale comparison intertwines scalar direct-image mates. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sfb-identity-open-underived-square-normalization: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Underived adjunction and pullback-square normalization at an identity open locus. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sfb-integral-quotient-exchange-comparison: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Reduction of the actual unbounded integral exchange. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sfb-integral-quotient-projection-comparison: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Reduction of the actual unbounded integral projection morphism. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sfb-integral-quotient-section-mate-realization: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Integral quotient scalar and geometric mate realization in section modules. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sfb-internal-scalar-mate-projection: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Restriction of an internal coefficient mate is the specified projection map. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sfb-kflat-scalar-comparison-normalization: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Representative and adjunction normalization of scalar pullback comparison. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sfb-norm-algcl-internal-hom-base-change: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Norm-algebraic-closure scalar extension preserves constructible derived internal Hom. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sfb-ringed-comparison-tensor-adjunction: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Tensor and adjunction compatibility of canonical ringed-topos path comparisons. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sfb-ringed-kunneth-factorizations: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Two factorizations of the ringed-topos external product comparison. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sfb-ringed-projection-canonical-normalization: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Identity and composition normalization of ringed projection mates. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sfb-ringed-projection-first-shift: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is The ringed projection mate commutes with shifts in its direct-image input. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sfb-ringed-projection-section-specialization: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Symmetry-ordered section specialization of the canonical projection mate. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sfb-ringed-projection-tensor-associativity: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical tensor constraints and associativity for one projection mate. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sfb-ringed-projection-tensor-composition: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Tensor and composition coherence of ringed-topos projection maps. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sfb-trace-base-change-first: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Trace and base-change rearrangement before the first triangle. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sfb-trace-base-change-second: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Trace and base-change rearrangement before the second triangle. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sp-binary-cover-site-presentation: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is A simultaneous subterminal site presentation and its module equivalences. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sp-completion-mate-comparison: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is The strict quotient-tower exchange realizes the completed-adjunction mate. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sp-constant-perfect-quotient-projection: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Perfect projection for one constant quotient. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sp-finite-free-direct-image-coherence: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Coherent finite-free coefficient comparison for ambient derived direct image. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sp-finite-free-direct-image-columns: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Finite-basis columns of the restricted canonical coefficient mate. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sp-flat-coefficient-chain-transpose: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Scalar extension of flat chain maps and their canonical derived transposes. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sp-p1-counit-scalar: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Scalar compatibility of the actual projective-line adjunction counit. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sp-proetale-direct-image-scalar-cocycle: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Coefficient cocycle for the ambient proper-comparison mate. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sp-proetale-projection-mate-identification: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Identify the prescribed pro-etale scalar/direct-image mate with the ringed-topos mate. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sp-proper-open-comparison-normalization: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Structural normalization of explicit proper/open comparison. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sp-varying-ring-proper-open-pasting: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Clopen proper/open projections and pasting over a varying ring system. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-sp-varying-ring-pullback-unit-coherence: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Identity unit law for actual varying-ring inverse-image compositors. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-trf-big-small-etale-localization-derived-pushforward: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Localization of big etale derived direct image and base-change compatibility. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-trf-bounded-below-derived-mate-model: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Bounded-below derived mates are computed by underived mates and comparison units. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-trf-external-comparison-triangles: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Triangle compatibility of the external direct-image comparison. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-trf-finite-horizontal-shriek-mate: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Compact-support exchange as a mate along finite horizontal arrows. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-trf-frobenius-transports-scalar-extension: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Coefficient compatibility of the chosen compact-support Frobenius transport. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-trf-proper-small-big-etale-derived-comparison: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Proper derived direct image comparison between small and big etale sites. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-trf-simplicial-proper-exchange: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Proper exchange for a simplicial etale augmentation. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-trf-support-product-base-change: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Support-product comparison with base change along the other leg. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-trf-weil-shriek-iterates: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Iterates of the Weil $!$-pushforward. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-boundary-proetale-projection-comparison: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Proper compact-support and tensor comparisons identify etale and pro-etale projection maps. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-arbitrary-ring-torsion-sheaf-base-change: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Injective acyclicity gives sheaf-level base change for arbitrary coefficients. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-augmented-diagram-projection-mate: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Projection mate for an augmented coefficient diagram before taking inverse limit. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-completed-exchange-unit: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Completed exchange extends the ordinary mate along its unit. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-completed-ordinary-comparisons: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Normalized ordinary coefficient, identity and composition comparisons. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-completed-pullback-reflection: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Reflection through the specified completed pullback unit. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-derived-adjunction-shift: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical derived ringed-topos adjunction is shift-compatible. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-derived-exchange-bounded-comparison: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is The bounded below exchange comparison equation. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-derived-exchange-module-termwise: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is K-injective representative of the module derived exchange mate. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-derived-exchange-termwise: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is The termwise construction of the derived exchange morphism. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-derived-exchange-unbounded-transport: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Transport of the exchange equation to arbitrary K-injective representatives. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-derived-inverse-image-composition: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Composition isomorphisms of derived inverse images and their coherence. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-derived-square-iso-pasting: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Identity and pasting laws of the derived square isomorphism. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-direct-image-composition-coherence: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Associativity and unit laws of the composition isomorphisms of direct images. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-discrete-exchange-site-comparison: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical etale/pro-etale exchange comparison for arbitrary discrete rings. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-etale-underived-exchange-restriction: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Underived exchange along an etale morphism is the restriction identification. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-exchange-forget-coefficients: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is The derived exchange morphism commutes with forgetting the coefficient ring. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-exchange-mate-cube: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Naturality of the adjunction mate across a cube. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-finite-level-rectangle: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Finite-level exchange rectangle. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-flat-scalar-tower-exchange: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Flat scalar restriction transports the strict-diagram adjunction mate. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-formal-exact-projection-mate: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Formal exact projection mate for specified shift and unit data. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-frobenius-exchange-restriction: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Finite-level exchange is the restricted ambient exchange. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-intrinsic-finite-exchange-rectangle: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Finite exchange rectangle for intrinsic coefficient reduction. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-mate-pasting: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Mates of pasted squares and of conjugate-whiskered squares. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-mate-whisker: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Mates are natural in the non-adjoint sides of the square. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-module-abelian-derived-exchange-compatibility: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Canonical coefficient comparisons intertwine derived exchange. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-module-abelian-stalk-exchange: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Forgetting module coefficients in the stalk of derived exchange. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-module-abelian-underived-exchange: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Coefficient forgetting respects underived exchange. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-ordered-exchange-coefficient-comparison: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Coefficient normalization of the raw ordered completed exchange. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-ordinary-ringed-exchange-coherence: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Identity and pasting for ordinary ambient ringed exchange. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-quotient-diagram-scalar-projection: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Strict quotient balancing preserves the diagram projection formula. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-realization-completed-mate: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Ordered completed exchange equals the completion-unit-conjugated ordinary mate. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-reflected-adjunction-coefficient-squares: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Unit-normalized reflection of coefficient squares and their adjunction mates. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-ringed-exchange-tensor-coherence: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Projection-formula coherence for a square of ringed topoi. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-ringed-projection-global-model: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Existence of the canonically normalized global projection package. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-ringed-projection-local-model: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Localization of a normalized global projection package. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-ringed-projection-mate-exact: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Exactness data for the ringed-topos projection mate. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-ringed-projection-restriction: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Localization comparisons for the ringed projection mate. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-ringed-projection-tensor-comparison: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Descent and signed shifts of the normalized pro-etale tensor comparison. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-ringed-slice-pullback-mate-normalization: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Slice pullback comparison is induced by the ringed localization square. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-signed-projection-resolution-normalization: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Normalized signed totalization on chosen finite-projective resolutions. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-square-iso-pasting: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Identity and pasting laws of the sheaf-level square isomorphism. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-strict-tower-exchange-mate-normalization: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Strict tower exchange agrees with the canonical mate. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-tensor-arrow-mate-naturality-shifts: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Naturality and shifts of the tensor mate of an arbitrary arrow. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lem-weil-pbc-tensor-arrow-mate-right-unit: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Right-action evaluation of the tensor mate of an arbitrary arrow. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lemma-weil-pbc-completed-exchange-coherence: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Completed exchange coherence. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lemma-weil-pbc-frobenius-tower-compatibility: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Frobenius compatibility with tower transitions. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lemma-weil-pbc-perfect-projection-formula: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Perfect projection formula for reductions. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lemma-weil-pbc-projection-formula-base-change-naturality: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Operator and base-change naturality of the formula. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs lemma-weil-pbc-projection-formula-tower-compatibility: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Projection formulas form a coefficient tower. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs prop-coef-integral-dualizing: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is The integral dualizing object and its adjunction. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs prop-weil-pbc-derived-inverse-image-adjunction: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Derived adjunction of inverse and direct image on D^+. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs prop-weil-pbc-direct-image-limits: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Direct image, derived limits, and completeness. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs sbc-thm-adic-smooth-base-change: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Adic smooth base change. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs sbc-thm-bounded-derived-smooth-base-change: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Bounded derived smooth base change. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs sk-def-exchange: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Derived exchange. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs sk-def-sf-exchanges: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Exchange and projection transformations, typed. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs sk-lem-pbc-finite: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Finite morphisms. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs sk-thm-properbasechange: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Proper base change on classical pro-étale complexes. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs sk-thm-smooth-base-change: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Smooth base change. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs thm-cbc-complete-proetale: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Complete pro-etale compact-support base change. Shared foundational tag is not equality of statements.

lem-sf-tensor-square-mate-transfer vs thm-sf-direct-image-tor-amplitude: the new node states a conditional categorical transfer for mixed tensor actions with the explicit common transpose, without geometric assumptions; the existing node is Direct image and finite Tor amplitude. Shared foundational tag is not equality of statements.

Further close candidates checked directly: lem-asd-adjunction-projection-map-mate concerns left-adjoint projection maps; our new transfer concerns right-adjoint counit projection maps with mixed actions and no second adjunction on J,K. lem-sf-semilinear-proper-open-mate-pasting supplies the system identification and is reused. lem-pur-system-clopen-tensor-compatibility and lem-sf-proper-open-tensor-compatibility state the downstream tensor-mate identity and depend on the parent, whereas new node 1 is before taking proper mates and new node 2 is conditional on its tensor square. lem-sf-semilinear-alpha-pullback concerns geometric base change, not tensor comparison. The blueprint searches for tensor mate, proper open, clopen, mate projection, open tensor, tensor compatibility and restriction adjunct found no node stating either new lemma. All DAG title and statement candidates were searched across all chapters; project concept searches found no exact completed declaration.

## What remains

The two new proofs are intentionally unstarted, so parallel workers can claim them. All original mathematical content is assigned above. No unresolved statement dispute or external literature request.
