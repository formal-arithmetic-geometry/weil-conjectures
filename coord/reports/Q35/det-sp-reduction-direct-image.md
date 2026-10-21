## Files written

- `dag/nodes/sec-smooth-purity/det-sp-reduction-direct-image.json`: statement unchanged; five-step assembly proof, 2120 characters, status `split`.
- `dag/nodes/sec-smooth-purity/lem-sp-supported-etale-tensor-origin.json`: new statement-only node, status `unsplit`; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-sp-proetale-direct-image-scalar-cocycle.json`: new statement-only node, status `unsplit`; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-sp-proetale-open-scalar-cocycle.json`: new statement-only node, status `unsplit`; no Mathlib match.
- `citations.json`: verbatim quotations supporting every node cited in every item step. Search logs and original outputs are retained unchanged.

Three new nodes; zero Mathlib leaves. Each new record has `proof: []`, `proof_deps: []`, and `proof_origin: null`. The arguments from the prior attempts are preserved as research notes below for their future stage-1 workers. They are not delivered as completed splits.

## Attachments

None. Searches of the live `lean/WeilConjectures/` by the item id and by compact-support coefficient change do not yield a declaration covering the entire arbitrary-finite-ring pro-etale comparison and its cocycle. The existing etale compact-support coefficient change concerns different categories and coefficient hypotheses. I read `lean/Sheaf/SecSmoothPurity/ReductionDirectImage.lean`: the claimed isomorphism and cocycle still have `sorry` proofs. Real definitions in `def-sp-reduction-direct-image-comparison` are reused, not reconstructed.

## WANTED

None. All sources used are available in the read-only repository.

## What was wrong and what changed

This repairs the human's deliberate 2026-10-21 re-split of an existing reviewed node. The current repository item is identical in every field to the retained `returned-item.json`; the retained repair differs from it only in `proof`, `proof_deps`, `proof_origin`, and `split_report`. Its statement is byte-for-byte unchanged. The existing Lean record, statement dependencies, blueprint/import data, prior audits, and accepted top-level tool uses are preserved.

The retained attempt had already reduced the eleven-step, 11273-character proof to a five-step, 2120-character assembly, but delivered its three refinement lemmas as proved `split` nodes. The mandatory initial dry run on this retry exited 1 and rejected exactly those three statuses. The latest route note explicitly resolves that conflict: new nodes are statement-only `unsplit`, with the next stage-1 worker responsible for splitting them. I changed exactly that shape and retained the previous proofs and report in the sandbox (`extracted-research-notes.md`, `retained-report-before-statement-only-repair.md`) and the research notes below. No gate or launcher file was changed.

Former Steps 1-2 use the existing owning definition of the actual natural B-linear counit mate, normalized open scalar isomorphism, and composite b. Former Step 3 is the new supported etale tensor-origin lemma. Former Step 4 uses the existing module/abelian derived direct-image comparison instead of repeating its injective-resolution proof. The finite presentation of B is a two-line finite-set argument within the item; the non-elementary finite-window projection theorem already has its node. The existing two transpose lemmas carry former Steps 6-8. General preservation gives Dctf membership. The former proper and open cocycle arguments become separate unsplit nodes; the final item step is just their displayed naturality paste. No new node restates compact-support invertibility or its full cocycle. All item steps are below 2000 characters, and its entire proof is well below 3000.

## Source error retained from the baseline

The baseline already corrected the missing standing separated finite-type-over-one-field setting, and retained its earlier `STATEMENT-DISPUTED` discussion in `previous-report.md`. No statement change is made by this repair. The intended finite-type setting is the one used in Stacks 0F10 and in the unit's uniform cohomological-dimension argument. No flatness, finite-pd, smoothness or separably-closed-field assumption is added.

## Not duplicates

I searched the whole DAG by scalar/coefficient composition, cocycle, open extension, tensor origin, supported origin and cohomological dimension, and ran whole-blueprint searches for extension by zero, cohomological dimension, scalar cocycle, open scalar, etale tensor origin, coefficient composition and tensor origin. I read the statements of the following close candidates before creating any node.

- lem-sp-proetale-open-scalar-cocycle vs lem-coef-etale-open-scalar-coherence: the latter is on the etale site with its specific cochain normalization interfaces; it does not state the ordinary pro-etale normalized open comparison used here.
- lem-sp-proetale-open-scalar-cocycle vs lem-fix-open-scalar-exchange: the existing statement commutes coefficient change with an open base-change square for one coefficient map; it does not give the tower A to B to C equation.
- lem-sp-proetale-open-scalar-cocycle vs def-sp-reduction-direct-image-comparison: the existing definition fixes e as an actual isomorphism; the new statement proves its coefficient-tower equation.
- lem-sp-proetale-direct-image-scalar-cocycle vs lem-sp-finite-free-direct-image-coherence: the existing theorem requires finite-free ring-sheaf extensions, while the new equation has arbitrary finite ell-primary ring maps and makes no invertibility assertion.
- lem-sp-proetale-direct-image-scalar-cocycle vs lem-fix-direct-image-scalar-exchange: the latter commutes one coefficient comparison with geometric base change; the new equation composes two coefficient maps without a base-change square.
- lem-sp-proetale-direct-image-scalar-cocycle vs lem-weil-pbc-mate-pasting: generic pasting alone does not identify the two scalar/pullback tensor comparisons with the specified coefficient associator; the new proof verifies that normalization and then computes the actual counit transposes.
- lem-sp-supported-etale-tensor-origin vs lem-weil-pbc-finite-ring-constructible-derived-origin: the existing equivalence supplies L and is reused; it does not state boundedness of the open-supported etale tensor H, which need not be bounded below for arbitrary etale input.
- lem-sp-supported-etale-tensor-origin vs lem-sf-bounded-below-ctf-reflection: the existing theorem is for valuation-quotient coefficients and starts with an object already in Dplus; the new lemma allows arbitrary finite coefficient maps and establishes H is in Dplus before using a bounded-below theorem.
- lem-sp-supported-etale-tensor-origin vs lem-cbc-proetale-extension-zero-comparison: the existing sheaf isomorphism is reused termwise; it does not assert tensor-origin boundedness.
- lem-sp-supported-etale-tensor-origin vs lem-weil-pbc-constructible-reduction-direct-image: that is an intrinsically complete valuation-ring proper-pushforward statement, not a finite-ring open-supported etale tensor-origin statement.
- lem-sp-supported-etale-tensor-origin vs lem-finite-compact-support-scalar-transport: that theorem compares named compact-support maps for bounded-below origins already given; it does not produce or bound H.

None of the new statements is a clause of the item: the origin lemma concerns an open immersion without proper pushforward, and the two cocycle lemmas hold on arbitrary ambient complexes, without either a compactification or an assertion that the proper comparison is invertible. The substantive finite-window argument is reused through its existing node, not moved into a new restatement.

## Mathlib searches

Every new node has its own six actual searches through `batch2/msearch.py Q35 det-sp-reduction-direct-image`: two LeanFinder phrasings, LeanSearch, Loogle and two Mathlib greps. The query strings in its JSON are exact matches to `searches.jsonl`. All services returned successfully; no outage is recorded as a negative result. I read the outputs, including their signatures and modules. The open searches found ordinary module scalar associativity and Zariski restriction comparisons, not pro-etale derived open extension. The proper searches found `CategoryTheory.mateEquiv_vcomp`, `mateEquiv_hcomp`, ordinary module scalar adjunctions and sheaf pullback composition. I read Mates.lean lines 159-195 and PullbackContinuous.lean lines 165-182: these give generic pasting and underived pullback composition, not the scalar-tensor normalization for the named derived coefficient maps. Neither new cocycle is a one-line specialization without that normalization. The origin searches found algebraic etale base change and `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`; the latter requires the bounds, whereas the new lemma proves the tensor bound and its etale origin. No Mathlib leaf is claimed. The item's old searches are retained; it already has Lean statements and is not newly a Mathlib candidate.

## Unfinished work

The item has a complete short assembly proof. The three new lemmas intentionally join the stage-1 queue as statement-only nodes, as required by the latest route note. No Lean was written or compiler, Lake, build, direct git command, shared-repository write, launcher write, or sub-agent was used.

## Review by Q35

I read `coord/brief-stage1.md`, `stages/1-dag.md`, the three blueprint levels in SETUP, GOAL, and delivery-errors B-E. I compared current main, the returned head and the retained sandbox by parsed JSON, and checked statement equality separately. I read the unit `sk-lem-sp-reduction`, chapter `sec-smooth-purity`, and all four paragraphs of the main-20261015 direct-image blueprint proof. The source route is still compactification, open tensor comparison, finite free terms and finite windows, then scalar associativity. No SGA source or substitute purity route is used. This detail node is not the unit's key statement, so neither unit nor chapter is edited.

For the new tensor-origin statement, I read Stacks `proetale.tex`, 09AK (`lemma-compare-constructible`) and 09AL (`lemma-compare-constructible-derived`), and the existing arbitrary-finite-ring origin theorem. Finite rings are Noetherian, so 09AL applies. I read the exact etale/pro-etale open extensions and their comparison, tensor pullback, scalar-extension preservation and the exact sheaf comparison unit. These support the recorded research argument: choose L, extend it by zero to K, identify its comparison with N, then reflect the finite interval of the tensor H from its comparison. The crucial lower bound is proved before any D+ direct-image comparison is applied. The statement introduces all coefficient rings, schemes, complexes and maps; it assumes finite Tor amplitude of M, not finite projective dimension of B.

For each new cocycle statement, I read the precise normalized comparison definition and the blueprint's Step 4. The proper node is for any scheme map and any ambient complex; it asserts equality of the named counit mates, without invertibility. Its research calculation verifies tensor-pullback associativity before transposing the two counits. The open node is for an arbitrary open immersion; it asserts equality of the normalized B-linear isomorphisms. Its research calculation uses equality after restriction only for maps between objects in the image of j!, with the open unit justified from the extension presheaf and localized-site equivalence. Neither lemma assumes the parent's proper compactification or Dctf hypotheses. These are strictly smaller comparison lemmas, not replacement names for the item.

For item Step 1, I opened `def-sp-reduction-direct-image-comparison` and the new tensor-origin statement. The former explicitly provides natural gamma, the open isomorphism e, and b=Rp_*(e)gamma, so the step does not infer invertibility of b from a bare definition. The latter explicitly provides bounded K and H and both comparison identifications. The hypotheses apply to the given finite rings, open immersion, and finite-Tor constructible M.

For Step 2, I opened `lem-kun-0f10`, `def-kun-cd`, `lem-weil-pbc-module-abelian-derived-direct-image-comparison`, and `lem-sf-projection-finite-constant`. I checked Stacks `etale-cohomology.tex`, 0F10 (`lemma-finite-cd`), clause (1): the field need not be separably closed. The module/abelian theorem explicitly compares derived direct images on D+; each module sheaf F is an object in degree zero there, so its underlying higher images have the same bound. Every A-module is ell-primary torsion. The finite ideal set makes A Noetherian; a finite free surjection onto B has a finite kernel, giving finite presentation. Thus all hypotheses of the existing Dminus finite-window projection theorem are supplied. The step does not require a bounded flat constructible model or finite pd of B.

For Step 3, I read both existing normalized transpose statements, the actual derived adjunction definition, and the ring-sheaf change-adjunction statement. They respectively supply the restricted scalar mate's transpose, the identical transpose for the transported etale projection with K,H in D+, injectivity of transposition, the direct-image restriction isomorphism d, and reflection of isomorphisms. Properness supplies the qcqs hypothesis used by the underlying site comparison. Hence the invertible map is the specified gamma, and composing with the already specified open isomorphism gives precisely b. No identification is taken from an unpublished proof detail.

For Step 4, I read `sk-prop-sf-rf-shriek-preservation` and clauses (1), (2), and (4) of `det-sp-scalar-extension-functor`. The former's restricted adjunction explicitly gives Rf! preservation over arbitrary finite commutative ell-primary rings, after its stated ordinary-module identification. It applies for both A and B. Scalar extension gives M_B and source membership. The category is full, so the ambient isomorphism is an isomorphism in Dctf. Naturality is explicitly part of the owning comparison definition.

For Step 5, I read both new cocycle equations, the actual definition b=Rp_*(e)gamma, and naturality of scalar associativity. The displayed middle equality is gamma naturality at e; the last equality substitutes the two cocycles. Restoring their alpha maps gives exactly the equation in the item, with the alpha on Rf!M on the left and Rf! of alpha_M on the right. The remaining paste is an elementary three-line composition of those cited equations; no additional comparison lemma is hidden in it.

For B1-B10 I checked all new records are self-contained statement-only nodes, have single-escaped TeX and exact blueprint places, inherit the correct chapter/unit, and retain actual search queries. The saved search outputs were reread rather than rerun: the statements and search questions have not changed. I read the generic Mathlib mate-pasting and underived sheaf pullback composition candidates; neither gives the named derived scalar normalization by a one-line specialization. For C1-C5 I read every cited statement and audited all citation quotations verbatim. No external tag is used as a substitute for a node. Proposed off-unit generic tools are named with specific reasons in split_report; top-level maintainer-owned tool uses are untouched. For C6 and D1-D5 I traversed the locally available dependency closures, found no path back to the item, checked the new nodes do not cite the parent, and checked the assembly uses statements rather than proof internals. The server preflight supplies the authoritative global DAG check. No node is an elementary finite-set argument or a duplicate of a broader existing node.

Small cases for E1-E7 were zero complexes, empty opens and schemes, j=id, p=id, A=B=C, zero target rings, and the nonflat map Z/ell^2 to F_ell. Both cocycles reduce to unit/counit identities for identity coefficients and to equality of zero maps for zero inputs. The tensor-origin hypothesis finite Tor amplitude is essential: M=F_ell over Z/ell^2 would not satisfy it, while M=A does and tensors to bounded B despite B having infinite pd over A. The origin lemma therefore does not mistakenly claim an arbitrary bounded input has bounded reduction. No geometric-point conservativity on arbitrary pro-etale complexes is invoked.

The concrete repair on this retry is removal of the three children's completed-split proofs/status, preservation of those arguments here, and clarification of the generic-tool reasons. The old claimed gate conflict is obsolete under the explicit statement-only route note. The initial failed dry run was fully polled before any subsequent invocation.

## Retained research notes for future stage-1 splitting

The following arguments were present in the earlier sandbox. They are retained as research evidence only; the new node records have no proof steps or proof dependencies.

### lem-sp-proetale-direct-image-scalar-cocycle

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-direct-image.proof.md, Step 4: projection maps compose because their counit transposes compose; returned Step 10.

1. Write $\lambda^{A,B}:q_B^*T_Y^{A,B}\simeq T_Z^{A,B}q_A^*$ for the balanced tensor comparison defining $\gamma$. Its compatibility with $\alpha$ follows on K-flat tensor representatives: the two paths pull back $((x\otimes b)\otimes c)$ to $q^*x\otimes\psi(b)c$. These equal balanced multilinear maps give equal maps of total complexes, hence equal derived maps. The K-flat pullback/tensor description and scalar associativity are exactly those of the cited statements. Uses: lem-weil-pbc-ringed-topoi-derived-tensor-pullback, det-sp-scalar-extension-functor, def-sp-reduction-direct-image-comparison.

2. Use those identifications to suppress $\lambda$ and $\alpha$. For $d=\gamma^{B,C}_{T E}\,T_Y^{B,C}(\gamma_E^{A,B})$, its $C$-adjoint transpose is
$$\begin{aligned}
\varepsilon^C q_C^*d
&=T_Z^{B,C}(\varepsilon^B_{T E})\,T_Z^{B,C}(q_B^*\gamma_E^{A,B})\\
&=T_Z^{B,C}\bigl(T_Z^{A,B}(\varepsilon^A_E)\bigr).
\end{aligned}$$
The first equality is the defining counit identity for $\gamma^{B,C}$ and naturality of $\lambda$; the second is the identity for $\gamma^{A,B}$. After associativity this is $T_Z^{A,C}(\varepsilon^A_E)$, the defining transpose of $\gamma_E^{A,C}$. Injectivity of the derived adjunction bijection proves the displayed equation with its $\alpha$ maps restored. Naturality holds because $\gamma$ and $\alpha$ are natural transformations. Uses: def-sp-reduction-direct-image-comparison, def-weil-pbc-proetale-operations, det-sp-scalar-extension-functor.

### lem-sp-proetale-open-scalar-cocycle

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-direct-image.proof.md, Steps 1 and 4: extension-by-zero scalar maps and their coefficient associativity; first paragraph of returned Step 11.

1. The open adjunction has unit $F\xrightarrow{\sim}j^*j_!F$. Indeed, on an object $V\to U$, the extension presheaf restricts to $F(V)$; all objects covering $V$ also factor through $U$, uniquely by the localization statement. Thus sheafification still restricts to $F$. Both functors are exact, so this identity and the adjunction hold termwise and descend to derived categories. Consequently restriction is injective on $\operatorname{Hom}(j_!P,j_!Q)$: the adjunction identifies this set with $\operatorname{Hom}(P,Q)$. Uses: def-weil-extension-by-zero, lem-weil-proetale-weakly-etale-localization, lem-cbc-proetale-extension-zero.

2. Under these unit identifications, $j^*e^{A,B}$ is the canonical scalar/restriction comparison: $e$ was defined by the unique comparison of composite left adjoints with the identity between their right adjoints. In the adjunction formula its restriction is therefore the tensor identity. The balanced tensor description of scalar extension and its associator makes the restrictions of the two maps in the assertion equal: both send $((m\otimes b)\otimes c)$ to $m\otimes\psi(b)c$. The same equality holds degreewise on K-flat representatives and survives localization. Their common source is isomorphic, via the successive $e$ maps, to $j_!^C(T_U^{B,C}T_U^{A,B}M)$, while the target is $j_!^CT_U^{A,C}M$. Injectivity from the first step now proves equality before restriction. This uses restriction only on the image of $j_!$, not on arbitrary pro-etale complexes. Uses: def-sp-reduction-direct-image-comparison, det-sp-scalar-extension-functor, lem-cbc-proetale-extension-zero.

### lem-sp-supported-etale-tensor-origin

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-direct-image.proof.md, Step 1: open-supported tensor comparison, made compatible with etale origin for the finite-window argument of Steps 2-3; returned Step 3.

1. The arbitrary-finite-ring constructible derived-origin equivalence supplies $L$ and $\nu_U^*L\simeq M$. Exactness of etale open extension makes $K=j_!^{\mathrm{et},A}L$ bounded. The natural sheaf comparison $\nu_Z^*j_!^{\mathrm{et},A}\simeq j_!^{\mathrm{pro},A}\nu_U^*$ extends termwise, since all three functors are exact; hence it descends through quasi-isomorphisms and gives $\nu_Z^*K\simeq N$. Uses: lem-weil-pbc-finite-ring-constructible-derived-origin, lem-weil-pbc-extension-by-zero-exact, lem-cbc-proetale-extension-zero-comparison, lem-cbc-proetale-extension-zero, prop-weil-pbc-site-comparison-finite-level.

2. Tensor pullback identifies $\nu_Z^*H$ with $N\otimes_A^LB_Z$. The normalized open scalar isomorphism identifies the latter with the underlying $A$-complex of $j_!^BM_B$. Scalar extension preserves $\Dctf$, so $M_B$ is bounded, and exact pro-etale open extension preserves this bound. Finally $\nu_Z^*$ is exact and its sheaf unit is an isomorphism: for every $i$, $H^i(\nu_Z^*H)=\nu_Z^*H^i(H)$ and $H^i(H)\simeq\nu_{Z,*}\nu_Z^*H^i(H)$. Thus zero cohomology after comparison implies zero cohomology before comparison. The finite interval bounding $\nu_Z^*H$ bounds $H$. No bounded-below comparison theorem has been applied to $H$ before proving this bound. Uses: lem-weil-pbc-ringed-topoi-derived-tensor-pullback, def-sp-reduction-direct-image-comparison, det-sp-scalar-extension-functor, lem-cbc-proetale-extension-zero, prop-weil-pbc-site-comparison-finite-level.

## Validation

The initial retained-version dry run exited 1 with exactly three new-node status errors. After the statement-only repair, the single dry-run invocation exited 0: `OK (not pushed) deliver/Q35/det-sp-reduction-direct-image at 037b75277a5: preflight passed`. Its server preflight includes the mandated DAG and split reviews. Local JSON checks additionally verified the unchanged item statement, the proof-dependency union, all 18 step/node citation quotations, the three empty-proof child records, and the 2120-character assembly (longest step 601 characters). A final dry run is run after this report cleanup, and delivery follows only after that invocation exits successfully.
