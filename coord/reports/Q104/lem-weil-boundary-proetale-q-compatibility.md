# Q104 stage-1 repair: lem-weil-boundary-proetale-q-compatibility

## Files written

- `dag/nodes/sec-six-functors/lem-weil-boundary-proetale-q-compatibility.json`: existing statement unchanged; split into a 2345-character assembly using the new pre-adjunction calculation. Existing Lean, audit, import, blueprint and review metadata retained.
- `dag/nodes/sec-six-functors/lem-weil-boundary-q-defining-composite-comparison.json`: statement, unsplit; no Mathlib match. It compares the projection-inverse/symmetry/final-arrow composites, with arbitrary compatible arrows to an object Y, before taking any exceptional adjunction transpose. No proof steps or proof dependencies.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint tag and q/comparison notions. The actual item declaration in `lean/Sheaf/Paper/BoundaryProEtaleQCompatibility.lean` ends in `sorry`. `BoundaryQFoundation.lean` defines `etaleQForAdjunction`, `proT` and `qSourceIso`; these are constructions, not a proof of their comparison. No Lean was written or compiled.

## WANTED

None. The three source passages used are available locally. No SGA source was used.

## Fault repaired and scope

The human's return is a deliberate re-split of the existing reviewed stage-1 proof, not a request to attach its already stated Lean declaration. The sandbox contained only dispatcher marker files and no item, report, or prior searches; I copied the current repository node, which is the returned proof (step lengths 1545, 1029, 767, 557; total 3898). There was therefore no retained alternative split or report to discard. All writes are in the assigned sandbox. The current repository and launcher were read-only.

The new independent work item carries the entire old step 1 calculation. Its statement is more reusable than the q clause: B is any bounded-below source object, Y any bounded-below target, v any comparison isomorphism, and a_e,a_p any compatible arrows. Its conclusion concerns the untransposed composites, with no exceptional right adjoint, duality object, or q equality. The item specializes it to B=G_e N, Y=N, v=theta_N and the exceptional counits. The item still proves the mate step itself; the new node does not restate its q conclusion.

Old step 2 remains the counit/naturality proof that the mate comparison transports transposes. Old step 3 remains the evaluation square and induction on finite composites, now making the arbitrary-pairing transpose argument explicit. Its symmetry assertion cites the existing symmetric monoidal pullback theorem rather than silently taking coherence from a statement asserting only a tensor isomorphism. Old step 4 remains the boundary specialization and the finite-Tor hypothesis check. The item proof is 2345 characters, below 3000, with no step longer than 2000. The new statement is 2368 characters and is delivered unsplit for another worker.

## Sources and route

I read `dag/chapters/sec-six-functors.json`, `dag/units/sk-prop-sf-biduality-general.json`, the three-level rules in SETUP, GOAL, the stage-1 brief and stage document, and delivery-errors B–E. The unit uses the ordinary operation and exceptional-adjoint route. The new node has the item's chapter and unit. It supplies a subcalculation of the same boundary-duality route and does not replace a unit step or alter the chapter or unit files.

The item's blueprint ancestor is `cor-weil-boundary-duality-discharge`, as confirmed by `tools/blueprint_refs.py ancestor`. I read its main-20261015 proof, final paragraph, beginning “The inverse of this composite is beta_L” and explaining the tensor-Hom and exceptional adjunction transposes. That paragraph supplies the intended evaluation normalization, not a pre-existing q comparison theorem. I also read the comparison paragraph of main-20261015 `thm-sf-pf-proetale.proof.md`, which says comparison carries pullback, tensor and the named projection transformation, and the final paragraph of `lem-weil-finite-duality-site-comparison.proof.md`, which specifies evaluation and double-dual normalization. The composite calculation is agent-written from these hypotheses; neither the new node nor this report attributes it as a theorem already proved by the blueprint. The item's proof_origin remains agent. The new unsplit node's proof_origin is null.

## Search record

`searches.jsonl` records every actual invocation; the new node copies their tool/query strings unchanged. I ran LeanFinder on the composite calculation, Loogle on `CategoryTheory.Adjunction.counit, CategoryTheory.BraidedCategory.braiding`, grep for projection comparisons and braiding naturality in CategoryTheory, and LeanSearch on symmetric monoidal derived pullback and the inverse-projection/counit composite. I tried a second LeanFinder phrasing about naturality of tensor symmetry and a second grep in CategoryTheory/Monoidal before concluding no match. All services answered; no unavailable service is recorded as absence.

The first LeanFinder hits include `CategoryTheory.Adjunction.derivedε_fac_app` and related derived-counit formulas. I read Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean:115–131: its equation transports a derived counit and contains no inverse projection or tensor-symmetry composite. Grep returned `braidingNatIso_hom_app` and naturality lemmas in Mathlib/CategoryTheory/Localization/Monoidal/Braided.lean; I read lines 40–90. They descend a braiding through a localization, without the source/target comparison square or the projection-inverse/final-arrow composite. LeanSearch returned categorical pullback-symmetry projection identities and monoidality of an inverse equivalence; the second LeanFinder returned condensed internal Hom and Kaehler-differential identities. Their displayed types concern different objects. None is an exact match or one-line specialization of the new site-derived composite equality. The second grep for projection formula/morphism in CategoryTheory/Monoidal returned no hits. There are zero new Mathlib leaves.

Whole-DAG searches included projection/counit/symmetry/comparison combinations (then reading the statements of the plausible nodes) and the exact boundary-comparison names. Whole imported-blueprint searches used `transpose`, `exceptional tensor`, `signed symmetry`, `projection transformation`, `counit-defined`, `q-map`, and `inverse projection`. Broad literal searches also caught `smallEtale` in names; I filtered those by the mathematical statements instead of treating a string hit as a duplicate. No imported blueprint node states the new composite comparison. Its blueprint.same_as is empty; its from.node is the corollary and via is the item.

## Not duplicates

lem-weil-boundary-q-defining-composite-comparison vs lem-weil-boundary-proetale-projection-comparison: the existing node supplies the individual projection and exceptional-counit comparison squares; the new node assumes these squares and proves equality of a composite with two signed symmetries and an inverse projection, for arbitrary compatible final arrows. It does not re-prove either square.

lem-weil-boundary-q-defining-composite-comparison vs def-weil-boundary-q-foundation: the existing definition constructs q and t and the source isomorphism; it asserts no equality between the two t composites.

lem-weil-boundary-q-defining-composite-comparison vs def-weil-boundary-q-maps: this defines the exceptional q compatibility predicate, not a theorem establishing the pre-adjunction composite equality; the new node does not require an exceptional right adjoint.

lem-weil-boundary-q-defining-composite-comparison vs lem-sfb-ringed-derived-monoidal-comparisons: that theorem provides canonical pullback symmetry and composition coherence, not a projection-inverse/final-arrow comparison. It is reused in assembly step 3 rather than duplicated as a separate symmetry node.

lem-weil-boundary-q-defining-composite-comparison vs lem-pur-finite-ring-site-tensor-transpose: its third clause transposes an evaluation to the coefficient unit using exceptional adjoints on localizing categories; the new lemma allows arbitrary Y and compatible final arrows, assumes just the two component inverses, and proves an untransposed equality without that ambient-adjoint or global projection-formula assertion.

lem-weil-boundary-q-defining-composite-comparison vs lem-weil-boundary-alpha-normalization: the latter identifies an etale duality map as an isomorphism by a chain of Hom bijections, with no two-site composite comparison.

lem-weil-boundary-q-defining-composite-comparison vs lem-sf-proper-product-counit-transpose: this concerns the two ordinary pullback/direct-image adjunctions of a proper fiber product, rather than comparison between two sites with an arbitrary compatible arrow.

No Stacks tag is newly cited; consequently there are no new/existing same-tag collision pairs to add.

## Review by Q104

I checked the item against the three source passages above and retained its statement byte-for-byte, including both projection inverses as explicit assumptions. The existing projection-comparison node was read in full: its precise square includes the identity compactification and its transported exceptional counit. I have not inferred finite Tor amplitude for G_e N, or applied a projection formula whose first variable must have finite Tor. The new lemma requires component invertibility instead. Its fully written source and target comparisons r and s keep the two tensor orders separate. In the projection square the domain is F_p C_Z B tensor C_T M, with F_p(v) on the pro-etale side and eta_B on the etale side. The conclusion has domain F_p C_Z(i_e^* M tensor B) and codomain C_T M tensor C_T Y. Both composites type-check on paper, including c_T and eta directions.

Assembly step 1 cites only the new node. Its quoted conclusion in citations.json is precisely the untransposed equality used. B=G_e N is bounded constructible by the item, hence bounded below; the comparison makes B' bounded below. M and Y=N are bounded below. v=theta_N is an isomorphism, the arrow square is the assumed exceptional counit square, and the projection square is exactly the item's assumed transformation comparison in these coordinates. No additional hypothesis is inserted.

Assembly step 2 uses the two given adjunctions and the definition of their mate. Substituting f=mu_e composed with F_e(g), applying naturality, and using the stated counit square proves the displayed equation. The Hom bijection is injective, so transposing it proves the q equality. This is elementary adjunction algebra and needs no independent uncited theorem. The source of every transpose remains visible, including 1 tensor theta_N.

Assembly step 3 cites the statement of `lem-weil-finite-duality-site-comparison` for evaluation and its double-dual transpose, the statement of `lem-weil-duality-pairing` identifying evaluation's transpose as the double-dual map, and `lem-sfb-ringed-derived-monoidal-comparisons` for canonical comparison commuting with signed symmetry. I read all three statements; the quotes in citations.json are verbatim. The old citation `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` alone states a natural tensor isomorphism, so I corrected that C4 issue by citing the theorem that explicitly asserts symmetry coherence. It is a generic tool of another unit, declared in split_report.tool_uses with the reason, not in the maintainer-owned top-level tool_uses. For arbitrary pairings I verified the transpose identity by composing with evaluation and using the assumed evaluation-defined chi, not by assuming that the cited theorem already asserts transport of every arbitrary pairing. Composition then is literal pasting and cancellation of the middle comparison isomorphism; induction begins with a primitive arrow and adds one such square at a time.

Assembly step 4 is substitution N=D_T K in the already proved statements. Its last arrow is governed by the explicitly assumed compatible dualizing square. The seven finite-Tor assumptions in the recorded boundary construction cover K, its dual, their two inverse images and the indicated duals. This step uses earlier proved steps and hypotheses, not a preservation claim hidden in a definition node. It is elementary and cites no further node.

For the new node I checked B1–B9: it has only a self-contained statement, no proof, no proof_deps, no parent dependency, explicit finite coefficient ring and schemes and morphism, actual named tensor/pullback/projection constructions, three kinds of logged Mathlib search, and precise blueprint provenance. The arbitrary compatible arrows make its task strictly smaller and logically independent of exceptional q transpose and duality. It is not a two-line elementary lemma: it requires descending the comparison/symmetry coherence to derived tensor and an inverse-projection diagram calculation, the 1545-character argument previously concentrated in the parent. Its future proof can use existing general monoidal coherence instead of reconstructing foundations.

I tested i=id with identity comparisons: both composites are the same signed swap/projection-inverse/swap/final-arrow expression. For B=0, M=0, Y=0, or Z empty all maps have the stipulated zero source or target and the equality holds. For v a nontrivial isomorphism the r and s factors place v after comparison in both tensor orders; the final-arrow square cancels it, so identity v is not silently assumed. The inverse projection square is assumed only at the two named components; no global invertibility or boundedness for their tensor product is used. In degrees a,b the two corresponding braidings carry the same (-1)^{ab}; comparison preserves this sign because it is additive and termwise. No sign has been replaced by an unsigned swap.

The return's required new independent node, short assembly, preserved statement, statement-only delivery, and retained mathematical content are all present. The following verbatim record preserves the old proof as the detailed handoff for workers; the extracted calculation is a statement-only work item, not a disguised proof embedded in its statement.

## Preserved calculation and allocation of the old argument

The new node's worker takes old step 1 below, replacing G_e N by B, N by Y, theta_N by v, and the counits by compatible arrows a_e,a_p. Invert the stated projection square, use the canonical derived signed symmetry to move the two comparison isomorphisms across the swaps, use naturality of eta at the source swap, and substitute the final-arrow square. In full coordinates this is exactly the new conclusion with r,s,c_T. This includes every part of the displaced argument; no hypothesis that B is finite-Tor is needed. The remaining old steps are realized by the item's steps 2–4, with explicit evaluation-transpose uniqueness and the existing symmetry theorem as described above.

### Original step 1

Fix $M,N$ as in the statement and put $B=G_eN$. By [def-kun-projection-formula-map], $\pi^\tau$ is the counit-defined composite on each site. The hypotheses give, after the monoidal comparison $C_Z(B\otimes_A^Li_e^*M)\cong C_ZB\otimes_A^LC_Zi_e^*M$ [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] and the pullback comparison $C_Zi_e^*M\cong i_p^*C_TM$ [lem-weil-pbc-comparison-pullback], the two equalities $\eta_{B\otimes i_e^*M}\circ\pi^p=C_T(\pi^e)\circ(\eta_B\otimes1)$ and $\mu^p_{C_TN}\circ F_p(\theta_N)=C_T(\mu^e_N)\circ\eta_B$, where $\theta:C_ZG_e\cong G_pC_T$ is the adjunction comparison. Both $\pi$'s are invertible by hypothesis, so inverting the first equality gives $C_T(\pi^e)^{-1}\circ\eta=(\eta_B\otimes1)\circ(\pi^p)^{-1}$. Comparison $C_W=\nu_W^*$ is applied termwise [def-sf-comparison-derived-pullback]; on K-flat flat-term representatives the monoidal comparison is the termwise identification of total tensor complexes, so it commutes with the termwise signed symmetry $\sigma$. Now compute $C_T(t^e_{M,N})\circ\eta_{i_e^*M\otimes B}$: naturality of $\eta$ moves $C_TF_e(\sigma)$ past $\eta$ to $F_pC_Z(\sigma)$; the inverted projection equality replaces $C_T(\pi^e)^{-1}\circ\eta$ by $(\eta_B\otimes1)\circ(\pi^p)^{-1}$; naturality of $\sigma$ moves $\eta_B\otimes1$ to $1\otimes\eta_B$; and the counit equality turns $C_T(1\otimes\mu^e_N)\circ(1\otimes\eta_B)$ into $1\otimes\mu^p_{C_TN}F_p(\theta_N)$. Hence $C_T(t^e_{M,N})\circ\eta=t^p_{C_TM,C_TN}\circ F_p(1\otimes\theta_N)$ under the displayed identifications.

### Original step 2

Transpose the equality of Step 1. For $X$ on $Z_e$ and $Y$ on $T_e$, the adjunction comparison $\theta$ is by definition the mate of $\eta$: the transpose of $C_T(\mu^e_Y)\circ\eta_{G_eY}$ under $F_p\dashv G_p$ is $\theta_Y$. Hence, for any $f:F_eX\to Y$ with $F_e\dashv G_e$ transpose $g:X\to G_eY$, the $F_p\dashv G_p$ transpose of $C_T(f)\circ\eta_X$ is $\theta_Y\circ C_Z(g)$: both are obtained from $g$ by applying $C_Z$, then $\theta_Y$, and the counit identity $\mu^p\circ F_p(\theta_Y)=C_T(\mu^e_Y)\circ\eta_{G_eY}$ with naturality of $\eta$ shows they have the same transpose. Apply this with $X=i_e^*M\otimes_A^LG_eN$, $Y=M\otimes_A^LN$ and $f=t^e_{M,N}$, whose transpose is $q^e_{M,N}$. By Step 1 the left side is $t^p_{C_TM,C_TN}\circ F_p(1\otimes\theta_N)$, whose transpose is $q^p_{C_TM,C_TN}\circ(1\otimes\theta_N)$. Uniqueness of transposes gives $\theta_{M\otimes N}\circ C_Z(q^e_{M,N})=q^p_{C_TM,C_TN}\circ(1\otimes\theta_N)$, which is the statement $q^p_{C_TM,C_TN}=C_Z(q^e_{M,N})$ under the named comparisons.

### Original step 3

The main-20261015 finite-duality site-comparison statement identifies the internal-Hom comparison, the dualizing-object comparison, the evaluation pairings, and the double-dual maps on the bounded finite-Tor class. The duality-pairing statement defines the double-dual map as the tensor–Hom transpose of evaluation after tensor symmetry. Hence comparison commutes with each primitive arrow used in a pairing: q by Steps 1--2, evaluation and its transpose by the duality comparison, and tensor symmetry by the termwise symmetry compatibility of Step 1. Naturality and cancellation of comparison isomorphisms then show, by induction on finite composites, that every pairing built from these arrows has its transpose transported to the corresponding pro-etale transpose.

### Original step 4

Set H=D_{T,e}K. The displayed pairing is the finite composite consisting of tensor symmetry, the q-map of Steps 1--2, and evaluation followed by the compatible identification G_e omega_{T,e}≅omega_{Z,e}. The bounded finite-Tor assumptions ensure that every internal Hom, dualizing object, and projection map lies in the comparison class. Step 3 transports each arrow and its transpose, so the transpose of this etale composite is carried to the transpose of the identical pro-etale composite, with C_TK, G_p C_T D_{T,e}K and the pro-etale dualizing objects.

## Unfinished work

The new statement-only node is intentionally unsplit for a separate worker. No other requested stage-1 work remains apart from the delivery checks and push, recorded below when complete.
