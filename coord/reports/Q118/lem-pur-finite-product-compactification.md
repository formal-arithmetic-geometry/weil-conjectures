# Worker report: Q118 / lem-pur-finite-product-compactification

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-finite-product-compactification.json`: item, unchanged statement; four assembly steps totalling 2153 characters.
- `lem-pur-product-exchange-counit-coordinates`: new statement, unsplit, no Mathlib match; compatible product geometry, exchange factorization, open-counit square and the normalized composition coordinate.
- `lem-pur-product-open-tensor-projection`: new statement, unsplit, no Mathlib match; supported source and target tensor comparisons and the proper/open projection identity.
- `lem-pur-product-forward-coordinate-transport`: new statement, unsplit, no Mathlib match; complete coordinate expansion of the forward composite and its normalized change-of-choices equation.
- `citations.json`: exact statement excerpts for every parent step/node citation.

The three new JSON files are under `dag/nodes/sec-smooth-purity/`. They have no proof steps or proof dependencies: each is a separate task for another worker, and their statements are self-contained without depending on one another or on this item. Their statement sizes are 3384, 3708 and 4273 characters. The proofs below are retained as report material, not put in any unsplit node's statement. No Lean or repository file was written, and no compiler was run.

## Attachments

None. Searches for the blueprint id, `finiteProduct_compactification`, product compactification and finite-product names under `lean/WeilConjectures/` found no project declaration proving the item. `lean/Sheaf/Paper/FiniteProductCompactification.lean`, read at its final theorem and proof docstring, contains `AlgebraicGeometry.ProEtale.finiteProduct_compactification` with `sorry`; it is not an attachment.

## WANTED

None. The necessary source material is present locally.

## Repair and source assessment

The sandbox initially contained only dispatcher brief files: no retained JSON, report, citations or searches. I copied the current repository node, which has the ten-step 8668-character proof quoted in the return. `returned-node.json` preserves that read version for comparison. There was no sandbox split/report on which to run an initial dry run. The actual mathematical statement, existing metadata, Lean record, old searches, blueprint fields and import flags are preserved. The new split replaces the proof and its proof dependency union and updates only split status/report.

The return asks to spread the work, with at least two comparable statement-only arguments, and retain all of the original argument. This repair creates three independent tasks, rather than restating the final equality. The parent proves that equality by a three-line naturality calculation and endpoint transport. The first new node does not mention the final product equality. The second proves an intermediate projection diagram with the essential open counit still present. The third expands and transports the forward map but never equates it with the ordinary product map. No one new node carries the item as a whole.

Source read for the item and all three new nodes: `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md`, especially the opening compactification/coherence paragraph and final symmetry/proper-reduction paragraph. That paragraph invokes constructible finite-Tor isomorphisms and an abstract six-functor framework; this item instead compares the explicitly defined finite-coefficient forward maps, so its detailed map calculation is agent-written, as its existing proof_origin says. I preserved this distinction and do not cite the paragraph as a proof on its stronger bounded-below non-Tor domain. The actual ingredients are the precise ambient finite-level statements named below. No SGA route is used. The blueprint ancestry remains `prop-pur-affine-space-composition-law`, Steps 3–4, through finite trace factorization and finite forward-product symmetry; the current coherence proof supplies the same proper-reduction route.

### Complete allocation of the returned argument

- Old Step 1: coefficient/ambient-operation notation and domain discipline are explicit in every new statement; the calculation for a displayed pair and extension to other choices belong to `lem-pur-product-forward-coordinate-transport` and parent Step 4.
- Old Steps 2–4: all go to `lem-pur-product-exchange-counit-coordinates`: product square, finite-type/Noetherian/quasi-compact hypotheses, compatible compactification triangle, actual g=bk exchange, equality of rho with ordinary exchange, lambda normalization, the counit equation and its explicit intermediate identities.
- Old Steps 5–6: go to `lem-pur-product-open-tensor-projection`: invertibility of eta, cancellation of the two signed symmetries, full-faithful support arguments, and w=e(chi tensor 1) with their distinct sources retained.
- Old Step 7: goes to `lem-pur-product-forward-coordinate-transport` for T, including every PF/Ex factor and z. Its one-line substitution for Omega remains explicit in parent Step 3.
- Old Step 8: goes to `lem-pur-product-open-tensor-projection`: the proper/open projection identity before and after precomposition by B0, with every Gamma, d and delta factor typed.
- Old Step 9: remains, without lost calculation, in parent Step 3, which substitutes w, applies naturality in chi, uses the counit square, cancels only eta, applies Rb and the natural direct-image compositor.
- Old Step 10: goes to `lem-pur-product-forward-coordinate-transport` as the explicit theta_h T_1 = T_2(theta_f tensor theta_g) equation, with factorwise refinement transport and the base-changed q choice specified. Parent Step 4 applies it.

The full returned proof is transcribed verbatim below, so no detail of a future child's proof has been discarded or replaced by an unexplained summary.

## Not duplicates

Searches read the whole DAG statements by product-compactification / exchange-counit / Psi-nu / open-tensor keywords and `tools/blueprint_refs.py search` with `product compactification`, `compactification`, `open counit`, `proper open`, `projection mate`, `projection-mate`, `forward product` and `tensor counit`; ancestor was queried explicitly. The broad compactification list has 239 blueprint hits; the precise product and forward queries have none. No new Stacks result is asserted: these are map calculations at the named blueprint place, so no new Stacks tags collide.

- `lem-pur-product-exchange-counit-coordinates` vs `lem-exc-proetale-derived-open-restriction`: the latter gives rho and lambda on an open Cartesian square, not their identification with the specified exchange followed by the compactification counit square.
- `lem-pur-product-exchange-counit-coordinates` vs `lem-sf-proper-open-tensor-compatibility`: that node normalizes Gamma and gives a generic tensor identity; it does not assemble the product compactification geometry, g=bk exchange or A0/open-counit equation.
- `lem-pur-product-exchange-counit-coordinates` vs `lem-sf-composition-projection-mate`: the existing node gives projection/composition coherence for a supplied triangle; the new task identifies the actual product triangle and its exchange/counit coordinates.
- `lem-pur-product-open-tensor-projection` vs `lem-pur-finite-open-product-swap`: the existing node gives e, its equality across open factorizations and signed swap; it does not compare e to w via chi, or give eta and the B0-precomposed proper/open projection diagram.
- `lem-pur-product-open-tensor-projection` vs `lem-sf-open-tensor-normalization`: this is the generic beta/gamma normalization and full faithfulness; the new task proves the supported-source/counit comparison and their pasted product diagram.
- `lem-pur-product-open-tensor-projection` vs `lem-sf-proper-open-projection-mate`: this is the generic square identity; the new task retains the nontrivial two open comparisons, chi, eta, B0 and their fully typed substitution into it.
- `lem-pur-product-forward-coordinate-transport` vs `lem-pur-pf-refinement-compatibility`: the latter transports one PF factor, while the new task expands and transports the whole specified forward composite, including actual exchange and alpha.
- `lem-pur-product-forward-coordinate-transport` vs `fix-lem-exchanges`: item 4 of that node transports exchange only, not this projection/symmetry/composition word.
- `lem-pur-product-forward-coordinate-transport` vs `prop-compactification-coherence-detailed`: the latter compares underlying compact-support functors and supplies cocycles, not naturality of the forward word.
- `lem-pur-product-forward-coordinate-transport` vs `def-pur-compact-product-arrows`: that node defines ordinary compact exterior-product arrows for a different abstract coefficient setup, not this chosen finite pro-etale forward composite.
- `lem-pur-product-open-tensor-projection` vs `lem-pur-compact-product-proper-support-compatibility`: that result concerns compact global sections with finite-Tor inputs and proper supports, not this unbounded ambient relative projection diagram.

## Mathlib search assessment

Each new node has five actual logged searches: two different LeanFinder phrasings, LeanSearch, Loogle and Mathlib-source grep, executed only with msearch.py. Raw outputs are retained as search-<node>-<index>.txt and their exact queries and outputs are recorded in the node; searches.jsonl supplies the delivery log. LeanSearch returned rate-limit errors for all three and is recorded unavailable. LeanFinder returned scheme coproduct/restriction results, light-condensed internal projectivity, topological compact support, algebraic tensor decompositions and adic completion; none has these map types. Loogle found counit_naturality, tensorHom_def and LaxBraided structure facts. These can implement individual formal steps but none constructs or identifies the specified pro-etale compactification maps by one-line specialization. The three grep patterns in CategoryTheory found no hits. The item retains its original logged searches from the delivered repository record; its statement/search question is unchanged.

## Review by Q118

I read the source proof just cited, the item, all three new statements and the existing ingredient statements. The source does not itself state the ambient non-Tor claim, so the detailed argument remains explicitly agent-written. I checked the return's numbered requirements: the parent statement is unchanged, all three children are unsplit statements with source/blueprint/search fields and no proofs, the parent is 2153 characters, and the allocation above and verbatim appendix retain every old argument. This repair changes the decomposition; it is not an unchanged re-push.

Parent Step 1 uses `lem-pur-product-exchange-counit-coordinates`. Its statement explicitly gives proper v,t, quasi-compact opens, Noetherian finite-type corners, induced q and h compactifications, the formula for B0, and Rt(chi)s=A0 epsilon_k. The inputs are the same finite coefficient datum, same j,a,k,b and witnessed M,N as the item; D has the additional witness required in the item when alpha is invoked. Thus no proper-base-change invertibility or Tor assumption is hidden. The child's intended argument is precisely old Steps 2–4: I read lem-weil-pbc-proper-base-change, lem-weil-pbc-proper-composition, lem-weil-pbc-open-immersion-base-change, lem-sfb-finite-type-composition-base-change, lem-weil-pbc-finite-type-over-noetherian and lem-weil-pbc-noetherian-open-subscheme-noetherian for the geometric hypotheses. I read the statements of def-exchange-projection and lem-weil-pbc-mate-pasting for the actual exchange factorization, lem-exc-proetale-derived-open-restriction for rho/lambda, lem-sf-proper-open-tensor-compatibility for Gamma's open-adjunction normalization, and lem-sf-composition-projection-mate for alpha's specified triangle. The explicit counit identities, rather than an appeal to a theorem's proof, are now part of this child's task.

Parent Step 2 uses `lem-pur-product-open-tensor-projection`. The statement explicitly gives eta invertible, nu eta=delta_k, w=e(chi tensor 1), and Psi nu eta=Rt(w) pi_t(s tensor 1). Its geometry and all maps are independently introduced, so it can be assigned immediately without waiting for the first child. I checked lem-sf-open-tensor-normalization's actual open-unit and fully faithful extension clauses, lem-pur-finite-open-product-swap's equality of the two factorizations of e, and lem-sf-proper-open-projection-mate's actual formula. The latter allows arbitrary unbounded objects and quasi-compact opens; child one verifies those geometric conditions, and they also follow directly from the same finite-type product setup used in child two. The statement preserves the distinct sources of w and e and the essential noninvertible chi. Its support/full-faithfulness comparisons are not mistaken for equality of maps merely after arbitrary pullback.

Parent Step 3 cites the three new statements plus def-exchange-projection and lem-weil-derived-direct-image-composition. All equalities substituted are literally present in child statements, including the exact T coordinate formula from `lem-pur-product-forward-coordinate-transport`. The definition node explicitly calls pi the counit-defined natural projection map, so its naturality in chi is available, rather than borrowed from an unquoted theorem proof. The direct-image compositor is explicitly a natural isomorphism on every finite unbounded input. The parent then writes the complete three-line equation. Only eta is cancelled. The Omega formula follows by substituting A0 and z in the very formula already written in the item's unchanged statement; no new theorem about Omega is needed. Applying Rb and naturality of kappa gives exactly Rc(e) Omega, with its correct target. This is a short elementary assembly of already stated identities, and no parent step exceeds 2000 characters.

Parent Step 4 uses `lem-pur-product-forward-coordinate-transport`'s explicit comparison equation. I checked its intended factorwise proof against lem-pur-pf-refinement-compatibility (bounded-below K,L and witnessed tensor), fix-lem-exchanges item 4 (witnessed finite compact-support exchange), thm-sf-comp-composition (canonical alpha independent of choices), and prop-compactification-coherence-detailed (common refinements and cocycle only on its witnessed domain). The item explicitly requires witnesses for every tensor in the forward word; compact-support functors preserve the witnessed class by thm-sf-comp-composition. Thus none is applied on an arbitrary ambient object when a witness is necessary. Natural symmetry and pasting of the factor squares yields precisely the child's theta equation, and applying it in the parent identifies the specified endpoints. No new node is a clause merely restating T=Rc(e) Omega.

For small cases I checked X or Z empty (all supported tensors and maps are zero, including eta as the unique automorphism of zero), j or k the identity (open units/counits and delta reduce to the identity; the counit square reduces to A0 itself), f and g already proper (j=k=1 reduces the three lemmas to the displayed ordinary exchange/projection word), M or N zero, and a disjoint extra compactification boundary. In the last case eta is invertible because J is extended from Z, while chi need not be invertible on the boundary; no child or parent cancels chi. General shifted complexes use the signed symmetry twice in nu; the restrictions cancel as inverse braidings, so no odd-degree sign has been suppressed. No finite Tor amplitude or constructibility is introduced by any new statement.

I corrected notation from the old proof by consistently distinguishing the exchange morphism A0 from the coefficient ring A. The projection's open q factor is d, and no spurious q-exchange is inserted. I kept each child free of proof sketches (B1), explicit in its objects and hypotheses (B2–B3), with ordinary single-backslash TeX (B4). Sources refer to the actual blueprint paragraph rather than invented Stacks tags (B5/B7). No Mathlib leaf is claimed (B6/B8). Blueprint ancestry and duplicate search are explicit (B9); the sorried Sheaf theorem is not attached (B10). citations.json was checked against each exact statement substring (C4), and the parent proof dependency union is exact. Old accepted tool uses are preserved as metadata; new off-unit proof tools are declared only in split_report where needed, not by editing maintainer tool_uses. No route was changed and no SGA source used.

## Unfinished work

The three new lemmas intentionally remain unsplit for parallel workers. The assigned stage-1 repair itself has a complete short parent proof. Delivery checks are recorded below after execution.

## Returned proof preserved verbatim

### Returned Step 1

Work throughout at $A=A_{E,n}$ with ordinary derived tensor; write $P_v=Lv^*$ and $R_v=Rv_*$, and suppress only the canonical pullback/tensor/direct-image compositors. Use $\epsilon_o:o_!P_o\to1$ for an open-adjunction counit, to distinguish it from the proper-adjunction counits defining $\pi$. All calculations below take place in the ambient unbounded categories. Compactification and composition isomorphisms are used only on bounded-below etale-origin objects, as required in the item. The definitions give the chosen-candidate formulas for $\operatorname{Ex}_!$ and $\operatorname{PF}$; the composition theorem gives the witnessed-domain $\alpha$. We prove the equality first for the displayed $(j,a)$ and $(k,b)$.

Cited nodes: def-pur-conventions, def-weil-derived-pullback-tensor-hom, def-weil-pbc-etale-origin-witness, def-exchange-projection, thm-sf-comp-composition, lem-weil-derived-direct-image-composition, lem-sf-open-tensor-normalization

### Returned Step 2

Set $W=\overline X\times_B Z$, with $v:W\to Z$, $i:W\hookrightarrow C$ and $j_q:P\hookrightarrow W$. Thus $q=vj_q$, $ti=kv$ and $ij_q=u$. The square $(i,v,k,t)$ is Cartesian. Both $v$ and $t$ are base changes of $a$, hence proper; $i$ and $j_q$ are base changes of the opens $k$ and $j$. All these schemes are finite type over $k$: proper maps are finite type, and finite type is stable under composition and base change. They are Noetherian since a field is Noetherian (its only ideals are $0$ and $k$) and finite type over a Noetherian scheme preserves that property. Opens in a Noetherian scheme are Noetherian and quasi-compact, so $k$ and $i$ are quasi-compact open immersions as required below. Thus $(j_q,v)$ compactifies $q$, and $(u,c)$ compactifies $h$ since $c=bt$ is proper. These are compatible compactifications in the triangle of [lem-sf-composition-projection-mate]. Write $\Gamma:k_!R_v\to R_ti_!$ for its normalized proper/open mate. The composition comparison in these coordinates is $\kappa_{b,t}^{-1}R_b\Gamma$, with the open compositor $i_!j_{q!}\cong u_!$ inserted. This uses the description of $\alpha$ as the normalized triangle mate, not an inversion of $\Gamma$ on arbitrary inputs.

Cited nodes: def-pc-fibre-product, def-weil-compactifications-refinements, lem-weil-pbc-proper-base-change, lem-weil-pbc-open-immersion-base-change, lem-weil-pbc-proper-composition, lem-sf-composition-projection-mate, lem-sf-ambient-proper-open-pasting, lem-weil-derived-direct-image-composition, lem-sfb-finite-type-composition-base-change, lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-noetherian-open-subscheme-noetherian

### Returned Step 3

Put $L=R_aH$, $L_0=P_bL$, $F=P_rH$, $E=P_iF$, $K=j_{q!}P_pM$, and $K_D=j_{q!}D$. The open base-change isomorphism is $\beta:E\xrightarrow{\sim}K$. Write
$$A=\operatorname{Ex}_{*,a,b,H}:L_0\to R_tF,\qquad \rho_F:P_kR_tF\xrightarrow{\sim}R_vP_iF.$$
Here $\rho$ is open restriction from [lem-exc-proetale-derived-open-restriction]. It is also $\operatorname{Ex}_{*,t,k}$: on a K-injective representative its restriction formula has transpose $P_i(\varepsilon_t)$ under $P_v\dashv R_v$, exactly the transpose in [def-exchange-projection]. Horizontal mate pasting along $g=bk$ therefore gives
$$B_0:=\operatorname{Ex}_{!,f,g,M}=R_v(\beta)\,\rho_F\,P_k(A):P_kL_0\to R_vK.$$
The last factor $R_v(\beta)$ is the open factor for the compactification $(j,a)$ of $f$. There is no exchange for $q$ in this formula.

Cited nodes: def-exchange-projection, lem-sf-open-tensor-normalization, lem-exc-proetale-derived-open-restriction, lem-weil-pbc-mate-pasting

### Returned Step 4

Let $m=i_!K$, $\chi=\epsilon_{i,F}\,i_!(\beta^{-1}):m\to F$, and $s=\Gamma_K\,k_!(B_0):k_!P_kL_0\to R_tm$. The needed square has vertical maps $\epsilon_{k,L_0}$ and $R_t\chi$, and its equation is
$$R_t(\chi)\,s=A\,\epsilon_{k,L_0}.\tag{*}$$
Here is the counit check. The normalized $\Gamma_E$ is the $k_!\dashv P_k$ adjunct of $\lambda_E^{-1}$, where $\lambda_E=P_kR_ti_!E\xrightarrow{\rho}R_vP_ii_!E\cong R_vE$ [lem-sf-proper-open-tensor-compatibility]. Naturality of $\rho$ and $P_i(\epsilon_{i,F})$ times the open unit equal to $1_E$ give
$$\rho_F\,P_k\bigl(R_t(\epsilon_{i,F})\Gamma_E\bigr)=1_{R_vE}.$$
Consequently $R_t(\epsilon_{i,F})\Gamma_E\,k_!(\rho_F)$ has open-adjunction transpose $1_{P_kR_tF}$, so equals $\epsilon_{k,R_tF}$. Substitute the formula for $B_0$ from Step 3, use naturality of $\Gamma$ with $\beta$, and use naturality of $\epsilon_k$ with $A$ to obtain (*). These are adjunction naturality and the triangle identity; no tensor, projection or exchange map is cancelled.

Cited nodes: lem-sf-proper-open-tensor-compatibility, lem-exc-proetale-derived-open-restriction, lem-sf-open-tensor-normalization, def-weil-pbc-adjunction-mate

### Returned Step 5

Write $\delta_o$ for the normalized open tensor map with the extended object in the first slot. Identify $P_kJ\cong N$ by the open unit. Define
$$\nu=k_!(\sigma_{N,P_kL_0})\,\delta_{k;N,L_0}\,\sigma_{L_0,J}:L_0\otimes J\xrightarrow{\sim}k_!(P_kL_0\otimes N),$$
$$\eta=\epsilon_{k,L_0}\otimes1_J:k_!P_kL_0\otimes J\to L_0\otimes J.$$
Then $\eta$ is an isomorphism and
$$\nu\eta=\delta_{k;P_kL_0,J}.\tag{**}$$
Indeed, the open tensor maps identify both source and target of $\eta$ with an object in the fully faithful image of $k_!$. Restriction to $Z$ makes $\eta$, $\nu$, and the displayed $\delta_k$ the identity on $P_kL_0\otimes N$, with the two symmetries in $\nu$ cancelling. Full faithfulness of open extension proves (**) and invertibility of $\eta$. This uses only the normalization and full-faithfulness clauses of the open-tensor lemma.

Cited nodes: lem-sf-open-tensor-normalization, def-weil-derived-pullback-tensor-hom

### Returned Step 6

The open factor in $\operatorname{PF}_q$ is
$$d=\gamma_{j_q;P_pM,N}:K\otimes P_vN\xrightarrow{\sim}K_D.$$
Define $w=i_!(d)\,\delta_{i;K,P_tJ}:m\otimes P_tJ\to u_!D$. It is related to the displayed $e$ by the explicit equation
$$w=e\,(\chi\otimes1_{P_tJ}).\tag{***}$$
Both maps in (***) have source canonically isomorphic, by $m=u_!P_pM$ and the open tensor comparison, to $u_!D$, and target $u_!D$. Their restrictions to $P$ are $1_D$: $\beta$, $d$, the open tensor comparisons and $e$ have that normalization, while the open counit $\chi$ restricts to the inverse of $\beta$ followed by the open unit identification. Full faithfulness of $u_!$ therefore proves (***). In particular, $w$ itself is not claimed to be $e$; its source is $m\otimes P_tJ$, whereas $e$ starts at $F\otimes P_tJ$.

Cited nodes: lem-sf-open-tensor-normalization, def-exchange-projection, lem-sf-ambient-proper-open-pasting

### Returned Step 7

Set
$$\Psi=\Gamma_{K_D}\,k_!R_v(d)\,k_!(\pi_{v;K,N})\,k_!(B_0\otimes1_N):k_!(P_kL_0\otimes N)\to R_tu_!D.$$
By [def-exchange-projection], these are exactly the exchange $B_0$ and the proper/open factors of $\operatorname{PF}_q$, followed by the triangle mate of Step 2. Let
$$z=R_b(\sigma_{J,L_0})\,\pi_{b;J,L}\,\sigma_{L,R_bJ}:L\otimes R_bJ\to R_b(L_0\otimes J).$$
Expanding $\operatorname{PF}_g$ for $(k,b)$, its open factor is $\delta_{k;N,P_bL}$. The symmetry immediately after $\operatorname{PF}_g$ in $T$ changes this factor to $\nu$. Thus, in the chosen compactification coordinates,
$$T=\kappa_{b,t}^{-1}R_b(\Psi\nu)\,z,\qquad
\Omega=\kappa_{b,t}^{-1}R_b\bigl(\pi_{t;F,J}(A\otimes1_J)\bigr)\,z.$$
These formulas display both the actual $\operatorname{Ex}_{*,a,b,H}$ and $\pi_b$ contributions. They follow by substitution of the specified definitions; no $q$-exchange or $k''$ open factor is inserted into $\operatorname{PF}_q$.

Cited nodes: def-exchange-projection, lem-sf-composition-projection-mate, lem-weil-derived-direct-image-composition, lem-sf-open-tensor-normalization

### Returned Step 8

Apply [lem-sf-proper-open-projection-mate] to $(i,v,k,t)$ with objects $K$ on $W$ and $J$ on $\overline Z$. Both vertical maps are proper and both horizontal maps are open by Step 2. Its identity, followed by $R_ti_!(d)$ and using naturality of $\Gamma$, is
$$\Gamma_{K_D}k_!R_v(d)\,k_!(\pi_{v;K,N})\,\delta_{k;R_vK,J}
=R_t(w)\,\pi_{t;m,J}(\Gamma_K\otimes1_J).$$
Precompose with $k_!(B_0)\otimes1_J$. Naturality of $\delta_k$ in its first input and (**) identify the left side with $\Psi\nu\eta$. Thus
$$\Psi\nu\eta=R_t(w)\,\pi_{t;m,J}(s\otimes1_J).\tag{****}$$
The projection-mate identity is valid on arbitrary unbounded objects, so no finite Tor-amplitude or constructibility assumption enters this application.

Cited nodes: lem-sf-proper-open-projection-mate, lem-sf-open-tensor-normalization, def-exchange-projection

### Returned Step 9

Use (***) in (****), naturality of the ordinary projection in its first input $\chi:m\to F$, and (*) to calculate
$$\begin{aligned}
\Psi\nu\eta
&=R_t(e)\,R_t(\chi\otimes1)\,\pi_{t;m,J}(s\otimes1_J)\\
&=R_t(e)\,\pi_{t;F,J}(R_t(\chi)s\otimes1_J)\\
&=R_t(e)\,\pi_{t;F,J}(A\otimes1_J)\eta.
\end{aligned}$$
Cancel the open-tensor isomorphism $\eta$ of Step 5. Apply $R_b$, precompose with $z$, and postcompose with $\kappa_{b,t}^{-1}$. The two expansions in Step 7 and naturality of $\kappa_{b,t}$ at $e$ give $T=R_c(e)\Omega$. This is ordinary composition and naturality of the defined maps. Neither a projection map, an exchange map nor $\chi$ is inverted.

Cited nodes: def-exchange-projection, lem-weil-derived-direct-image-composition

### Returned Step 10

Finally compare any original choices defining the forward maps with the displayed choices. The compactification-coherence theorem supplies common refinements and normalized comparisons satisfying the cocycle. The projection-refinement lemma gives the commuting square for each $\operatorname{PF}$ factor, including the base-changed compactification of $q$. Item 4 of [fix-lem-exchanges] gives that square for $\operatorname{Ex}_!$ on its witnessed domain. The composition theorem gives independence of $\alpha$ under those comparisons. Symmetry is natural. Pasting these squares shows that $T$ for the original choices equals the $T$ calculated above after the specified source and target identifications. The calculation applies separately to every displayed pair $(aj,bk)$, so it also proves the assertion for any such pair, without asserting refinement naturality of an unspecified product route. Every compared tensor input has the bounded-below etale-origin witness explicitly required in the item.

Cited nodes: prop-compactification-coherence-detailed, lem-pur-pf-refinement-compatibility, fix-lem-exchanges, thm-sf-comp-composition, def-weil-derived-pullback-tensor-hom

## Delivery validation

The initial dry run rejected three citation excerpts as shorter than 40 characters. I enlarged them to the actual exchange/counit equations and the full forward-coordinate assertion, then rechecked every substring against its cited statement. The next required deliver.py --no-push invocation exited 0: server preflight passed, OK (not pushed), provisional commit 1eaa741831e. The final dry run is repeated after this report update, before pushing. Local structural inspection also confirmed the unchanged item statement, exact proof dependency union, four steps under 3000 characters, three statement-only unsplit children, complete explicit statement dependencies, and all citation substrings. No local DAG/preflight scripts or compiler were run.
