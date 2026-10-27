# Repair of lem-sf-product-compactification-identity (Q37)

## Files written

- dag/nodes/sec-six-functors/lem-sf-product-compactification-identity.json: existing statement, preserved verbatim; short four-step assembly, status split.
- dag/nodes/sec-six-functors/lem-sf-kunneth-first-open-substitution.json: statement, no Mathlib match, status unsplit; proof and proof_deps empty.
- dag/nodes/sec-six-functors/lem-sf-kunneth-second-open-substitution.json: statement, no Mathlib match, status unsplit; proof and proof_deps empty.
- citations.json: verbatim statement excerpts for every citation in every parent proof step.
- report.md: this report, including the complete previous argument and assignment of its work.

## Attachments

None. I searched the live WeilConjectures source for the blueprint tag and the compactification, open, Kunneth and externalProduct notions. There is no declaration stating the equality of these specified morphisms. In particular the Nonempty isomorphisms in SixFunctors/Etale/Derived/Kunneth/OrdinaryCompactSupport.lean (including nonempty_iso_derivedTensor_leftDerivedUpperStar_openImmersionLowerShriek) supply isomorphisms, not either substitution identity or the specified exchange/projection compactification equality. Relative.lean also states existence/assembly results, not these identities. They do not justify an attachment.

## WANTED

None.

## What was wrong and what changed

The returned proof was mathematically reviewed but too large to be one work item: nine steps, 7744 characters. The actual sandbox contained only dispatcher markers, no delivered node files, report or searches.jsonl. I therefore copied the current shared-repository node as the repair baseline, preserving its exact statement, ancestry, ten previous searches, sources and reviewer-owned metadata. The parent remains the same proposition.

The first new node carries the vertical exchange factorization and the first open-factor substitution (old steps 3 and 4, with the finite-domain/compositor setup of old step 1). The second carries the signed projection-composition calculation and the second substitution (old steps 2 and 5--7, with the same setup), including an explicit statement of the proper/open tensor square and the normalization identifying Gamma with the compositor. The parent now only applies these two identities, identifies their two tensor maps with e_{j,k}, and proves refinement compatibility. Its proof text has 2187 characters in total; no step exceeds 2000. The new statement lengths are comparable (about 2400 and 2900 characters). Neither new node asserts the two-open product compactification identity or its refinement clause. Their proof fields are empty so separate workers can take these two arguments immediately.

The complete previous proof is retained verbatim below, including all uses and sources, so no calculation is lost by moving work into statement-only tasks. The first task owns old steps 3--4; the second owns old steps 2,5--7. Old step 1 is common setup already explicit in both new statements and in the parent; old steps 8--9 remain the parent's assembly and refinement argument. The second task's needed square is stated explicitly rather than hidden behind a claim of canonicality. No statement dispute or route change was needed.

## Sources read

I read the chapter record sec-six-functors and the relative-product unit sk-thm-sf-kunneth-relative, preserving their route. I read literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md, especially the sentence reducing symmetry to proper f,g, for the item and both new nodes. I also read sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md in that snapshot: its pentagon argument is old step 2; its open restriction and proper mate argument is the source route for old steps 5--6. These are agent-formulated identities expanding that blueprint argument, not the verbatim assertion of a Stacks theorem; hence each new node's primary source is that exact blueprint paragraph.

For the underlying canonical constructions I read literature/stacks-project/sites-cohomology.tex Tag 0GL1, lemma-j-shriek-and-tensor (derived open tensor comparison), and literature/stacks-project/more-etale.tex Tags 0F7B, lemma-shriek-proper-and-open; 0F7C, lemma-shriek-proper-and-open-compose; 0F7D, lemma-shriek-proper-and-open-compose-horizontal; and 0F7J, lemma-shriek-composition. The tag-to-label pairs were checked in tags/tags. Finite Lambda is a torsion ring, so the proper/open comparison is in the stated torsion-ring case; the open arrows are separated and locally quasi-finite. These Stacks facts supply constructions and compositors, not an unstated assertion that every isomorphism of the relevant objects equals the specified lambda. No SGA source was used.

## DAG, blueprint and Mathlib searches

I searched the whole DAG for one-open, first-open, second-open, open-factor, product compactification, proper/open square, and the underlying Stacks tags. I ran blueprint_refs.py ancestor for the item: the ancestor is lem-sf-kunneth-coherence. I ran whole-blueprint searches for one-open, proper/open, Kunneth, open factor, proper/open projection, open substitution, external tensor comparison, and broader projection/compactification words. The closer candidates were opened and distinguished below. Both new nodes are created below the existing non-blueprint item: from.node is lem-sf-kunneth-coherence, via is [lem-sf-product-compactification-identity], and from.place specifies the symmetry reduction and exactly which old steps the task carries. There is no other blueprint node with either new statement; same_as remains empty.

For each new node I ran msearch.py with its own mathematical question: two LeanFinder phrasings, one LeanSearch query, Loogle, and a Mathlib source grep. All ten exact queries and their real results are recorded in searches.jsonl and copied without changing their query text into the appropriate node's mathlib_searches. The first LeanSearch request was rate-limited and is recorded unavailable. All other kinds ran. The hits were ordinary Scheme.Modules restriction/pushforward compositors, exponentiable-morphism over-category adjunctions, Day-convolution/diagram external products, elementary tensor extensionality or condensed internal projectivity. I read Mathlib/CategoryTheory/Monoidal/ExternalProduct/Basic.lean:32--45 (diagram tensor products), Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:231 and :478 (ordinary module functor compositors), and Mathlib/CategoryTheory/LocallyCartesianClosed/ExponentiableMorphism.lean:186--200 (over-category right-adjoint composition). Their types do not assert either identity in constant-coefficient derived sheaf shriek functors, and obtaining such an identity is not a one-line specialization. The AlgebraicGeometry grep found no shriek/Kunneth/projectionFormula declaration. Thus both new nodes are unsplit, not Mathlib leaves. The item's previous Mathlib searches are unchanged and their recorded results were read rather than rerun.

## Not duplicates

lem-sf-kunneth-first-open-substitution vs lem-sf-product-compactification-identity: the new node changes only the first morphism by a single open factor, with an arbitrary second morphism, and computes a vertical-pasting identity and one-open correction. The parent compares two complete compactifications and proves refinement compatibility.
lem-sf-kunneth-second-open-substitution vs lem-sf-product-compactification-identity: the new node changes only the second morphism, with the first already proper, and asserts its explicitly normalized proper/open tensor square. It does not assert the parent's two-open identity or its refinement compatibility.
lem-sf-kunneth-first-open-substitution vs lem-sf-kunneth-second-open-substitution: the first uses vertical exchange pasting for f=aj; the second uses horizontal pasting for g=bk, Theta composition and the proper/open adjunction square. Symmetry of Kunneth is not used to identify them (that symmetry is the result these computations support).
lem-sf-kunneth-first-open-substitution vs lem-sf-open-external-tensor-normalization: the existing node compares tensor extension maps on the product schemes; it has no shriek exchange/projection composite lambda or its vertical-pasting equation.
lem-sf-kunneth-second-open-substitution vs lem-sf-open-external-tensor-normalization: the existing node gives e_2 and its normalization, not the proper/open pushforward square or the lambda substitution.
lem-sf-kunneth-first-open-substitution vs prop-sf-pf-coherence: the pentagon is an input to the first calculation, but the existing statement does not compute a relative external product lambda or combine vertical exchange with open tensor.
lem-sf-kunneth-second-open-substitution vs prop-sf-pf-coherence: the general base-change square and pentagon are inputs; their existing statement does not assert the square with a genuinely arbitrary second-factor L on the open Y, or the required lambda substitution.
lem-sf-kunneth-first-open-substitution vs fix-lem-exchanges: the existing statement gives exchange pasting and refinement compatibility; it does not combine that pasting with the projection pentagon and e_1 to compute lambda.
lem-sf-kunneth-second-open-substitution vs fix-lem-exchanges: the existing statement gives horizontal exchange pasting; it has no proper/open tensor comparison or signed Theta composite.
lem-sf-kunneth-second-open-substitution vs lem-sf-proper-open-tensor-compatibility: the existing statement compares Gamma with tensoring an object pulled from the target. The new square is S_Q(e_2) PF_Q at H and J_k L, uses E_H and a general L on Y, and then yields the relative-product substitution; neither assertion is a direct specialization of that existing formula.
lem-sf-kunneth-second-open-substitution vs lem-sf-proper-open-projection-mate: the existing mate formula has source J_k S_s C tensor A with A on the proper target; it is a generic tensor-interchange input. The new square has source S_Q H tensor J_k L with L on Y, uses proper exchange E_H and e_2, and is then combined with the second relative-product composite.
lem-sf-kunneth-first-open-substitution vs lem-kun-bc-kunneth-compat: that node is ordinary cohomology over a separably closed field with constant first factor and Rj_*, not the specified relative shriek composite with j_! and arbitrary finite-Tor K,L.
lem-sf-kunneth-second-open-substitution vs lem-kun-bc-kunneth-compat: that node concerns the ordinary cohomological Leray/base-change square, not extension by zero in the second morphism or the proper/open tensor square.
lem-sf-kunneth-first-open-substitution vs lem-sf-exterior-projection-kunneth: that node compares projection with external Kunneth for two maps; it assumes the Kunneth comparisons whose coherence is above this item, rather than giving this open-factor identity.
lem-sf-kunneth-second-open-substitution vs lem-sf-exterior-projection-kunneth: its exterior projection identity is not the second-open substitution and is not a route to establish this antecedent compactification identity.
lem-sf-kunneth-first-open-substitution vs lem-sf-pf-open-factor-coherence: that node is a completed integral open-unit/tensor/reduction assertion; the new node is a finite-coefficient exchange/projection identity with an arbitrary second morphism.
lem-sf-kunneth-second-open-substitution vs lem-sf-pf-open-factor-coherence: that integral open-normalization statement does not give the finite proper/open square with E_H or the relative-product substitution.
lem-sf-kunneth-first-open-substitution vs lem-pur-system-compactification-pf-substitution: that node is strict-system coefficient projection compatibility under a proper refinement of a fixed map; the new node factors the first map by an open immersion and includes exchange for an external product.
lem-sf-kunneth-second-open-substitution vs lem-pur-system-compactification-pf-substitution: that node compares projections under a proper refinement; it has neither the horizontal exchange nor the open-second-input proper/open tensor square of this new assertion.

## Review by Q37

I checked the returned re-split instruction against the files, not just their sizes. Both new tasks carry separate non-elementary arguments; they are not new names for the whole product identity. Their statements define their own finite field, coefficient ring, schemes, maps, categories, lambda, signed Theta and open tensor comparisons, and do not refer back to the parent statement. They have proof=[], proof_deps=[], proof_origin=null, status=unsplit. The old argument is preserved below with all nine texts unabridged; putting that guide in the report avoids inserting a proof sketch in a statement-only node. No compiler, Lake, build, repository write or git command was used by me.

For parent step 1 I opened lem-sf-proetale-constructible-origin, whose clause (ii) supplies the etale-origin witness, and thm-sf-comp-composition, whose statement supplies the choice-independent, associative compositor on that witnessed domain. The first new lemma gives exactly the equation displayed in this step, for arbitrary g, so g=bk is allowed. Its proper morphism is a; s is its base change and proper. The first lemma's exchange factorization is retained explicitly in its statement, rather than being treated as a definition of lambda. This carries the old first-open calculation without assuming the product identity.

For parent step 2 I compared the second new statement with the exact substitution needed at M=j_!K. The six-functor datum provides operations on the finite-Tor domain. Here a and b are proper, k and its base change w are open, Q and s are base changes of a and proper. The definition of Gamma is the adjunct of the inverse proper exchange for J_w C, with the unit normalization; its explicit equality to alpha_Qw inverse alpha_ks is the precise extra identification old step 5 needed. The square is asserted in the derived category with its actual signed maps, not on cohomology. In the preserved proof guide the comparison test is made on maps whose source is J_k of an object: the open adjunction is valid for them; restriction is never claimed to detect arbitrary maps. The exchange postcomposition used there is invertible by proper base change with Q proper. This is the substantial work deliberately left to the second independent task.

For parent step 3 I opened lem-sf-open-external-tensor-normalization. Its statement expressly says the opposite factorization through bar X times_B Y gives the same map, so it does identify J_w(e_1)e_2 with e_{j,k}, including the signed open tensor convention. I also reread the associativity and choice-independence clause of thm-sf-comp-composition. Naturality of its natural isomorphisms moves e_1 across J_k S_s to S_Q J_w, then associativity identifies S_b S_Q=Rc_* and J_w J_v=J_u. This is the short assembly, with no symmetry of lambda assumed.

For parent step 4 I opened fix-lem-exchanges, clause (4), which explicitly intertwines compactification refinements; prop-sf-pf-coherence, which explicitly asserts naturality and compactification independence of the specified projection transformations; thm-sf-comp-composition, which gives independence and associativity of compositors; and prop-compactification-coherence-detailed, whose actual statement gives transitivity and common-refinement independence only on witnessed etale-origin inputs. The witnesses from step 1 meet that hypothesis. Replacing each constituent of lambda by the intertwined one makes the left sides agree; the two proved equations then make the right sides agree. Thus refinement compatibility is proved in the parent, not assumed as a new hypothesis. citations.json contains the exact clauses used in all four steps.

I tested the new statements with identity open immersions: beta and the open tensor comparison become identities; e_1 or e_2 becomes the identity under canonical pullback comparisons; for k=identity, Gamma and E are identities and the square reduces to the same PF_Q on both sides. With an empty source or a zero input, every map is the unique corresponding zero-object map. With the proper part an identity, the first assertion reduces to the normalized open projection/base-change maps. Shifts retain both copies of the signed symmetry in Theta, so there is no silently removed Koszul sign. The statements require no density of an open immersion. I checked these cases before writing the new statements and reread them afterwards for type consistency, especially C on W versus C on U in E and Gamma. No false inference, new hypothesis or weakened conclusion was found.

The remaining B--E checklist is satisfied as follows: the new statements are self-contained TeX with single escaped TeX commands in their decoded values; every specialized notion is defined inline or cited by its genuine defining statement; no new proof-only fact is disguised as a definition; no new Mathlib match is asserted. I read the close DAG candidates above, used existing nodes for all parent inputs, and checked that the new nodes have no dependency on this item or its symmetry ancestor. Generic coherence statements provide the refinement argument; the unit route is unchanged. Statement-only nodes have no hidden proof steps. All parent uses are exactly its proof_deps union, each with a verbatim citation. No proof step is longer than 2000 characters. The item statement is byte-for-byte equal as a decoded JSON string to the baseline. Search outputs, including the rate limit, are faithfully recorded.

## What remains

The two extracted nodes are intentionally unsplit and require future proofs by separate workers. Nothing in this stage-1 delivery claims those proofs are finished. The full item assembly and refinement argument are complete relative to those two statements. Delivery/check results follow below when the required dry run completes.

## Preserved complete previous argument, assigned to the new tasks

### Old step 1: Common finite-domain and composition setup (both new nodes and parent step 1)

Write $P_h=Lh^*$, $S_h=Rh_!$, and $J_i=i_!$ for open $i$; for proper $h$, identify $S_h=Rh_*$. All products and tensors below are derived and over $\Lambda$. The operations on the finite-Tor domains are supplied by [def-sf-datum]. Whenever applying the concrete finite-level composition or exchange theorem on pro-etale categories, use the etale-origin witness for bounded constructible inputs given by [lem-sf-proetale-constructible-origin]. The composition comparisons are the normalized ones of [thm-sf-comp-composition]. We insert these comparisons in equations involving $S_hS_e=S_{he}$; their associativity allows parentheses to be suppressed. No assertion about an arbitrary unbounded pro-etale complex is needed.

Cited nodes: def-sf-datum, lem-sf-proetale-constructible-origin, thm-sf-comp-composition.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md; Symmetry paragraph: finite-level domains and composition comparisons.

### Old step 2: Second-open substitution task

For any $h:V\to W$, set $\Theta_h(A,N)=S_h(\sigma)\operatorname{PF}_{h,N,A}\sigma:A\otimes S_hN\to S_h(P_hA\otimes N)$. Thus $\Theta_g(F,L)=\Psi_g(F,L)$, including both specified symmetries. The composition pentagon of [prop-sf-pf-coherence], conjugated by these symmetries, gives
$$\Theta_{he}(A,N)=S_h\bigl(\Theta_e(P_hA,N)\bigr)\Theta_h(A,S_eN).$$
Indeed substitute the two-factor formula for $\operatorname{PF}_{he}$, move each symmetry past the natural transformation in the other input, and cancel the adjacent $\sigma^2=1$. This also gives naturality of $\Theta$ in both inputs; no symmetry of the Kunneth map is being assumed.

Cited nodes: prop-sf-pf-coherence.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md; Pentagon paragraph, with the signed tensor symmetry.

### Old step 3: First-open substitution task

First remove the open factor of $f=aj$, keeping $g$ fixed. Put $U=\bar X\times_BY$, with $r:U\to\bar X$, $s:U\to Y$, and $v=j\times_B\operatorname{id}_Y:T\hookrightarrow U$, so $q=sv$. Let
$$\beta:P_rJ_jK\longrightarrow J_vP_pK$$
be normalized open base change. The vertical-pasting identity of [fix-lem-exchanges] and the compactification definition [def-exchange-projection] give, under $S_q=S_sJ_v$,
$$\operatorname{Ex}_{aj,g}(K)=S_s(\beta)\operatorname{Ex}_{a,g}(J_jK).$$
Here the first square is the base change of $a$ along $g$, and the second the base change of $j$ along $r$; their outer rectangle is the square for $(aj,g)$. The open exchange in this factorization is precisely $\beta$, with identity restriction by [lem-sf-open-tensor-normalization].

Cited nodes: fix-lem-exchanges, def-exchange-projection, lem-sf-open-tensor-normalization.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md; Symmetry paragraph: expand the first compactification by vertical exchange pasting.

### Old step 4: First-open substitution task

Set
$$e_1=\operatorname{PF}_{v,P_pK,P_sL}(\beta\otimes1):P_rJ_jK\otimes P_sL\longrightarrow J_v(P_pK\otimes P_qL).$$
The composition pentagon for $q=sv$ expands $\operatorname{PF}_q$ into $\operatorname{PF}_s$ followed by $S_s\operatorname{PF}_v$. Naturality of $\operatorname{PF}_s$ moves $\beta$ through its first input. Substitution of step 3 into the displayed definition of $\lambda$ therefore gives
$$\lambda_{aj,g}(K,L)=S_gS_s(e_1)\,\lambda_{a,g}(J_jK,L),$$
where the target is read using $S_gS_sJ_v=S_t$. This is an equality of the actual composites: the initial $\Theta_g$ is unchanged, the middle two factors are those just expanded, and the final compositors agree by associativity. The map $e_1$ is the one-open external tensor comparison by [lem-sf-open-external-tensor-normalization], not a separately chosen isomorphism.

Cited nodes: prop-sf-pf-coherence, thm-sf-comp-composition, lem-sf-open-external-tensor-normalization.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md; Symmetry paragraph: first open-factor substitution in the specified composite.

### Old step 5: Second-open substitution task

Now remove the open factor of $g=bk$, with the first morphism $a$ proper. For this calculation let $M=J_jK$, $W=\bar X\times_B\bar Y$, and denote its projections by $P:W\to\bar X$ and $Q:W\to\bar Y$. Keep $U=\bar X\times_BY$, with $w=\operatorname{id}_{\bar X}\times_Bk:U\hookrightarrow W$ and projections $r,s$. Write $H=P_PM$, $F=S_aM$. The square $(w,s,Q,k)$ is Cartesian. Put $E_H=\operatorname{Ex}_{Q,k}(H):P_kS_QH\to S_sP_wH$. Horizontal pasting in [fix-lem-exchanges] says
$$\operatorname{Ex}_{a,bk}(M)=E_H\,P_k\operatorname{Ex}_{a,b}(M).$$
Let $\Gamma_N:J_kS_sN\to S_QJ_wN$ be the normalized proper/open map for this square. It is the $J_k\dashv P_k$-adjunct of the inverse open-restriction comparison, as specified in [lem-sf-proper-open-tensor-compatibility]. It is also the composition comparison $\alpha_{Q,w}^{-1}\alpha_{k,s}$: take $j=\operatorname{id}_U$, $q=s$, $i=k$, $b=w$, $p=Q$ in the compatible triangle of [lem-sf-composition-projection-mate]. In particular its restriction, followed by exchange and $P_wJ_w=1$, is the identity.

Cited nodes: fix-lem-exchanges, lem-sf-proper-open-tensor-compatibility, lem-sf-composition-projection-mate.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md; Symmetry paragraph: horizontal exchange pasting and the normalized proper/open compositor.

### Old step 6: Second-open substitution task

Put $N=P_wH\otimes P_sL$ and define the one-open tensor map
$$e_2:H\otimes P_QJ_kL\xrightarrow{1\otimes\beta}H\otimes J_wP_sL\xrightarrow{\text{signed open tensor}}J_wN.$$
The precise open base-change and tensor maps of [lem-sf-open-tensor-normalization] restrict to the identity. The needed square is
$$S_Q(e_2)\operatorname{PF}_{Q,H,J_kL}=\Gamma_N\,J_k\bigl(\operatorname{PF}_{s,P_wH,L}(E_H\otimes1)\bigr)\Theta_k(S_QH,L).$$
To verify it, precompose both sides with $\Theta_k(S_QH,L)^{-1}$. Their common source is now $J_k(P_kS_QH\otimes L)$. By $J_k\dashv P_k$ and its normalized invertible unit, it suffices to compare their restrictions along $k$. Postcompose the restricted maps with $E_{J_wN}$ and $S_s(P_wJ_wN\cong N)$; this is invertible by proper base change (A2) of [def-sf-datum]. The left side becomes $\operatorname{PF}_{s,P_wH,L}(E_H\otimes1)$ by the base-change square of [prop-sf-pf-coherence], naturality of exchange, and $P_we_2=1$. The right side becomes exactly the same map by the normalization of $\Gamma_N$ in step 5 and $P_k\Theta_k=1$ under the open-unit identifications. Thus the square commutes. This argument uses the open adjunction on the source; it does not claim that restriction detects arbitrary maps.

Cited nodes: lem-sf-open-tensor-normalization, lem-cbc-proetale-extension-zero, def-sf-datum, prop-sf-pf-coherence, fix-lem-exchanges, lem-sf-proper-open-tensor-compatibility.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md; Base-change paragraph: open-unit test of the proper projection square.

### Old step 7: Second-open substitution task

Expand $\Theta_{bk}(F,L)$ by step 2 as $S_b\Theta_k(P_bF,L)\Theta_b(F,J_kL)$. Insert the horizontal-pasting equation of step 5 in $\lambda_{a,bk}$. Naturality of $\Theta_k$ moves $P_k\operatorname{Ex}_{a,b}(M)$ past $\Theta_k$, leaving inside $S_b$ precisely
$$\Gamma_NJ_k\bigl(\operatorname{PF}_{s,P_wH,L}(E_H\otimes1)\bigr)\Theta_k(S_QH,L),$$
preceded by $\operatorname{Ex}_{a,b}(M)\otimes1$ and $\Theta_b(F,J_kL)$. Step 6 replaces this displayed factor by $S_Q(e_2)\operatorname{PF}_{Q,H,J_kL}$. The remaining composite is the defining $\lambda_{a,b}(M,J_kL)$. Associativity of the composition comparisons identifies the factor $\Gamma$ with the final $\alpha$'s. Consequently
$$\lambda_{a,bk}(M,L)=S_bS_Q(e_2)\,\lambda_{a,b}(M,J_kL),$$
with targets identified using $S_bJ_kS_s=S_bS_QJ_w$. This calculation retains the signed symmetries through $\Theta$, rather than replacing the Kunneth morphism by an unspecified isomorphism.

Cited nodes: prop-sf-pf-coherence, fix-lem-exchanges, thm-sf-comp-composition, lem-sf-composition-projection-mate.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md; Symmetry paragraph: second open-factor substitution in the specified composite.

### Old step 8: Parent assembly/refinement, retained

Apply step 4 with $g=bk$, then step 7 with $M=J_jK$. On $W=\bar T$, the resulting tensor comparison is
$$J_w(e_1)\,e_2:(J_jK)\boxtimes(J_kL)\longrightarrow J_wJ_vD\cong J_uD.$$
This is exactly the factorization through $\bar X\times_BY$ of [lem-sf-open-external-tensor-normalization]; that statement identifies it with $e_{j,k}$, including the equality with the opposite factorization and its signed symmetry normalization. Composing the two equations and using the associative composition law, $S_bS_Q=Rc_*$ and $J_wJ_v=J_u$, proves
$$\lambda_{aj,bk}(K,L)=Rc_*(e_{j,k})\lambda_{a,b}(J_jK,J_kL).$$
The source and target identifications are respectively those of the given compactifications of $f,g$ and their product, as required.

Cited nodes: lem-sf-open-external-tensor-normalization, thm-sf-comp-composition.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md; Symmetry paragraph: assemble the two substitutions and identify the normalized product-open map.

### Old step 9: Parent assembly/refinement, retained

Finally take a refinement of either chosen compactification and apply the preceding equality to both choices. By [fix-lem-exchanges](4), exchange intertwines the refinement comparisons; by [prop-sf-pf-coherence], so does the projection map. Naturality of tensor symmetry and independence and associativity of the compositors in [thm-sf-comp-composition] then show that the left sides are the same specified $\lambda_{f,g}$ under the source and target comparisons. Hence the right sides intertwine those comparisons as well, by the two proved equalities. Transitivity and independence of common refinement in [prop-compactification-coherence-detailed] extend this assertion to comparison via any common refinement. This proves the requested refinement compatibility without assuming separately that an arbitrary product comparison is multiplicative.

Cited nodes: fix-lem-exchanges, prop-sf-pf-coherence, thm-sf-comp-composition, prop-compactification-coherence-detailed.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md; Symmetry paragraph: independence of compactification, now for the actual composite.

