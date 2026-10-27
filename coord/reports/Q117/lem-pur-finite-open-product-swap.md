# Worker report: lem-pur-finite-open-product-swap

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-finite-open-product-swap.json`: existing statement, re-split with a four-step assembly of 2017 characters, unchanged statement and inherited fields.
- `dag/nodes/sec-smooth-purity/lem-pur-two-open-tensor-chain-normalization.json`: new statement, unsplit; no Mathlib match. The two tensor orders of a nested-open construction with an arbitrary input isomorphism are stated explicitly, including their restriction equations.
- `dag/nodes/sec-smooth-purity/lem-pur-supported-tensor-isomorphism-transport.json`: new statement, unsplit; no Mathlib match. A given normalized supported tensor isomorphism is transported through an arbitrary Cartesian isomorphism square; its restriction, signed conjugate and uniqueness are specified.
- `citations.json`: exact statement excerpts for every step/node citation.

Two new nodes, zero Mathlib leaves. Neither new node contains proof steps or proof dependencies. Their statements are 2463 and 2582 characters. They are separate proof tasks: the first constructs nested projection chains, the second takes an already supplied comparison and proves its transport and uniqueness. Neither assumes nor states the original product-open theorem.

## Attachments

None. I searched the project source under `lean/WeilConjectures/` for the item tag and product/open/swap notions and read `lean/Sheaf/Paper/FiniteOpenProductSwap.lean:459` through the theorem ending at line 519. `WeilConjectures.FiniteOpenProduct.finiteOpenProductSwap` has `sorry` as its proof. Its helper maps specify actual composites but do not prove the six conclusions. The retained Lean record and all upstream audit fields are unchanged. No Lean was written or compiled.

## WANTED

None.

## Repair of the return

The sole return requires spreading the old 7886-character argument over at least two new statement-only nodes, with the parent proof at most 3000 characters. I did not replace it by a shorter proof without creating proof tasks. The two new nodes isolate comparable mathematical arguments, are unsplit and independent of one another, and are both used by the short parent assembly. The exact old nine steps appear below, including their dependency lists. The following allocation makes every part recoverable by the later workers:

| Returned argument | New task or assembly |
| --- | --- |
| Step 1: four Cartesian squares, projection equations, open inclusions and their composites | Parent Step 1 retains the equations and open-subset argument. |
| Step 2: composite adjunction unit and actual open compositor | First new node, displayed compositor unit equation. |
| Step 3: right-extension comparison, two signed symmetries, K-flat descent | First new node, the explicitly defined rho and its restriction assertion. |
| Steps 4 and 5: first ordered chain and its restriction | First new node, e_L and its actual restriction equation; parent Step 2 supplies the two Cartesian base changes. |
| Step 6: opposite ordered chain and its restriction | First new node, e_R and its actual restriction equation; parent Step 2 specializes to the other pair of squares. |
| Step 7: equality detection on an extension-supported source | Second new node, injectivity for all targets i_!D_0; parent Step 3 applies the identity-square case. |
| Step 8: swapped square, pulled-back reversed construction, normalized restriction | Second new node, explicitly constructed f and its restriction; parent Step 4 supplies the product swaps and projection equations. |
| Step 9: signed conjugation, cancellation and actual-map uniqueness | Second new node, explicitly constructed f^rev and its unit equation; parent Step 4 applies its injectivity. |

There was no retained sandbox node or report at the start, only launcher marker files. I therefore compared against and copied the current repository node, which contains exactly the nine-step proof and 7886-character count in the return. I retained its statement, existing searches, source and blueprint metadata, Lean declarations, audit and review records. I added only the new stage-1 decomposition and updated its split report. No repository or launcher file was changed and no git command was run in the shared repository.

## Independent proof tasks and retained arguments

### First new node: nested-open tensor chains

The source route is the open-extension part of the signed-symmetry reduction in `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md`. It is an agent-formulated ordinary-unbounded lemma, not a quotation of that six-functor theorem. I read Stacks `sites-cohomology.tex`, Tag 0GL1, label `lemma-j-shriek-and-tensor`, which states the derived open projection isomorphism for arbitrary objects. Its proof uses a K-flat representative, not boundedness. For the exact compositor I read `categories.tex`, Tag 0DV0, `lemma-compose-counits`, and Tag 0B65, `lemma-transformation-between-functors-and-adjoints`, as background; the already existing composite-adjunction and conjugate-iso-unit-equation nodes state the needed unit form.

The later worker has the following full argument. Let u=vw. The composite adjunction v_!w_! left adjoint to w^*v^* has unit w^*(eta^v) after eta^w by `def-weil-pbc-composite-adjunction`. Identify its right adjoint with u^* by the restriction compositor. `lem-weil-pbc-conjugate-iso-unit-equation` gives the unique invertible mate, hence exactly the specified unique-left-adjoint compositor in `def-sf-finite-open-tensor-operations`, with the displayed unit equation. This treats the pro-etale categories themselves and does not import an etale-only construction.

For rho, its three factors are signed symmetry, gamma, and extension of signed symmetry. The normalization of gamma is the identity under the actual open units (`lem-sf-open-tensor-normalization`). Restriction respects signed symmetry (`lem-pur-derived-pullback-tensor-iso`). The two resulting symmetries cancel: for homogeneous degrees a,b the scalar is (-1)^(ab+ba)=1. `lem-pur-cochain-pullback-tensor-coherence` supplies that cochain calculation in arbitrary degrees, and `lem-weil-pbc-site-derived-tensor-descent` supplies its K-flat descent in the unbounded categories. This is exactly the old Step 3; no finite Tor interval or bounded tensor complex is inserted.

For e_L, gamma_v first passes the ambient tensor factor inside v_!. Apply 1 tensor delta, then rho_w, then the specified compositor. Every factor is invertible. Restrict successively along v and w. The gamma and rho restrictions are the identities already identified; the restriction of delta followed by the inverse w-unit is precisely d, not an assumed identity for arbitrary delta. The inverse v-unit is the map a. The compositor equation combines the two remaining units into eta^u. Thus the actual restriction is eta^u after (a tensor d) after mu, as stated. The compatibility with pullback composition is exactly the composition clause of `lem-pur-derived-pullback-tensor-iso`.

For e_R, the chain is rho_v, delta tensor 1 inside v_!, gamma_w, compositor. Its target is u_!(Q tensor w^*F), with no unexplained reorder. Restriction now gives d tensor a; the same compositor unit equation gives the displayed right restriction formula. This is the old opposite-factorization argument with F and the ambient factor generalized, rather than an omitted appeal to “similarly”. The product-specific beta maps are added in the parent: for the left chain F=alpha^*M and Q=q^*N; for the right chain F=beta'^*N and Q=p^*M.

### Second new node: supported transport and signed conjugation

This is the agent-formulated restriction argument in the same blueprint symmetry reduction. Stacks 0GL1 supplies only background on the tensor comparison, not this theorem. The node explicitly uses the actual normalized beta of `lem-sf-open-tensor-normalization`, and the pullback/tensor composition and signed compatibility of `lem-pur-derived-pullback-tensor-iso`. It assumes the normalized isomorphism f' as input. It does not assume any product factorization, proper morphism, six-functor datum or external-product theorem.

The later worker first expands f as the tensor/pullback inverse, pullback of f', normalized beta, and extension of mu_h. Restrict along i. The canonical square comparison identifies i^*g^* with h^*i'^*. Substitute the supplied unit equation for i'^*f'. The beta restriction is the identity after the open units by the normalization node. Naturality of these units and composition compatibility of mu identify the surviving source comparison with (a tensor b) after mu_i. This proves the stated actual unit equation and invertibility. In the identity square these same canonical composition and unit identifications give f=f'. This is the old Step 8 transport calculation written for a square independent of products.

For injectivity, f identifies R tensor H with i_!(P tensor Q). Given two arrows into i_!D_0 with equal restriction, precompose with f inverse. Full faithfulness of i_! identifies the resulting arrows uniquely with maps P tensor Q to D_0. Naturality of the invertible open unit identifies their restrictions, conjugated by the two units, with those maps. They are therefore equal. Tensor symmetry transfers this detection statement to source H tensor R. Restriction is never assumed faithful on all ambient sources. This is the full old Step 7, for arbitrary D_0 rather than only the endomorphism case.

Finally restrict i_!(sigma_PQ) after f after sigma_HR. Naturality of eta moves i_!(sigma_PQ) through the unit. Compatibility of mu and pullback with signed symmetry, followed by naturality for a,b, gives the displayed equation with b tensor a. Equivalently the two exchanged symmetries cancel; on homogeneous tensors this is the old Step 9 scalar (-1)^(ab+ba)=1, valid in odd degrees and in characteristic two as well. The supported-source injectivity already proved gives uniqueness of f^rev among all arrows with that restriction. This completes precisely the transport/detection/sign work formerly inline in the item.

## Mathlib and duplication searches

Every new node has logged LeanFinder, Loogle, LeanSearch and grep calls, and a second natural-language phrasing. All calls were made with the required `msearch.py Q117 lem-pur-finite-open-product-swap` command. Their exact query strings and actual hits are in `searches.jsonl` and in the nodes' `mathlib_searches`; no unexecuted query is recorded. All services responded successfully on this run.

For the first node, the semantic hits include `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` and `restrictFunctorAdjCounitIso`. I read `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:416` and `:478`: these concern ordinary structure-module restriction and direct image, not extension by zero on unbounded constant-module pro-etale categories, their tensor chains, or the displayed actual unit equations. Loogle gave general monoidal-adjunction unit and counit identities; these are ingredients, not a one-line specialization to either explicit chain. The second phrasing returned small-object iteration and presheaf extension results. The full-source grep for extension-by-zero names had zero hits.

For the second node, Loogle gave braided functor and monoidal localization declarations, and semantic search gave scheme pullback carrier tensorCongr and free-module pullback results. None includes the normalized open-support comparison f', open beta, or restriction detection on its essential image. The grep found `CategoryTheory.MonoidalCategory.externalProductSwap` at `Mathlib/CategoryTheory/Monoidal/ExternalProduct/Basic.lean:80` and `externalProductFlip` at :91. I read both: they are braidings of diagram functors, not the asserted derived open base-change statement. LeanSearch returned free-monoidal normalization and ordinary module tensor congruences. The second phrasing again returned ordinary module restriction. Hence both nodes remain unsplit, with no Mathlib match.

I searched the whole DAG by titles, statement text, compositor/two-stage/nested-open/tensor/signed-conjugation/restriction-detection terms, and the relevant Stacks tags 0GL1, 0B65, 0DV0. I ran `tools/blueprint_refs.py search` for `open tensor`, `open compositor`, `extension zero symmetry`, `signed symmetry`, `two-stage`, `fully faithful open`, `projection composition`, `normalized tensor`, `Cartesian transport`, `open external`, and `open composition`. I read the pertinent existing candidates listed below. The nearest blueprint ancestor is `prop-pur-affine-space-composition-law`; the new nodes' via lists put this item before its inherited via list. The parent retains its non-unspecified blueprint place and empty same_as. No blueprint node states either generic comparison lemma.

## Not duplicates

lem-pur-two-open-tensor-chain-normalization vs def-sf-finite-open-tensor-operations: the existing node defines actual rho, gamma and compositors; it asserts no nested-chain invertibility or restriction equations.
lem-pur-two-open-tensor-chain-normalization vs lem-sf-open-tensor-normalization: the existing theorem normalizes one open tensor and base-change map; the new task proves the two mixed tensor chains for two composable opens and arbitrary delta, including the compositor unit.
lem-pur-two-open-tensor-chain-normalization vs lem-amb-open-projection-composition: the existing theorem is an ordinary etale gamma-composition identity for an already extended input; the new task is pro-etale and has a second factor whose restriction is only supplied as w_!Q, and includes both mixed tensor orders and their actual restriction equations.
lem-pur-two-open-tensor-chain-normalization vs lem-sfb-ringed-projection-tensor-composition: the existing comparison is the right-adjoint direct-image projection map; the new chains are formed from left-adjoint extension by zero and normalized open units.
lem-pur-two-open-tensor-chain-normalization vs lem-sf-open-external-tensor-normalization: the existing statement assumes a six-functor datum and bounded constructible finite-Tor inputs on product schemes; the new statement concerns arbitrary unbounded inputs on nested opens and supplied delta, without a product or six-functor datum.
lem-pur-supported-tensor-isomorphism-transport vs lem-sf-open-external-tensor-normalization: the existing bounded-ctf six-functor product theorem constructs a comparison; the new task transports an already supplied comparison through an arbitrary Cartesian isomorphism square in ordinary unbounded categories and proves restriction injectivity for every i_!D_0.
lem-pur-supported-tensor-isomorphism-transport vs lem-pur-comparison-unit-injective-model: the existing node computes an etale/pro-etale comparison unit on an injective model; it is not a faithfulness or open-support tensor-transport assertion.
lem-pur-supported-tensor-isomorphism-transport vs lem-pur-comparison-pullback-open-unit: the existing node concerns the site-comparison adjunction unit on sheaves, not a tensor comparison into an open extension on unbounded pro-etale derived categories.
lem-pur-supported-tensor-isomorphism-transport vs lem-fix-tensor-pullback-square: the existing statement is a scalar-extension and inverse-image square, explicitly with no extension-by-zero exchange; the new task contains normalized beta and a supported target, with a signed conjugate and uniqueness.
lem-pur-supported-tensor-isomorphism-transport vs lem-pur-supported-coefficient-open-tensor: the existing theorem has closed-support coefficient mates and first-variable open cuts; the new task has a supplied open-extension tensor isomorphism and arbitrary isomorphism square, without closed supports or supported coefficient construction.
lem-pur-supported-tensor-isomorphism-transport vs lem-sf-open-tensor-support: the existing theorem states essential-image membership only; it constructs no Cartesian transported arrow or signed conjugate and gives no actual restriction equations.
lem-pur-two-open-tensor-chain-normalization vs lem-pur-finite-open-product-swap: the new task supplies nested projection chains for arbitrary delta, not any Cartesian product or either equality of product comparisons.
lem-pur-supported-tensor-isomorphism-transport vs lem-pur-finite-open-product-swap: the new task assumes a normalized comparison and transports it; it does not construct either product comparison from open base change and gamma.

## Review by Q117

I read the current item, its nine old steps, all ten old cited statements, the two new statements, the four assembly steps, the unit sk-prop-an (especially its Step 6 symmetry clause), the fixed chapter record, SETUP's three route levels, GOAL.md and delivery-errors B through E. I also read the current ancestor proof in `sec-smooth-purity/sk-prop-sp-composition/prop-pur-affine-space-composition-law.proof.md`, whose Step 3 accounts for even shifts. Our finite open lemma supplies the arbitrary-degree interchange needed before trace evaluation; it does not replace the affine-space route by a general purity or SGA theorem.

For assembly Step 1 I opened `def-pc-fibre-product`, `lem-weil-pbc-open-immersion-base-change` and `def-weil-open-immersion`. The definition gives the universal property used for all listed projection identities and Cartesian squares; the base-change lemma says exactly that an arbitrary base change of an open is open, with no finiteness hypothesis missing. Composition of opens is the explicit open-subset and repeated structure-sheaf restriction argument in the step. No separatedness of an arbitrary intersection or implicit affine-intersection claim is used.

For Step 2 I checked both displayed chains of the first new node, not merely its title. For the first order, the substitutions are V=X times_B bar Z, F=alpha^*M, H=t^*k_!N, Q=q^*N and delta the second normalized beta. Precomposing by the first normalized beta identifies its source with E. For the opposite order, V'=bar X times_B Z, F=beta'^*N, ambient factor R=r^*j_!M, Q=p^*M and delta the beta for j,w'. This is exactly its e_R chain, with target p^*M tensor q^*N. `lem-sf-open-tensor-normalization` explicitly states invertibility and identity restrictions of beta and gamma for arbitrary unbounded objects. `lem-pur-derived-pullback-tensor-iso` explicitly includes signed compatibility and composition compatibility at finite level for arbitrary unbounded objects. Thus the two restriction equations apply with d equal to the canonical restriction identification; neither is only an existential isomorphism. I corrected the tempting over-generalization “delta restricts to identity” by giving arbitrary delta and the explicit d=(eta^w)^-1 w^*delta in the new statement. The product case uses the normalization hypothesis supplied by beta.

For Step 3 I checked the second new node's injectivity clause and identity-square clause, both literally present in its statement. Set f'=e_{j,k}, R'=R, H'=H, P'=p^*M and Q'=q^*N; the preceding step supplies its required normalized isomorphism, not merely an arrow. Its injectivity conclusion then compares the opposite map. The proof task underneath uses full faithfulness only for sources in the essential image, as explicitly stated, so this is not a false use of conservativity or faithfulness on all derived ambient objects.

For Step 4 I checked the actual four swap projection identities and the Cartesian square by the fibre-product universal property. Apply the second new node with R'=r'^*k_!N and H'=t'^*j_!M, hence R=H of the parent and H=R of the parent, and with P=q^*N, Q=p^*M. Its displayed f is the exact tensor-pullback/base-change transport required for tilde e, not a freely chosen isomorphism. Its f^rev has precisely the two symmetries in the parent's formula, in their stated order; its restriction equation and injectivity give equality with e_{j,k}. I verified this against the tensor coherence node, which states the signed compatibility needed here. No transport assertion has been hidden under an unsupported “canonical” or “standard”. The citations file now quotes the transport statement for this step, not just the uniqueness sentence.

For each new node all schemes, categories, coefficient data, maps and complexes are introduced within its statement. The only assumptions additional to the common finite setting belong to its own independent problem: a supplied delta for the nested chain, and a supplied normalized isomorphism f' for transport. Neither changes the parent statement. Definition and operation nodes are in stmt_deps; both proof lists and proof_deps are empty as required. The full proof instructions are in this report, not smuggled into a statement. The source places explicitly identify these as agent-formulated lemmas rather than claiming the blueprint or Stacks literally states them. The new statements refer to no Stacks tag for their meaning. The old source metadata is retained.

I tested the nested-chain statements with w and v identities, one empty open, all zero complexes, and delta multiplied by a scalar automorphism: the latter multiplies d and the restriction by that scalar, so the explicit equations still hold. I tested transport with the identity square and with an empty source open; injectivity then concerns a zero source, not all ambient objects. The reversed signed formula was checked on two odd-degree homogeneous tensors, where each individual symmetry is minus one but their product is plus one; characteristic two gives the same identity. These checks retain arbitrary unboundedness and use no constructibility, etale origin, properness, finite Tor-amplitude or six-functor structure. The first node's tensor-compatibility hypotheses are valid because the finite coefficient ring and schemes are exactly within the existing coherence theorem's finite-level case.

The off-unit normalization theorem is still the same generic tool already declared and accepted on the returned node. Both newly used proof lemmas are in the parent's own unit sk-prop-an. There is no cycle: the new statements depend only on existing coefficient/operation/normalization/coherence nodes, none on this item or its ancestors. The first extracted task covers old Steps 2--6 and the second old Steps 7--9; their statement sizes and actual proof burdens are comparable. All four parent steps are below 2000 characters and the total is below 3000. I checked every argument in the long returned proof against that allocation, retaining all of it below rather than dropping it.

## Unfinished work

No stage-1 repair remains. The two new proof tasks are deliberately unsplit and available for other workers. Dry-run and delivery results are recorded after running the required tools.

# Returned proof retained verbatim

### Original Step 1

Put $V=X\times_B\bar Z$, with projections $\alpha:V\to X$, $\beta:V\to\bar Z$. Then $v=j\times1:V\to C$ and $w=1\times k:P\to V$ satisfy $u=vw$, $\alpha w=p$, $\beta w=kq$, $rv=j\alpha$, $tv=\beta$. These equations follow by composing the two projections in the fibre-product universal property [def-pc-fibre-product]. The squares $(j,v;r,\alpha)$ and $(k,w;\beta,q)$ are Cartesian by that same property. Thus $v,w$ are open by [lem-weil-pbc-open-immersion-base-change]. Likewise put $V'=\bar X\times_BZ$, with projections $\alpha':V'\to\bar X$, $\beta':V'\to Z$, and opens $v'=1\times k:V'\to C$, $w'=j\times1:P\to V'$. Here $u=v'w'$, $\alpha'w'=jp$, $\beta'w'=q$, $rv'=\alpha'$, $tv'=k\beta'$. Their two analogous squares are Cartesian too. Composites of opens are open: an open subset of an open subset is open, and the structure sheaf restricted twice is restricted once [def-weil-open-immersion].

Uses: def-pc-fibre-product, lem-weil-pbc-open-immersion-base-change, def-weil-open-immersion

### Original Step 2

Write $\eta^i:1\xrightarrow{\sim}i^*i_!$ for the actual open units of [lem-sf-open-tensor-normalization]. The composite adjunction [def-weil-pbc-composite-adjunction] for $v_!w_!\dashv w^*v^*$ has unit $w^*(\eta^v_{w_!D})\circ\eta^w_D$. Identify $w^*v^*$ with $u^*$ by the canonical restriction composition. The unique mate of this identification [lem-weil-pbc-conjugate-iso-unit-equation] is the canonical open compositor $c_{v,w}:v_!w_!\to u_!$ of [lem-cbc-extension-zero-composition]. Its unit equation is
$$u^*(c_{v,w,D})\circ w^*(\eta^v_{w_!D})\circ\eta^w_D=\eta^u_D.$$
Consequently this compositor restricts to the identity after the specified units. This argument applies in the present unbounded pro-etale categories, since their open adjunctions and invertible units are supplied by the normalization lemma itself. It also gives the same assertion for $(v',w')$. In particular no etale-only construction of a compositor or unnormalized choice of an isomorphism is being substituted.

Uses: lem-sf-open-tensor-normalization, def-weil-pbc-composite-adjunction, lem-weil-pbc-conjugate-iso-unit-equation, lem-cbc-extension-zero-composition

### Original Step 3

We will use the right-extension version of the open tensor map. For an open $i:W\hookrightarrow Y$, $F\in D(Y,A)$ and $Q\in D(W,A)$ it is the explicit composite
$$\rho^i_{F,Q}:F\otimes^Li_!Q\xrightarrow{\sigma}i_!Q\otimes^LF\xrightarrow{\gamma}i_!(Q\otimes^Li^*F)\xrightarrow{i_!\sigma}i_!(i^*F\otimes^LQ).$$
Every arrow is invertible by [lem-sf-open-tensor-normalization] and signed symmetry. Under restriction it becomes $\sigma_{Q,i^*F}\circ\sigma_{i^*F,Q}=1$: on homogeneous tensors of degrees $a,b$ the coefficient is $(-1)^{ab+ba}=1$. The sign formula is given by [lem-pur-cochain-pullback-tensor-coherence]; the K-flat tensor models and descent of [lem-weil-pbc-site-derived-tensor-descent] justify the same calculation in the unbounded derived category. Compatibility of restriction with these signed identifications is [lem-pur-derived-pullback-tensor-iso]. Thus $i^*\rho^i$ is the identity, with the specified tensor and unit identifications.

Uses: lem-sf-open-tensor-normalization, lem-pur-derived-pullback-tensor-iso, lem-pur-cochain-pullback-tensor-coherence, lem-weil-pbc-site-derived-tensor-descent

### Original Step 4

Set $R=Lr^*j_!M$, $H=Lt^*k_!N$, $F=L\alpha^*M$, $Q=Lq^*N$. The first Cartesian square of Step 1 gives the specified $\beta_j:R\xrightarrow{\sim}v_!F$. Apply it and the tensor map for $v$ to obtain
$$E=R\otimes^LH\longrightarrow v_!F\otimes^LH\xrightarrow{\gamma_v}v_!(F\otimes^LLv^*H).$$
Since $tv=\beta$, the inner second factor is $L\beta^*k_!N$. The second Cartesian square gives its specified isomorphism $\beta_k:L\beta^*k_!N\xrightarrow{\sim}w_!Q$. Inside $v_!$ apply $1_F\otimes\beta_k$ and then $\rho^w_{F,Q}$ of Step 3. Since $\alpha w=p$, the result is $v_!w_!(Lp^*M\otimes^LQ)=v_!w_!D$. Finally apply $c_{v,w,D}$. This composite is exactly the definition of $e_{j,k}$ in the item, including its two inner signed symmetries. Every arrow is an isomorphism. Here all $\beta,\gamma$ are supplied on arbitrary unbounded complexes by [lem-sf-open-tensor-normalization]; the pullback/tensor identifications are those of [lem-pur-derived-pullback-tensor-iso].

Uses: lem-sf-open-tensor-normalization, lem-pur-derived-pullback-tensor-iso

### Original Step 5

Restrict the composite in Step 4 along $u=vw$. The first base-change map becomes $1_{Lp^*M}$: first restrict along $v$ and use its normalization, then along $w$. The map $\gamma_v$ becomes the identity after restricting along $v$, hence also after $w$. The second base-change map becomes $1_Q$ after restriction along $w$. The map $\rho^w$ becomes the identity by Step 3, and the compositor does so by Step 2. The intermediate pullback-composition and tensor identifications agree with the composite ones by the composition clause of [lem-pur-derived-pullback-tensor-iso]. Thus, identifying $u^*E$ and $u^*u_!D$ with $D$ using precisely the given units, one has $u^*e_{j,k}=1_D$.

Uses: lem-sf-open-tensor-normalization, lem-pur-derived-pullback-tensor-iso

### Original Step 6

For the opposite factorization set $G=L\beta'^*N$ on $V'$ and $P_0=Lp^*M$ on $P$. Its first base-change map is $H\xrightarrow{\sim}v'_!G$, from the Cartesian square with $k,v'$ and $t,\beta'$. The complete alternative chain is
$$R\otimes^LH\longrightarrow R\otimes^Lv'_!G\xrightarrow{\rho^{v'}_{R,G}}v'_!(Lv'^*R\otimes^LG)\longrightarrow v'_!(w'_!P_0\otimes^LG)\xrightarrow{v'_!\gamma_{w'}}v'_!w'_!(P_0\otimes^Lw'^*G)\xrightarrow{c_{v',w'}}u_!D.$$
The third arrow uses $rv'=\alpha'$ and open base change $L\alpha'^*j_!M\cong w'_!P_0$ in the square with $j,w'$ and $\alpha',p$. The last inner identification is $\beta'w'=q$. This is $e^{\mathrm{op}}_{j,k}$ with the extension factor put first whenever $\gamma$ is used. Each arrow is invertible by the same cited normalization lemma. On restriction, both base-change maps and $\gamma_{w'}$ are identities, $\rho^{v'}$ is the identity by Step 3, and the compositor is the identity by Step 2. Therefore $u^*e^{\mathrm{op}}_{j,k}=1_D$.

Uses: lem-sf-open-tensor-normalization, lem-pur-derived-pullback-tensor-iso

### Original Step 7

Restriction detects equality between the two maps just constructed. More explicitly, for any $a,b:E\to u_!D$ with equal restrictions, compose with $e_{j,k}^{-1}$ to get two maps $u_!D\to u_!D$. Full faithfulness of $u_!$ in [lem-sf-open-tensor-normalization] expresses them uniquely as $u_!a_0,u_!b_0$ for endomorphisms of $D$. Naturality of $\eta^u$ gives $(\eta_D^u)^{-1}u^*(u_!a_0)\eta_D^u=a_0$, and the same formula for $b_0$. Equal restrictions imply $a_0=b_0$, and hence $a=b$. Apply this to Steps 5 and 6 to conclude $e_{j,k}=e^{\mathrm{op}}_{j,k}$. This uses faithfulness only on the image of extension by zero, not on all ambient derived objects.

Uses: lem-sf-open-tensor-normalization

### Original Step 8

On $C',P'$ apply Steps 1--5 with $(j,M)$ and $(k,N)$ interchanged. The reversed map $e_{k,j}$ is an isomorphism and restricts to $1_{D'}$, where $D'=Lp'^*N\otimes^LLq'^*M$ on $P'$. The square with vertical opens $u,u'$ and horizontal isomorphisms $s,\bar s$ is Cartesian by the fibre-product universal property. Its normalized open base change gives
$$L\bar s^*u'_!D'\xrightarrow{\beta}u_!Ls^*D'.$$
The projection equalities $p's=q$, $q's=p$, $r'\bar s=t$, $t'\bar s=r$ identify the pullback of the reversed source with $H\otimes^LR$ and $Ls^*D'$ with $Q\otimes^LP_0$. Tensor and pullback composition use [lem-pur-derived-pullback-tensor-iso]. This is exactly the specified transport $\widetilde e_{k,j}$. After restriction along $u$, the square comparison identifies $u^*L\bar s^*e_{k,j}$ with $Ls^*u'^*e_{k,j}=1_{Ls^*D'}$, and the displayed $\beta$ is the identity by [lem-sf-open-tensor-normalization]. Thus $u^*\widetilde e_{k,j}=1_{Q\otimes^LP_0}$.

Uses: lem-sf-open-tensor-normalization, lem-pur-derived-pullback-tensor-iso, def-pc-fibre-product

### Original Step 9

Consider $h=u_!(\sigma_{Q,P_0})\circ\widetilde e_{k,j}\circ\sigma_{R,H}:E\to u_!D$. Restriction preserves the signed symmetry by [lem-pur-derived-pullback-tensor-iso], and the unit is natural on the map $\sigma_{Q,P_0}$. Step 8 therefore gives
$$u^*h=\sigma_{Q,P_0}\circ1_{Q\otimes^LP_0}\circ\sigma_{P_0,Q}=1_D.$$
The cancellation is precisely the signed calculation of Step 3, valid in all degrees. Comparing with Step 5, apply the injectivity argument of Step 7 to obtain $h=e_{j,k}$, the asserted equality of actual morphisms. All inputs to the open normalization and finite-level tensor comparison theorems were arbitrary unbounded objects of the constant-$A$ module derived categories. No compact-support pushforward for $a,b$, constructible preservation, finite Tor interval, or six-functor datum was used.

Uses: lem-sf-open-tensor-normalization, lem-pur-derived-pullback-tensor-iso
