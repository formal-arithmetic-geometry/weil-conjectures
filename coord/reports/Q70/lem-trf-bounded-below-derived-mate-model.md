# Worker report

## Files written

- Item: lem-trf-bounded-below-derived-mate-model, split; its statement is unchanged.
- lem-trf-bounded-below-square-localization: statement, unsplit; no complete Mathlib match.
- lem-trf-derived-mate-counit-reduction: statement, unsplit; no complete Mathlib match.
- lem-trf-derived-transpose-comparison-unit: statement, unsplit; no complete Mathlib match.
- citations.json: verbatim statement excerpts for every citation of every assembly step.

## Attachments

None. Searched the project by the item blueprint tag and mate/localization names. CategoryTheory.Adjunction.boundedBelowDerivedMateModel in lean/Sheaf/CategoryTheory/BoundedBelowDerivedMateModel.lean still has sorry. The source theorem CategoryTheory.Adjunction.derivedPlus_mateEquiv_app_fac is proved but takes a derived square and hθ as additional inputs, so does not attach the whole item. CategoryTheory.boundedBelowDerivedSquare is real construction data, not a theorem giving its component factorization. The proved homotopy mate formula covers only one ingredient of the third node.

## WANTED

None: the source calculations and Stacks remark are locally available.

## What was wrong and what changed

The returned 5459-character seven-step argument did too much work in one item. This repair distributes all of it, rather than deleting calculations. The sandbox initially contained only dispatcher .brief files, no node, report or searches; restored the current repository's reviewed version, which agrees with the return's seven step lengths and retains all its statement, citations, searches and metadata. No repository or Lean file was written, no git or compiler was run. New nodes are statement-only, status unsplit, with empty proof/proof_deps and null proof_origin, for other workers to split independently. They do not depend on the parent or on each other. The assembly is below 3000 characters.

## Work distribution and retained argument

The localization node takes old steps 1 and 3 (1847 characters); the counit reduction takes old steps 4 and 5 (1399 characters); the transpose comparison takes old step 2 and steps 6 and 7 (2213 characters). Step 2's adjunction existence and normalization remain explicitly cited in the assembly as well. These are separate arguments: the first has no adjoints or injective hypotheses; the second accepts an arbitrary already normalized square and stops at its derived transpose; the third has no derived square and identifies that transpose with the ordinary mate. None is a restatement of the whole item. The extraction of these calculation blocks follows the human's explicit re-split instruction even though individual substitutions within them are elementary.

The following original text is retained verbatim as the proof handover for the new statement-only nodes; it is not placed in their proof fields.

### Original step 1; assigned to lem-trf-bounded-below-square-localization

Work on $K^+(-)$, the homotopy categories of bounded-below complexes, and write $q$ for their derived localization. Termwise application of an additive functor preserves lower bounds and chain homotopies: it sends a homotopy equation $f-g=dh+hd$ to the same equation after applying the functor. The termwise components $\sigma_{N^n}$ form a chain map by naturality of $\sigma$ with each differential, giving $\sigma^K:K(L')K(G)\to K(H)K(L)$. For the exact functors $F=L,L',G,H$, [lem-weil-pbc-exact-functor-derived-factorization] gives $\phi_{F,N}:D(F)(qN)\xrightarrow{\sim}qK(F)N$, natural in $N$; termwise application preserves the zero terms below a lower bound, so these descend on the bounded-below localizations $D^+$. Put $E=D(L)$, $E'=D(L')$, $T=D(G)$ and $S=D(H)$. All comparison maps below are these fixed isomorphisms, not arbitrary identifications.

Cited nodes: lem-weil-pbc-exact-functor-derived-factorization, def-weil-abstract-derived-category.

### Original step 2; assigned to lem-trf-derived-transpose-comparison-unit

By [lem-weil-pbc-right-derived-plus-injective], $U=\mathbf R R$ and $U'=\mathbf R R'$ exist with natural comparison maps $\alpha:qK(R)\to Uq$ and $\alpha':qK(R')\to U'q$. Apply [lem-trf-bounded-below-derived-adjunction] to $L\dashv R$ and $L'\dashv R'$. Its hypotheses hold because $L,L'$ are exact and their target categories $\mathcal A,\mathcal A'$ have enough injectives. It supplies the specified adjunctions $E\dashv U$ and $E'\dashv U'$, units $\eta^D,\eta'^D$, counits $\varepsilon^D,\varepsilon'^D$, and both comparison identities in its statement. Use [lem-weil-pbc-termwise-adjunction-homotopy] for the termwise homotopy adjunctions and write $\eta'^K,\varepsilon^K$ for their unit and counit.

Cited nodes: lem-weil-pbc-right-derived-plus-injective, lem-trf-bounded-below-derived-adjunction, lem-weil-pbc-termwise-adjunction-homotopy.

### Original step 3; assigned to lem-trf-bounded-below-square-localization

Construct the required derived square. For $N\in K^+(\mathcal B)$ set
$$A_N=\phi_{L',K(G)N}\circ E'(\phi_{G,N}),\qquad B_N=\phi_{H,K(L)N}\circ S(\phi_{L,N}).$$
These identify $E'T(qN)$ with $qK(L')K(G)N$ and $SE(qN)$ with $qK(H)K(L)N$, respectively. Both termwise composites invert quasi-isomorphisms by exactness. Apply clause (2) of [lem-weil-pbc-localization-universal-property] to $q:K^+(\mathcal B)\to D^+(\mathcal B)$ and the natural transformation $q\sigma^K$. It gives the unique $\theta:E'T\to SE$ satisfying
$$\theta_{qN}=B_N^{-1}\circ q(\sigma^K_N)\circ A_N.$$
Thus $\theta$ is precisely $D(\sigma)$, a $\mathrm{TwoSquare}(T,E,E',S)$, and multiplication by $B_N$ proves, for every bounded-below homotopy complex $N$,
$$B_N\circ\theta_{qN}=q(\sigma^K_N)\circ\phi_{L',K(G)N}\circ E'(\phi_{G,N}).\tag{h\theta}$$
This is exactly the factorization hypothesis of the source's mate theorem, with its comparison maps retained. The following steps prove its needed conclusion directly.

Cited nodes: lem-weil-pbc-localization-universal-property, lem-weil-pbc-exact-functor-derived-factorization.

### Original step 4; assigned to lem-trf-derived-mate-counit-reduction

Fix $P\in K^+(\mathcal A)$ and put $X=qP$, $N=K(R)P$, $Z=qK(G)N$, $W=qK(H)P$, $a=\alpha_P$, $t=T(a)\circ\phi_{G,N}^{-1}:Z\to TU(X)$ and $h=\phi_{H,P}:S(X)\to W$. By the component formula of [def-weil-pbc-adjunction-mate],
$$b^D_X=U'(S(\varepsilon^D_X)\circ\theta_{U(X)})\circ\eta'^D_{TU(X)}.$$
Naturality of $\eta'^D$ with $t$ and of $\theta$ with $a:qN\to U(X)$ gives
$$U'(h)\circ b^D_X\circ t=U'\!\left(h\circ S(\varepsilon^D_X\circ E(a))\circ\theta_{qN}\circ E'(\phi_{G,N}^{-1})\right)\circ\eta'^D_Z.$$
Indeed $\eta'^D_{TU(X)}\circ t=U'E'(t)\circ\eta'^D_Z$ and $\theta_{U(X)}\circ E'T(a)=SE(a)\circ\theta_{qN}$; substitute these two equalities and use functoriality. No derived comparison unit is canceled.

Cited nodes: def-weil-pbc-adjunction-mate.

### Original step 5; assigned to lem-trf-derived-mate-counit-reduction

The counit identity in [lem-trf-bounded-below-derived-adjunction] reads $\varepsilon^D_X\circ E(a)=q(\varepsilon^K_P)\circ\phi_{L,N}$. Naturality of $\phi_H$ with $\varepsilon^K_P:K(L)N\to P$ reads
$$h\circ S(q\varepsilon^K_P)=q(K(H)(\varepsilon^K_P))\circ\phi_{H,K(L)N}.$$
Substitute these into Step 4. Its argument of $U'$ becomes
$$q(K(H)(\varepsilon^K_P))\circ B_N\circ\theta_{qN}\circ E'(\phi_{G,N}^{-1}).$$
Using $(h\theta)$ from Step 3 cancels $E'(\phi_{G,N})$ with its inverse and changes this to $q(d)\circ\phi_{L',K(G)N}$, where
$$d=K(H)(\varepsilon^K_P)\circ\sigma^K_N:K(L')K(G)N\to K(H)P.$$
Consequently $U'(h)\circ b^D_X\circ t=U'(q(d))\circ U'(\phi_{L',K(G)N})\circ\eta'^D_Z$.

Cited nodes: lem-trf-bounded-below-derived-adjunction, lem-weil-pbc-exact-functor-derived-factorization.

### Original step 6; assigned to lem-trf-derived-transpose-comparison-unit

Apply the primed unit identity of [lem-trf-bounded-below-derived-adjunction] to $K(G)N$. It gives
$$U'(\phi_{L',K(G)N})\circ\eta'^D_Z=\alpha'_{K(L')K(G)N}\circ q(\eta'^K_{K(G)N}).$$
Naturality of the right-derived comparison $\alpha'$ on the homotopy morphism $d$ from Step 5 is
$$U'(q(d))\circ\alpha'_{K(L')K(G)N}=\alpha'_{K(H)P}\circ q(K(R')(d)).$$
Hence the last expression of Step 5 equals
$$\alpha'_{K(H)P}\circ q\!\left(K(R')(d)\circ\eta'^K_{K(G)N}\right).$$
The comparison is natural on every bounded-below homotopy complex, so this use needs no injectivity of $K(H)P$.

Cited nodes: lem-trf-bounded-below-derived-adjunction, lem-weil-pbc-right-derived-plus-injective.

### Original step 7; assigned to lem-trf-derived-transpose-comparison-unit

The termwise adjunction of [lem-weil-pbc-termwise-adjunction-homotopy] has exactly the termwise unit and counit. The mate component formula in [def-weil-pbc-adjunction-mate], applied in each degree, therefore gives
$$K(R')(d)\circ\eta'^K_{K(G)N}=K(b)_P,$$
since its degree-$n$ map is $R'(H(\varepsilon_{P^n}))\circ R'(\sigma_{R(P^n)})\circ\eta'_{G(R(P^n))}=b_{P^n}$. Step 6 becomes $U'(h)\circ b^D_X\circ t=\alpha'_{K(H)P}\circ q(K(b)_P)$. Inserting the definitions of $h$ and $t$, this is the precise equality
$$U'(\phi_{H,P})\circ b^D_{qP}\circ T(\alpha_P)\circ\phi_{G,K(R)P}^{-1}=\alpha'_{K(H)P}\circ q(K(b)_P).$$
Passing from a complex to its homotopy class identifies $qK(b)_P$ with $Q(C(b)_P)$. This is the displayed conclusion under the specified canonical localization identifications. Only the $\phi$'s were inverted; $\sigma$, $\alpha$, $\alpha'$ were never inverted, and nowhere was preservation of injectives by $H$ used.

Cited nodes: lem-weil-pbc-termwise-adjunction-homotopy, def-weil-pbc-adjunction-mate.

## Not duplicates

- lem-trf-bounded-below-square-localization vs lem-weil-pbc-localization-universal-property: the existing generic localization theorem is an ingredient; the new node includes the termwise chain/homotopy construction, lower bounds, both composite comparisons, and the explicit hθ formula for arbitrary exact squares.
- lem-trf-bounded-below-square-localization vs def-weil-pbc-derived-square-iso: existing node concerns invertible inverse-image squares of schemes, while the new statement treats arbitrary noninvertible transformations of four exact additive functors.
- lem-trf-bounded-below-square-localization vs lem-weil-pbc-derived-square-pasting: the latter compares pasting of invertible squares, not construction and the component formula for an arbitrary transformation.
- lem-trf-bounded-below-square-localization vs lem-pc-homotopy-pullback-square-localization: the latter concerns tensor pullbacks along scheme morphisms and an extra map a, not arbitrary exact functors and descent of a noninvertible transformation.
- lem-trf-bounded-below-square-localization vs lem-weil-pbc-ringed-square-localization: the latter identifies a geometric ringed square with a derived square isomorphism, not the abstract noninvertible square and factorization here.
- lem-trf-derived-mate-counit-reduction vs lem-trf-bounded-below-derived-adjunction: that node constructs a single derived adjunction and its unit/counit identities; the new node combines two adjunctions, square naturality and the exact localization comparisons to give a particular intermediate mate reduction.
- lem-trf-derived-mate-counit-reduction vs lem-pc-derived-mate-pasted-unit: that node uses unbounded K-injective derived functors and a different pattern of adjunctions; it concludes a full pasted mate formula, not this bounded-below intermediate counit reduction.
- lem-trf-derived-mate-counit-reduction vs lem-pur-exact-derived-mate: that node treats unbounded K-injective categories and the final mate comparison; the new node is the intermediate bounded-below formula before the primed transpose is identified.
- lem-trf-derived-transpose-comparison-unit vs lem-weil-pbc-termwise-adjunction-homotopy: the existing node has termwise units/counits, not their comparison with the canonical bounded-below derived unit in the presence of a square.
- lem-trf-derived-transpose-comparison-unit vs lem-trf-bounded-below-derived-adjunction: the latter has a unit identity for one object; the new node also identifies the chain-level mate of a square and moves its counit-square composite through the natural right-derived comparison.
- Each new node vs lem-trf-bounded-below-derived-mate-model: square existence, intermediate counit reduction, and underived-transpose comparison are three different proper parts of the original argument; none asserts the original final equality.

Searched the whole DAG by tags/names and statement concepts, and the whole blueprint via blueprint_refs search for derived mate, derived square, comparison units, counit reduction, termwise mate, localization square, derived transpose, and counit comparison. No blueprint node states any new node. The exact source of the new nodes is the project calculation, not Stacks 07A7: that remark supplies only the counit-transpose normalization, not these three abstract comparison results. Thus the new source fields cite the actual theorem/definition and line ranges, without misattributing them to a Stacks tag.

## Mathlib search assessment

All new-node searches were actually run through msearch.py and the exact records are copied from searches.jsonl. Each node has two semantic phrasings, Loogle and grep, plus the LeanSearch attempt. LeanSearch returned a rate-limit service error and is marked unavailable. Initial short-namespace Loogle queries were invalid identifiers and are recorded as invalid, followed by successful fully qualified searches. Read CategoryTheory.Localization.fullyFaithfulWhiskeringLeft (Predicate.lean:278), exact functor comparisons (ExactFunctor.lean:41,61), CategoryTheory.mateEquiv and its counit formulas (Mates.lean:84,123), and derivedη_fac_app/derivedε_fac_app (Derived/Adjunction.lean:103,131). They supply ingredients rather than a one-line specialization giving the complete extracted statements. DerivabilityStructure/Basic hits concern Guitart exactness for a localizer morphism, rather than descent of this arbitrary double composite square. No Mathlib leaf is claimed.

## Review by Q70

I read Stacks sites-cohomology.tex, Tag 07A7 (remark-base-change, lines 4032–4059), which normalizes the exchange as the transpose of the counit composite. I checked the full source theorem derivedPlus_mateEquiv_app_fac, lines 419–484, and the actual boundedBelowDerivedSquare construction at lines 45–73. For the first new node these provide the exact double-comparison square and hθ, while the existing localization-universal-property statement supplies unique descent, not an invertibility assertion. For the second I read the source's mate expansion, naturalities, unprimed counit formula and its final key calculation. For the third I read the primed unit calculation and the proved mapHomotopyCategoryPlus_mateEquiv_app in HomotopyCategory/Adjunction.lean:599–648, including its actual degreewise proof. These sources cover precisely the retained old arguments.

Assembly step 1 cites square-localization, whose statement explicitly gives hθ at every bounded-below homotopy complex. Step 2 cites derived-adjunction for existence and both comparison identities: its hypotheses need enough injectives only on A and A', which the item has, and exact L,L'. It also cites counit-reduction, whose statement accepts exactly step 1's hθ and concludes exactly the displayed intermediate expression. Step 3 cites transpose-comparison-unit, whose statement has exactly that expression on its left and alpha'_W q(K(b)_P) on its right. The definition of the derived category explicitly permits localization from the homotopy category, so it supports the final identification with Q(C(b)_P). Every cited statement was read; citations.json copies the exact formula or sentence used. No citation uses an internal proof construction instead of its statement.

I checked the types: t goes from qK(G)K(R)P to TU(qP), h from S(qP) to qK(H)P, d from K(L')K(G)K(R)P to K(H)P, and both sides of the intermediate and final equations end in U'(qK(H)P). Naturality is used on arbitrary homotopy complexes. The only inverses are the exact-functor phi isomorphisms; sigma, alpha, alpha' are never canceled. No preservation of injectives by H, no enough injectives on B or B', no extra invertibility was introduced. The item statement is unchanged. The new statements are self-contained and list all defining notions. The elementary components stay inside the larger arguments requested by the re-split return, rather than becoming separate trivial nodes.

For edge cases, zero sigma gives zero square, zero d and zero mate in the additive categories; identity functors and identity adjunctions reduce all comparisons and all three identities to sigma or its ordinary transpose. The zero complex gives the zero morphism. An arbitrary lower bound, including a negative one, is preserved by every additive termwise functor because it preserves zero objects; no nonnegative restriction is used. The comparison identity remains meaningful when H(P) is not injective and alpha' is not an isomorphism. Reading each retained step shows that no argument was lost: steps 1/3 go to square descent, 4/5 to counit reduction, and 2/6/7 to primed transpose comparison (with adjunction existence additionally in the assembly). There are no assembly steps above 2000 characters. Checked delivery-errors B–E for statement-only shape, honest searches, source attribution, notion dependencies, duplicate scope, citation coverage, cycles, route and every applied hypothesis. No source error or statement dispute was found. No SGA source or change of unit/chapter route is used.

## Unfinished work

Only the new statement-only nodes await their own workers, as explicitly required by the return. Delivery validation is recorded below after the server checks.

## Delivery validation

The first server dry run rejected the phrase “the item's formula” in assembly step 3 as a standalone-reading violation (B2). Replaced it with the explicit final formula, retaining the complete equation and all hypotheses.

Server dry run passed: OK (not pushed), commit 5bcc51307ec. A final typography correction writes the primed comparison as alpha^{prime}; the final dry run revalidates that exact snapshot before delivery.


## Landing-refusal repair, 2026-10-22

The return at head 8e4c1af415e reports side completion not promoted to the live queue DAG, rather than a failed mathematical review. I continued the retained sandbox, including all three new nodes, citations, logged searches and the preceding review. The first new dry run completed successfully at a8b90d3fd3e against the delivery tool's current fetched base. The delivery tool constructs the rebased commit; I ran no git command in the read-only repository.

I compared the retained item with the current read clone. The current item has the original seven-step argument reproduced above, while the retained item assembles the three extracted results. Its statement, statement dependencies, source, blueprint route, audit, Lean and review metadata are identical; only proof, proof dependencies and split report differ. None of the three extracted ids exists in the current read clone. The released stage-1 repair note still explicitly requests this re-split and at least two independent new nodes. The new split report records this current-base comparison, so this repair includes a refreshed explanation of the landing refusal and dependency audit rather than an unexplained unchanged re-push.

### Current dependency and source re-reading by Q70

I re-opened every current statement used by the assembly and the statements defining all new-node hypotheses: def-sp-abelian, def-sp-injective-resolutions, def-weil-size-convention, def-weil-abstract-derived-category, def-weil-pbc-bounded-derived-subcategories, lem-weil-pbc-exact-functor-derived-factorization, lem-weil-pbc-right-derived-plus-injective, def-weil-pbc-adjunction-mate, lem-weil-pbc-termwise-adjunction-homotopy and lem-trf-bounded-below-derived-adjunction. I also re-read localization-universal-property for the square-node handover. In particular the derived-adjunction node currently records closed upstream attachments for derivedPlus, derivedPlus_unit_app_fac and derivedPlus_counit_app_fac; its two displayed identities are still precisely the normalizations required in assembly step 2 and the new counit and transpose nodes. Thus its newer completion metadata requires no change to the proof equations or additional hypotheses. Exact-functor-derived-factorization supplies natural phi isomorphisms and preservation of quasi-isomorphisms; termwise-adjunction-homotopy explicitly supplies restriction to bounded-below homotopy categories. Right-derived-plus-injective supplies the natural comparison on arbitrary bounded-below complexes, not just injective complexes. Localization-universal-property clause (2) explicitly supplies unique descent of a noninvertible natural transformation. These facts remain exactly the ingredients assigned to the three extracted nodes.

I re-read Stacks 07A7, remark-base-change in sites-cohomology.tex, the full source derivedPlus_mateEquiv_app_fac at lines 419–484, its derived unit/counit normalizations at lines 143–160, the termwise mate proof at HomotopyCategory/Adjunction.lean lines 599–648, and boundedBelowDerivedSquare plus the still-sorried boundedBelowDerivedMateModel in the Sheaf module. The general upstream formula assumes theta and htheta: it does not attach the item by itself. The Sheaf definition gives the concrete fully faithful localization lift, but the final theorem remains sorry. For the recorded Mathlib hits I inspected fullyFaithfulWhiskeringLeft, mateEquiv and derived unit/counit factorization declarations; their scope remains the ingredients described in the existing search assessment. I read searches.jsonl and retained its exact successful, invalid-query and unavailable-service results; the statements and search questions have not changed, so no search was repeated or invented.

For step 1 I rechecked both composite phi maps and the type of the square equation against square-localization's statement. For step 2 I rechecked the unprimed counit identity and the domains of t and d against counit-reduction. For step 3 the transpose-comparison statement gives exactly the intermediate right side; the derived-category definition explicitly identifies localization through complexes with localization through homotopy classes. All five citation quotes still occur verbatim in their current statements. The only inverses remain phi isomorphisms. In the zero-square and identity-adjunction cases the equations still reduce respectively to zero and to the ordinary square; allowing noninjective H(P) introduces no cancellation of alpha'. Each new node remains a self-contained statement only. The assembly remains below 3000 characters, with no step exceeding 2000, and all seven original arguments remain in the handover above. This addresses the return without altering the statement, route or retained mathematical split.


## Repeated landing-refusal repair: returned head 8449ebf9c0a

The current return in coord/returns/Q70.md is dated 2026-10-22 09:24 UTC at head 8449ebf9c0a and repeats the side-completion/live-queue promotion refusal. The earlier 8e4c1af415e entry above describes the preceding repair, not this latest return. I retained that work and its verbatim seven-step handover. The initial dry run in this repair exited successfully at 4ea4dc9ffc6 before any edits. That is validation of the delivery overlay, not evidence that the maintainer has promoted a side completion into the live DAG. This delivery still requires that maintainer action identified by the return; no worker-owned field can perform it.

I compared the retained delivered files with the present read clone. Only proof, proof_deps and split_report differ on the item; the statement, stmt_deps and all remaining fields agree. The three extracted ids are absent from that read clone. The released stage-1 repair note still requires at least two independent statement-only nodes, so the retained three-node extraction is the work to land. The delivery tool rebases the worker-owned fields onto its current fetched origin/sheaf-dag and preserves the maintainer metadata.

### Review by Q70 of the current-base repair

I reopened every cited statement and every statement defining a new node's hypotheses, including the localization universal property used by its retained proof handover. The current derived-adjunction node has closed upstream attachments for derivedPlus and its two comparison formulas; its statement continues to give both identities with enough injectives only on the target of L. In assembly step 2 I now write the precise unprimed counit normalization explicitly. Its strengthened citations.json excerpt copies both current formulas verbatim, rather than quoting existence alone. The square and transpose statements require no adjustment of hypotheses. In particular the right-derived-plus-injective statement gives a natural comparison on arbitrary bounded-below homotopy complexes; its injective-complex isomorphism clause is not used for H(P).

I reread Stacks 07A7, the source mate calculation at PlusAdjunction.lean:419–484 and the unit/counit identities at 143–160, the homotopy mate calculation at HomotopyCategory/Adjunction.lean:599–648, and the Sheaf construction and theorem. The project theorem assumes a derived square and htheta, so it is only an ingredient; the Sheaf theorem at line 108 still ends in sorry. There is no attachment for the whole item. I read every retained search-log result and the relevant Mathlib declarations for localization, exact-functor comparisons, mates and derived units/counits. Their scopes remain the ingredients already recorded; the search questions did not change, and no recorded search was invented or repeated.

For assembly step 1, square-localization supplies exactly B_N theta_(qN)=q(sigma_N) A_N. Step 2 uses the current derived adjunction and its counit normalization, and counit-reduction takes that very square equation to its displayed intermediate expression. Step 3 uses transpose-comparison's second equality on that expression, then the derived-category definition's equivalence of localization from complexes and homotopy classes. Every quote was checked as a verbatim substring. The source, domain and codomain of t, h and d still match; only phi isomorphisms are inverted. Zero sigma, the zero complex, identity adjunctions and arbitrary negative lower bounds give the expected identities, and no assumption that H preserves injectives appears. The new nodes have empty proof fields, remain independent of their parent and each other, and retain all seven arguments in the report handover. Delivery-errors B–E therefore give no further correction.

Current read-clone dependency statement fingerprints (SHA-256 of the UTF-8 statement) provide a baseline for a future changed-dependency audit:

- def-sp-abelian: 58f56570b56b9d82aaa311dcf93d3264b6df01633c2469e205c8acd002bd9d6e
- def-sp-injective-resolutions: 7ac43cd1029124547c795b9847375cc19ae2b987e60918e6a0ed4e26cb121f2a
- def-weil-abstract-derived-category: 9b8a86dbaa2660eea2db6af7f33887dd07d6908422dc7b9a7f18c311ff63f298
- def-weil-pbc-adjunction-mate: e55ec8c5d6d1f099b6f4dd8e4495aa716957ae71b0c77ac74929aa2fdbf6b87c
- def-weil-pbc-bounded-derived-subcategories: 141fb8ca9d331facd1dd0a3629eb7f565e8876875382b5be1395382b78f2567a
- def-weil-size-convention: ae70e9588534895e24d390692173670d382f84fc7444b8a6d171cd35cbef2d7c
- lem-trf-bounded-below-derived-adjunction: 106b5d4d82ac614b2d7b4f62b8da7770e890e86f0b863adf3dbc1945c57b1db7
- lem-weil-pbc-exact-functor-derived-factorization: 3ee0bb75f20234a0b53251f84ddf62e82780bf8bd4b857d6e9e1195d6bbf0288
- lem-weil-pbc-localization-universal-property: d98f07b6e5f9568644e3ce808dd725ccf96a84d84556adc7b62fdabcf4674d0d
- lem-weil-pbc-right-derived-plus-injective: e8e08b7ad258c79d0b8afb87fa834b75a432851905b241c24ec0a36c9b54897a
- lem-weil-pbc-termwise-adjunction-homotopy: 7f470a340df0930b3613553540bfbb9aa63791ca631e860ba4cd78cfe2894635

The final dry run below revalidates the changed assembly and citation snapshot before pushing.


## Current landing-refusal repair: returned head 908b41f55c6

The latest visible return is dated 2026-10-22 13:36 UTC, head 908b41f55c6. Its single repair instruction is to rebase on the current DAG, reread changed citations, adjust and push. I began with the retained files and a dry run, which exited OK at bc323f26ce2. I then rebuilt the sandbox item from the current read-clone item and overlaid only the retained proof, proof_deps and refreshed split_report. Thus current metadata is preserved explicitly. The delivery tool fetches its current base again when packaging. No git command was run in the repository.

I compared all eleven dependency statement hashes with the preceding repair's baseline above: every one agrees. I nevertheless reopened their statements and the three new statements, including localization-universal-property for the handover. No changed statement requires a new hypothesis or proof route. The three new ids remain absent from the read clone. The released stage-1 repair note still requires the three-part extraction, rather than treating the original reviewed seven-step proof as completed work.

For an explicit adjustment to the assembly, step 1 now gives both A_N and B_N as composites of the fixed exact-localization comparisons. This records their exact order and prevents htheta being read with arbitrary comparison isomorphisms. I expanded its citation quote to include the definitions of both composites and the square equation. The other four quotes remain verbatim; together the five entries cover every step citation.

### Review by Q70 of returned head 908b41f55c6

For step 1 I checked square-localization's full statement: E'T(qN) maps through A_N to qK(L')K(G)N, and SE(qN) maps through B_N to qK(H)K(L)N. The square equation thus has the exact source and target required by PlusAdjunction.lean:419–429. I read the concrete fully faithful localization lift in boundedBelowDerivedSquare at lines 45–73. It constructs the square but is not a proof of the whole item.

For step 2 I reread derived-adjunction's two identities and counit-reduction's statement. The target categories A and A' have enough injectives, and L and L' are exact, exactly as required; no such assumption is imposed on B or B'. Substitution of the now explicit square comparisons and the unprimed counit normalization gives the intermediate expression printed in counit-reduction. The source proof's naturality and key calculation at PlusAdjunction.lean:439–484 use those same maps.

For step 3 I checked transpose-comparison's expression against step 2 term for term. Its unit normalization and naturality are valid at arbitrary W=K(H)P, including noninjective W. The degreewise mate calculation in HomotopyCategory/Adjunction.lean:599–648 identifies its ordinary transpose, and derived-category's statement explicitly permits localization through the homotopy category. Stacks 07A7 (remark-base-change) supplies the counit-transpose convention only; no larger claim is attributed to it. The whole-item Sheaf theorem still ends in sorry, while the proved upstream mate theorem assumes theta and htheta. Neither is an attachment for the whole item.

The B–E review found all three extracted statements self-contained with empty proof and proof_deps; their hypotheses and fixed comparison maps agree with the source. The original seven arguments remain verbatim in the handover. Zero sigma, zero complexes, identity adjunctions and negative lower bounds remain valid; only phi isomorphisms are inverted. No source dispute, extra injectivity or invertibility assumption, cycle, or new route was introduced. I read the retained search-log results and preserved their actual invalid-query and unavailable-service outcomes; unchanged statements and search questions did not justify repeating those searches. No Lean or compiler work was performed.

The refusal concerns maintainer-owned promotion from side completion into the live queue DAG. This refreshed delivery does not claim that a worker can perform that promotion; it supplies the rebased, adjusted split for L to promote and land. Final dry run and delivery follow on this exact snapshot.


## Repair of returned head febfd17fe31, 2026-10-23

The latest return in coord/returns/Q70.md is dated 2026-10-22 16:32 UTC and names delivered head febfd17fe31. The mathematical reader approved that delivery; landing refused side completion not promoted to the live queue DAG. I continued the retained delivered files. The required first dry run exited OK at 17ec71074dd, before any new edits. I then rebuilt the sandbox item from the current read-clone item, overlaying only proof, proof_deps and split_report. Its other fields agree exactly with the current node, and the three extracted ids are still absent from the read clone. The released stage-1 repair order still requests the extraction, so the old reviewed seven-step proof is not grounds to discard it. The delivery tool fetches its base and builds the rebased commit; no git command was run in the read-only repository.

I compared all eleven dependency statement fingerprints against the baseline above: every hash agrees. Thus there is no changed cited statement requiring altered hypotheses or a replacement argument. I reopened those eleven statements and all three extracted statements anyway. In assembly step 2 I explicitly typed h:S(X) to qW, t:Z to TU(X), and d:K(L')M to W. This adjustment distinguishes the homotopy complex W=K(H)P from the derived object qW at the exact interface between counit reduction and transpose comparison. Both sides of the intermediate equation have source Z and target U'(qW). The final equation consequently has the same type before removing only the fixed phi identifications.

### Current review by Q70

Step 1 uses precisely square-localization's definitions of A_N and B_N and its unique square equation, without assuming sigma invertible. Step 2 uses derived-adjunction's canonical adjunction and counit normalization and counit-reduction's displayed intermediate identity. The item supplies exact L,L' and enough injectives on A,A', exactly the hypotheses of those statements. Step 3 uses transpose-comparison's displayed second identity, then the derived-category definition's equivalence of complex and homotopy localization. The five citation excerpts cover every step citation and remain verbatim substrings. I also reopened localization-universal-property clause (2) for the square-node handover; it supplies unique descent of arbitrary natural transformations, rather than only isomorphisms.

I reread Stacks 07A7 (sites-cohomology.tex, remark-base-change), the source derivedPlus_mateEquiv_app_fac at PlusAdjunction.lean:419–484, its unit/counit formulas at 143–160, and mapHomotopyCategoryPlus_mateEquiv_app at HomotopyCategory/Adjunction.lean:599–648. For square-localization I checked the real localization preimage construction in boundedBelowDerivedSquare. For counit-reduction I checked mate expansion, both naturalities, and the counit substitution in the source. For transpose-comparison I checked the primed unit formula, comparison naturality, and the actual degreewise mate proof. The whole-item Sheaf theorem still has sorry; the proved upstream theorem still requires theta and htheta as inputs. Neither establishes every clause of the item without further work, so there is no attachment.

I read the retained searches.jsonl results, including failed identifier queries and unavailable LeanSearch results, and inspected the Mathlib localization and derived-adjunction hits. The statements and search questions are unchanged, so the logged searches are reused, not repeated or invented. I refreshed blueprint searches for derived mate and localization square; neither found a blueprint duplicate. No new node was created in this repair beyond the retained three-node extraction.

For B–E I checked self-contained statements, all defining hypotheses, statement-only shape, comparison order, citation coverage and absence of an extra injectivity requirement. Zero sigma, zero complexes and identity adjunctions reduce the formulas to zero or the ordinary square. Arbitrary negative lower bounds are preserved termwise. Noninjective H(P) is allowed because alpha' is used only by naturality and never inverted. The original seven arguments remain verbatim in the handover, with separate square descent, counit reduction and transpose comparison statements. No assembly step exceeds 2000 characters and the total remains below 3000. No Lean, compiler, repository or launcher file was changed.

This addresses the worker's requested rebase, rereading and split adjustment. The return's promotion into the live queue DAG remains L's action; this report does not claim that a successful worker dry run performs it. The final dry run and delivery validate the refreshed snapshot below.
