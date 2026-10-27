# Q113 repair: lem-pur-affine-space-trace-factorization

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-affine-space-trace-factorization.json`: existing statement, unchanged byte-for-byte as a decoded string; split, three assembly steps, 1485 proof-text characters.
- `dag/nodes/sec-smooth-purity/lem-pur-affine-line-composite-transpose.json`: statement, unsplit, no Mathlib match; naturality/unit normalization of the actual line evaluation and the composite exceptional-transpose equation. This is the first independent argument.
- `dag/nodes/sec-smooth-purity/lem-pur-base-changed-line-trace-evaluation.json`: statement, unsplit, no Mathlib match; evaluating the pulled-back line trace via the specified projection map, before identifying any binary product. This is the second independent argument.
- `dag/nodes/sec-smooth-purity/lem-pur-affine-space-last-factor-product.json`: statement, unsplit, no Mathlib match; applicability of both concrete forward products and identification of their inverse composites. This is the third independent argument.
- `citations.json`: verbatim statements for every citation in the three assembly steps. `searches.jsonl` and the fifteen raw search result files preserve the actual searches; `returned-node.json` preserves the current repository's returned proof used below.

## Attachments

None. I searched `lean/WeilConjectures/` both for the exact blueprint tag and for affine trace/integration, purity-composition and ordered-transpose terms. In `WeilConjectures/EtaleCohomology/Purity/Smooth/AffineSpaceTrace.lean`, `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace` is only an existence of an isomorphism, with `sorry`. The module explicitly says that the trace and its counit normalization are not constructed. `Smooth/AffineSpace.lean` similarly records existence statements rather than the actual comparisons. Neither attaches this item or any new obligation.

## WANTED

None. This repair expands the already agent-written blueprint integration argument; it does not attribute the expanded map equalities literally to a missing textbook. No prohibited SGA route was used.

## What was wrong and what changed

The return asked for a real distribution of 7087 proof characters, not a shorter paraphrase. On this retry the sandbox contained only dispatcher marker files, with no node, report, citations or logged searches to recover. I copied the existing live item (including its proof, sources, recorded old searches, blueprint fields and audit) into the sandbox. It has the exact six returned steps of lengths 1302, 1110, 1105, 996, 938 and 1636. The parent's statement is preserved. No chapter or unit record is changed, and no repository or launcher file is written.

The new statements have lengths 2372, 2361 and 2809 characters, respectively, including all their independent hypotheses and map definitions. All three are statement-only (`status: unsplit`, empty proof and proof-dependency lists, null proof origin), so three workers can begin separately. The parent only substitutes their equalities and uses the ordered definition. Its 1485-character assembly is below the 3000-character return limit, and its longest step is below 2000. No whole conclusion has been renamed as a new node: the first obligation mentions no product; the second mentions neither an exceptional transpose nor Kunneth; the third mentions no trace evaluation or exceptional inverse image.

## Allocation of every old argument

The text of every old step is retained verbatim in the appendix. This allocation is the handoff guide for the independent workers; the new node files themselves contain no proof sketches.

- Old Step 1: the affine-space coordinate geometry, Tate identification, rank-one finite Tor argument, etale-origin witnesses, comparison of Tor amplitude, four projection formulas and two product exchanges belong to `lem-pur-affine-space-last-factor-product`. Its conclusions explicitly include their applicability, invertibility, and the bounded-below etale-origin condition on every tensor in both forward composites. The corresponding generic projection/exchange applicability at arbitrary `(f,M)` is also included in `lem-pur-base-changed-line-trace-evaluation`. The exceptional-input assertion `Rp^!K in D^b_ctf` belongs to `lem-pur-affine-line-composite-transpose`; its statement includes it, rather than silently adding it to the parent's hypotheses.
- Old Steps 2 and 3: line evaluation `b`, its two symmetries, naturality, proper/open tensor-unit normalization, and the actual composite-adjunction transpose equation belong to `lem-pur-affine-line-composite-transpose`. The final rank-one identification with `I_1` is the parent's assembly Step 1 using the identity case of `def-pur-affine-space-comparison`. The first worker must prove the counit-pasting equation, not assume a twisted pullback is already an exceptional adjoint.
- Old Steps 4 and 5: the base-change equality for the actual line integrations, the typed composites `C` and `D`, substitution into the line evaluation, projection-formula naturality at `t_Y`, and the proper/open unit normalization belong to `lem-pur-base-changed-line-trace-evaluation`. Its conclusion is exactly the equality before postcomposition with `I_m`. The final naturality of the tensor unitor after postcomposition remains written in the parent's last step.
- Old Step 6: checking both forward-product domains, using finite forward-product symmetry, inverting the two concrete composites, and expanding the swapped inverse into the four arrows defining `D` belong to `lem-pur-affine-space-last-factor-product`. Its conclusion is the actual equality `kappa = D`, not existence of some product isomorphism. The supplied `kappa` is an isomorphism exactly as the unchanged parent assumes; this supplies boundedness of `V_m tensor U` in the old argument. No assertion from the abstract six-functor-datum theorem is used as a theorem for concrete operations.

The first worker's expected tools are the line definition, finite compact-support projection formula, ringed projection unit normalization, composite adjunction, mate-pasting, and constructible exceptional preservation. The second worker's tools are the line definition, finite compact-support projection formula and its naturality, ringed projection unit normalization, and finite compact-support exchange. The third worker's tools are finite twists, etale-origin and Tor-amplitude comparison, the four finite compact-support projection formulas, two exchanges, composition, pullback tensor compatibility and the existing finite forward-product symmetry. These are precisely the tools cited in the old steps below, with no argument discarded.

## Not duplicates

I searched the whole DAG by titles and statement regular expressions for ordered counits/integrations, line transposes, composite counits, last-coordinate products, base-changed line traces, forward-product symmetry and tensor-unit normalization. I ran `tools/blueprint_refs.py search` for trace, projection, product, iterated trace, transpose, product symmetry, ordered integration, line trace, last-coordinate and binary product. The broad results were narrowed by reading the following candidate statements. The nearest blueprint ancestor is `prop-pur-affine-space-composition-law`; all new nodes use `via: [lem-pur-affine-space-trace-factorization]`. There is no equal blueprint statement, so all `same_as` lists are empty. The sources are the local blueprint, not Stacks-tag-labelled new lemmas, so there is no new-node/existing-node pair sharing a source tag.

lem-pur-affine-line-composite-transpose vs lem-pur-composite-integration-counit: the existing result assumes twisted pullback functors already are right adjoints, coefficient-form counits, tensor-action and projection/composition identities. The new result computes the transpose of an arbitrary map into the constructible exceptional adjoint; it does not assume purity or those projection/composition identities.

lem-pur-affine-line-composite-transpose vs def-pur-affine-line-purity-comparison: the definition gives `b` and its transpose, but does not state naturality, tensor-unit normalization or the composite exceptional-transpose equation.

lem-pur-affine-line-composite-transpose vs lem-weil-pbc-mate-pasting: the latter is a generic categorical pasting theorem; it does not supply line-evaluation normalization, admissibility of the intermediate exceptional input, or the geometric formula specialized to the specified projection maps.

lem-pur-base-changed-line-trace-evaluation vs lem-amb-affine-trace-line-counit-base-change: the existing node transports an actual one-coordinate counit through a base-change square. The new node assumes the trace's base-change equality and evaluates the further pushforward/projection composite for arbitrary `M`, without assuming a twisted-pullback adjunction.

lem-pur-base-changed-line-trace-evaluation vs lem-pur-ordered-tensor-coefficient-mate: the existing formal statement assumes all relevant scalar, evaluation and projection squares and compares scalar transport. The new statement proves a concrete compact-support evaluation equality from the given trace base change; it has no scalar-extension functors or assumed projection square.

lem-pur-base-changed-line-trace-evaluation vs lem-weil-finite-compact-projection-formula: that node gives invertibility and naturality of PF, not this integration/exchange evaluation equality for the specific maps and unit normalization.

lem-pur-affine-space-last-factor-product vs lem-pur-finite-forward-product-symmetry: the existing result equates forward composites without assuming invertible projection transformations. The new result establishes the applicability and invertibility for shifted Tate lines and identifies their actual inverse composite with the specified `kappa`; it is not the forward-symmetry statement.

lem-pur-affine-space-last-factor-product vs lem-sf-kunneth-coherence: the latter requires an abstract six-functor datum and asserts general coherence. The new result works with concrete finite chosen-compactification maps and only the specified construction of the supplied binary isomorphism.

lem-pur-affine-space-last-factor-product vs lem-sf-proper-product-counit-transpose: that result requires both maps proper and an abstract datum, and computes an ordinary pullback/pushforward transpose. Affine-space projections here are not proper and no such abstract datum is an input.

lem-pur-affine-space-last-factor-product vs lem-pur-affine-space-trace-factorization: the parent evaluates an ordered exceptional transpose against actual integrations. The new statement only compares the two product maps and checks their domains, with no integration or exceptional functor.

## Mathlib searches read

For each new node I ran two distinct LeanFinder phrasings, Loogle, a Mathlib source grep through the required command, and LeanSearch. The queries in the node files are copied exactly from `search-plan.json` and the actual `searches.jsonl` log. Every service answered successfully in this run. All raw returned signatures were read; no service failure is called a negative match.

For the first node the closest hits were `CategoryTheory.Adjunction.comp_counit_app`, `homEquiv_counit`, `counit_naturality`, and scheme-module pullback/pushforward conjugation. They describe the categorical core, but do not state the compact-support line normalization, its Tor/constructibility domain, and its specific exceptional transpose. The second node's Loogle hits were tensor-unitor naturality; semantic searches returned measure integration, scheme tensor-pullback identities and linear-algebraic trace. The third node's searches returned ordinary product projections, scheme affine charts and measure-theoretic Fubini. No returned declaration is an exact or one-line generalized instance of any new statement. These remain unsplit obligations, with zero Mathlib leaves. The parent's old searches, already read from the returned item, are preserved without invented reruns.

## Review by Q113

I read `GOAL.md`, the three levels of `SETUP.md`, the smooth-purity chapter and `sk-prop-an` unit record, the current main-20261015 unit integration paragraph, and the ancestor master `prop-pur-affine-space-composition-law.md` Steps 3--4. The current unit says that the trace on affine space is the recursively integrated affine-line counit, using compact-support composition and PF, with base-change compatibility. The ancestor's binary-product identification needs an actual-map argument; even degree alone does not prove it. I retained that argument as the third obligation, without adding coordinate-permutation invariance to this item.

For the three new nodes, the same integration paragraph is the source intent, and the exact returned steps listed above specify the expanded arguments. I also read Scholze's local lecture notes, Definition 5.1 and its following construction of the comparison as adjoint to PF followed by the counit, and Theorem 7.19's affine-line reduction. Those notes confirm the permitted route but are not falsely claimed to state any of these detailed finite pro-etale equalities. The parent proof remains explicitly agent-originated.

Assembly Step 1 uses the new composite-transpose statement with `M=T_m`, `K=A_Y`, `theta=gamma_m`: its conclusion is exactly `I_m Rp_!(b) alpha^-1`, and its first assertions give naturality and the line unit normalization needed for the rank-one case. I opened `def-pur-affine-space-comparison`: its recursion uses the conjugate of the same `alpha`, with identity at rank zero and the canonical Tate identification. Thus this citation supplies the equality between `Theta` and the ordered next comparison, not an unproved purity isomorphism. The derived statement of the first new node asserts exceptional admissibility and etale-origin domains, so this assembly has not hidden the exceptional preservation argument or introduced a new hypothesis.

Assembly Step 2 uses the new evaluation statement: I checked that its `P=X_m times_Y X_1`, `q`, `r`, `T`, `U`, `V` and `W` identify respectively with this item's `X_(m+1)`, `q_m`, last coordinate, `T_1`, `U`, `V_m` and `T_(m+1)`. The unchanged parent assumes `V_m,U` bounded constructible of finite Tor amplitude. The base change `p_m` is separated finite type over `k`, and so is one of the allowed changes of base in the actual trace hypothesis. The conclusion and the typed `C,D` definitions are in the cited statement and are quoted verbatim in `citations.json`. Nothing is obtained from a cited proof.

Assembly Step 3 uses the new last-factor product statement: it has exactly the three bounded finite-Tor objects assumed in the parent and exactly the supplied isomorphism `kappa`. Its displayed equality is the four-arrow `D` of Step 2, in the same order with the same two symmetries. The source is `V_(m+1)` and the target is `V_m tensor U`. Substitution and the tensor unitor's naturality give the parent's final formula. This last categorical manipulation is elementary and explicitly written; the step is still marked non-elementary because the product comparison it cites is not elementary.

I also reopened all statements used in the old six steps. In particular: finite PF explicitly includes witnessed pro-etale realizations and naturality; comparison Tor amplitude reflects the bound to the etale representatives; finite CBC is for bounded-below etale-origin inputs; the exceptional preservation theorem is for the constructible functor and finite coefficients; the proper projection-mate lemma explicitly asserts the tensor-unit component is the identity. Finite forward-product symmetry asserts equality of the actual composites, not merely an isomorphism of objects; its extra tensor-domain hypothesis is retained explicitly in the third new statement and must be proved there. The explicit construction inside the *statement* of relative Kunneth is used, without applying its abstract-datum theorem under absent hypotheses. These observations check C1, C3 and C4 at the interfaces and preserve the old arguments as proof tasks rather than burying them in the assembly.

I checked B1--B10 and C1--C8 with the new statements open: all objects are introduced independently, all formulas use ordinary TeX escaping, references for every notion are in `stmt_deps`, each new node has empty proof fields and real logged searches, and no new node refers to its parent as a dependency. The blueprint provenance points through the parent, but is not a proof edge. The parent uses only same-unit obligations and its ordered definition, so no new off-unit tool-use approval is requested. When the three children are split, their generic tool uses are the listed obligations from the old proof, not a change of unit route.

Small cases: for `m=1`, the product argument is a two-line product and keeps both symmetries; no unjustified coordinate-invariance assertion is made. At `p=id`, the first new node's formula reduces to the line transpose with identity compact-support comparison, and at `theta=id` it is the defining line evaluation. For `M=0` or empty `X` all maps in the evaluation node have zero source, so the equations are valid; empty `Y` also gives zero objects. For `f=id`, evaluation specializes to the line's two-symmetry PF and tensor-unit law. At the point base and finite field coefficients, each shifted Tate line has even shift and the product type is correct; no sign is silently removed for an arbitrary shifted `M`, since the second node retains the specified symmetries. The new nodes require only finite stages and never presume a global ambient adjunction or the disputed unrestricted ambient preservation.

The precise correction requested by the return is therefore three real proof obligations with all six original arguments assigned, and a short typed assembly. No statement dispute was found and no statement was weakened. This is my own direct-delivery review; the maintainer still independently reviews the resulting delivery.

## What remains unfinished

The three new nodes are intentionally unproved, each with status `unsplit`, as the return requires. All of their arguments are preserved below for their future workers. No Lean was written or compiled. The parent assembly is complete relative to their statements. Delivery validation is recorded after the required server dry run.

## Verbatim returned proof, with new-node ownership

### Returned Step 1

Fix $m\geq1$. Write $p=p_m:X_m\to Y$, $q=q_m:X_{m+1}\to X_m$ and $r:X_{m+1}\to X_1$ for the first-$m$ and last-coordinate projections, respectively. Thus $pq=ar=p_{m+1}$ and $q$ is the base change of $a$ along $p$. The ordered definition [def-pur-affine-space-comparison] supplies these identifications and the twist identification $T_{m+1}=q^*T_m\otimes^L r^*T$. All sources and bases are separated finite type. Each $T_j$ is bounded constructible of finite Tor amplitude: by [prop-weil-twist-preserves] its unshifted twist is locally free of rank one; shifting by $2j$ shifts its Tor interval. The assumption supplies this property for $V_j$, including $U=V_1$. Bounded constructible inputs have etale representatives by [lem-sf-proetale-constructible-origin]; [lem-sf-comparison-tor-amplitude] gives the finite-Tor property of those representatives. Consequently [lem-weil-finite-compact-projection-formula] applies to the four pairs $(q,r^*T,T_m)$, $(p,T_m,U)$, $(r,q^*T_m,T)$ and $(a,T,V_m)$. The exchanges for the two product squares are isomorphisms by [thm-cbc-finite-level-proetale]. The intermediate exceptional input $Rp^!A_Y$ of the ordered recursion is in $D^b_{ctf}$ by [thm-sf-preservation-class](2). Only the constructible adjunction already specified in the ordered definition is used.

Cited nodes: def-pur-affine-space-comparison, prop-weil-twist-preserves, lem-sf-proetale-constructible-origin, lem-sf-comparison-tor-amplitude, lem-weil-finite-compact-projection-formula, thm-cbc-finite-level-proetale, thm-sf-preservation-class.

### Returned Step 2

For any affine-line projection $u:L\to B$, put $F_uK=u^*K\otimes^L A_L(1)[2]$ and write $b_{u,K}:Ru_!F_uK\to K$ for the defining transpose in [def-pur-affine-line-purity-comparison]. That definition gives $b_{u,K}=\rho_K(1_K\otimes t_B)\Pi^u_K$, where $\rho$ is the tensor-unit map and $\Pi^u_K$ is precisely its two-symmetry inverse projection formula. It is natural in $K$, by the naturality in [lem-weil-finite-compact-projection-formula]. At $K=A_B$ the projection transformation is the tensor-unit identification: the proper factor has this normalization by [lem-weil-pbc-ringed-projection-mate-exact], while the open tensor comparison in [def-exchange-projection] sends $x\otimes1$ to $x\otimes1$ and is the identity after the unit identifications. The two symmetries in $\Pi^u_{A_B}$ are also unit identifications. Hence $b_{u,A_B}=t_B$. The rank-one case of the recursion [def-pur-affine-space-comparison] is the specified line comparison (the rank-zero map and the composition with the identity are identities). The inverse Hom bijection takes that comparison back to $b_{a,A_Y}$. Therefore $I_1=t_Y$.

Cited nodes: def-pur-affine-line-purity-comparison, lem-weil-finite-compact-projection-formula, lem-weil-pbc-ringed-projection-mate-exact, def-exchange-projection, def-pur-affine-space-comparison.

### Returned Step 3

Compute the actual transpose at the next stage. Abbreviate $\gamma_m=\gamma_{p,A_Y}:T_m\to Rp^!A_Y$ and $\alpha=\alpha_{p,q}:Rp_!Rq_!\xrightarrow{\sim}R(pq)_!$. By [def-pur-affine-space-comparison], $\gamma_{m+1}$ is $c_{p,q}^{-1}\gamma_{q,Rp^!A_Y}F_q(\gamma_m)$ after the fixed twist identification. Its transpose, written on $Rp_!Rq_!F_qT_m$, is
$$\varepsilon_{p,A_Y}\,Rp_!\bigl(\varepsilon_{q,Rp^!A_Y}\,Rq_!(\gamma_{q,Rp^!A_Y})\,Rq_!F_q(\gamma_m)\bigr).$$
This is the counit formula of [def-weil-pbc-composite-adjunction]; [lem-weil-pbc-mate-pasting](2),(3) applies because $c_{p,q}$ was defined as the conjugate of this same $\alpha$. The inner counit and comparison give $b_{q,Rp^!A_Y}$. Naturality of $b_q$ (Step 2), applied to the map $\gamma_m$, gives
$$b_{q,Rp^!A_Y}\,Rq_!F_q(\gamma_m)=\gamma_m\,b_{q,T_m}.$$
Substitution and $I_m=\varepsilon_{p,A_Y}Rp_!(\gamma_m)$ yield the typed identity
$$I_{m+1}=I_m\,Rp_!(b_{q,T_m})\,\alpha^{-1}:V_{m+1}\longrightarrow A_Y.$$
Here $b_{q,T_m}$ has source $Rq_!T_{m+1}$ and target $T_m$; in particular no nonexistent untwisted line trace is being substituted.

Cited nodes: def-pur-affine-space-comparison, def-weil-pbc-composite-adjunction, lem-weil-pbc-mate-pasting, def-pur-affine-line-purity-comparison.

### Returned Step 4

Let $E:p^*U\xrightarrow{\sim}Rq_!r^*T$ be the canonical compact-support exchange for the base change of $a$ by $p$. The hypothesis on the specified line integrations says $p^*t_Y=t_{X_m}E$, so $t_{X_m}=p^*t_Y\,E^{-1}$. The canonical line-pullback and tensor identifications of the ordered definition are used throughout. Applying the line-transpose definition at $K=T_m$ gives
$$b_{q,T_m}=\rho_{T_m}(1_{T_m}\otimes p^*t_Y)(1_{T_m}\otimes E^{-1})\Pi^q_{T_m}.$$
Define, only as temporary maps in this proof,
$$C=Rp_!(1_{T_m}\otimes E^{-1})\,Rp_!(\Pi^q_{T_m})\,\alpha^{-1}:
V_{m+1}\longrightarrow Rp_!(T_m\otimes p^*U),$$
$$D=(\operatorname{PF}_{p,T_m,U})^{-1}C:
V_{m+1}\longrightarrow V_m\otimes U.$$
The inverses here are those justified in Step 1. Substituting the displayed expression for $b_{q,T_m}$ in Step 3 gives
$$I_{m+1}=I_m\,Rp_!\bigl(\rho_{T_m}(1_{T_m}\otimes p^*t_Y)\bigr)C.$$
This uses the assumed base-change equality only for $p:X_m\to Y$, which is among its allowed changes of base.

Cited nodes: def-pur-affine-line-purity-comparison, def-pur-affine-space-comparison, def-exchange-projection.

### Returned Step 5

Use naturality of the specified projection transformation [lem-weil-finite-compact-projection-formula] for the coefficient morphism $t_Y:U\to A_Y$. Both coefficients belong to $D^b_{ctf}$, as checked in Step 1. If $P_W=\operatorname{PF}_{p,T_m,W}$, naturality is
$$Rp_!(1_{T_m}\otimes p^*t_Y)\,P_U=P_{A_Y}(1_{V_m}\otimes t_Y).$$
The unit normalization $Rp_!(\rho_{T_m})P_{A_Y}=\rho_{V_m}$ follows exactly as in Step 2 from the proper counit-defined projection map [lem-weil-pbc-ringed-projection-mate-exact] and the open tensor comparison of [def-exchange-projection]. Multiply the naturality equality on the right by $P_U^{-1}C=D$ and insert it into Step 4. The result is
$$I_{m+1}=I_m\,\rho_{V_m}(1_{V_m}\otimes t_Y)D
=\rho_{A_Y}(I_m\otimes t_Y)D.$$
The last equality is just naturality of the tensor unitor and the bifunctor law for tensoring morphisms. It remains to identify this particular $D$ with the product map in the statement.

Cited nodes: lem-weil-finite-compact-projection-formula, lem-weil-pbc-ringed-projection-mate-exact, def-exchange-projection.

### Returned Step 6

Apply [lem-pur-finite-forward-product-symmetry] to $(f,M)=(p,T_m)$ and $(g,N)=(a,T)$. Its bounded-below etale-origin conditions hold: the source $V_m\otimes U$ is isomorphic to the assumed bounded constructible $V_{m+1}$ by the specified $\kappa_{m,1}$; every tensor inside a compact-support functor is a bounded etale-origin complex tensored with a shifted Tate line, hence is bounded and of etale origin by [prop-weil-twist-preserves] and [lem-sf-proetale-constructible-origin]. Exchanges identify $Rq_!r^*T$ with $p^*U$ and $Rr_!q^*T_m$ with $a^*V_m$. The canonical tensor comparisons [lem-pur-derived-pullback-tensor-iso] give the identifications in both forward composites. Every arrow of those composites is invertible by Step 1 and the composition comparisons [thm-sf-comp-composition]. Inverting their symmetry equality identifies their inverse products.
For $(p,a)$ that inverse is exactly the map $\kappa_{m,1}$ specified in [thm-sf-kunneth-relative]: only its displayed construction is being used, not its abstract-datum theorem. For $(a,p)$, restore the original external tensor order and the target order $V_m\otimes U$. Expanding the inverse composite then gives, in order, $\alpha^{-1}$, $Rp_!(\Pi^q_{T_m})$, $Rp_!(1_{T_m}\otimes E^{-1})$ and $P_U^{-1}$. This is $D$ from Step 4; the two symmetries in $\Pi$ are precisely the source and target symmetries in that expansion. Thus $D=\kappa_{m,1}$. Step 5 yields $I_{m+1}=(I_m\otimes t_Y)\kappa_{m,1}$ with the tensor-unit identification understood. Together with Step 2 this proves both assertions for every $m\geq1$. No coordinate-permutation invariance has been invoked.

Cited nodes: lem-pur-finite-forward-product-symmetry, prop-weil-twist-preserves, lem-sf-proetale-constructible-origin, lem-pur-derived-pullback-tensor-iso, thm-sf-comp-composition, thm-sf-kunneth-relative.
