# Q156 stage-1 repair report

## Files written

- `dag/nodes/sec-six-functors/lem-pur-weil-semilinear-exchange-reindexing.json`: existing statement preserved verbatim, now a five-step assembly (2170 characters).
- `dag/nodes/sec-six-functors/lem-pur-isomorphism-finite-mate-normalization.json`: statement, unsplit, no Mathlib match; owns old steps 1–5, 3184 characters of the original argument.
- `dag/nodes/sec-six-functors/lem-pur-isomorphism-finite-exchange-coherence.json`: statement, unsplit, no Mathlib match; owns old steps 6–8, 2882 characters of the original argument.
- `dag/nodes/sec-six-functors/lem-pur-isomorphism-completed-reduction-reindexing.json`: statement, unsplit, no Mathlib match; owns old steps 9–11, 2216 characters of the original argument.
- `dag/nodes/sec-six-functors/lem-pur-isomorphism-strict-integral-exchange-normalization.json`: statement, unsplit, no Mathlib match; owns old steps 12–14, 2489 characters of the original argument.
- `dag/nodes/sec-six-functors/lem-pur-isomorphism-exchange-scalar-refinement-descent.json`: statement, unsplit, no Mathlib match; owns old steps 15–16, 1807 characters of the original argument.
- `citations.json`: one verbatim statement quote for every citation in the five assembly steps.
- `searches.jsonl` and per-node `.search-results.json`: executed searches and their returned results, retained for reuse.
- `original-reviewed-node.json`: exact read-only snapshot of the prior reviewed item for lossless argument recovery; this is supporting sandbox material, not a new DAG node.

## Attachments

None. The whole project source was searched for the blueprint tag and for pro-etale reindexing, semilinear exchange, completed exchange and compactification exchange. The generic finite exchange and compactification-comparison declarations cover constituent operations, not the complete item. In particular `AlgebraicGeometry.ProEtale.completedRightDerivedLowerShriekOfCompactificationBaseChangeMap` in `WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/Derived/CompletedExchange.lean:284` uses a completed target and constant-ring coordinates. Its docstring explicitly distinguishes that target from the blanket extension-by-zero completeness assertion. It is not an attachment for this node's completed-ring, specified-strict-lift statement. No claim is made that the two coefficient categories are definitionally the same.

## Wanted literature

None. The source used for the extraction is already present. The existing proof is explicitly agent-written; the tiny blueprint assembly paragraph is not represented as a detailed human proof.

## What was wrong and what changed

The return requires distribution of work, not shorter prose. The reviewed proof had 12,578 characters in 16 steps. There were no retained node files, report or search log in the sandbox at the start, only the brief marker files. I copied the current read repository item and preserved its statement, citations, source, blueprint ancestry and previous reviewed argument. Five separate statements now expose the five argument blocks; every new node has status `unsplit`, empty `proof` and empty `proof_deps`. The parent is a short assembly. No old argument is discarded: the complete text and original cited nodes are reproduced below under their destination nodes. The new nodes do not cite the parent, so the extraction introduces no cycle.

The extraction deliberately keeps map normalizations, quotient transitions, completion units, proper/open compositors and finite-Tor/witness restrictions. The finite and integral comparisons are separate arguments; the scalar/refinement node is a conditional transfer statement whose finite and integral hypotheses are supplied by the preceding assembly steps. None of the new nodes restates the whole item. The smallest allocated argument has 1,807 characters and the largest 3,184; there is no one dominant child carrying the whole proof.

The source-to-Lean difference about a completed compact-support target is reported above; I do not silently change the target or identify completed coefficient modules with constant non-torsion modules. The extraction retains exactly the supplied domains of the existing item. In the integral normalization child, completeness and the intermediate objects are explicitly those required by `def-cbc-completed-exchange-map`, not a new assertion that ordinary extension by zero preserves every complete object on every pro-etale site.

## Unfinished work

The proofs of the five newly exposed statements are intentionally left to separate stage-1 workers, as the return directs. Their complete inherited argument and citation list are below. No Lean was written and no compiler, Lake or build tool was run.

## Sources and searches

For the item and each new node I read `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-pur-weil-equivariance-compatibilities.proof.md`, its current DAG ancestor, the unit `sk-thm-sf-package` and chapter `sec-six-functors`, and the prior 16-step reviewed extraction. For the derived-limit background I also read Stacks Tag 0A07, `sites-cohomology.tex`, label `lemma-Rf-commutes-with-Rlim` (the ringed-topos derived-limit commutation argument), and Tag 099N, `proetale.tex`, label `lemma-pushforward-Noetherian-case` (constant-coefficient derived completion and completed pullback). These supply background to the existing nodes, not an identification of the constant and completed ambient module categories. The blueprint proof contains the constituent-compatibility assembly sentence; the refinements below are agent-extracted arguments, with that limitation made explicit in each source place. No source route is replaced. In particular no prohibited SGA route is used.

I searched the whole imported blueprint with `tools/blueprint_refs.py search` for `reindexing`, `strict reduction`, `semilinear`, `exchange normalization`, `scalar compactification`, `proper mate`, `coefficient transport`, `completed pullback` and `refinement comparison`. DAG statement searches included reindexing with exchange/completed/compact-support terminology, then the potentially overlapping nodes listed below. The exact new ids are fresh in the read repository. The common blueprint ancestor printed by the ancestor tool is `prop-pur-weil-equivariance-compatibilities`; each new node records this ancestor and the parent in `via`.

For every new statement, I ran LeanFinder, LeanSearch, Loogle and the required msearch grep, then a second semantic phrasing. All actual query strings and hits are in the node records and search log. Three LeanSearch queries returned a rate-limit error and are recorded as `unavailable`. Two Loogle names for the scalar/refinement node were not accepted as identifiers: those queries are recorded as invalid, and the successful quoted-substring query `"localization"` is recorded separately. No invalid or unavailable query is used as evidence of mathematical absence. All five nodes have successful semantic, Loogle and grep searches. The hits include generic mates, derived-adjunction units/counits, module pushforward comparisons, affine-space reindexing, ordinary injective resolutions and Ore localization. They do not give these full specified maps by one-line specialization. I read the generic mate correspondence in `Mathlib/CategoryTheory/Adjunction/Mates.lean:84`, the sheaf pushforward comparison in `Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean:228`, and the site pushforward comparison in `Mathlib/CategoryTheory/Sites/Continuous.lean:402`. These are useful infrastructure, already represented by existing DAG constituent nodes, rather than Mathlib matches for the five children.

## Not duplicates

- lem-pur-isomorphism-finite-mate-normalization vs lem-weil-proetale-isomorphism-inverse-image: the existing node gives equivalence and section reindexing of inverse image; the new node identifies the specified derived proper mate and the open-adjunction-normalized compact-support factors.
- lem-pur-isomorphism-finite-mate-normalization vs lem-cbc-proetale-extension-zero-base-change: the existing node asserts the finite open comparison; the new node identifies its reindexing normalization and the proper derived mate, not only invertibility of the open factor.
- lem-pur-isomorphism-finite-exchange-coherence vs lem-weil-pbc-mate-pasting: the existing node is abstract mate pasting; the new node contains the compact-support proper/open vertical-interchange equation and finite quotient-coefficient square.
- lem-pur-isomorphism-finite-exchange-coherence vs lem-cbc-complete-proetale-composition-pasting-coherence: the existing node supplies the strict constant-tower compositor and refinement equation; the new node combines the actual finite semilinear exchanges with identity/horizontal pasting and finite quotient-coefficient compatibility.
- lem-pur-isomorphism-finite-exchange-coherence vs fix-lem-exchanges: the existing theorem assumes a square of k-morphisms; the new node handles underlying-scheme isomorphisms without k-linearity, on explicit finite domains.
- lem-pur-isomorphism-completed-reduction-reindexing vs lem-pod-canonical-coefficient-pullback-reduction: the existing node concerns the coefficient object and its specified cone projections; the new node concerns every complete complex, arbitrary strict towers, the derived-limit comparison and diagram-site direct-image mates.
- lem-pur-isomorphism-completed-reduction-reindexing vs lem-pod-integral-pullback-system-comparison: the existing node is comparison to coherent coefficient systems, with constructibility hypotheses; the new node is exact equivalence and projection-normalized reindexing on completed-ring modules and strict towers, including arbitrary tower derived limits and direct-image mate normalization.
- lem-pur-isomorphism-completed-reduction-reindexing vs lem-weil-proetale-isomorphism-inverse-image: the existing node concerns sheaves and constant-ring modules; the new node includes completed-ring module and ringed-diagram categories, derived limits and the specified completion unit.
- lem-pur-isomorphism-strict-integral-exchange-normalization vs def-cbc-completed-exchange-map: the existing node defines the projection-conjugated strict lift; the new node proves its equality with reindexing as a derived strict-tower morphism, then identifies the reconstructed proper and open factors and their coherence.
- lem-pur-isomorphism-strict-integral-exchange-normalization vs lem-cbc-strict-tower-proper-open-calculus: the existing node concerns constant-ring strict towers and normalized proper/open maps; the new node identifies the actual completed-ring reduction lift H-prime R(e) H-inverse with reindexing and reconstructs the completed exchange.
- lem-pur-isomorphism-exchange-scalar-refinement-descent vs lem-pod-isomorphism-scalar-comparison-agreement: the existing node compares two specified scalar/pullback isomorphisms; the new node concerns compact-support exchanges, coefficient-category transport and canonical refinement descent.
- lem-pur-isomorphism-exchange-scalar-refinement-descent vs lem-coef-frobenius-exchange-equivalence: the existing node asserts invertibility for the Frobenius square at rational coefficients; the new node transports normalized identities and descends through refinements for any underlying-scheme isomorphism.
- lem-pur-isomorphism-exchange-scalar-refinement-descent vs lem-sf-integral-compactification-comparison-bridge: the existing node compares two integral composition normalizations; the new node is the semilinear base-change/refinement compatibility and scalar/common-stage descent of already normalized exchanges.
- lem-pur-isomorphism-exchange-scalar-refinement-descent vs fix-lem-exchanges: only the already supplied compactification/composition comparisons from clause (4) are used; its base-change/pasting theorem for k-linear arrows does not imply the semilinear descent assertion.

## Review by Q156

I checked the repair against B–E with the statements and the source open. The five new statements introduce their schemes, coefficient rings, strict categories, maps and domains themselves. Their statements contain conclusions and map characterizations, not proof sketches; their proof fields are empty. Every bracketed notion has the corresponding existing statement/definition dependency. Finite constructible finite-Tor domains are retained for quotient extension; etale-origin and bounded-below requirements are retained when a compact-support composition comparison is declared invertible. The integral node requires the actual completed objects and intermediates of the defining domain. The scalar node does not introduce reduction of rational coefficients. Equalities of strict maps are asserted in the derived strict-tower category, not inferred from faithful evaluations. All identifications between derived objects are isomorphisms of derived objects, never only per-degree consequences.

For parent Step 1 I read the full statement of `lem-pur-isomorphism-finite-mate-normalization`: it states the precise proper mate transpose, the open-unit normalization and their ordered compact-support composite. These give the finite displayed identity on exactly the parent's finite domain. For Step 2 I read `lem-pur-isomorphism-finite-exchange-coherence`: its three equations give identity, horizontal and vertical pasting and its final paragraph gives quotient extension with finite-Tor restrictions. For Step 3 I read `lem-pur-isomorphism-completed-reduction-reindexing`: it states the completed-ring equivalence, projection-induced derived-limit comparison, actual completion-unit identification, strict reduction transitions, and diagram-site mate reindexing needed next. For Step 4 I read `lem-pur-isomorphism-strict-integral-exchange-normalization`: it gives the equality of the specified strict lift to reindexing before taking the limit, the exact three-factor reconstructed map and open factor, and the strict coherence and reduction squares. For Step 5 I read `lem-pur-isomorphism-exchange-scalar-refinement-descent`: its hypotheses are supplied by Steps 1–4, and its conclusions are the scalar, common-stage and canonical refinement/composition comparisons that the parent takes. `citations.json` contains exact verbatim quotes of these statements, so none of the assembly steps relies on a child's unwritten proof.

For the inherited argument I also opened the existing cited statements, particularly the normalized proper/open calculus, completed-exchange definition, projection/exchange tensor coherence, direct-image/limit comparison, quotient-tower reconstruction, operation/reduction compatibility and compactification-composition coherence. The important distinction is that the completed-exchange definition specifies H and H-prime and v, while the new integral node must prove their normalization; the definition itself is not cited for that conclusion. The old uses and full text below remain available so the workers assigned those new statements have not lost the section/transposition calculation, K-injective argument, tensor calculation, strict transition calculation or limit reconstruction.

Small cases were checked for each new statement. For the finite normalization node, g=identity gives the mate of the identity square, j=identity removes the open factor, and the empty open/zero input gives the unique zero comparison. For finite coherence, h=identity and identity compactification towers reduce the pasting equations to unitors; n=m makes coefficient comparison the identity and does not create a false invertibility claim for arbitrary direct image. For completed reindexing, u=identity and K=0 respect the actual quotient-projection unit; the tensor transition formula gives the same image for consecutive quotients and their composites. For strict integral normalization, H and H-prime have exactly the source/target in the definition, so r H and H-prime R(e) are maps with the same source and target; multiplying by H-inverse has the stated direction. Taking j=identity or K=0 checks the factor order. For scalar/refinement descent, identity field extensions and identity refinements give identities, the displayed refinement equation has source G_g F_(c2) and target F_(c1-prime) G_(g-prime), and common refinements and field composita retain the prescribed cocycles. No new mathematical counterexample to this item's supplied-domain statement was found. The changed completed-target Lean declaration is explicitly reported above instead of used to justify an attachment.

The five parent steps are all shorter than 2,000 characters; their combined length is below 3,000. The earlier long proof is fully allocated below rather than compressed into a child that restates the entire item. The new arguments are substantive combinations of the existing constituent facts and their actual map normalizations, not newly minted elementary consequences. The same-tag gate adds no pairs because the new source fields point to the blueprint extraction, not fresh Stacks-tag claims; the meaningful nearby pairs have nevertheless been compared above. All five new nodes can be claimed independently since their statement dependencies only name pre-existing notions/maps and none cites the parent or a sibling. This review is my own self-check as author, not a second-reader review.

## Preserved argument and exact allocation

The following is the complete previous reviewed argument, verbatim, including all 16 step texts. The source for every old step is the blueprint file cited above; each original `source.place` is also retained. This is report material for future workers; no proof has been smuggled into any statement-only node.

### lem-pur-isomorphism-finite-mate-normalization

Original step 1 (577 characters; elementary=false):

Work over $S=Y$: the structure maps are $f:X\to Y$ and $g:Y'\to Y$. Both are separated finite type, and $\ell$ is invertible on $Y$. Thus the formulas of [def-exchange-projection] apply without making $g$ a $k$-morphism. Put $G_T=u^{-1}$ for each of the isomorphisms $u=g,g',\bar g$. By [lem-weil-proetale-isomorphism-inverse-image], these functors relabel site objects, are exact equivalences, and carry the constant coefficient ring to the same constant ring. Therefore their module pullbacks are precisely $G_T$, including on complexes by [def-weil-pbc-proetale-operations].

Original cited nodes: `def-exchange-projection`, `lem-weil-proetale-isomorphism-inverse-image`, `def-weil-pbc-proetale-operations`.

Original source place: Constituent compact-support compatibility in the assembly paragraph; setup of semilinear reindexing over the target scheme.

Original step 2 (788 characters; elementary=true):

First compare underived direct images. For a sheaf $F$ on $\overline X$ and an object $V\to Y'$ of its small pro-etale site, [def-weil-proetale-inverse-image] gives
$$(g^{-1}p_*F)(V)=F(\overline X\times_Y V),\qquad (p'_*\bar g^{-1}F)(V)=F(\overline X'\times_{Y'}V\to\overline X).$$
The canonical fibre-product identification identifies these two section modules and their restriction maps. Denote the resulting natural isomorphism by $r_F$. Its transpose under $p'^*\dashv p'_*$ is $\bar g^{-1}\varepsilon_p\circ\theta_{p_*F}$: both maps take a section on $\overline X\times_Y V$ to its restriction along the same map into that fibre product. The mate characterization of [def-weil-pbc-adjunction-mate] therefore identifies $r$ with the specified underived unit--square--counit composite.

Original cited nodes: `def-weil-proetale-inverse-image`, `lem-weil-proetale-isomorphism-inverse-image`, `def-weil-pbc-adjunction-mate`.

Original source place: Constituent compact-support compatibility in the assembly paragraph; section formula and transpose of the proper factor.

Original step 3 (790 characters; elementary=false):

Take a K-injective representative $F\to I$. The equivalence $\bar g^{-1}$ preserves K-injectives: it is a right adjoint to its exact inverse equivalence, so [lem-weil-pbc-right-adjoint-preserves-kinjective] applies. Thus $g^{-1}p_*I$ and $p'_*\bar g^{-1}I$ compute the two derived direct images. Step 2 applied to $I$ defines their reindexing isomorphism $r_F:g^{-1}Rp_*F\simeq Rp'_*\bar g^{-1}F$. The fraction characterization of the canonical derived adjunction in [lem-pc-pre-derived-adjoint-functors-general] carries its underived transpose to $\bar g^{-1}\varepsilon_p\circ\theta_{Rp_*F}$. Hence, by the mate characterization in [def-weil-pbc-adjunction-mate], this $r_F$ is exactly $\operatorname{Ex}_{*,p}(F)$ of [def-exchange-projection], with its specified derived unit and counit.

Original cited nodes: `lem-weil-pbc-right-adjoint-preserves-kinjective`, `lem-pc-pre-derived-adjoint-functors-general`, `def-weil-pbc-adjunction-mate`, `def-exchange-projection`.

Original source place: Constituent compact-support compatibility in the assembly paragraph; derive the section comparison with the actual adjunction normalization.

Original step 4 (686 characters; elementary=false):

For the open factor use the canonical isomorphism $\beta:\bar g^{-1}j_!\simeq j'_!g'^{-1}$ of [lem-cbc-proetale-extension-zero-base-change]. Its reindexing normalization is fixed by the open adjunction: its inverse is the transpose of $g'^{-1}K\to g'^{-1}j^{-1}j_!K\cong j'^{-1}\bar g^{-1}j_!K$. This is explicitly the normalization of $\beta$ in [lem-cbc-strict-tower-proper-open-calculus]; applying it to constant towers and evaluating gives the finite comparison. Relabeling an open slice preserves this unit map, so the reindexing identification of the two left adjoints has precisely this transpose. Uniqueness under the open adjunction identifies that reindexing map with $\beta$.

Original cited nodes: `lem-cbc-proetale-extension-zero-base-change`, `lem-cbc-strict-tower-proper-open-calculus`.

Original source place: Constituent compact-support compatibility in the assembly paragraph; normalize open extension by zero.

Original step 5 (343 characters; elementary=true):

By definition, $\operatorname{Ex}_!^c=Rp'_*(\beta)\circ\operatorname{Ex}_{*,p}(j_!-)$. Substituting Steps 3 and 4 gives exactly the two displayed factors in the statement. Each is invertible and natural in the input, so their ordered composite is the claimed natural isomorphism. This identifies the proper factor itself as the specified mate.

Original cited nodes: `def-exchange-projection`.

Original source place: Constituent compact-support compatibility in the assembly paragraph; multiply the two identified factors.

### lem-pur-isomorphism-finite-exchange-coherence

Original step 6 (638 characters; elementary=false):

For identity and successive isomorphisms, the pullback square maps are identity and pasted relabelings, respectively. Clauses (4) and (1) of [lem-weil-pbc-mate-pasting] identify their direct-image mates with identity and horizontal composite. The open comparisons satisfy the identical identity and successive-base-change equations by [lem-cbc-strict-tower-proper-open-calculus]. Inserting these equations into $Rp'_*(\beta)r$ gives
$$e_{gh}=(e_h\,g'^{-1})\circ(h^{-1}e_g),\qquad e_1=1,$$
with the canonical pullback and direct-image compositors. These equations concern the named transformations, since Steps 3--5 identified each factor.

Original cited nodes: `lem-weil-pbc-mate-pasting`, `lem-cbc-strict-tower-proper-open-calculus`.

Original source place: Constituent compact-support compatibility in the assembly paragraph; identity and horizontal isomorphism-pasting.

Original step 7 (1100 characters; elementary=false):

To check vertical composition, expand the compact-support comparison on a compatible compactification tower as a proper/open interchange followed by direct-image and open-extension compositors. The interchange in [lem-cbc-strict-tower-proper-open-calculus] is the mate of its explicitly specified pullback/open map $\alpha_Q$; its base-change equation applies to any scheme base change, including the present isomorphism. The direct-image pieces paste by clause (2) of [lem-weil-pbc-mate-pasting], and the open pieces by the open-composition clause of the same proper/open calculus. Consequently the expanded composite satisfies
$$e_{hf}(G_ZD)=(D'G_X)(F_h'e_f)(e_hF_f),$$
where $F$ denotes the chosen compact-support composites and $D:F_hF_f\to F_{hf}$ is the tower composition comparison. The equality holds for the constituent maps even before restricting to inputs on which $D$ is invertible. On witnessed inputs this is exactly the comparison and equation of [lem-cbc-complete-proetale-composition-pasting-coherence]. Finite-level equalities follow by using constant strict towers and evaluation.

Original cited nodes: `lem-cbc-strict-tower-proper-open-calculus`, `lem-weil-pbc-mate-pasting`, `lem-cbc-complete-proetale-composition-pasting-coherence`.

Original source place: Constituent compact-support compatibility in the assembly paragraph; proper/open interchange in vertical compact-support composition.

Original step 8 (1144 characters; elementary=false):

For a finite quotient $A_{E,n}\to A_{E,m}$, the pullback and compact-support coefficient comparisons on finite constructible finite-Tor inputs are supplied by [lem-fix-operation-reduction]. For the proper factor, use the canonical projection-formula comparison with the coefficient object $B=A_{E,m}$; it need not separately be invertible. Apply [lem-weil-pbc-ringed-exchange-tensor-coherence] with $Q=B$: its two equal composites say exactly that the proper mate commutes with this tensor-coefficient comparison. Pullback identifies the constant sheaf $B$ with the same $B$ by reindexing; on a flat tensor representative both orders send $x\otimes b$ to the same relabeled section tensored with $b$. For the open factor, the comparison is characterized by its open unit as in Step 4, which coefficient extension preserves by [lem-fix-operation-reduction]. The composite of these proper and open coefficient comparisons is the compact-support comparison in that lemma. Composing the two commuting squares proves the finite quotient assertion, without assuming finite quotient extension commutes invertibly with arbitrary ordinary direct images.

Original cited nodes: `lem-fix-operation-reduction`, `lem-weil-pbc-ringed-exchange-tensor-coherence`, `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.

Original source place: Constituent compact-support compatibility in the assembly paragraph; finite quotient-coefficient extension, with the finite-Tor hypothesis retained.

### lem-pur-isomorphism-completed-reduction-reindexing

Original step 9 (673 characters; elementary=false):

At the integral stage put $P_n=\mathcal O_E/\varpi_E^n$ and $A_T=\varprojlim_n(P_n)_T$. The coefficient identifications of [lem-weil-pbc-profinite-coefficient-inverse-image] identify $g^{-1}A_Y$ with $A_{Y'}$, respecting every quotient projection and transition. Relabeling therefore defines an exact equivalence also on these completed-ring module categories and on their strict diagram categories: the inverse is the reverse relabeling with the inverse ring identification. Applying both equivalences termwise preserves quasi-isomorphisms, giving the derived equivalences. The same section and K-injective argument of Steps 2--3 applies to these ringed and diagram sites.

Original cited nodes: `lem-weil-proetale-isomorphism-inverse-image`, `lem-weil-pbc-profinite-coefficient-inverse-image`, `lem-sf-exact-functor-derived-triangulated`, `lem-weil-pbc-right-adjoint-preserves-kinjective`.

Original source place: Constituent compact-support compatibility in the assembly paragraph; completed coefficient rings and diagram-site reindexing.

Original step 10 (762 characters; elementary=false):

These exact equivalences commute canonically with $R\lim$ on strict towers. Indeed they commute with ordinary limits and preserve K-injective towers by the exact-inverse argument of Step 3; applying the definition of $R\lim$ on a K-injective tower gives the comparison, induced by its projections. For complete $K$, [prop-weil-pbc-koszul-reconstruction] identifies the canonical quotient-tower map $K\to R\lim K_\bullet$ as an isomorphism. Hence
$$Lg^*_{\mathrm{comp}}K=R\lim(g^{-1}K_\bullet)\cong g^{-1}R\lim K_\bullet\cong g^{-1}K.$$
By [def-weil-pbc-completed-pullback], its comparison from ordinary pullback is exactly the map induced by those quotient projections. Thus this identifies completed pullback with reindexing using the specified completion unit.

Original cited nodes: `lem-weil-proetale-isomorphism-inverse-image`, `lem-weil-pbc-right-adjoint-preserves-kinjective`, `lem-weil-pbc-ringed-strict-tower-homotopy-limit`, `prop-weil-pbc-koszul-reconstruction`, `def-weil-pbc-completed-pullback`.

Original source place: Constituent compact-support compatibility in the assembly paragraph; completed pullback, including its canonical unit.

Original step 11 (781 characters; elementary=false):

Use the strict notation of [def-cbc-completed-exchange-map]: $\mathcal R_T(F)=\Delta F\otimes^LQ_{T,\bullet}$ and $v_\bullet=H'\mathcal R_{Y'}(e_M)H^{-1}$. The reduction/relabeling comparison $t_{g,F}$ is a map on diagram sites, not merely on evaluations. On a flat tensor representative its component sends a relabeled $x\otimes a$ to that same $x\otimes a$. For a transition $P_{n+1}\to P_n$, both composites send it to $x\otimes\bar a$. The coefficient identifications of [lem-weil-pbc-profinite-coefficient-inverse-image] ensure this equality respects the completed module actions. Thus $t$ identifies the actual strict reduction diagram with its reindexing; the derived tensor comparison of [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] supplies its derived isomorphism.

Original cited nodes: `def-cbc-completed-exchange-map`, `lem-weil-pbc-profinite-coefficient-inverse-image`, `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.

Original source place: Constituent compact-support compatibility in the assembly paragraph; strict reduction objects and their transition maps.

### lem-pur-isomorphism-strict-integral-exchange-normalization

Original step 12 (842 characters; elementary=false):

Let $r_\bullet:B_\bullet\to D_\bullet$ be direct-image reindexing on the diagram sites of Step 9. Apply [lem-weil-pbc-ringed-exchange-tensor-coherence] on those sites to the coefficient object $Q_{Y,\bullet}$. Its two paths are, in the notation of [def-cbc-completed-exchange-map], exactly $r_\bullet H$ and $H'\mathcal R_{Y'}(e_M)$: $H$ is the projection mate followed by $t_g$, $H'$ is the projection mate followed by $t_{\bar g}$, and Step 9 identifies the exchange mates with reindexing. Therefore
$$r_\bullet H=H'\mathcal R_{Y'}(e_M),\qquad r_\bullet=H'\mathcal R_{Y'}(e_M)H^{-1}=v_\bullet.$$
This is equality in the derived strict-tower category. It does not infer equality from the individual evaluations. The projection comparisons used here are invertible on these reduction diagrams as specified in [def-cbc-completed-exchange-map].

Original cited nodes: `def-cbc-completed-exchange-map`, `lem-weil-pbc-ringed-exchange-tensor-coherence`.

Original source place: Constituent compact-support compatibility in the assembly paragraph; identify the actual specified strict proper exchange before taking the limit.

Original step 13 (787 characters; elementary=false):

Now take $R\lim$ of the equality in Step 12. In [def-cbc-completed-exchange-map] the proper factor is $c_{p',T}^{-1}R\lim(v_\bullet)s$. The direct-image/limit comparison $c_{p',T}$ is the canonical one of [prop-weil-pbc-direct-image-limits], and $s$ uses precisely the quotient-tower pullback comparison of Step 10 and the projection mate of Step 12. Thus these source and target identifications turn this composite into $g^{-1}Rp_*M\simeq Rp'_*\bar g^{-1}M$. The completed open factor is induced by the finite open maps and the strict-tower limit comparison, as [lem-cbc-completed-extension-zero-comparison] specifies. By Steps 4, 10 and 11 it becomes exactly $\bar g^{-1}j_!\simeq j'_!g'^{-1}$. The integral $e$ is consequently the same ordered reindexing composite as at finite level.

Original cited nodes: `def-cbc-completed-exchange-map`, `prop-weil-pbc-direct-image-limits`, `lem-cbc-completed-extension-zero-comparison`.

Original source place: Constituent compact-support compatibility in the assembly paragraph; reconstruct the two integral factors with their specified comparisons.

Original step 14 (860 characters; elementary=false):

All integral coherence equations hold before $R\lim$. For identity and successive isomorphisms use the mate-pasting equations and the strict open equations of [lem-cbc-strict-tower-proper-open-calculus] on the diagram sites of Step 9. For vertical composition use its base-change equation for the normalized proper/open interchange, exactly as in Step 7. For coefficient reduction use the tensor/exchange equation on the quotient diagram of Step 12, and the open-unit equation of Step 4. These are equalities of strict-tower transformations, identified with the chosen integral lift in Step 12. Functorial $R\lim$ and the canonical direct-image/limit comparison of [prop-weil-pbc-direct-image-limits] preserve each equality. This proves identity, horizontal and vertical pasting and reduction compatibility of the integral maps with their strict normalization.

Original cited nodes: `lem-weil-pbc-mate-pasting`, `lem-cbc-strict-tower-proper-open-calculus`, `lem-weil-pbc-ringed-exchange-tensor-coherence`, `prop-weil-pbc-direct-image-limits`, `lem-fix-operation-reduction`.

Original source place: Constituent compact-support compatibility in the assembly paragraph; strict integral coherence, before reconstruction.

### lem-pur-isomorphism-exchange-scalar-refinement-descent

Original step 15 (844 characters; elementary=false):

On the supplied higher-coefficient domains, [def-exchange-projection] specifies that rational maps are scalar localizations of integral maps and common-stage maps are represented over one finite field with coherent scalar comparisons. Applying scalar localization to the equalities of Steps 13--14 preserves compositions, identity maps and isomorphisms. The scalar comparisons in [lem-fix-operation-reduction] preserve the units, counits and tensor comparisons, so coefficient extension carries the same ordered two-factor map to the one over the extended field. By [def-weil-algebraically-closed-coefficients], two such maps represent the same common-stage morphism after passage to a common finite extension. This gives all the rational and algebraically closed comparisons and equations, with no reduction operation on rational coefficients.

Original cited nodes: `def-exchange-projection`, `lem-fix-operation-reduction`, `def-weil-rationalization-karoubi`, `def-weil-algebraically-closed-coefficients`.

Original source place: Constituent compact-support compatibility in the assembly paragraph; scalar localization and common-stage transport.

Original step 16 (963 characters; elementary=false):

Finally, on the compactification-independent domains named in [fix-lem-exchanges], its clause (4) supplies the canonical refinement/compactification and composition comparisons. Their normalized proper/open maps commute with scheme-isomorphism base change by the base-change equation of [lem-cbc-strict-tower-proper-open-calculus]; this applies also to refinement squares, where its $\alpha_Q$ is the clopen-section projection. Hence replacing a compactification conjugates the two-factor identity of Step 5 or 13 by precisely those comparisons. For compositions, use the refinement-invariance and vertical equation of [lem-cbc-complete-proetale-composition-pasting-coherence], then Steps 14--15 at higher stages. The conclusion is the displayed identity with canonical compactification comparisons inserted. Only these supplied comparisons are taken from [fix-lem-exchanges]; its exchange-pasting theorem for $k$-morphisms is never applied to a semilinear arrow.

Original cited nodes: `fix-lem-exchanges`, `lem-cbc-strict-tower-proper-open-calculus`, `lem-cbc-complete-proetale-composition-pasting-coherence`.

Original source place: Constituent compact-support compatibility in the assembly paragraph; insert compactification comparisons on their stated field-base domains.

## Validation

The required server delivery dry run exited successfully: `OK (not pushed) deliver/Q156/lem-pur-weil-semilinear-exchange-reindexing at 565161de530: preflight passed`. It includes the server preflight, DAG and split checks. The final report update is followed by a final dry run before push. A local data audit also verified the exact unchanged statement, all 16 original step texts verbatim in this report, five statement-only children, the 2,170-character assembly, resolved statement dependencies and verbatim citation quotes. No local check_dag, review_split or preflight script was run.
