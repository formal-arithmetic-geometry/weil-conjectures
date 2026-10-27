# Q149 repair: thm-pod-finite-reduction

1. Files written: dag/nodes/sec-six-functors/thm-pod-finite-reduction.json (item, split); dag/nodes/sec-six-functors/lem-sf-pod-smooth-dual-reduction-data.json (statement, unsplit, no Mathlib match); dag/nodes/sec-six-functors/lem-sf-perfect-pairing-reduction-adjoints.json (statement, unsplit, no Mathlib match). citations.json contains exact statement quotes. No new Mathlib leaves.
2. Attachments: none. The project has no declaration tagged thm-pod-finite-reduction. Transport.lean explicitly excludes change of coefficient ring. AdicReconstruction.lean uses reduction as an endofunctor over the original ring, and InvertibleDualizing.lean gives only a formal twist comparison, not the requested pairing square. None states the item exactly.
3. WANTED: none. The blueprint proof and Stacks source needed here are present.
4. The returned split had six steps and about 6918 characters of proof work in one node. This repair leaves its statement literally unchanged and adds two independently actionable, statement-only lemmas of comparable proof workload. The sandbox contained only dispatcher brief markers, not a retained report or node; the current read-only repository supplies the returned six-step head and all its existing search results. Existing item metadata and searches are retained. No repository or launcher files were changed.
5. Nothing mathematical is left outside the delivered statements and assembly. Proofs of the two new lemmas are intentionally deferred to their own stage-1 workers, as the return requests. No compiler, Lake or build command was run.

## Re-split allocation and preserved arguments

The smooth-dual-reduction-data lemma takes returned steps 1 and 2 (1425 + 854 characters) and the evaluation/trace contraction used by step 4. It states the actual reduced local models, finite-Tor and perfectness conclusions, the evaluation-compatible shifted dual comparison and trace-contraction identity. A future worker can use lem-weil-pbc-strict-perfect-ringed-pullback-model for the local-model argument, lem-fix-operation-reduction for Hom/evaluation and compact supports, thm-sf-dual-perfect for the oriented dual, and thm-pur-finite-reduction-of-purity for the normalized trace. These are suggestions, not proof dependencies on the unsplit node.

Returned step 3 is already exactly covered by the existing stronger prop-sf-mixed-cup-coefficient-change: its finite quotient passage includes our A_n to A_m, and its square gives the identity needed. Creating another node would duplicate it. Its unresolved proof task includes the projection transformation, pullback comparison and counit-transpose calculation written below; these details are preserved verbatim for the worker of that node. The parent uses only the square, so no premature invertibility argument is needed. Step 4 stays as the short composition of that cup square with the new contraction square.

The inverse-adjoint-comparison lemma takes the formal content of returned steps 5 and 6 (836 + 1685 characters). It is stated for a strong monoidal functor and a specified evaluation-compatible invertible dual comparison h, rather than tied to schemes. The parent retains the geometric perfectness assertion and the application of the existing Hom/evaluation comparison giving h. The new node must construct ell using the dual of c inverse, verify its evaluation identity, compare both uncurried adjoints after precomposition by c tensor 1, cancel this isomorphism, use injectivity of uncurrying, and take horizontal inverses. Its statement includes every resulting specified-map equality and invertibility of r. This is neither the whole Poincare item nor a restatement of its clause: it has no scheme, trace or cup product and takes a commuting pairing square as input.

The complete returned arguments follow, without shortening or dropping any sentence. They are a handoff record in this report, not proof steps on either new unsplit node.

### Returned step 1

Write $\operatorname{red}_T(-)=(-)\otimes^L_{A_n}A_m$ on $T=X,s$. In the conventions [def-pod-conventions], the input $K_n$ is a site-perfect bounded constructible finite-Tor complex. The reduction functor has target $D^b_{ctf}(T,A_m)$ as stated in [thm-pur-finite-reduction-of-purity]. Moreover $K_m=\operatorname{red}_XK_n$ is site-perfect: on any cover giving the model of [def-weil-site-perfect-complex], tensor the bounded finite-projective model termwise with $A_m$. This computes the derived tensor: finite-projective terms are flat since their tensor functors are retracts of finite sums of the identity, and the bounded-above flat-complex lemma [lem-pc-bounded-above-flat-kflat-site] makes the model K-flat. Each term remains a direct summand of a finite free module, because tensoring the two splitting maps preserves their composite identity. The local condition of [def-weil-site-perfect-complex] at a finite stage is word for word the condition defining perfectness over $\Lambda_X$ in [def-pod-perfect-complex-on-x] (a pro-etale cover on which the complex is quasi-isomorphic to a bounded complex of finite projective modules), and $K_n,K_m$ lie in $D^b_{ctf}$; so $K_n$ and $K_m$ are perfect over $A_{n,X}$ and $A_{m,X}$ respectively, which is the hypothesis of the duality and identification theorems used in steps 2 and 6. Thus the pairing and duality assertions for site-perfect inputs apply at both stages.

Cited statements: def-pod-conventions, thm-pur-finite-reduction-of-purity, def-weil-site-perfect-complex, lem-pc-bounded-above-flat-kflat-site, def-pod-perfect-complex-on-x.

### Returned step 2

Use the coefficient dual and its evaluation of [def-pod-coefficient-dual-on-x]. The site-perfect internal-Hom and evaluation clauses of [lem-fix-operation-reduction] give $\operatorname{red}_X(K_n^\vee)\cong K_m^\vee$, carrying the reduction of $\operatorname{ev}_{K_n}$ to $\operatorname{ev}_{K_m}$. By [thm-sf-dual-perfect], the dual remains perfect and the orientation-induced identification $\mathbb D_XK\cong K^\vee(d)[2d]$ is compatible with reduction, shifts and evaluation. Put $L_i=K_i^\vee(d)[2d]$ for $i=n,m$; its indicated comparison identifies $\operatorname{red}_XL_n$ with $L_m$. The smooth trace is the orientation followed by the exceptional counit, precisely the composite in [def-pur-smooth-trace]. The orientation and trace comparison squares commute by [thm-pur-finite-reduction-of-purity], applied to $a_X$ and the coefficient unit.

Cited statements: def-pod-coefficient-dual-on-x, lem-fix-operation-reduction, thm-sf-dual-perfect, def-pur-smooth-trace, thm-pur-finite-reduction-of-purity.

### Returned step 3

Put $C_i=R\Gamma_c(X,K_i)$ and $D_i=R\Gamma(X,L_i)$. Here $L_i$ is bounded constructible finite-Tor by step 2 and the twist and shift conventions. Applying [thm-pod-point-perfectness] to $L_i$ shows that $D_i$ is a perfect point complex, hence lies in $D^b_{ctf}(s,A_i)$ as required by the projection transformation defining the cup product. The compact-support clause of [lem-fix-operation-reduction] gives the canonical isomorphism $c:\operatorname{red}_sC_n\xrightarrow{\sim}C_m$. Keep the ordinary comparison $r:\operatorname{red}_sD_n\to D_m$ as a morphism at this point: under $La_{X,m}^*\dashv Ra_{X*,m}$ of [fix-prop-adjunctions], it is the adjoint of
$$La_{X,m}^*\operatorname{red}_sRa_{X*,n}L_n\cong\operatorname{red}_XLa_{X,n}^*Ra_{X*,n}L_n\xrightarrow{\operatorname{red}_X(\varepsilon_n)}\operatorname{red}_XL_n\cong L_m.$$
Here the first comparison is the pullback comparison of [lem-fix-operation-reduction]. The mixed-support cup product of [def-pod-mixed-support-cup-product] is the projection transformation followed by this ordinary counit. The tensor and compact-support comparisons preserve the projection transformation because they preserve its defining adjunction maps, units and counits, as stated in [lem-fix-operation-reduction]; the counit square is exactly the defining transpose equation for $r$. Composing these two squares gives
$$c_{K_n\otimes L_n}\circ\operatorname{red}_s(\smile_{c,n})=\smile_{c,m}\circ(c\otimes r),$$
with the canonical tensor and $L_i$ comparisons understood. This uses no inverse of $r$.

Cited statements: lem-fix-operation-reduction, fix-prop-adjunctions, def-pod-mixed-support-cup-product, thm-pod-point-perfectness.

### Returned step 4

The pairing in [def-pod-derived-poincare-pairing] is exactly cup product, followed by compactly supported evaluation, followed by the normalized trace. Compose the cup-product identity from step 3 with the evaluation and trace squares of step 2. Under the canonical tensor-unit identification $\operatorname{red}_sA_n\cong A_m$, this gives the equality of morphisms $\operatorname{red}_sC_n\otimes^L_{A_m}\operatorname{red}_sD_n\to A_m$,
$$\operatorname{red}_s(\beta_{K_n})=\beta_{K_m}\circ(c\otimes r).$$
It proves the asserted coefficient compatibility of the pairing itself.

Cited statements: def-pod-derived-poincare-pairing.

### Returned step 5

By [thm-pod-point-perfectness], $C_n$ and $C_m$ are perfect point complexes; the theorem applies to our separated finite-type $X_0$ without any properness hypothesis. The point case of [lem-fix-operation-reduction] therefore gives the evaluation-compatible isomorphism $h:\operatorname{red}_s(C_n^\vee)\xrightarrow{\sim}(\operatorname{red}_sC_n)^\vee$. Define
$$\ell=(c^{-1})^\vee\circ h:\operatorname{red}_s(C_n^\vee)\xrightarrow{\sim}C_m^\vee.$$
This is the left vertical map in the statement. Its direction is forced by contravariance: dualize $c^{-1}:C_m\to\operatorname{red}_sC_n$, not $c$. It satisfies
$$\operatorname{ev}_{C_m}\circ(c\otimes\ell)=\operatorname{red}_s(\operatorname{ev}_{C_n})$$
under the tensor comparisons, by evaluation compatibility of $h$ and naturality of evaluation for the inverse isomorphisms $c,c^{-1}$.

Cited statements: thm-pod-point-perfectness, lem-fix-operation-reduction.

### Returned step 6

Let $b_i^\sharp:D_i\xrightarrow{\sim}C_i^\vee$ be the tensor–Hom adjoint of $\beta_{K_i}$. These are isomorphisms by [thm-pod-identification-of-the-comparison] at $A_n$ and $A_m$, since step 1 verified site-perfectness at both stages. The uncurrying and evaluation formulas of [lem-pod-closed-uncurry-laws] identify the uncurrying of $b_m^\sharp\circ r$ with $\beta_{K_m}\circ(1_{C_m}\otimes r)$. Precompose with $c\otimes1$ and use step 4; the result is $\operatorname{red}_s(\beta_{K_n})$. For the other morphism, the evaluation formula gives the precomposed uncurrying explicitly as
$$\operatorname{ev}_{C_m}\circ(c\otimes\ell)\circ(1\otimes\operatorname{red}_s(b_n^\sharp))
=\operatorname{red}_s(\operatorname{ev}_{C_n})\circ(1\otimes\operatorname{red}_s(b_n^\sharp))
=\operatorname{red}_s(\beta_{K_n}).$$
The first equality is step 5; the second is the adjoint evaluation identity and the tensor/evaluation compatibility of [lem-fix-operation-reduction]. Cancel the isomorphism $c\otimes1$ and use injectivity of the adjunction bijection (equivalently the inverse curry/uncurry identities of [lem-pod-closed-uncurry-laws]). Thus
$$b_m^\sharp\circ r=\ell\circ\operatorname{red}_s(b_n^\sharp).$$
Multiplying by the two horizontal inverses yields
$$r\circ\operatorname{red}_s((b_n^\sharp)^{-1})=(b_m^\sharp)^{-1}\circ\ell.$$
In particular $r=(b_m^\sharp)^{-1}\circ\ell\circ\operatorname{red}_s(b_n^\sharp)$ is an isomorphism: all three factors are isomorphisms. The last equality is exactly the displayed square, with its canonical right vertical comparison. Every tensor product used here is derived; the argument uses perfectness of $C_n$, not flatness of $A_m$ as an $A_n$-module.

Cited statements: thm-pod-identification-of-the-comparison, lem-pod-closed-uncurry-laws, lem-fix-operation-reduction.

## Sources and search audit

I read the current main-20261015 thm-pod-finite-reduction.md and its .proof.md, both paragraphs, together with the recorded chapter and sk-thm-sf-package unit. The first paragraph supplies the first new lemma's route; the second supplies the cup square and the abstract inverse-adjoint calculation. The first lemma's local-model data are supported by Stacks sites-cohomology.tex, Tag 08H3, lemma-strictly-perfect-pullback; I also read lemma-pullback-K-flat, Tag 08JH lemma-Rhom-strictly-perfect and Tag 08JJ lemma-dual-perfect-complex. These ringed-site results do not assume global projectivity of locally finite-free module sheaves. The categorical lemma is an explicit formal extraction from the blueprint's second paragraph, not attributed to a nonexistent Stacks result. I read Mathlib CategoryTheory/Monoidal/Closed/Basic.lean lines 155-202 and LinearAlgebra/PerfectPairing/Basic.lean lines 30-54: the former supplies uncurry laws, while the latter concerns ordinary modules and does not prove either new statement.

All new Mathlib searches were run with the required unmodified msearch.py and recorded in searches.jsonl. For each proposed argument I tried two natural-language phrasings, Loogle and source grep, and also LeanSearch. Some LeanSearch requests returned a rate-limit response and are recorded unavailable, never as no match. The later categorical query succeeded. Its hits concern strong monoidal structures and rigid adjunctions, not the asserted comparison with a general morphism r. The item retains its earlier searches, whose unchanged results are readable in the source JSON. I did not repeat those unchanged queries.

## Not duplicates

lem-sf-pod-smooth-dual-reduction-data vs lem-weil-pbc-strict-perfect-ringed-pullback-model: the existing node proves strict-perfect pullback models on arbitrary ringed topoi; the new node additionally identifies smooth shifted coefficient duals and their actual normalized trace contractions across finite quotient rings.
lem-sf-pod-smooth-dual-reduction-data vs lem-fix-site-perfect-scalar-hom: the existing node gives a single canonical internal-Hom comparison; it has no smooth orientation, normalized trace or compact-support contraction.
lem-sf-pod-smooth-dual-reduction-data vs lem-sf-package-normalized-orientation-perfect-duality: that node asserts orientation/trace and biduality package data, not the termwise quotient models and evaluation-normalized finite-reduction identity for the contraction of K with its shifted coefficient dual.
lem-sf-pod-smooth-dual-reduction-data vs thm-sf-dual-perfect: that node identifies Verdier and shifted coefficient duals and preserves evaluation, but states neither the explicit reduced local model nor the compact-support trace-contraction square.
lem-sf-perfect-pairing-reduction-adjoints vs lem-pod-closed-uncurry-laws: those are the basic adjunction identities; the new node constructs the contravariant comparison and proves the two specified adjoint squares and invertibility of r from the pairing square.
lem-sf-perfect-pairing-reduction-adjoints vs lem-fix-monoidal-dual-hom-comparison: the existing node supplies invertibility of an internal-Hom comparison on dualizable objects, but has no second pairing, c, r or inverse-adjoint square.
lem-sf-perfect-pairing-reduction-adjoints vs lem-coef-rational-scalar-transpose-compatibility: that node treats rational coefficient-field extension and retract formulas on sheaves; it does not apply to arbitrary strong monoidal functors and gives no criterion making a merely given comparison r invertible.
lem-sf-perfect-pairing-reduction-adjoints vs lem-pod-point-duality-coefficient-compatibility: that node identifies point-section dual comparisons; it does not compare the adjoints of two pairings or infer invertibility of r.
No new cup node was created: prop-sf-mixed-cup-coefficient-change already includes its full required statement. Blueprint searches for pairing square, inverse adjoints, site-perfect reduction, smooth trace, coefficient dual and monoidal functor found no blueprint node stating either new assertion. Whole-DAG searches also checked these related non-blueprint nodes. No Stacks tag is introduced as the primary source of a new node; therefore no new same-tag pair is hidden.

## Review by Q149

I checked the return's only numbered requirement by distributing the work into two new statements, not by deleting the old proof. Their allocations are about 2279 and 2521 characters of the old argument, with cup comparison reused from an existing node. Both have empty proof and proof_deps, null proof_origin and Mathlib match, status unsplit, inherited chapter/unit and precise blueprint provenance. The parent is a short three-step assembly; no step exceeds 2000 characters and total proof text is below 3000. No new statement is a clause of the original target: one supplies the local geometric contraction inputs and one is a categorical comparison criterion conditional on a pairing square.

For new parent step 1 I read the complete statement of lem-sf-pod-smooth-dual-reduction-data: it supplies exactly the perfectness, L comparison and contraction identity the step takes. I checked n >= m >= 1, separated finite type, smooth pure dimension d, constructibility and exceptional admissibility at both stages against the unchanged item and def-pod-conventions. For step 2 I read prop-sf-mixed-cup-coefficient-change in full: its list explicitly includes A_E,n to A_E,m, and its displayed square is precisely the cup identity. Step 1 verifies the membership hypotheses for K_n and L_n. I then read def-pod-derived-poincare-pairing: its three-arrow composite is cup, evaluation, trace, so substituting the two squares gives the pairing identity without extra theorems or properness.

For step 3 I read thm-pod-point-perfectness, which explicitly gives finite-stage perfectness for compact supports without properness, and lem-fix-operation-reduction, which explicitly includes the coefficient dual of a perfect point complex and evaluation compatibility. Thus h is an isomorphism without assuming the quotient is flat. I read thm-pod-identification-of-the-comparison: it states exactly that b_i is the tensor-Hom adjoint of beta_i and an isomorphism for perfect K_i. The first new lemma supplies those hypotheses at both stages. Finally I checked the full categorical node: its h and pairing equations are exactly those just obtained; c has the correct direction, ell dualizes c inverse, and the conclusion types match the unchanged displayed square. Its input only requires r to be a morphism. Every parent use has a verbatim quote in citations.json.

For the future proof of the first new lemma, I opened all returned cited statements: the finite reduction theorem explicitly has D^b_ctf target, site-perfectness and perfect-on-X have the same finite-stage local condition, the bounded-above flat K-flat node licenses termwise derived tensor, the operation-reduction node preserves evaluation and the defining units/counits, the dual-perfect node preserves the oriented identification, and the purity-reduction node includes the normalized smooth trace. For the future categorical proof the existing closed-uncurry node states the actual evaluation formula and inverse adjunction identities required, not just full faithfulness of a representable functor. The old argument is therefore preserved with available inputs, rather than with unsupported comparison claims.

I tested n=m (all geometric comparisons are identities), m=1<n (the ring map can be nonflat, so termwise K-flat derived tensor and perfect duality are essential), K_n=0 (all pairings are zero between zero complexes and are perfect), and d=0, X=s, K_n=A_n (the trace/evaluation comparisons reduce to coefficient multiplication). In the abstract node, F=id and c=id reduce the relation to b' r=b; if r is zero and a source is nonzero, the pairing-square hypothesis with invertible adjoints cannot hold. These checks detect the variance error of dualizing c rather than c inverse and any attempt to infer invertibility from an arbitrary mate. I found no statement error to dispute. No SGA source was used; smooth purity stays on the diagonal/deformation route already in the DAG.

Off-unit tools used by the parent: none newly introduced; the new nodes inherit its unit, and the existing cup, point-perfectness, comparison and operation-reduction statements lie on the retained route. The old bounded-above K-flat tool is suggested only for the future proof of the new unsplit data lemma, not cited as an off-unit proof dependency of the parent.
