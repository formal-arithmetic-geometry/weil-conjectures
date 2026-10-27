# Stage-1 repair: lem-pod-rational-purity-pairing (Q47)

1. Files written: the item, with its live statement and stmt_deps byte-identical, a ten-step assembly of 2436 characters, and exactly three new statement-only tasks:
   - lem-pod-inverse-contravariant-bidual: statement, unsplit, no Mathlib match. Only the coefficient-bidual transposition calculation of old Step 6; no domain theorem, Tate twist, trace or cup-product bundle.
   - lem-pod-point-weil-pairing-realization: statement, unsplit, no Mathlib match. The point-Hom calculation of old Step 10, at finite E, with its representative formula, tensor unit compatibility, complementary degrees and invariant scalar.
   - lem-pod-rational-weil-common-stage-descent: statement, unsplit, no Mathlib match. Old Step 11 as its own task: simultaneous realization of arbitrary rational data and inverse data with the actual operation, evaluation/transposition, purity/mate and point-action comparisons. It transports equations; it does not assume or reassert the parent's equivariance conclusions.
   citations.json contains every citation of every parent step with an exact complete statement copied from the cited node.
2. Attachments: none. Searches for the item tag and the new ids in lean/WeilConjectures found none. WeilSheaf/Operations.lean explains that it supplies forgetful compatibility for pullback and ordinary pushforward only; it explicitly lacks the tensor, Hom, exceptional and comparison lifts. The geometric Poincare and finite-stage bidual declarations do not give all the rational-Weil/mate/point clauses of this item.
3. WANTED: none. The source used is literature/blueprint/main-20261015/blueprint/sec-poincare-duality/sk-lem-finite/prop-weil-operations.proof.md, sentence 3 and the final smooth-pairing clause of sentence 4, together with the live reviewed rational expansion. These are agent-written sources, so the parent's proof_origin remains by agent. No SGA source is used.
4. The returned delivery wrongly promoted citation assemblies into new nodes. In response to D1 I removed the never-landed smooth-trace-lift node and restored Nagata, naturality/mate, cancellation and trace composition in parent Steps 1–4. In response to C5 I removed mixed-cup-assembly and dual-twist-evaluation; domains and twist remain parent Steps 5 and 7, and projection/counit/cup assembly is the elementary citation Step 8. Only the genuine bidual calculation becomes a node. In response to D2 common-stage descent is now an independent third node; its old one-sentence copies have been removed from the finite-E bidual and point tasks. The point node keeps its accepted argument. The released stage-1 keep_plan order is still applicable; the unchanged live statement, route and all eleven original arguments are retained. There is no statement dispute.
5. No mathematical argument is unfinished in this one-level split. The three tasks are intentionally statement-only for subsequent workers. The required dry run and push remain the delivery steps. No count/length waiver is needed: there are three new nodes and 2436 parent-proof characters, every step below 2000 characters.

## Not duplicates

lem-pod-inverse-contravariant-bidual vs lem-pod-constructible-mate-coherence: the existing node states evaluation and mate equivariance, but does not identify the transpose of symmetry/evaluation with the canonical coefficient bidual arrow and its double inverse-contravariant datum. The parent cites existing evaluation directly; the new task is only the bidual calculation.
lem-pod-inverse-contravariant-bidual vs lem-pod-derived-automorphism-hom-evaluation: the existing node gives the evaluation-defined Hom comparison and preservation of transposition; it does not give the double contragredient Weil equation for the coefficient bidual map. This calculation is precisely the new task, not a new copy of Hom transport.
lem-pod-inverse-contravariant-bidual vs cor-coef-verdier-weil-equivariance: the existing node concerns duality into the geometric dualizing object Ra^!Lambda and its biduality; this task is coefficient duality into Lambda_X on any separated finite-type X_0, with no purity identification or smooth dimension assumption. For singular X these are different duals.
lem-pod-inverse-contravariant-bidual vs prop-pod-dual-tate-data-compatibility: the existing statement uses normalized strict data and asserts evaluation plus the purity/Verdier identification; it does not state the coefficient-bidual equation for arbitrary rational Weil isomorphisms.
lem-pod-inverse-contravariant-bidual vs prop-pod-biduality-at-the-point: that is underlying perfect point biduality and tensor-Hom comparison, not coefficient-site Frobenius compatibility of the canonical transpose.
lem-pod-point-weil-pairing-realization vs lem-pod-fixed-pair-truncation-cohomology: the latter is a unary Weil arrow's cohomology action, not a tensor pairing with complementary degrees, the unit comparison and conjugation in End(Lambda_s).
lem-pod-point-weil-pairing-realization vs thm-pod-equivariance-of-the-twisted-pairing: that is the geometric strict-data pairing, whereas this is a general shifted pairing of two rational point complexes with arbitrary rational Weil data and the explicit canonical-transport representatives.
lem-pod-rational-weil-common-stage-descent vs prop-weil-pbc-common-stage-calculus: the existing finite-diagram statement gives representatives and equality at a further stage in one pair category; it does not retain operation expressions across several scheme categories, evaluation/transposition/purity/mate maps and the point actions. That existing calculus is input for the new operation-diagram task, not claimed absent.
lem-pod-rational-weil-common-stage-descent vs det-sp-qbar-finite-descent: the existing node adds compatibility for f^* and Rf_! only; the new task also retains internal Hom contravariance and inverse Weil data, evaluation/transposition, exceptional mates, normalized smooth trace and canonical point transports. It asserts their simultaneous canonical realization, beyond bare diagram descent.
lem-pod-rational-weil-common-stage-descent vs lem-wf-common-stage-weil-iterate: the existing node concerns finite collections of pairs and iterations of pullback. It does not preserve the tensor/Hom, purity/mate, trace and point-pairing comparisons in this task.
lem-pod-rational-weil-common-stage-descent vs lem-pod-equivariant-mates-coefficient-transport: the existing node transports an already supplied compatible adjunction/mate system. It does not simultaneously realize a finite diagram with arbitrary inverse Weil arrows, Hom transposes, cohomology vectors and point action, including choosing a later field where inverse identities and all specified equations actually hold.
lem-pod-rational-weil-common-stage-descent vs thm-pod-qbar-coefficient-pairing: that statement is perfectness/independence of the geometric Poincare pairing. This task is simultaneous descent of arbitrary rational Weil-operation diagrams and transfer of equations, without assuming or proving perfectness or the parent's pairing identity.

I searched the whole DAG by bidual, inverse contravariant, finite diagram, common-stage and pairing; blueprint_refs.py searches for those notions and point transport were read. The nearest blueprint ancestor is prop-weil-operations. Each new from.via is [lem-pod-rational-purity-pairing], with the exact orientation/trace or smooth-pairing source clause; same_as is []. There are no Stacks-tag sources for these particular formal Weil calculations, hence no same-tag pairs. The finite-field and coefficient notions remain those of the existing definitions.

## Search evidence

The earlier searches.jsonl and per-node full search results are retained. The point node's same mathematical question is covered by its two earlier semantic phrasings, Loogle, source grep and LeanSearch; their full results were read and reused. Narrowing it to finite E removes a clause, not a new unsearched notion. For each newly named bidual/descent task I ran msearch.py with two distinct semantic phrasings, Loogle, Mathlib grep and LeanSearch; results are copied unchanged into mathlib_searches and the per-node result files.

Bidual searches returned sheaf free/pullback naturalities and condensed ihom section formulas, ordinary LinearEquiv.dualMap and module evaluation naturality. These are not the rational derived coefficient-site double-contragredient statement; Loogle and grep had zero hits. Descent searches returned Witt vector Frobenius solutions, elliptic-curve point maps, condensed internal-projectivity criteria and generic filtered ring/complex colimits. The nine Loogle hits concern generic filtered colimit homs/instances, not canonical sheaf operation diagrams and point transport. Neither task is a one-line specialization of those declarations. Both services were available; nothing unavailable has been recorded as a negative result.

## Review by Q47

I read the returned review, the released repair note, the live reviewed eleven-step split, the chapter and unit, and the current blueprint proof. The chapter and unit route are unchanged. All three new nodes have empty proof and proof_deps and null proof_origin; the parent uses their statements only. The statement and stmt_deps of the parent are preserved exactly. The rejected sandbox files and report are archived under returned-version/, outside the delivery DAG, so the previous searches and mathematical work are retained without delivering the redundant nodes.

For parent Step 1 I read def-weil-finite-type-morphism (finite type includes quasi-compactness), lem-pc-separated-quasi-separated (separated diagonal is quasi-compact), thm-nagata-compactification (separated finite type to a qcqs target is compactifiable), both base-change statements (open and proper) and def-weil-compactifications-refinements (factorization with exactly those factors). Y_0 is separated finite type in the purity paragraph; the quasi-compactness is over the affine field point. Thus Nagata has its actual hypotheses, and the compactification is defined over k_0 as the next lemma requires.

For Step 2 I read lem-pur-rational-weil-naturality-mate: it gives naturality for every rational arrow, the exact displayed gamma/b/e formula, and equality with the right mate of beta inverse, not merely matching endpoints. I also read def-pur-canonical-rational-purity-realization to check the gamma is the coefficient-normalized realization in the intrinsic categories. Its smooth pure dimension, separated finite type and base-field compactification hypotheses are exactly present. Step 3 substitutes u=theta_K and cancels P_X gamma with its inverse; the resulting equation is literally the arrow definition in def-weil-weil-sheaf-complex. This is a two-line elementary citation step.

For Step 4 I read the functor-on-Weil-arrows equation of lem-pod-semilinear-field-operation-lifts and the exact exceptional counit equation of lem-pod-constructible-mate-coherence. Multiplying F(gamma)theta_FH=theta_FG P F(gamma) by epsilon and then using epsilon theta_FG=theta P epsilon gives the required trace composite equation. This is now an elementary citation step, not the rejected new smooth-trace task. For a_X the schemes are separated and smooth of dimension d as required, and the smooth trace uses the coefficient unit and the same normalized counit.

For Step 5 I read the field conventions in def-weil-finite-tor-amplitude, thm-sf-ctf-stability clauses (ii)–(iv),(vii), and the coefficient-site local finite-projective definition. These give bounded constructibility for Hom, tensor and direct images. The extra site-perfect hypothesis is actually assumed on K: it is not inferred from constructibility. Dualizing the finite direct-summand models reverses the finite interval, so K^vee remains site-perfect. The unit has its one-term rank-one model. This keeps the Hom/evaluation domain valid for the new bidual task and its second dual.

For Step 6 I read the exact RHom(theta inverse,c)h_g formula in operation-lifts and tensor-evaluation clause in mate-coherence. They supply evaluation equivariance directly; no new evaluation wrapper is cited. I separately read the characterization and transposition preservation in lem-pod-derived-automorphism-hom-evaluation, which the new coefficient-bidual statement uses to pin its actual canonical transpose. The new statement claims just delta_K theta_K=theta_double P(delta_K). It does not add a Tate scalar, purity, direct-image domains, or a duplicate evaluation theorem. Its calculation is expanded below. No chosen integral Frobenius datum is needed.

For Step 7 I read def-weil-frobenius-coefficient-twists, especially its functorial tensoring rule, and lem-pur-twist-frobenius-scalar: the canonical Tate line has q^{-d} and the unit at m=0 has 1. Tensoring the evaluation arrow with the line identity is therefore the displayed twisted evaluation; the sign is not reversed. This is an elementary citation step and no dual/twist bundle remains.

For Step 8 I read def-pod-mixed-support-cup-product in full: its projection input is Ra_*L, and its second map is Ra_!(1 tensor epsilon_L), with epsilon_L the ordinary counit La^*Ra_*L to L. I read the projection and ordinary-adjunction clauses in mate-coherence and the tensor/direct-image functoriality in operation-lifts. Composition of these arrow equations gives cup equivariance, followed by evaluation and the shifted trace from Steps 4 and 7. The shift comparisons are supplied in derived-automorphism-hom-evaluation. I read lem-sf-point-fibre-derived-tensor: it identifies this tensor and retains unit, symmetry and associativity. Thus B has exactly the required fiber, with A=Ra_!K and D=Ra_*K^vee(d). There is no comparison between ordinary and compact support, and this short composition is elementary from its cited statements.

For Step 9 I read the revised point node, and for its source I read the canonical shift-preserving point equivalence, point-transport naturality at every rational arrow, unit scalar at m=0, and pullback tensor unit compatibility. Its hypotheses are exactly the B equation obtained in Step 8, finite-E point complexes and canonical unit datum. Setting n=2d gives degrees i and 2d-i; tensoring their unit-source representatives targets the n-shift of A tensor D. Its conclusion gives both the transported representatives and c_s P(b)c_s inverse=b, and hence the desired scalar identity with the specified point actions.

For Step 10 I read the revised common-stage node against old Step 11, def-weil-algebraically-closed-coefficients, common-stage-calculus, det-sp-qbar-finite-descent, operation-lifts, derived-automorphism-hom-evaluation, rational-weil-naturality-mate, canonical-rational-purity-realization, and point-transport-natural. The general diagram lemmas alone do not identify the operation-generated maps; the new task retains those exact comparisons. It realizes the finite list of theta and theta inverse together and equalizes their two inverse equations, rather than assuming an integral invariant lattice. For point vectors it retains the canonical point functor and unit datum. All equations in Steps 1–9 are equations of rational arrows and therefore pass by this node; one may choose a field for each arbitrary finite list of vectors, which proves the universal degreewise assertion without trying to put infinitely many vectors over a single field.

Small cases were checked for every task. For biduality on a point theta=ell, the first dual datum is ell inverse and the double is ell; delta intertwines them. For K=0 all equations are zero. For point realization n and i are arbitrary integers, including complexes supported away from the chosen degrees; then the relevant group or pairing is zero. The unit pairing with theta_A=t and theta_D=t inverse is invariant, and replacing both by t would violate the B hypothesis unless t squared=1. For descent an empty finite collection is representable at any finite starting field; a collection with one arrow theta=ell and its inverse is representable rationally although no integral invertible theta on the rank-one lattice exists. Finitely many inverse/equality witnesses can be put over one compositum and then a later common field. Nonproper X_0 never changes the two support positions. For purity f=id,d=0 the cancellation and trace reduce to their normalized identity maps. These tests found no false statement.

No new parent step exceeds 2000 characters and no lemma is hidden in a long elementary step. No permission, compiler or build is involved; the only writes are in this sandbox. The independent maintainer review remains required after direct delivery.

## Bidual calculation retained for the new task

Write D(M)=RHom(M,Lambda_X), theta=theta_K, alpha=theta_DK, h=h_DK. The canonical delta is characterized by ev_DK(1_DK tensor delta)=ev_K sigma_DK,K. To compare delta theta and theta_DDK P(delta), apply this tensor-Hom adjunction, whose injectivity reduces equality to equality of maps DK tensor PK to Lambda_X. The first uncurries to ev_K sigma (1 tensor theta).

For the second, insert theta_DDK=RHom(alpha inverse,c)h. Naturality of evaluation and the evaluation-defined comparison give

    ev_DK(1 tensor theta_DDK P(delta))
      = c ev_PDK(alpha inverse tensor h P(delta))
      = c P(ev_DK) mu^{-1}(alpha inverse tensor P(delta))
      = c P(ev_DK(1 tensor delta)) mu^{-1}(alpha inverse tensor 1).

Replace the inner composite by ev_K sigma. Compatibility of mu with symmetry changes this into

    c P(ev_K) mu^{-1}(1 tensor alpha inverse) sigma_DK,PK.

The existing evaluation Weil equation is ev_K(theta tensor alpha)mu=c P(ev_K). Cancelling alpha against alpha inverse reduces the last map to ev_K(theta tensor 1) sigma_DK,PK=ev_K sigma_DK,K(1 tensor theta), precisely the first uncurried map. Injectivity of transposition proves the new bidual equation. This uses the canonical evaluation-defined h, not an arbitrary Hom isomorphism. The site-perfect model check in Step 5 ensures every Hom and evaluation in this calculation is on its actual domain.

## Preservation of the live eleven-step argument

The following is the complete live proof retained verbatim as source material, not proof sketches inside statement-only nodes. Its distribution is old 1→new 1; old 2→new 2; old 3→new 3; old 4→new 4; old 5→new 5; old 6→new 6 plus the bidual task; old 7→new 7; old 8–9→new 8; old 10→the point task and new 9; old 11→the descent task and new 10. This replaces the rejected four-wrapper allocation without losing any argument.

### Original Step 1

For the purity assertion choose a compactification over the finite base field. The target $Y_0$ is quasi-compact because its finite-type structure morphism to the affine $\operatorname{Spec}k_0$ is quasi-compact [def-weil-finite-type-morphism]. It is quasi-separated because its structure morphism is separated, by [lem-pc-separated-quasi-separated]. Apply [thm-nagata-compactification] to the separated finite-type $f_0$ to obtain $X_0\xrightarrow{j_0}\bar X_0\xrightarrow{\bar f_0}Y_0$. Its base change to $k$ is a compactification $c=(j,\bar f)$, since open immersions and proper morphisms are stable under base change [lem-weil-pbc-open-immersion-base-change, lem-weil-pbc-proper-base-change]. Here compactification has exactly the meaning of [def-weil-compactifications-refinements]. Thus the extra computational choice in the rational naturality/mate lemma is available; it is not an additional hypothesis on $f_0$.

Cited statements: def-weil-finite-type-morphism, lem-pc-separated-quasi-separated, thm-nagata-compactification, lem-weil-pbc-open-immersion-base-change, lem-weil-pbc-proper-base-change, def-weil-compactifications-refinements.

### Original Step 2

Use [lem-pur-rational-weil-naturality-mate] with $c$ from Step 1. Its hypotheses hold: $X_0,Y_0$ are separated finite type, $f$ is smooth of pure dimension $d$, and the coefficient category is rational or common-stage. Its $\gamma$ is the transported canonical purity family, realized in our intrinsic categories as specified in [def-pur-canonical-rational-purity-realization]. It gives both naturality for every rational arrow and the equality of the displayed $e_K$ with the right mate of $\beta^{-1}$, where $\beta:P_YRf_!\simeq Rf_!P_X$ is compact-support exchange. In particular it identifies the actual adjunction normalization, not just the endpoints of $e_K$. The comparison is invertible because the formula is a composite of three isomorphisms.

Cited statements: lem-pur-rational-weil-naturality-mate, def-pur-canonical-rational-purity-realization.

### Original Step 3

Apply that naturality with $u=\theta_K:P_YK\to K$. Substitute the definition of $e_K$ and cancel the adjacent inverse factors:
$$Rf^!(\theta_K)e_KP_X\gamma_{f,K}=Rf^!(\theta_K)\gamma_{f,P_YK}b_K=\gamma_{f,K}H(\theta_K)b_K.$$
By the arrow equation in [def-weil-weil-sheaf-complex], this says precisely that $\gamma_{f,K}$ is a Weil morphism for the pullback/twist datum $H(\theta_K)b_K$ and the specified exceptional datum $Rf^!(\theta_K)e_K$. Naturality used here is the assertion for arbitrary rational arrows in [lem-pur-rational-weil-naturality-mate], not a restriction to integral Weil isomorphisms.

Cited statements: lem-pur-rational-weil-naturality-mate, def-weil-weil-sheaf-complex.

### Original Step 4

Write $F=Rf_!$, $G=Rf^!$ and denote the induced Weil data by $\theta_{FH}$ and $\theta_{FG}$. The functor on pairs in [lem-pod-semilinear-field-operation-lifts] carries Step 3 to
$$F(\gamma_K)\theta_{FH}=\theta_{FG}P_YF(\gamma_K).$$
For the lifted adjunction [lem-pod-constructible-mate-coherence] gives $\varepsilon_K\theta_{FG}=\theta_KP_Y\varepsilon_K$. Consequently
$$\varepsilon_KF(\gamma_K)\theta_{FH}=\theta_KP_Y\varepsilon_K\,P_YF(\gamma_K)=\theta_KP_Y(\varepsilon_KF(\gamma_K)).$$
This is the claimed smooth-trace equivariance, with exactly the trace composite in the statement. It also proves the trace assertion for $a_X$ at the coefficient unit, which is the trace used below.

Cited statements: lem-pod-semilinear-field-operation-lifts, lem-pod-constructible-mate-coherence.

### Original Step 5

Now assume the pairing hypotheses. All operations below have their stated constructible domains. At the field stages $D^b_{ctf}=D^b_c$ by [def-weil-finite-tor-amplitude]. Apply [thm-sf-ctf-stability], including its field-passage clause (vii), to $K$, the coefficient unit and the separated finite-type $a_X$. Internal Hom, tensor and the two direct images have bounded constructible outputs; thus $K^\vee$, $K^\vee(d)$ and the cohomology complexes used below are defined. The site-perfect first-variable condition required for the elementary coefficient-dual comparisons is exactly the hypothesis on $K$; it is not replaced by mere constructibility. The coefficient unit is site-perfect, and dualizing a bounded local finite-projective model again gives such a model, with the degrees reversed.

Cited statements: def-weil-finite-tor-amplitude, thm-sf-ctf-stability, def-weil-site-perfect-complex.

### Original Step 6

Put $P=P_X$, and let $c:P\Lambda_X\simeq\Lambda_X$ be the coefficient datum. The Hom formula of [lem-pod-semilinear-field-operation-lifts] gives the inverse contravariant datum $\theta_{K^\vee}=R\mathcal Hom(\theta_K^{-1},c)h_g$. The evaluation identity and preservation of tensor–Hom transposition in [lem-pod-derived-automorphism-hom-evaluation] give
$$\operatorname{ev}_K(\theta_K\otimes\theta_{K^\vee})\mu_g=c\,P(\operatorname{ev}_K).$$
Indeed precomposition by $\theta_K^{-1}$ cancels the $\theta_K$ on the first evaluation argument, and postcomposition gives $c$. Tensor evaluation and ordinary adjunction maps are Weil morphisms by [lem-pod-constructible-mate-coherence]. The coefficient bidual map is the transpose of evaluation after the tensor symmetry. Transpose the last equation with $K$ and $K^\vee$ interchanged: the same preservation of transposition gives $\delta_K\theta_K=\theta_{K^{\vee\vee}}P(\delta_K)$. Thus evaluation and the canonical bidual map carry the rational Weil structures claimed, without choosing an integral datum for $K$.

Cited statements: lem-pod-semilinear-field-operation-lifts, lem-pod-derived-automorphism-hom-evaluation, lem-pod-constructible-mate-coherence.

### Original Step 7

Tensor the evaluation equation of Step 6 with the identity of the Tate line and insert the canonical associators. The twist rule in [def-weil-frobenius-coefficient-twists] makes $\operatorname{ev}_K(d):K\otimes^LK^\vee(d)\to\Lambda_X(d)$ equivariant. Its line datum is the canonical roots-of-unity transport, not the trivial line datum. By [lem-pur-twist-frobenius-scalar] its point scalar is $q^{-d}$; the same lemma at $m=0$ says the target coefficient unit has Frobenius $1$. This checks both the sign of the twist and the scalar in the final pairing.

Cited statements: def-weil-frobenius-coefficient-twists, lem-pur-twist-frobenius-scalar.

### Original Step 8

Let $L=K^\vee(d)$ and $a=a_X$. Before taking point fibers, the mixed-support cup product of [def-pod-mixed-support-cup-product] is
$$Ra_!K\otimes^LRa_*L\xrightarrow{\operatorname{PF}}Ra_!(K\otimes^LLa^*Ra_*L)\xrightarrow{Ra_!(1\otimes\varepsilon_L)}Ra_!(K\otimes^LL).$$
The second projection input is $Ra_*L$. By [lem-pod-constructible-mate-coherence], the projection transformation and ordinary counit are Weil morphisms. Tensor and direct-image functoriality are [lem-pod-semilinear-field-operation-lifts]; composing their arrow equations therefore makes this particular cup product equivariant. This argument takes place in the rational category itself and uses neither a finite-coefficient cup theorem outside its domain nor a Frobenius-stable lattice.

Cited statements: def-pod-mixed-support-cup-product, lem-pod-constructible-mate-coherence, lem-pod-semilinear-field-operation-lifts.

### Original Step 9

Compose the cup morphism of Step 8, $Ra_!$ of twisted evaluation from Step 7, and the smooth trace from Step 4, with the canonical shift by $2d$. The result is the specified derived pairing $B:A\otimes^LD[2d]\to\Lambda_s$, where $A=Ra_!K$ and $D=Ra_*K^\vee(d)$. The pair functors and their shift/tensor comparisons are those of [lem-pod-semilinear-field-operation-lifts, lem-pod-derived-automorphism-hom-evaluation]. Composing Weil-morphism equations gives
$$B(\theta_A\otimes\theta_{D[2d]})\mu_{g_s}=c_sP_s(B).$$
Under the canonical point tensor comparison of [lem-sf-point-fibre-derived-tensor] its fiber is exactly tensor product, mixed-support cup, evaluation and normalized trace in the statement. No comparison of ordinary and compact-support cohomology was used.

Cited statements: lem-pod-semilinear-field-operation-lifts, lem-pod-derived-automorphism-hom-evaluation, lem-sf-point-fibre-derived-tensor.

### Original Step 10

Identify $H^i(\operatorname{Fib}_sA)$ with $\operatorname{Hom}(\Lambda_s,A[i])$, and similarly for $D$, using the shift-preserving point equivalence [lem-weil-point-fibre-equivalence]. For a representative $x:\Lambda_s\to A[i]$, naturality [lem-weil-frobenius-point-transport-natural] says that its transported representative is $P_s(x)c_s^{-1}$: the point transport on the unit followed by $c_s$ is the identity by [lem-pur-twist-frobenius-scalar] at $m=0$. Hence $F_Ax=\theta_A[i]P_s(x)c_s^{-1}$, and likewise for $y$. These are exactly the exchange-then-Weil-datum actions in [def-weil-frobenius-cohomology-transport]. Substitute these two formulas into the pairing of Step 9. Its Weil equation cancels the two input data; the unit compatibility of the pullback tensor comparison $\mu_{g_s}$ [lem-pur-derived-pullback-tensor-iso] identifies $c_s^{-1}\otimes c_s^{-1}$, composed with $\mu_{g_s}$, with $P_s$ of the unit tensor constraint. The result is $c_sP_s(\langle x,y\rangle)c_s^{-1}=\langle x,y\rangle$, since the coefficient-unit Frobenius is $1$. The degrees are $i$ and $2d-i$, whose sum becomes zero after the shift $[2d]$ in $B$. This proves the displayed degreewise identity.

Cited statements: lem-weil-point-fibre-equivalence, lem-weil-frobenius-point-transport-natural, lem-pur-twist-frobenius-scalar, def-weil-frobenius-cohomology-transport, lem-pur-derived-pullback-tensor-iso.

### Original Step 11

Every equality above was an equality of rational arrows. For $\overline{\mathbf Q}_\ell$, represent the finitely many objects, Weil isomorphisms, their inverses and vectors under consideration over one finite coefficient extension, as in [def-weil-weil-sheaf-complex]. The operation formulas and evaluation/transposition comparisons are common-stage formulas [lem-pod-semilinear-field-operation-lifts, lem-pod-derived-automorphism-hom-evaluation]; the purity/mate identities hold in that category by [lem-pur-rational-weil-naturality-mate], and point transport is scalar-compatible by [lem-weil-frobenius-point-transport-natural]. Apply Steps 1–10 over that finite field and pass to their morphism classes. This proves the same equations at the algebraically closed stage. On a point with $d=0$ and $\theta_K=\ell$, Step 6 gives dual datum $\ell^{-1}$, so evaluation multiplies by $\ell\ell^{-1}=1$; the zero complex gives zero throughout. For a nonproper $X_0$, the two factors remain $Ra_!$ and $Ra_*$ throughout Steps 8–10. These checks explain why neither an invariant lattice nor properness has entered.

Cited statements: def-weil-weil-sheaf-complex, lem-pod-semilinear-field-operation-lifts, lem-pod-derived-automorphism-hom-evaluation, lem-pur-rational-weil-naturality-mate, lem-weil-frobenius-point-transport-natural.

Resumption check: the retained repair passed the server dry run at bc57743433f. I then normalized accidentally doubled TeX command escapes in parent Steps 3–4 and 6–8 and 10; mathematical text, statement, dependencies and searches are unchanged. Exact citation quotes were rechecked against the current live statements and the new sandbox statements. The final dry run below supersedes that receipt.
