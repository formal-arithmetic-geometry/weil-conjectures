# Worker report: Q36, lem-zl-point-weil-heart-flag

## Files written

- Item: dag/nodes/sec-deligne-laumon-general/lem-zl-point-weil-heart-flag.json — statement unchanged, five-step assembly.
- lem-zl-point-heart-finite-stage: statement, unsplit; no exact Mathlib match.
- lem-zl-automorphism-flag-finite-coefficients: statement, unsplit; no exact Mathlib match.
- lem-zl-point-equivariant-diagram-lift: statement, unsplit; no exact Mathlib match.

## Attachments

None. Searched WeilConjectures for the item's tag and point/Weil flag notions. Sheaf.Paper.PointWeilHeartFlag.zl_point_weil_heart_flag (namespace WeilConjectures), lines 336–343, ends in sorry. The invariant categorical filtration theorem in WeilConjectures.RepresentationTheory.InvariantFlagCategoricalFiltration is over ZMod ℓ with trivial quotient actions, not this item.

## WANTED

None. The argument follows the available current blueprint, with the existing agent-written detailed proof as its elaboration. No SGA route is used.

## What was wrong and what changed

The released 2026-10-22 repair order explicitly overrides the previous reviewed split: its 7362-character proof left too much work in one node. The sandbox initially had only dispatcher markers, with no node, report or search log. I read the current repository node and repair note; there was no retained split on which to run the initial dry run. I copied the current node without a git command. Its statement and all maintainer-owned fields are retained.

Three new self-contained statements divide the work, rather than restating the item's filtration-and-purity conclusion. The first handles old steps 1–2 (actual finite heart representative and exact normalized heart equivalence); the second handles old steps 3–4 (linear algebra and simultaneous finite matrix field); the third handles old steps 5–6 (inverse point transport, lifted diagram identities, exactness, endpoint and common-stage normalization). They have no proof steps or proof dependencies: future workers split them independently. Old steps 7–8 remain the elementary purity calculation and degenerate-case assembly. Every original argument is reproduced below, allocated to its new work package or retained assembly step, with no shortening of its mathematical content.

No source or item statement correction. The existing p-linear-triangular statement omits the algebraically closed hypothesis which its source unit imposes; the new coefficient-flag statement makes the algebraic-closure hypothesis explicit. This reports the existing omission without editing that node or broadening the new claim to arbitrary coefficient fields.

## Not duplicates

Blueprint searches: ancestor gives thm-zl-real-mixed-by-curves. Searches for 'heart point', 'point heart', 'invariant flag', 'equivariant diagram', 'coefficient flag', 'triangular', and 'finite coefficient' were read, as well as a title-level scan and whole-DAG keyword searches for adapted bases, finite-stage heart descent and point equivalences. The broad 'point' search produced many unrelated geometric-point nodes; the targeted searches and statement reads below resolve the relevant candidates. No new source has a Stacks tag because these statements elaborate the explicitly cited blueprint point argument, rather than a Stacks result. All new blueprint.from records name paragraph 7 and carry via=[lem-zl-point-weil-heart-flag]. All same_as lists are empty.

- lem-zl-point-heart-finite-stage vs lem-weil-point-fibre-equivalence: the latter is a derived equivalence; the former asserts the exact restriction to hearts with canonical scalar/cohomology normalization, and an actual finite-stage Weil heart representative.
- lem-zl-point-heart-finite-stage vs lem-a1-point-realization-standard-cohomology: t-exactness/cohomology compatibility alone does not assert the restricted equivalence or descent of a given Weil pair and its inverse equations.
- lem-zl-point-heart-finite-stage vs lem-fd-common-stage-comparison-descent: the latter transports supplied equivalences between sf and PBC coefficient models, not descent of an arbitrary heart Weil pair or the point-heart equivalence.
- lem-zl-automorphism-flag-finite-coefficients vs p-linear-triangular: the latter supplies a flag over an algebraically closed field, not the adapted-basis finite-field model, inverse matrix, restrictions and exact quotient diagram over a single finite extension. These additional requirements are the separate descent work package.
- lem-zl-point-equivariant-diagram-lift vs lem-weil-pbc-invariant-flag-categorical-filtration: the latter realizes a flag of representations over ZMod ℓ with trivial quotient actions; the new statement realizes arbitrary finite equivariant vector diagrams in the raw rational Weil heart with normalized point transport and a prescribed object.
- lem-zl-point-equivariant-diagram-lift vs lem-zl-classical-weil-filtration-heart-transport: the latter assumes a classical lisse Weil filtration and its normalized realization on a scheme; the new statement starts from arbitrary finite vector diagrams at a point without a classical sheaf or a given classical filtration.
- lem-zl-point-equivariant-diagram-lift vs lem-weil-point-transformation-coefficient-descent: that node descends supplied integral natural transformations, not equivariant diagrams or Weil heart objects.
- lem-zl-point-equivariant-diagram-lift vs lem-zl-punctual-spectrum-exact-fibre: the latter provides an exact fibre functor with local eigenvalue detection, not essential surjectivity, lifted diagrams or chosen endpoints.

## Mathlib searches

Every query in the new nodes was run using msearch.py and the full returned hits are saved in the sandbox text files as well as node results. Each work package has LeanSearch, LeanFinder (two phrasings), Loogle and source grep. LeanSearch is currently available. The first flag Loogle query reports unknown identifier LinearMap.IsTriangularizable; I also ran Module.End, "eigenvalue" and inspected its hits. The targeted Triangularizable.lean grep and source read give Module.End.exists_eigenvalue at line 63, an ingredient only, and its TODO at line 34 expressly leaves the invariant-chain formulation for future work. LieModule.IsTriangularizable, Weights/Basic.lean:704, is the spanning generalized-eigenspace condition, not the new finite coefficient flag statement. The heart searches give general Ext/exact-functor/abelian-transfer results; the lift searches give FullyFaithful.preimageIso, which I read at Functor/FullyFaithful.lean:205, and Witt-vector isocrystals, which use different coefficients and semilinear operators. None is a one-line specialization proving the new statements. No Mathlib leaves are claimed. Existing searches on the unchanged item were retained.

## Review by Q36

I read the current main-20261015 thm-zl-real-mixed-by-curves proof, especially paragraph 7's dimension-zero Jordan filtration and weights, the chapter record and sk-i-dl-general-real unit step 1, and the full eight-step returned proof. I opened the statements of every original dependency, including the actual common-stage Hom equality rule, constructible truncations, the heart definition, point-fibre equivalence, point realization/cohomology and scalar compatibility, point transport invertibility and naturality, local Frobenius, triangularization, and weight/logarithm conventions. The new statements spell out the conclusions those arguments establish, without replacing raw sf coefficients by PBC coefficients or assuming continuity of arbitrary Frobenius powers.

Assembly step 1 uses lem-zl-point-heart-finite-stage for both the actual E0-heart Weil pair and its endpoint/fibre identification; def-weil-local-frobenius-trace gives exactly the transport-then-Weil composite used for F0. Assembly step 2 uses the coefficient-flag statement for all flag spaces, ranks, quotient automorphisms and the one finite E; its hypotheses hold because Omega is an algebraic closure, V0 is finite dimensional and F0 invertible. Step 3 uses the diagram-lifting statement for the chosen inclusions, quotient projections and their composites, and step 1's normalized scalar comparison to pin its designated final object. Use the finite category presented by these arrows and their zero/composition relations (equivalently their images as linear maps); indices only move forward through this flag/quotient diagram, so only finitely many composites occur. All arrows commute with the restricted/quotient F. The new lifting statement explicitly supplies the Weil equations, heart exactness, correct local F and the fixed endpoint; no extra equivalence assertion is silently borrowed from a definition. Step 4 uses the weight, real-power and positive-log definitions verbatim: the rank-one scalar is nonzero, its complex modulus is positive and q>1, so the displayed cancellation proves the purity equality. Finite maximum supplies the bound. Step 5 uses the first new statement's reflection of zero objects, the empty flag allowed in the second, and empty mixed filtrations allowed by the weight definition; it invokes the lemmas for arbitrary finite-field datum, so changing the finite base field changes q consistently.

For the first new node I checked that replacing K by H0(K) uses the cited truncation theorem, not an unsupported claim that every original representative is already in the heart. Common-stage inverse and intertwining equalities have finitely many representatives and therefore a common field stage. For the second I checked that algebraic closure is the coefficient field Omega, not the geometric characteristic-p field k: a matrix with irreducible quadratic characteristic polynomial need not have a flag over E0, but its basis entries and inverses lie in a finite extension E. Injective restrictions are surjective in the same finite dimension; quotient maps and inverse Frobenius are both present. For the third I checked the direction theta = omega^{-1}(A iota^{-1}); naturality gives omega(Lg*u)iota_i=iota_j omega(u), and faithfulness yields u theta_i=theta_j Lg*u. Lifting the inverse gives an actual Weil isomorphism. The designated endpoint agrees with the original structure, and exactness survives scalar extension via the point-heart equivalence; no new functor normalization is chosen.

Small cases: zero V gives no quotient or weight conditions; rank one works for every nonzero scalar, including non-unit complex absolute value and nonintegral real weight; a nontrivial 2x2 Jordan block is allowed; a quadratic irreducible E0-operator is handled only after enlarging E; singular F is correctly excluded. For diagram lifting, zero objects, zero arrows, a zero quotient, and a prescribed nontrivial endpoint automorphism satisfy the asserted universal identities. Nonzero off-diagonal entries are retained, not diagonalized. All new nodes have complete object/hypothesis declarations, genuine statement-only bodies, explicit blueprint origin, and recorded real searches. No new node restates the entire item or a pure-factor filtration clause. No non-elementary assembly step is longer than 2000 characters; the total is below 3000. This repair adds three comparable work packages as required, rather than merely shortening the original text. There is no separate reader in this direct-delivery brief; this is my signed self-review.

## Preserved full argument and allocation

### Original step 1: lem-zl-point-heart-finite-stage

First choose an actual finite heart stage for the given sheaf. Write its underlying common-stage object as $(E_0,K)$. The constructible truncation theorem identifies $\mathcal H^0(E_0,K)$ with $(E_0,\mathcal H^0K)$, and the canonical truncation isomorphism identifies this with $\mathcal F$, since $\mathcal F$ is in the heart. Use this identification to replace the representative by the heart object $\mathcal H^0K$. Represent the Weil map, its inverse, the identification with the original object and its inverse at common finite stages. There are finitely many inverse and intertwining equations. By the equality rule in the Hom colimits, each holds at a further finite stage; a common upper bound makes all hold simultaneously. Thus, after one enlargement, there is a genuine heart object $M$ over $E_0$ with an isomorphism $\theta:Lg_s^*M\to M$ whose image is the prescribed Weil sheaf. No continuity of the powers of $\theta$ is required by the Weil-pair definition.

Original cited statements: def-weil-algebraically-closed-coefficients, prop-constructible-truncations, def-weil-constructible-heart, def-weil-weil-sheaf-complex.

### Original step 2: lem-zl-point-heart-finite-stage

Use the stated point-fibre equivalence at finite coefficient fields together with the point-realization cohomology theorem. Its restriction to hearts is a fully faithful equivalence with finite-dimensional vector spaces: a heart object has fibre concentrated in degree zero; conversely, if a preimage $C$ of $W[0]$ is chosen under the equivalence, then $\mathcal H^0 C$ is a heart preimage, because $\operatorname{Fib}_s(\mathcal H^0 C)\cong H^0(\operatorname{Fib}_s C)[0]=W[0]$. Full faithfulness is inherited from the full derived subcategories. This equivalence preserves and reflects kernels and cokernels: their universal factorization properties transfer bijectively across the Hom bijections. It therefore preserves and reflects short exact sequences. These fibre identifications commute with enlarging the finite coefficient field by the scalar/cohomology compatibility in the point-realization theorem. In particular the fibre $V_0$ of $M$ is finite dimensional and $V=V_0\otimes_{E_0}\Qlb$.

Original cited statements: lem-weil-point-fibre-equivalence, lem-a1-point-realization-standard-cohomology, def-weil-constructible-heart.

### Original step 3: lem-zl-automorphism-flag-finite-coefficients

Apply the invariant-flag theorem over the algebraically closed coefficient field $\Qlb$, rather than over the geometric base field $k$, to $F:V\to V$. It gives $0=W_0\subset W_1\subset\cdots\subset W_d=V$ with $\dim W_j=j$ and $F(W_j)\subset W_j$. Each restriction is injective because $F$ is, and sends a basis of $W_j$ to $j$ independent vectors in the $j$-dimensional space $W_j$; these form a basis. Hence $F(W_j)=W_j$ and also $F^{-1}(W_j)=W_j$. Thus $F$ and $F^{-1}$ induce mutually inverse operators on every $W_j/W_{j-1}$. Choose $b_j\in W_j\setminus W_{j-1}$ successively. Their images generate the one-dimensional successive quotients, so $b_1,\ldots,b_j$ is a basis of $W_j$. On the $j$th quotient the induced operator is multiplication by a scalar $\alpha_j$, nonzero because it is invertible. This argument allows repeated eigenvalues and nonzero off-diagonal entries.

Original cited statements: p-linear-triangular.

### Original step 4: lem-zl-automorphism-flag-finite-coefficients

Choose an $E_0$-basis of $V_0$. Let $B$ be the change-of-basis matrix whose columns are the adapted vectors $b_j$ in this basis after extension to $\Qlb$. Enlarge $E_0$ to a finite field $E\subset\Qlb$ containing all entries of $B$, $B^{-1}$ and the matrices of $F$ and $F^{-1}$ in the adapted basis. Such an extension is finite: every one of these finitely many entries is algebraic over $\mathbf Q_\ell$, and adjoining them successively multiplies finitely many finite degrees. Put $W_{j,E}=\operatorname{span}_E(b_1,\ldots,b_j)$ inside $V_0\otimes_{E_0}E$. The triangular matrix equations for $F$ and $F^{-1}$ hold over $E$ because they hold in its containing field $\Qlb$. They preserve every $W_{j,E}$; the scalar on $W_{j,E}/W_{j-1,E}$ is $\alpha_j\in E^\times$. The coordinate inclusion and quotient maps, and the bases exhibiting their exact sequences, are now all over this same $E$.

Original cited statements: def-weil-algebraically-closed-coefficients.

### Original step 5: lem-zl-point-equivariant-diagram-lift

At this finite stage use the heart equivalence in step 2 to choose heart objects $M_j$ with specified fibres $W_{j,E}$, taking $M_d=M\otimes_{E_0}E$. Write $A_j=F|_{W_{j,E}}$ under these identifications. Let $\iota_{M_j}:\operatorname{Fib}_s(M_j)\to\operatorname{Fib}_s(Lg_s^*M_j)$ be the specified point transport. It is an isomorphism. Full faithfulness of the point-fibre equivalence lifts the map $A_j\circ\iota_{M_j}^{-1}$ uniquely to a map $\theta_j:Lg_s^*M_j\to M_j$; it lifts its inverse as well, so faithfulness gives the two inverse identities. Pullback along the scheme automorphism $g_s$ commutes with constructible truncations, hence both source and target are in the heart. Thus $(M_j,\theta_j)$ is an actual constructible $E$-Weil sheaf. For $j=d$, the equation $F=\operatorname{Fib}_s(\theta)\circ\iota_M$ in the definition of local Frobenius shows that this is exactly the original Weil structure after scalar extension, not a separately chosen automorphism.

Original cited statements: lem-weil-point-fibre-equivalence, lem-a1-point-realization-standard-cohomology, lem-weil-frobenius-cohomology-transport-iso, def-weil-frobenius-point-transport, prop-constructible-truncations, def-weil-local-frobenius-trace, def-weil-weil-sheaf-complex.

### Original step 6: lem-zl-point-equivariant-diagram-lift

Lift each vector inclusion $u:W_{j-1,E}\to W_{j,E}$ by full faithfulness. It is a monomorphism and its cokernel has the prescribed quotient fibre by the exact heart equivalence of step 2. Naturality of point transport says $\operatorname{Fib}_s(Lg_s^*u)\iota_{M_{j-1}}=\iota_{M_j}\operatorname{Fib}_s(u)$. Combining this with $A_ju=uA_{j-1}$ and the formula in step 5 gives $\operatorname{Fib}_s(u\theta_{j-1})=\operatorname{Fib}_s(\theta_j Lg_s^*u)$; faithfulness proves Weil equivariance. For the cokernel $Q_j$, define its Weil isomorphism by lifting the induced quotient automorphism composed with $\iota_{Q_j}^{-1}$, just as in step 5. The same equation with the quotient projection makes that projection Weil equivariant. Therefore the lifted sequence is short exact in the underlying constructible heart, with the required Weil structures. Composition of the lifted inclusions makes $M_j$ a Weil subobject of $M_d$; pass to $\Qlb$ and identify the endpoint with $\mathcal F$. All these constructions and inverse maps were made at the single field $E$. After extension to $\Qlb$ the adapted coordinate bases still exhibit exact vector-space sequences; the same point equivalence and cohomology comparison at the common stage reflect their exactness in the common-stage heart.

Original cited statements: lem-weil-point-fibre-equivalence, lem-a1-point-realization-standard-cohomology, lem-weil-frobenius-point-transport-natural, lem-weil-frobenius-cohomology-transport-iso, def-weil-weil-sheaf-complex.

### Original step 7: retained elementary assembly

The unique closed point of $\operatorname{Spec}k_0$ has residue cardinality $q$. The specified fibre and point-transport identifications give local Frobenius $\alpha_j$ on the quotient, by the defining composite of local Frobenius and step 5. Since $\iota$ is a field isomorphism and $\alpha_j\ne0$, the number $r_j=|\iota(\alpha_j)|$ is positive. Put $w_j=2\log(r_j)/\log(q)$. Since $q>1$, $\log(q)>0$, and the positive real power convention gives $q^{w_j/2}=\exp((\log(r_j)/\log(q))\log(q))=r_j$. The purity definition therefore makes the quotient punctually $\iota$-pure of weight $w_j$. The finite Weil filtration constructed above is exactly the mixedness filtration of that definition (and, when a bound is wanted, take the maximum of its finitely many weights).

Original cited statements: def-weil-local-frobenius-trace, def-weil-punctual-weights, def-weil-real-power, def-wf-positive-real-logarithm.

### Original step 8: retained elementary assembly

If $d=0$, the faithful heart equivalence identifies $\mathcal F$ with zero; take the empty filtration with its sole endpoint $0=\mathcal F$. There are no quotient or weight conditions to check. For a finite extension of $k_0$, carry out the same construction with that finite field as the base datum and its cardinality $q'$ in the logarithmic calculation. The point equivalence, the natural invertible point transports, and the truncation assertions are stated for every finite-field datum, so the proof has the same hypotheses. No step imposed reality, diagonalizability, or semisimplicity.

Original cited statements: lem-weil-point-fibre-equivalence, def-weil-punctual-weights.

## What could not be finished

Nothing in the authorized stage-1 repair. The three new nodes intentionally await independent splitting. No Lean was written and no compiler, Lake or build tool was run.

## Dry-run repair

The first required deliver.py --no-push completed with one gate failure: the coefficient-flag node cited no definition node. I opened and added the existing def-weil-algebraic-closure, def-pc-field-tower, def-weil-finite-dimensional-subspace, def-weil-vector-space-dimension and def-weil-vector-space-scalar-extension statements at the notions they actually define. No mathematical hypothesis or conclusion changed. Its citations.json quote was refreshed verbatim.
