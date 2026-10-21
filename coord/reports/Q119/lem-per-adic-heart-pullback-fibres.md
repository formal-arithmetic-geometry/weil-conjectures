# Worker report: lem-per-adic-heart-pullback-fibres

1. Files written: `dag/nodes/sec-deligne-laumon-a1/lem-per-adic-heart-pullback-fibres.json`: unchanged statement, five-step assembly, status split. `citations.json` contains all eleven parent step/node citation pairs.

- `dag/nodes/sec-deligne-laumon-a1/lem-per-adic-common-stage-truncations.json`: statement, status unsplit, no Mathlib match.

- `dag/nodes/sec-deligne-laumon-a1/lem-per-adic-stratified-pullback-texact.json`: statement, status unsplit, no Mathlib match.

- `dag/nodes/sec-deligne-laumon-a1/lem-per-adic-normalized-fibre-exactness.json`: statement, status unsplit, no Mathlib match.

- `dag/nodes/sec-deligne-laumon-a1/lem-per-adic-normalized-fibre-comparisons.json`: statement, status unsplit, no Mathlib match.

2. Attachments: none. The library search under `lean/WeilConjectures/` found finite/discrete stalk and integral exactness infrastructure, not the whole statement. The recorded `lean/Sheaf/Paper/AdicHeartIntrinsicFibres.lean:313` theorem assembles an imported theorem with `sfAdicCommonFiber_exists`; the latter has `sorry` at line 291. It is therefore not evidence of a completed attachment. The explicit instruction to re-split the live reviewed node is respected.

3. WANTED: none. Bhatt–Scholze and the current blueprint are present locally.

4. Fault repaired: the human returned this item because its 14-step proof had 14,832 characters and concentrated too much work in one item. The sandbox initially had only `.brief2`–`.brief5`, no report, nodes or search log. I copied the current live node, retaining all its fields and its statement. This is a real re-split, not a rebase or unchanged push. No target, chapter, unit, Lean file or launcher file is changed.

5. Unfinished work: precisely the four separately queued arguments below, intentionally delivered statement-only for other stage-1 workers. Each has `proof: []`, `proof_deps: []`, `proof_origin: null`, a self-contained statement, source, blueprint origin and four actually executed Mathlib searches. Nothing is being claimed proved in Lean.

## Repair allocation

The parent retains the finite-type-to-Noetherian/dimension check and the immediate cohomology/exact-heart consequences of existing integral, localized and continuous realization nodes (returned steps 1–2). Creating another realization node would duplicate existing statements. Its four new inputs allocate the remaining twelve steps without discarding an argument:

| New statement-only node | Returned steps | Original argument characters | Work assigned |
| --- | --- | ---: | --- |
| lem-per-adic-common-stage-truncations | 3–5 | 2858 | Finite-free scalar exactness, coherent truncation descent, t-structure axioms and common-stage heart identification. |
| lem-per-adic-stratified-pullback-texact | 6–8 | 3022 | Completed integral preservation and localization, finite-free stratum calculation, bounded devissage and exact heart restriction. |
| lem-per-adic-normalized-fibre-exactness | 9–11 | 3576 | Normalized local lattices and fractional morphisms, exactness via representation kernels/cokernels, conservativity and detection. |
| lem-per-adic-normalized-fibre-comparisons | 12–14 | 3465 | Finite quotient pullback and scalar comparison, common-stage fibre descent and exactness, geometric-point independence and constructible rank loci. |

The parent assembly is 2248 characters, below 3,000. The four new tasks have comparable argument sizes; none restates the full theorem. Their statements expose the normalization, equations and hypotheses needed to recover the allocated arguments. The full returned arguments are preserved below, rather than replaced by terse summaries.

## Sources and searches

I read Bhatt–Scholze, *The pro-étale topology for schemes*, locally with `pdftotext`: Lemma 6.8.2 (continuous completed coefficients), Definition 6.8.3 and Proposition 6.8.4 (lisse coefficients, integral systems, full faithfulness and etale-local lattices), Corollary 6.8.5 and Lemma 6.8.7 (kernel/cokernel and constructible exactness), Definitions 6.8.6/6.8.8/6.8.10 and Proposition 6.8.11 (stratified sheaves and bounded derived structures), Proposition 6.8.14 (rational realization and finite coefficients), and Remark 6.8.15 (derived module pullback). The new nodes' source places distinguish these arguments. Coherent pair-category truncation assembly and the extra normalization equations are consequences spelled out in the returned argument, not quotations of a single source theorem. No SGA source or trace route is used.

The current blueprint read is `literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-smooth-pullback-t-exact.md` and its `.proof.md`. Its first paragraph uses exact ordinary pullback and the support-preimage assertion. These coefficient-level tasks supply that paragraph; they do not alter the smooth relative-dimension or duality route. The chapter and unit records were read; this item is not their key node and neither record is edited.

Before creating nodes I searched the entire DAG by titles, statements and the source places 6.8.4/6.8.7/6.8.14, including normalized fibres, rational hearts, common-stage t-structures, pullback t-exactness, ranks and continuous realization. `tools/blueprint_refs.py ancestor` confirmed the ancestor `lem-per-smooth-pullback-t-exact`. Blueprint searches were run for `t-structure`, `fibre`, `lisse`, `scalar extension`, `common-stage truncation`, `geometric coefficient fibres`, `rank loci`, `continuous rational realization`, `truncations`, `lisse geometric`, `locally constant rank`, `completed pullback` and `fibre functors`. An exact search for all four new ids in DAG and Lean found none. The nearest relevant existing statements are distinguished below. A finite-field-only result was not silently applied over arbitrary k.

`search-plan.json`, `search-results.json` and `searches.jsonl` retain the actual commands/results. Each new node has its own distinct LeanFinder and LeanSearch phrasing, a Loogle query and Mathlib-source grep, all through the required `msearch.py Q119 lem-per-adic-heart-pullback-fibres` command. All services returned successfully. I read the resulting names and signatures: t-structure truncation constructors do not prove coherent finite-coefficient descent; ordinary module pullback is not completed constructible adic t-exactness; a point of an arbitrary topos does not construct normalized adic fibres or their conservativity; module rank-at-stalk and scheme-fibre facts concern other objects. Hence no exact or one-line Mathlib specialization was found. There are zero new Mathlib leaves. No unavailable service is reported as a negative result.

## Not duplicates

lem-per-adic-common-stage-truncations vs prop-weil-localized-tstructure: the latter states localization at one finite field, whereas the new task proves finite-scalar t-exactness, coherence of truncations and the bounded structure on the common-stage pair category.
lem-per-adic-common-stage-truncations vs lem-sbc-coherent-pair-functor-descent: generic coherent functor descent does not verify finite-coefficient t-exactness, orthogonality, bounds or the common-stage heart; the new task applies that tool and checks those axioms.
lem-per-adic-stratified-pullback-texact vs lem-a1-constructible-pullback-t-exact: the existing result fixes k to an algebraic closure of a finite field and its prescribed point category; the new statement covers an arbitrary field and the raw continuous realization with local finite-free calculations.
lem-per-adic-stratified-pullback-texact vs lem-per-continuous-rational-derived-realization: realization identifies completed pullback with derived module inverse image; it does not establish that this inverse image is t-exact on constructible objects or performs the bounded heart devissage.
lem-per-adic-normalized-fibre-exactness vs lem-per-lisse-completed-system-comparison: lisse integral/rational comparison and full faithfulness do not themselves extend local fibre prescriptions over a stratified constructible heart, or identify its exact sequences with representation kernels and cokernels.
lem-per-adic-normalized-fibre-exactness vs def-pod-lisse-adic-fibre-functors: the latter defines functors for already lisse system categories; the new task proves independence from local stratifications/charts/lattices and exactness/detection for the whole continuous constructible rational heart.
lem-per-adic-normalized-fibre-exactness vs lem-dl-a1-constructible-fibres-exact: the existing assertion has a fixed finite-field geometric setting and specified point-fibre category; the new task constructs normalized lattice fibres over arbitrary k without a global lisse lattice.
lem-per-adic-normalized-fibre-comparisons vs det-lem-stratified-lattice-rank: rank loci of a lisse condensed module do not compare actual completed pullback with normalized finite-level stalk maps, establish scalar-limit equations or descend those fibres to the raw common-stage heart. The new task also identifies those normalized fibre dimensions with lisse ranks.
lem-per-adic-normalized-fibre-comparisons vs lemma-openclosed-stalk-upperstar: ordinary etale-sheaf stalk comparison is only the finite-level input; the new task proves compatibility with normalized transitions, limits, rationalization, scalar associators and common stages, and identifies the rank loci for these fibres.

The sources of the new nodes are Bhatt–Scholze places, not Stacks tags. The source-specific same-Stacks-tag comparison requirement therefore creates no additional pairs. All four share the parent's broader coefficient source intentionally: their distinct arguments are the purpose of this human-requested re-split.

## Review by Q119

I checked the five node JSON files against the opened sources and the return request. The parent statement is byte-for-byte the live returned statement, including the raw (no Karoubi envelope) rationalizations, derived-complete integral data with etale-origin witnesses, arbitrary base field and the noncanonical nature of geometric-point independence. No hypothesis is added to make a proof easier. The four new statements introduce k, X, ell and the finite fields, completed rings and categorical presentations independently. References to earlier new nodes specify the standard structure or the fibre prescription, not unintroduced geometric objects. They contain conclusions only, without proof sketches or hidden `proof_deps`.

Parent step 1 cites the actual statements of `lem-weil-pbc-finite-type-over-noetherian` and `lem-fin-finite-type-fibre-dimension-bound`: a field spectrum is a one-point Noetherian quasi-compact base, and its sole scheme fibre is the original scheme. Thus their hypotheses hold and supply exactly Noetherianity and finite dimension. `prop-weil-pbc-integral-tstructure` states ambient canonical truncations, and `prop-weil-localized-tstructure` states t-exact localization and both natural truncation comparisons. Composing these with the shift gives the asserted cohomology formula. `def-weil-pbc-rational-category` gives localized Hom modules, so an identity killed by a uniformizer power is zero after localization; bounded truncation then puts an object with off-zero torsion cohomology in the heart. `lem-per-continuous-rational-derived-realization` explicitly identifies this localized heart with continuous constructible module sheaves. `det-lem-coefficient-heart-closure` explicitly says it is abelian and its inclusion is exact. I do not use the definition of a rational category as a substitute for a t-structure theorem.

Parent step 2 takes scalar t-exactness, functorial truncations, descended maps/triangles, boundedness and the isomorphism-closed heart from the new `lem-per-adic-common-stage-truncations`. Its statement says each of these. Its allocated proof is returned steps 3–5: finite-free completed scalar tensor, canonical truncation comparisons and their associator equations, Hom orthogonality in a filtered colimit, the truncation triangle, finite bounds and passage to one finite enlargement for finitely many cohomology identities. This does not assume a non-small unspecified colimit; it uses exactly the finite-subextension pair category of the existing definition. The node only depends in its statement on existing coefficient and t-structure notions, never on the parent.

Parent step 3 takes the actual completed integral preservation, rationalization, common-stage exactness and local finite-free degree-zero calculation from `lem-per-adic-stratified-pullback-texact`, all expressly in its statement. Returned steps 6–8 remain its assigned argument: integral witnesses and coherent scalar maps are retained; strata are fibre products Y times_X S, with empty ones permitted; finite free complexes give the K-flat chart calculation; restriction and stratum detection kill other cohomology; finite bounded truncation induction gives t-exactness and triangle/short-exact correspondence gives exact heart restriction. There is no assumption that an arbitrary coefficient-ring map is flat, or that a scheme map factors through a stratum merely from its set image.

Parent step 4 takes the precise lattice-limit formula, fractional map normalization, choice independence, exactness and detection from `lem-per-adic-normalized-fibre-exactness`. Its statement includes each property; it is not just a definition of lisse sheaves. Returned steps 9–11 allocate the nontrivial descent of local lattice choices and rational morphisms, followed by exactness on common connected lisse charts. Bhatt–Scholze 6.8.4(6) supplies etale-local lattices, not a global lattice. The existing local lattice statement likewise supplies one object/point at a time, so finite lists use fibre-product refinements. Including lisse kernels and cokernels among the model objects is retained: this is what identifies the representation exact sequence with the original continuous-sheaf one. Joint conservativity uses exactness and constructible kernels/cokernels; it is not an assertion that geometric points detect every sheaf on the pro-etale topos.

Parent step 5 takes the two displayed comparisons, their coherence and common-stage descent, exactness/conservativity, and rank conclusions from `lem-per-adic-normalized-fibre-comparisons`. The statement explicitly includes quotient-transition compatibility, actual completed pullback, successive scalar extensions and their associators, the commuting pullback/scalar square, finite rank loci and noncanonical underlying-point independence. Returned steps 12–14 remain assigned here. Naturality of the finite etale stalk comparison supplies equality of transition squares before the inverse limit; the finite integral scalar-limit calculation precedes inversion of the uniformizer. At common stages, finite diagrams descend to one field and field extension is faithfully exact on finite-dimensional vector spaces. On a connected etale lattice chart the representation has one dimension; etale maps are open, so the dimension is locally constant on the stratum, and quasi-compactness makes its image finite. The old proof's reference to a later-numbered scalar step is resolved by placing these tasks in this single statement, rather than leaving a circular proof order.

For each new node I checked its source place as listed above: truncation node against 6.8.11 and 6.8.14; pullback node against 6.8.2/6.8.6/6.8.8/6.8.14/6.8.15; fibre node against 6.8.4/6.8.5/6.8.7; comparison/rank node against 6.8.3/6.8.4/6.8.6/6.8.14/6.8.15. These support the unchanged route and the allocated explicit arguments. The exact requested coherence is recorded in the new statements for later workers, not falsely attributed to a source theorem that only states a weaker result.

Edge checks: X or Y empty gives vacuous geometric-point assertions and zero fibres; rank zero gives the zero free system and zero vector space; identity g and E=L give identity maps under the specified normalizations; ramified L/E uses the normalized quotient scalar system and inversion of its own uniformizer rather than identifying quotient indices; disconnected strata may have different ranks and are refined by clopen rank loci. A shifted torsion integral object may enter the rational heart after localization, so I retained isomorphism-closed rational classes and did not require all integral representatives to be concentrated in degree zero. Algebraically closed extensions Omega of arbitrary size affect neither finite-level stalk comparisons nor finite fibre dimensions, and no canonical isomorphism between two arbitrary geometric points is claimed.

Every parent citation was checked against the statement actually delivered or the current existing node, and `citations.json` quotes its words verbatim. Every non-elementary step has its input nodes. No parent step is marked elementary to conceal work. No step exceeds 2,000 characters, and the total is below 3,000. No new node cites the parent or a downstream consumer; the standard structure, pullback and fibre inputs are assembled in an acyclic order. The report records the cross-unit generic infrastructure through `split_report.tool_uses`, while maintainer-owned fields remain untouched.

## Second reading by Q119

This heading records my own direct-delivery rereading of the files and sources described above, not a claim that a second worker or agent reviewed them. The brief explicitly authorizes direct delivery and forbids starting agents. The maintainer's independent review remains the next human/project review.

## Full returned arguments, allocated without loss

These are the 14 returned proof steps, including their dependency lists, for the next workers to reuse. They are kept here because the new nodes must carry statements only. Steps 1–2 are assembled from existing results in parent step 1; steps 3–14 are assigned to the four new nodes as shown. One pre-existing typographical control character before `arpi` in returned step 9 is displayed as `[U+000B]` below; the new statements correctly use `\varpi_E`. `returned-proof.json` in the sandbox retains the original bytes of all JSON text values.

### Returned step 1 → parent step 1, existing rational/continuous realization inputs

The schemes $V,T$ are Noetherian by [lem-weil-pbc-finite-type-over-noetherian], applied to their structure maps to the one-point Noetherian scheme $\operatorname{Spec}k$. They are finite-dimensional by [lem-fin-finite-type-fibre-dimension-bound], whose bound on the sole fibre of either structure map is a bound on the scheme. The assumed unit $\ell\in k$ remains a unit in every local ring. Thus [prop-weil-pbc-integral-tstructure] and [prop-weil-localized-tstructure] apply, giving the integral and rational t-structures and the rational heart exactly as stated. Composing the two truncation comparisons of the latter theorem with the shift identifies the rational degree-$r$ cohomology of $QL$ with $Q\mathcal H^r(L)$, since the integral truncations are the ambient ones. These are isomorphism-closed classes; no assertion about the vanishing of the cohomology of every integral representative is made. If the finitely many nonzero ambient cohomology sheaves outside degree zero are killed by powers of $\varpi$, their images under $Q$ are zero: their identities become zero in the localized Hom groups of [def-weil-pbc-rational-category]. The localized cohomology formula and bounded truncation triangles then put $QL$ in the rational heart, as asserted.

Inputs: lem-weil-pbc-finite-type-over-noetherian, lem-fin-finite-type-fibre-dimension-bound, prop-weil-pbc-integral-tstructure, prop-weil-localized-tstructure, def-weil-pbc-rational-category.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Proposition 6.8.11(3) and Proposition 6.8.14(2); integral and localized standard t-structures.

### Returned step 2 → parent step 1, existing rational/continuous realization inputs

Use [lem-per-continuous-rational-derived-realization] on each $W=V,T$. Write $B_W=\widehat{\mathcal O}_{E,W}$ and $E_W=B_W[1/\varpi]$. Its equivalence $J_W$ identifies the rational heart with the constructible continuous $E_W$-module sheaves. The coefficient sheaves are the continuous ones in [det-lem-coefficient-heart-closure], whose kernels and cokernels of constructible sheaf maps are constructible and whose inclusion in all module sheaves is exact. Thus exactness in this heart is precisely ordinary sheaf exactness in this model. This comparison uses completed coefficient sheaves; it never replaces $E_W$ by the discrete constant sheaf of $E$.

Inputs: lem-per-continuous-rational-derived-realization, det-lem-coefficient-heart-closure.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Definitions 6.8.6 and 6.8.8, Lemma 6.8.7 and Proposition 6.8.14(2).

### Returned step 3 → lem-per-adic-common-stage-truncations

For $E\subset L$, [lem-weil-finite-free-completed-scalar-comparison] identifies integral scalar extension with ordinary derived tensor by a finite free completed coefficient module. After choosing a basis only to check exactness, the underlying tensor functor is a finite direct sum and hence is exact. By [lem-sp-exact-functor-preserves-homology] it preserves the cohomological halves. The integral constructible restriction and its exact rationalization are the functors of [prop-weil-pbc-scalar-extension], which applies under Step 1's general Noetherian finite-dimensional hypotheses. Since rational halves are isomorphism closures of integral halves, rational scalar extension is t-exact. The comparison theorem [lem-pod-texact-truncation-comparison] gives its natural truncation comparisons. Its identity, composition and natural-transformation clauses make them compatible with the scalar associators and their unit and pentagon equations of [prop-weil-pbc-scalar-extension]. Cohomology, the indicated composite of truncations and a shift, has the same compatibility.

Inputs: lem-weil-finite-free-completed-scalar-comparison, lem-sp-exact-functor-preserves-homology, lem-pod-texact-truncation-comparison, prop-weil-pbc-scalar-extension.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Propositions 6.8.11 and 6.8.14, finite extension of coefficient fields.

### Returned step 4 → lem-per-adic-common-stage-truncations

For $\overline{\mathbf Q}_\ell$, descend each of the two truncation functors and its maps by [lem-sbc-coherent-pair-functor-descent], using Step 3's scalar comparisons. The source pair category and its distinguished triangles are exactly [def-weil-pbc-qbar-category]. Its scalar diagram is the one with associators in [prop-weil-pbc-scalar-extension], so the descent hypotheses hold. The formula sends $(E,K)$ to $(E,\tau_E K)$ and a common-stage arrow to its truncation conjugated by those comparisons. The theorem supplies independence of representatives, functoriality and descent of the truncation maps and their equations. Distinguished truncation triangles are represented by the finite-stage triangles.

Inputs: lem-sbc-coherent-pair-functor-descent, def-weil-pbc-qbar-category, prop-weil-pbc-scalar-extension.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Proposition 6.8.14 and the prescribed common-finite-stage category; functorial descent of truncations.

### Returned step 5 → lem-per-adic-common-stage-truncations

These are the asserted bounded t-structure classes. Indeed shifting a representative proves the shift inclusions in [def-weil-t-structure]. For objects in degrees $\le0$ and $\ge1$, pass to a common coefficient field. Every further extension preserves these bounds by Step 3, so every Hom group in the directed system is zero by finite-stage orthogonality. Its colimit is the common-stage Hom group by [def-weil-pbc-qbar-category], hence zero. Step 4 supplies the truncation triangle with its required end bounds. Each object already has two finite bounds at its field of definition. This proves the three axioms and boundedness. Their intersection is the isomorphism closure of finite-stage heart objects: for an object in the intersection its finite-stage nonzero-degree cohomologies become zero at a single further stage (there are only finitely many degrees); at that stage it is isomorphic to its degree-zero cohomology. Here being zero in the filtered Hom colimit means the identity becomes zero at a further stage. This also proves the stated description of the heart.

Inputs: def-weil-t-structure, def-weil-pbc-qbar-category.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Common-stage t-structure axioms and boundedness, written out from the finite-stage structures.

### Returned step 6 → lem-per-adic-stratified-pullback-texact

The completed integral pullback preserves shifts and distinguished triangles by [lem-cbc-completed-pullback-triangles]. By [lem-a1-integral-pullback-completed-comparison] and [lem-pur-integral-operations-preserve-constructible](1), it preserves the integral constructible categories, including the finite reduction witnesses. Its $A$-linear action therefore extends to an exact functor on raw rationalizations by [lem-pur-semilinear-scalar-localization]. The comparison with finite coefficient extension is [lem-pur-integral-operations-scalar-extension], transported through the same completed-pullback comparison and extended on fractions by that localization lemma. Its unit and tower equations persist. Thus [prop-weil-pbc-descent-functors] gives the exact triangulated common-stage pullback as well. This proves the exact triangulated functor clause at both field stages, before proving preservation of the hearts.

Inputs: lem-cbc-completed-pullback-triangles, lem-a1-integral-pullback-completed-comparison, lem-pur-integral-operations-preserve-constructible, lem-pur-semilinear-scalar-localization, lem-pur-integral-operations-scalar-extension, prop-weil-pbc-descent-functors.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Lemmas 6.5.9 and 6.8.2, Proposition 6.8.14 and Remark 6.8.15; exactness and scalar-compatible completed pullback.

### Returned step 7 → lem-per-adic-stratified-pullback-texact

Let $\mathcal F$ be in the $E$-heart, represented under $J_T$ by a constructible $E_T$-module $F$. Choose a finite locally closed stratification where $F$ is lisse. On each stratum choose a pro-etale cover trivializing $F$ as $E^r$ with its continuous coefficient sheaf. Pull these strata and covers back to $V$: [lemma-constructible-pullback-stratification] gives a finite locally closed stratification, constructible since $V$ is Noetherian by [def-weil-constructible-subset], and [def-weil-pbc-proetale-site] gives the base-changed covering families. By the composition and restriction comparisons of [lem-per-continuous-rational-derived-realization], the restriction of the actual pullback to each such chart is derived module pullback of the finite free model. A finite free module placed in degree zero is K-flat by [lem-pc-bounded-above-flat-kflat-site]; its derived pullback is therefore the same finite free target module in degree zero, by $b'\otimes e_j\mapsto b'e_j$. Exact restriction commutes with cohomology, and [lem-weil-pbc-noetherian-stratum-detection] now kills every other cohomology sheaf. Hence $Lh^*\mathcal F$ lies in the target heart. This uses fibre-product strata, including empty ones, and needs no flatness assertion about $h^{-1}E_T\to E_V$.

Inputs: lemma-constructible-pullback-stratification, def-weil-constructible-subset, def-weil-pbc-proetale-site, lem-per-continuous-rational-derived-realization, lem-pc-bounded-above-flat-kflat-site, lem-weil-pbc-noetherian-stratum-detection.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Definitions 6.8.6 and 6.8.8, Remark 6.8.15; local finite-free calculation of degree-zero pullback.

### Returned step 8 → lem-per-adic-stratified-pullback-texact

A bounded object is built from its finitely many cohomology objects by truncation triangles. Since pullback is triangulated and preserves the heart by Step 7, induction through these triangles preserves its cohomological interval: each $\mathcal H^j(K)[-j]$ stays in degree $j$, and the two halves are extension-closed by [lem-weil-heart-short-exact-triangles](2),(5). Thus pullback is t-exact at $E$. The common-stage object formula of [prop-weil-pbc-descent-functors] and the isomorphism-closed description in Step 5 show that it preserves both halves and the heart at $\overline{\mathbf Q}_\ell$. A short exact heart sequence is a distinguished triangle by [lem-weil-heart-short-exact-triangles](4); its image is a distinguished triangle of heart objects and hence is short exact. We may therefore write its restriction as $h^*$.

Inputs: lem-weil-heart-short-exact-triangles, prop-weil-pbc-descent-functors.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Bounded truncation devissage after Remark 6.8.15; heart exactness.

### Returned step 9 → lem-per-adic-normalized-fibre-exactness

Define the geometric fibre of $F$ using its lisse stratum. Choose an affine etale integral-model chart at the point by [lem-weil-pbc-continuous-affine-etale-lattice], applied to the continuous coefficient sheaves identified in Step 2. On that chart, [lem-per-lisse-completed-system-comparison] identifies it with a normalized tower $(N_n)$ of finite free etale sheaves, followed by rationalization. Thus its fibre at $\bar t$ is $(\varprojlim_n(N_n)_{\bar t})\otimes_AE$, the prescription of [def-pod-lisse-l-adic-sheaves]. The inverse limit is finite free by [lem-pod-adic-limit-finite-modules](1),(2): the reductions have the constant finite free rank near the point. For finitely many maps choose common charts carrying their source and target lattices; the full faithfulness of the rational realization in [lem-per-lisse-completed-system-comparison] writes each map as an integral map divided by a power of $[U+000B]arpi$. Changing charts or integral models gives the same fibre maps: the fully faithful rational realization identifies both model maps after restricting to a common chart and clearing their denominators, and the normalized tower maps agree at every level. Hence the construction glues naturally and is independent of these choices. At $\overline{\mathbf Q}_\ell$ extend the resulting $E$-space to $\overline{\mathbf Q}_\ell$.

Inputs: lem-per-lisse-completed-system-comparison, def-pod-lisse-l-adic-sheaves, lem-pod-adic-limit-finite-modules, lem-weil-pbc-continuous-affine-etale-lattice.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Proposition 6.8.4(1),(4),(6); normalized coefficient-system construction of fibres.

### Returned step 10 → lem-per-adic-normalized-fibre-exactness

For a short exact sequence in the $E$-heart, take a common connected stratification adapted to its three sheaves using [det-lem-coefficient-heart-common-stratification]. Restriction is exact by its clause (3). Refine by common affine etale integral-model charts from [lem-weil-pbc-continuous-affine-etale-lattice], and then by their connected components. Lattice existence for each of the finitely many objects and fibre-product refinement give a common cover; full faithfulness in [lem-per-lisse-completed-system-comparison] clears the denominators of the finitely many arrows on each quasi-compact chart. On each such chart the rationalized normalized-system category is the lisse $E$-sheaf category of [cor-galois-lisse-representations](2). The representation equivalence is exact, so evaluating the three representations at a geometric point gives a short exact sequence of finite-dimensional $E$-vector spaces. The comparison with the continuous-sheaf category is fully faithful. Include also the lisse kernels and cokernels supplied by [det-lem-coefficient-heart-closure] in the finite list when choosing the model charts. Their universal properties then transport through this fully faithful comparison; they are exactly the corresponding representation kernels and cokernels. Thus the exact sequence being evaluated is precisely the restricted original one. This proves exactness of every fibre functor.

Inputs: det-lem-coefficient-heart-common-stratification, lem-per-lisse-completed-system-comparison, cor-galois-lisse-representations, det-lem-coefficient-heart-closure, lem-weil-pbc-continuous-affine-etale-lattice.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Corollary 6.8.5 and Lemma 6.8.7, representation calculation on common lisse charts.

### Returned step 11 → lem-per-adic-normalized-fibre-exactness

If a heart object has zero fibres everywhere, its continuous-sheaf realization is zero: on any lisse chart the representing $E$-representation has underlying vector space zero, so that local system is zero by [cor-galois-lisse-representations](2) and [lem-per-lisse-completed-system-comparison]. Exact stratum restriction detects zero by [det-lem-coefficient-heart-common-stratification](3). For a heart morphism with all fibre maps invertible, exactness from Step 10 makes the fibres of its kernel and cokernel zero. Both are constructible by [det-lem-coefficient-heart-closure], so both vanish, and the morphism is an isomorphism. This proves joint conservativity. Applied to the image of a morphism, the same argument also detects a zero morphism and, by kernels, images and cokernels, detects exactness of short complexes.

Inputs: cor-galois-lisse-representations, lem-per-lisse-completed-system-comparison, det-lem-coefficient-heart-common-stratification, det-lem-coefficient-heart-closure.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Corollary 6.8.5 and Lemma 6.8.7; zero detection on a finite stratification.

### Returned step 12 → lem-per-adic-normalized-fibre-comparisons

For $\bar v$ and $\bar t=h\bar v$, restrict to the lisse stratum of $\bar t$ and its fibre-product stratum at $\bar v$. Take an integral-model chart as in Step 9 and base change it along $h$. The comparison [lem-per-lisse-completed-system-comparison] identifies module pullback of the lisse model with pullback of its normalized finite etale systems. At each level [lemma-openclosed-stalk-upperstar] gives $((h_n)^*N_n)_{\bar v}\cong(N_n)_{\bar t}$, naturally in $N_n$. These maps commute with the quotient transitions, since the stalk comparison is natural. Taking the inverse limit, then tensoring with $E$, gives $(h^*\mathcal F)_{\bar v}\cong\mathcal F_{\bar t}$. The pullback in this calculation is the actual completed rational one by [lem-per-continuous-rational-derived-realization], not an independently chosen heart functor. The local-model independence of Step 9 makes the comparison global and natural.

Inputs: lem-per-lisse-completed-system-comparison, lemma-openclosed-stalk-upperstar, lem-per-continuous-rational-derived-realization.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Proposition 6.8.4 and Remark 6.8.15; finite etale stalk comparison followed by inverse limit and rationalization.

### Returned step 13 → lem-per-adic-normalized-fibre-comparisons

These constructions commute with finite coefficient extension. On lisse models the comparison [lem-per-lisse-completed-system-comparison] is induced by the finite quotient scalar maps. Clause (3) of [lem-pod-adic-limit-finite-modules] identifies their limits with extension of the finite integral fibre; after inverting the uniformizer this is $F_{\bar t}\otimes_E L$. The tensor and stalk comparison of [lem-pod-lisse-tensor-and-scalar-extension](3) and the transition compatibility in Step 12 ensure that the two routes through a finite extension give the same map on pure tensors, hence the same map. Their identity and composition equations persist. Each finite list of objects, arrows and equations in the common-stage category is represented after a finite enlargement by its definition [def-weil-pbc-qbar-category]. Exactness at $\overline{\mathbf Q}_\ell$ therefore follows from Step 10 and exactness of vector-space extension; detection follows since extension of fields reflects a nonzero finite-dimensional vector space (a basis remains a basis). This proves the common-stage exactness, conservativity and all scalar-compatibility assertions.

Inputs: lem-per-lisse-completed-system-comparison, lem-pod-adic-limit-finite-modules, lem-pod-lisse-tensor-and-scalar-extension, def-weil-pbc-qbar-category.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Proposition 6.8.14; normalized finite-stage scalar comparisons and their common-stage descent.

### Returned step 14 → lem-per-adic-normalized-fibre-comparisons

At each point choose an affine etale chart with an integral model by [lem-weil-pbc-continuous-affine-etale-lattice], and identify its normalized local-system model by [lem-per-lisse-completed-system-comparison]. On a connected component of that chart, [cor-galois-lisse-representations](2) identifies its fibres with vector spaces of the one fixed representation, hence with a fixed dimension; every geometric point over a fixed underlying point gives that dimension. The same holds for all choices of algebraically closed field, because the finite etale fibres and their pullback comparisons are [lemma-openclosed-stalk-upperstar]. Since [lem-weil-pbc-etale-morphism-open-map] says etale charts are open, these local ranks descend to a locally constant rank function on each lisse stratum. Thus two geometric fibres over the same point are isomorphic vector spaces, without a claimed canonical choice of isomorphism. Each Noetherian stratum is quasi-compact, so this locally constant function takes finitely many values; refine by its clopen rank loci. The finitely many positive-rank strata form the nonzero-fibre locus, a constructible subset by [def-weil-constructible-subset]. At $\overline{\mathbf Q}_\ell$ use a common finite coefficient model and Step 13: scalar extension preserves each rank and the zero-rank locus. This proves the final stratification, rank and constructibility clauses.

Inputs: lem-per-lisse-completed-system-comparison, cor-galois-lisse-representations, lemma-openclosed-stalk-upperstar, lem-weil-pbc-etale-morphism-open-map, def-weil-constructible-subset, lem-weil-pbc-continuous-affine-etale-lattice.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Definitions 6.8.3 and 6.8.6, Proposition 6.8.4; ranks and nonzero loci.
