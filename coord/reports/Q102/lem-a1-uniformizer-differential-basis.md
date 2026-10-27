# Worker report

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-a1-uniformizer-differential-basis.json: existing statement, re-split into two assembly steps; unchanged statement and stmt_deps.
- dag/nodes/sec-deligne-laumon-a1/lem-a1-smooth-curve-closed-stalk-structure.json: new statement-only node, status unsplit; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-a1-dvr-separable-residue-differential-basis.json: new statement-only node, status unsplit; no Mathlib match.
- citations.json: full verbatim statement quotations for all three assembly citations.

## Attachments

None. The project's uniformizer_differential_basis in lean/Sheaf/AlgebraicGeometry/Curve/UniformizerDifferentialBasis.lean:73 ends in sorry. Searches of the blueprint tag and uniformizer/differential concepts under lean/WeilConjectures found no complete project declaration for the item or the new statements.

## Wanted literature

None.

## What was wrong and what changed

The released stage-1 repair note of 2026-10-22 explicitly reopens the reviewed split. The original six-step proof carries too much work for one worker. The sandbox at resumption contained only dispatcher markers; no retained node, report or earlier search log existed, so I continued from the current live node, including its reviewed correction to Step 5. The existing Lean statement and all upstream/blueprint metadata are retained. No Lean file, compiler, library build or repository mutation was used.

The two independent work items have comparable original argument sizes: geometry receives Steps 1–3 (2670 characters); local algebra receives Steps 4–6 (2064 characters). The geometric lemma does not assume residue separability and gives dimensions, regularity, DVR structure and arbitrary differential rank, with no particular uniformizer. The algebraic lemma assumes the DVR structure and differential rank and works with an arbitrary local k-algebra, with no scheme or smoothness hypothesis. Neither restates the entire item. Each new node has an empty proof, empty proof_deps, null proof_origin and status unsplit. The complete arguments below are future-worker handoff material, not proof steps in the new node JSON.

## Original argument retained and allocated

### Old Step 1 → lem-a1-smooth-curve-closed-stalk-structure

First check both meanings of dimension needed below. The curve hypothesis gives $\sup_{y\in X}\dim\mathcal O_{X,y}=1$ by [def-pc-curve, def-pc-dimension]. By [lem-pc-scheme-dimension-local-rings], the topological dimension of $X$ is also $1$. Since $X$ is integral, it is irreducible and has a generic point $\eta$ by [lem-sc-scheme-sober]. The closed point $x$ differs from $\eta$: otherwise $X=\overline{\{x\}}=\{x\}$ would have dimension zero. The strict generalization $x,\eta$ and [lem-sc-scheme-stalk-dimension-generalization-chains] give $\dim A\geq1$, while the supremum defining the curve dimension gives $\dim A\leq1$. Thus $\dim A=1$. Moreover every open neighbourhood $N$ of $x$ contains $\eta$ and the strict chain of irreducible closed subsets $\{x\}\subsetneq N$, so $\dim N\geq1$. Its dimension is at most $\dim X=1$: taking closures in $X$ of a strict chain of irreducible closed subsets of $N$ preserves strictness, as intersecting those closures with $N$ recovers the chain. Consequently $\dim_x X=\min_{N\ni x}\dim N=1$ by [def-kun-dimension].

Cited nodes: def-pc-curve, def-pc-dimension, lem-pc-scheme-dimension-local-rings, lem-sc-scheme-sober, lem-sc-scheme-stalk-dimension-generalization-chains, def-kun-dimension.

### Old Step 2 → lem-a1-smooth-curve-closed-stalk-structure

Choose an affine open $U=\operatorname{Spec}B$ containing $x$, and let $\mathfrak q$ be the corresponding prime. Restricting the smooth structure morphism to $U$ is smooth by [lem-weil-pbc-smooth-restrict-open-subschemes]. By [lem-weil-pbc-smooth-ring-map-iff-smooth-affine], $B$ is a smooth $k$-algebra. The canonical localization identification [lem-weil-pbc-affine-open-stalk-localization] gives $A\cong B_{\mathfrak q}$ as $k$-algebras. Apply [lem-weil-pbc-smooth-over-field-regular-local] to this smooth algebra and this prime: $A$ is regular local, in particular Noetherian. Since Step 1 proved $\dim A=1$, [lem-sc-regular-dim1-dvr] shows that $A$ is a discrete valuation ring. This proves the asserted discrete valuation ring property of $A$.

Cited nodes: lem-weil-pbc-smooth-restrict-open-subschemes, lem-weil-pbc-smooth-ring-map-iff-smooth-affine, lem-weil-pbc-affine-open-stalk-localization, lem-weil-pbc-smooth-over-field-regular-local, lem-sc-regular-dim1-dvr.

### Old Step 3 → lem-a1-smooth-curve-closed-stalk-structure

For $f:X\to\operatorname{Spec}k$, the sole fibre is $X$ itself. Step 1 gives $\dim_x X=1$, so [lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension] supplies an affine open $W=\operatorname{Spec}C$ containing $x$ for which $\Omega_{C/k}$ is free of rank one. (The affine open of the base in that lemma is the nonempty $\operatorname{Spec}k$.) Write $\mathfrak p$ for $x$ in this chart. By [lem-weil-pbc-affine-open-stalk-localization], $A\cong C_{\mathfrak p}$; by [lem-weil-pbc-kahler-differentials-localization], $\Omega_{A/k}\cong(\Omega_{C/k})_{\mathfrak p}$. Localizing an isomorphism $C\xrightarrow{\sim}\Omega_{C/k}$ and its inverse therefore gives an isomorphism $A\xrightarrow{\sim}\Omega_{A/k}$. In particular choose a basis element $e$ of this free rank-one $A$-module. No assertion about the particular differential $dt$ has been made yet.

Cited nodes: lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension, lem-weil-pbc-affine-open-stalk-localization, lem-weil-pbc-kahler-differentials-localization.

### Old Step 4 → lem-a1-dvr-separable-residue-differential-basis

Let $t$ be any uniformizer. By [def-sc-discrete-valuation-ring], $A$ is a local domain, its maximal ideal $\mathfrak m$ is nonzero, and $\mathfrak m=tA$. Hence $t\neq0$ and $t$ is not a unit. Its class in $\mathfrak m/\mathfrak m^2$ is nonzero: if $t\in\mathfrak m^2=t^2A$, write $t=t^2b$ and cancel the nonzero $t$ in the domain to get $1=tb$, contradicting $t\in\mathfrak m$.

Cited nodes: def-sc-discrete-valuation-ring.

### Old Step 5 → lem-a1-dvr-separable-residue-differential-basis

Put $\kappa=A/\mathfrak m=\kappa(x)$. The hypotheses of [lem-weil-pbc-separable-residue-cotangent-injective] hold: $A$ is a Noetherian local $k$-algebra by Step 2; $k\to A$ is injective since $A$ is nonzero and $k$ is a field; and the residue extension $\kappa(x)/k$ is finite separable by assumption. It is finitely generated as a field extension, since any finite $k$-vector-space basis of $\kappa$ generates it as a field. It is separable over $k$ in the sense of [def-weil-pbc-separable-field-extension], (2): every subextension $k\subset K'\subset\kappa$ is algebraic over $k$, so the empty family is a transcendence basis of $K'/k$ [def-weil-pbc-transcendence-basis] (vacuously algebraically independent, with $k(\emptyset)=k$), and $K'/k$ is separable algebraic because every element of $K'\subset\kappa$ is separable over $k$ by [def-weil-pbc-separable-algebraic-extension]; hence $K'/k$ is separably generated. Thus that node gives an injective map $\mathfrak m/\mathfrak m^2\to\Omega_{A/k}\otimes_A\kappa$ sending $a\bmod\mathfrak m^2$ to $da\otimes1$. Applying it to the nonzero class from Step 4 shows $dt\otimes1\neq0$.

Cited nodes: lem-weil-pbc-separable-residue-cotangent-injective, def-weil-pbc-separable-algebraic-extension, def-weil-pbc-separable-field-extension, def-weil-pbc-transcendence-basis.

### Old Step 6 → lem-a1-dvr-separable-residue-differential-basis

Write $dt=ae$ in the basis $e$ chosen in Step 3. Tensoring the basis isomorphism and its inverse with $\kappa$ identifies $\Omega_{A/k}\otimes_A\kappa$ with $\kappa$, carrying $dt\otimes1$ to the residue $\overline a$. Step 5 therefore says $a\notin\mathfrak m$. In a local ring every element outside the maximal ideal is a unit; hence $a$ is a unit. The map $A\to\Omega_{A/k}$, $b\mapsto b\,dt=ba e$, has inverse $ce\mapsto ca^{-1}$. Thus it is an isomorphism, and $dt$ is a basis. Since $t$ was arbitrary this proves the assertion for every uniformizer.

Cited nodes: .

## Searches and blueprint route

Read SETUP's chapter/unit/node distinction, the chapter sec-deligne-laumon-a1, unit sk-thm-dl-a1-upper, GOAL.md, and the main-20261015 lem-a1-finite-map-curve proof, especially its third paragraph. The new nodes remain below its local-parameter calculation and inherit the same chapter and unit. blueprint_refs ancestor returned lem-a1-finite-map-curve; via is [lem-a1-uniformizer-differential-basis]. Whole-blueprint searches for uniformizer, smooth curve, cotangent, uniformizer differential, closed point smooth, discrete valuation ring, cotangent injective and smooth differentials found no equivalent blueprint statement. Whole-DAG searches by tags 0C1E/00TU and parameter/smooth-curve keywords were followed by reading the candidate statements. The more specialized curve-local-ring and vector-field nodes do not cover these statements.

The two new nodes each record LeanFinder, LeanSearch, Loogle and Mathlib-source grep, including a second semantic phrasing. All queries and actual results are retained in searches.jsonl. Read the returned TFAE.lean cotangent-dimension statements (228–247), StandardSmoothCotangent.lean basisKaehler_apply and free/rank results (233–248, 314–318), and Smooth/Local.lean's Jacobian criterion. None specializes in one line to either new node: cotangent dimension does not provide scheme closed-point dimension and differential freeness; presentation bases are for chosen presentation variables, not every uniformizer. Existing item searches are retained, not invented or rerun.

## Not duplicates

lem-a1-smooth-curve-closed-stalk-structure vs lem-sfb-norm-pair-geometric-witness: the existing node concerns normed sections on a smooth proper curve over an algebraically closed field, not local structure over an arbitrary field.

lem-a1-smooth-curve-closed-stalk-structure vs lem-sfb-smooth-derivation-zero-divisor: the existing node is about global vector fields and divisor degree on a proper curve over an algebraically closed field, not the local structure of an arbitrary smooth integral curve.

lem-a1-smooth-curve-closed-stalk-structure vs lem-a1-uniformizer-differential-basis: the new statement supplies only the geometric local structure, without a separability hypothesis or a specified differential basis; the item also proves every uniformizer differential is a basis.

lem-a1-dvr-separable-residue-differential-basis vs lem-sfb-norm-pair-geometric-witness: the existing node concerns orbit norms and a specific differential on a smooth proper curve over an algebraically closed field, not arbitrary DVR k-algebras.

lem-a1-dvr-separable-residue-differential-basis vs lem-sfb-smooth-derivation-zero-divisor: the existing node identifies global vector fields and their zero divisor, whereas the new node is a criterion for every uniformizer in an arbitrary DVR k-algebra.

lem-a1-dvr-separable-residue-differential-basis vs lem-a1-uniformizer-differential-basis: the new statement is a local-algebra criterion assuming a DVR and a rank-one differential module; the item must construct these inputs from a smooth curve.

lem-a1-dvr-separable-residue-differential-basis vs lem-weil-pbc-separable-residue-cotangent-injective: the existing node gives only conormal injectivity for a general Noetherian local algebra; the new statement combines its finite algebraic separability specialization with the nonzero uniformizer class and rank-one unit-coefficient argument to obtain a basis.

Additional keyword candidate lem-sc-smooth-connected-curve-local-rings assumes an algebraically closed ground field and gives valuations, not arbitrary-field local differential rank. lem-weil-pbc-regular-local-separable-residue-smooth is an affine smoothness/regularity equivalence assuming residue separability, not the geometric rank-one result without that assumption.

## Review by Q102

I read curves.tex Tag 0C1E (lemma-uniformizer-works), its full proof, algebra.tex Tag 00TT (lemma-characterize-smooth-over-field, especially its final regularity assertion), Tag 00TU (lemma-computation-differential, statement and proof), Tag 00RT (lemma-differentials-localize, part 2), and morphisms.tex Tag 02G1 (lemma-smooth-omega-finite-locally-free). For the geometric new statement I checked that the first and last sentences of 0C1E require both dimension conventions and differential localization; for the algebraic new statement I checked its finite-separable residue hypothesis really supplies 00TU, and that the final argument uses freeness, not just a rank assertion.

I opened and read the statements of every old cited node. For old Step 1, lem-pc-scheme-dimension-local-rings identifies the supremum with topological dimension, lem-sc-scheme-sober supplies the generic point, and lem-sc-scheme-stalk-dimension-generalization-chains supplies the stalk dimension lower bound. def-pc-curve/def-pc-dimension give the upper bound, and def-kun-dimension gives the neighbourhood convention. Irreducibility makes every nonempty open irreducible, the generic point differs from the closed point, and taking closures preserves the strict chains. The geometric new node explicitly includes both dimensions.

For old Step 2, the restriction lemma really preserves smoothness, the smooth-affine equivalence applies with base Spec k, affine-open-stalk-localization clause (c) supplies the localization compatible with the k-structure, smooth-over-field-regular-local asserts regularity at that prime, and regular-dim1-dvr has the required dimension supplied by Step 1. For old Step 3, the smooth differential rank node uses dimension AT the fibre point, which Step 1 supplies since the unique fibre over Spec k is X. The localization node identifies Omega after localizing, not just some abstract module of equal rank. Localizing a chosen isomorphism and its inverse gives an actual free rank-one basis.

For old Steps 4–6, I retained the cancellation t=t²b => 1=tb in the nonzero domain, and the contradiction with t in the maximal ideal. The injectivity node's Noetherian hypothesis is furnished by regularity/DVR structure; k maps injectively into the nonzero ring A, and its residue algebra is a field extension. A finite vector-space basis generates the residue field as a field. I retained the reviewed distinction between separable algebraic and separable field extensions: every intermediate subfield is algebraic with empty transcendence basis and is separable algebraic. Thus 00TU's node gives exactly the map carrying the nonzero cotangent class to dt tensor 1. Tensoring the chosen basis isomorphism AND its inverse identifies the latter with the nonzero residue of the coefficient a; a is therefore a unit. The explicit inverse ce -> ca^{-1} is preserved. These are the work assigned to the algebraic new node, not an unexplained invocation of Nakayama.

For assembly Step 1, the geometric node's own statement explicitly gives every fact used: Noetherian DVR and a free rank-one differential module. def-weil-residue-field defines kappa(x) as the quotient of this same stalk by its maximal ideal, with its induced k-extension, so the given finite separability is the one the algebraic node requires. For assembly Step 2, that algebraic node's statement explicitly gives the isomorphism for every generator of the maximal ideal, including the inverse; its assumptions are exactly supplied in Step 1. citations.json quotes the actual statements verbatim. No step uses a cited node's internal proof in place of its statement, and all non-elementary assembly facts are cited.

Edge cases checked: A=k[T]_(T), and all unit multiples of T; a nonrational separable closed point (P(T)), where P'(T) is a unit; an arbitrary imperfect base field, for which smoothness alone still gives differential rank one. The closed point assumption is needed for stalk dimension: at the generic point of a curve the local ring is a field. For k=F_p(a), A=k[T]_(T^p-a), the smooth curve's stalk is a DVR and its differentials are rank one but d(T^p-a)=0; its inseparable residue field excludes it from the algebraic lemma and the item, as required. A field itself is excluded by the nonzero maximal ideal in the DVR definition. No perfectness, rationality or algebraic closure has been added to either new statement.

I checked delivery-errors B–E: complete standalone statements with every object introduced, inline residue quotient and cited notions, single TeX escaping, correct tags and labels, genuine logged searches with no fabricated queries, no elementary-only new node, no duplicate, no circular dependence, and no copied clause carrying the whole item. The explicit human order requires these two statement-only work items; the report preserves every old argument rather than deleting it to fit the 3000-character limit. No SGA source is used. Each assembly step is below 2000 characters. The item statement and statement dependencies are unchanged, so no statement dispute or unit-route departure was introduced.

## What remains

The two new nodes are deliberately unsplit for parallel stage-1 work. Their complete inherited argument is retained above. This delivery repairs the requested one-level split; it does not claim Lean proofs for them.
