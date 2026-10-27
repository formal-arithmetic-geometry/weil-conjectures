# Repair delivery: lem-trf-formal-jacobian-quadratic-criterion

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-formal-jacobian-quadratic-criterion.json`: existing statement unchanged; five assembly steps, 2,272 characters in their text, status split.
- `dag/nodes/sec-trace-formula/lem-trf-formal-minimal-presentation-minors.json`: statement, unsplit; no Mathlib match, no proof steps or proof dependencies.
- `dag/nodes/sec-trace-formula/lem-trf-minimal-jacobian-binary-hypersurface.json`: statement, unsplit; no Mathlib match, no proof steps or proof dependencies.
- `dag/nodes/sec-trace-formula/lem-trf-binary-quadratic-model-depth.json`: statement, unsplit; no Mathlib match, no proof steps or proof dependencies.
- `dag/nodes/sec-trace-formula/lem-trf-cotangent-quadratic-relation-invariance.json`: statement, unsplit; no Mathlib match, no proof steps or proof dependencies.
- `citations.json`: every use of every assembly step, with the complete verbatim cited statement.
- `report.md`: this report. `searches.jsonl` and `search-results/` retain the actual search evidence. `returned-node.json` retains the returned input for comparison.

## Attachments

None. The project-wide search in `lean/WeilConjectures/` found no declaration tagged with the item or an exact proof by the relevant notions. The existing `lean/Sheaf/TraceFormula/FormalJacobianQuadraticCriterion.lean` ends its theorem in `sorry`; it cannot be an attachment. No Lean source was changed or compiled.

## WANTED

None. The Stacks source is present locally and supplies the whole route; the semilinear ring-isomorphism calculation is an explicit supplement to its intrinsic quadratic condition.

## What was wrong and what changed

The return asks for genuine distribution of 7,111 characters of argument, not an editorial shortening. The repository copy contains exactly the returned ten-step proof. This sandbox was empty on arrival (no item, report, citations or search log), so I copied that repository item and retained all its metadata. The delivery tool takes current server main as its base and preserves maintainer-owned fields. There is no discarded earlier sandbox attempt. The statement, ancestry, chapter, unit and Lean record remain unchanged. I created four independent, self-contained statement-only nodes. They do not assert an isomorphism to a quadratic model, let alone the three-way criterion; none is the whole item or one of its equivalence clauses.

The allocation is:

- Old steps 1–2 (2,155 characters): `lem-trf-formal-minimal-presentation-minors`. Its task is coordinate elimination plus the identity-block/residual-minor computation. It assumes none of (a), (b), (c).
- Old steps 3–5 (1,606 characters): `lem-trf-minimal-jacobian-binary-hypersurface`. Its task is the embedding-dimension exclusion, principal kernel, and polar-matrix calculation in a minimal presentation. Its conclusion is a power series with nondegenerate quadratic initial term, not a quadratic normal-form isomorphism. The previous node supplies its input but it can be proved in parallel from its self-contained hypotheses.
- Old step 8 (930 characters): `lem-trf-binary-quadratic-model-depth`. Its task is the regular-sequence lower bound, support-dimension upper bound, nonzerodivisor depth drop, and comparison of depths over a quotient. Its statement is slightly more useful: a nonzero binary quadratic suffices, even a degenerate one. Its proof workload uses the same five existing project lemmas as old step 8.
- The cotangent-dimension and semilinear content of old steps 9–10: `lem-trf-cotangent-quadratic-relation-invariance`. Its task is the lift-independent quadratic multiplication map, its semilinear functoriality, its polar determinant transformation, and the explicit principal-kernel computation. Old step 9's principal-kernel application remains assembly step 4. Old step 10's derivative/Nakayama calculation and return from residual minors to the original J remain assembly step 5.
- Old steps 6–7 remain assembly step 3, applying the existing Morse node and forgetting structure.

These workloads are comparable (about 0.9–2.2 thousand characters of the old argument apiece). Each can be assigned to a different worker without waiting for a proof of the other new statements. Their proofs are deliberately empty, as instructed. The original argument is recorded verbatim below so that no reasoning is lost by the redistribution.

## Review by N6

I read `literature/stacks-project/curves.tex`, lines 3824–3960 and 4064–4170, against the tag map: 0C48 is `lemma-reduced-quotient-regular-ring-dim-2`, 0C49 is `lemma-nodal-algebraic`, 0C4B is `lemma-fitting-ideal-well-defined`, and 0C4C is `lemma-fitting-ideal`. The source's elimination, identity block, minor-order bound, two-variable principal kernel and polar calculation are exactly the four stages used here. I also read the chapter and unit records. The inherited nodal ingredient remains below the locality node; there is no proposed change to the unit's or chapter's route. No SGA source is used.

For the first new node, I checked that choosing g from the linear terms of I does not presuppose any of the three conditions. A basis of these terms extended to all variable linear terms gives full F-algebra coordinates by the existing parameter-coordinate theorem. Evaluation at g=0 kills exactly the eliminated-variable ideal; thus the h_j generate the residual H and have no linear terms. The Jacobian block is identity plus residual derivatives. Every (e−1)-minor occurs and larger minors lie in that ideal; e=0,1 yields an actual unit minor. This is the material of old steps 1–2, not just the generic minor-invariance theorem. The first node's conclusion explicitly supplies every output used in assembly step 1, including the quotient isomorphism, basis and the residual ideal.

For the second new node, I checked its convention for e=0,1 and for too few columns. Its hypotheses are genuinely a minimal presentation, depth one and equality of the minor ideal with the maximal ideal. The bound forces e=2 (Nakayama excludes e≥3); the regular-surface depth-one principal result then gives f≠0, and invariance allows replacing the residual generator list by f. Only after this does the matrix of its linear derivative terms show b²−4ac≠0. Assembly step 2 gets precisely these conclusions from its statement. No normalization theorem or any part of the ring-isomorphism converse is hidden in this node.

For the model-depth node, I checked the source's explicit-computation clause and the statements of the five depth/regularity ingredients in the old proof. The ambient series ring is nonzero Noetherian local and a domain, dimension two, its two variables are a regular sequence, and its support as its own finite module is its whole spectrum. Hence depth is exactly two. A nonzero Q in the maximal ideal is a nonzerodivisor; depth drop applies and depth over the quotient identifies the resulting one with ring depth. This does not use nondegeneracy, so the new statement's nonzero-Q hypothesis is sufficient. Assembly step 4 explicitly derives Q≠0 from the item hypothesis before citing it.

For the cotangent-relation node, I checked the discussion preceding 0C49 as well as its conditions (1) and (2). I wrote the quadratic-relation space concretely as the kernel of the map on homogeneous expressions, so no undefined symmetric-square convention is needed. Changing a lift changes a quadratic product only in m³. The abstract ring isomorphism preserves powers of m, induces its own residue-field map σ, and respects multiplication; it need not respect the given coefficient field. Substitution therefore induces a semilinear map on the kernels. In a chosen binary basis the polar matrix transforms to Pᵀσ(B)P, so nondegeneracy is preserved, also in characteristic two. Modulo p³, a multiple of a generator f∈p² has quadratic part just its constant multiplier times f₂; hence the kernel is F f₂, including f₂=0. These assertions appear in the new node's statement, not merely its future proof. Assembly step 4 uses its explicit cotangent-dimension assertion. Step 5 uses its explicit kernel computation, semilinear kernel bijection and polar-determinant transformation.

I opened and read the full statement of every old node still cited by the assembly. In step 3, `lem-trf-formal-binary-morse` supplies a continuous automorphism with α(f)=f₂ under exactly the discriminant hypothesis obtained in step 2. Passing to quotient and preserving maximal-ideal powers is elementary. In step 4, `lem-weil-pbc-power-series-field-cohen-regular-complete` gives regularity and dimension two of S over the field F, and `lem-trf-regular-surface-depth-one-principal` assumes an ideal in the maximal ideal with quotient depth one and gives a nonzero principal generator: these hypotheses have all been established before application. In step 5, `lem-weil-pbc-nakayama-local-generators` applies to the finite maximal ideal, generated by the two residual variables. Its two derivative classes span modulo m² by the displayed invertible polar matrix. `lem-trf-formal-jacobian-minor-invariance` says the fixed-size ideal is independent of the generator list, which is exactly what changing h_j to f needs; it is not being asked to handle a change of number of ambient variables. That latter comparison was explicitly supplied by the first new node. Depth invariance under a ring isomorphism follows directly by identifying maximal ideals and regular sequences. Every one of these citations has a verbatim statement quote in citations.json.

I tested the edge cases rather than assuming characteristic zero. With I=0, the first node has t=0, H=0 and no nonzero minors. With I equal to the full variable ideal, e=0 and a unit (n−1)-minor gives J=R; with e=1 the identity block still yields a unit. In a minimal three-variable quotient, entries of the residual Jacobian lie in m, so its two-minors lie in m² and cannot generate a nonzero finite m. For H=(uv) the binary node yields discriminant one; for H=(u²) the discriminant is zero and the gradient fails to span m (in characteristic two it vanishes). The depth lemma still gives depth one for u², showing why nondegeneracy is a separate question. For f∈(u,v)³, the cotangent kernel in degree two is zero and cannot match the kernel of a nondegenerate quadratic model. For f=uv+higher terms in characteristic two the polar matrix is [[0,1],[1,0]], invertible without dividing by two. A nontrivial automorphism of F acts semilinearly, which the new relation node allows. The original n≥2, I⊆n, and F-field hypotheses all remain in force.

I reviewed B–E of delivery-errors point by point: the four new nodes contain statements only, all objects and conventions are introduced, existing notions have their defining nodes or inline definitions, TeX has single escaping, the source tags and labels were read, no Mathlib leaf was asserted from an approximate hit, all new nodes have ancestry and whole-blueprint searches, and no finished upstream declaration was overlooked in the requested searches. I checked each use against its statement (C4), the union of uses against proof_deps, and the assembly for unrecorded non-elementary claims (C1). The two elementary manipulations in the final step are the written derivative linear-term computation and scalar-square determinant change; the deeper kernel identification and all invariance assertions have cited nodes. None of the five assembly steps exceeds 2,000 characters. The source needs no correction, and the item statement needs no dispute.

## Mathlib and duplicate search evidence

For each of the four proposed statements I ran leanfinder, Loogle, grep and leansearch using msearch.py, and then a second semantic phrasing. The complete results are retained in search-results and the exact queries and digests in searches.jsonl and the node fields. One first Loogle query rejected `Ideal.Quotient` as an unknown identifier; I recorded that query as unavailable and ran a valid corrected derivative query. The two depth-pattern searches returned zero. I also ran the corrected `MvPowerSeries, IsSMulRegular` query for the depth statement. The derivative-only hits have no depth, minimal-presentation or hypersurface conclusion. I read the derivative source and the nearby dimension-drop source returned by the semantic search; the latter states Krull-dimension drop, not depth. No one-line specialization proves any new node.

I ran blueprint_refs.py ancestor for the item and whole-blueprint searches for Jacobian, quadratic, cotangent, power series, minimal presentation and nondegenerate. I searched the whole DAG for the tags and for minimal-presentation, cotangent-kernel, polar, quadratic-hypersurface and depth phrases, and opened the related node statements. The formal Jacobian chain rule and invariance nodes are tools for a minimal-presentation proof, not statements of its coordinate elimination/block calculation. Rational-node and separable-node completion theorems require geometric nodal hypotheses and do not compute an arbitrary local ring's degree-two relation kernel. The regular-surface lemma gives a principal equation but says nothing about the residual Jacobian, the embedding dimension, or the quadratic discriminant. The existing model-normalization theorem changes higher terms into quadratic form but does not prove depth or semilinear invariance. These existing nodes are retained or mentioned as ingredients, not duplicated.

## Not duplicates

- lem-trf-formal-minimal-presentation-minors vs def-trf-formal-power-series-partial-derivative: the existing node defines the termwise derivative; it proves none of the new node's coordinate, depth or relation claims .
- lem-trf-formal-minimal-presentation-minors vs lem-trf-formal-jacobian-minor-invariance: the existing lemma only preserves a fixed-size minor ideal under changes of generators and parameters; it neither eliminates variables nor identifies the quadratic cotangent kernel or computes model depth .
- lem-trf-formal-minimal-presentation-minors vs lem-trf-formal-jacobian-coordinate-chain-rule: the existing lemma proves the formal derivative chain rule and invertibility of a coordinate-change Jacobian, rather than the new node's algebraic component .
- lem-trf-formal-minimal-presentation-minors vs lem-trf-formal-jacobian-quadratic-criterion: the existing item states the three-way quadratic-model equivalence; the new node isolates only the indicated algebraic component and asserts no such equivalence .
- lem-trf-formal-minimal-presentation-minors vs lem-trf-nodal-point-local-criterion: the existing lemma characterizes geometric nodes on algebraic curves by a geometric/lci singular-scheme condition; the new node is a formal local algebra component independent of an algebraic curve .
- lem-trf-formal-minimal-presentation-minors vs def-trf-adic-continuous-differentials: the existing node defines an inverse limit of differential modules, rather than proving the new algebraic statement .
- lem-trf-minimal-jacobian-binary-hypersurface vs lem-trf-regular-surface-depth-one-principal: the existing lemma gives a nonzero principal generator in a regular local surface; it does not force two variables from Jacobian minors or show nondegeneracy of its quadratic term .
- lem-trf-minimal-jacobian-binary-hypersurface vs lem-trf-coprime-generators-mprimary-or-unit: the existing statement is Let $(A,\mathfrak n)$ be a regular local ring [def-weil-regular-scheme] of Krull dimension $2$ [def-weil-pbc-krull-dimension-ring]. Let $g_1,\ldots,g_r\in A$ be a finite list such ; it does not state the new component .
- lem-trf-minimal-jacobian-binary-hypersurface vs lem-trf-formal-jacobian-quadratic-criterion: the existing item states the three-way quadratic-model equivalence; the new node isolates only the indicated algebraic component and asserts no such equivalence .
- lem-trf-minimal-jacobian-binary-hypersurface vs lem-trf-nodal-point-local-criterion: the existing lemma characterizes geometric nodes on algebraic curves by a geometric/lci singular-scheme condition; the new node is a formal local algebra component independent of an algebraic curve .
- lem-trf-binary-quadratic-model-depth vs lem-trf-rational-node-quadratic-completion: the existing lemma descends a geometric node to an F-linear completed quadratic normal form; the new node has no geometric-node hypotheses or descent conclusion .
- lem-trf-binary-quadratic-model-depth vs lem-trf-formal-binary-morse: the existing lemma normalizes a series with nondegenerate quadratic term; it neither constructs a minimal quotient nor derives its quadratic term, depth or intrinsic relation space .
- lem-trf-binary-quadratic-model-depth vs lem-trf-formal-jacobian-quadratic-criterion: the existing item states the three-way quadratic-model equivalence; the new node isolates only the indicated algebraic component and asserts no such equivalence .
- lem-trf-binary-quadratic-model-depth vs lem-trf-nodal-point-local-criterion: the existing lemma characterizes geometric nodes on algebraic curves by a geometric/lci singular-scheme condition; the new node is a formal local algebra component independent of an algebraic curve .
- lem-trf-binary-quadratic-model-depth vs lem-sfb-separable-node-quadratic-completion: the existing lemma is about completed local rings of finite-type geometric nodes with separable residue fields; the new node supplies the indicated formal or intrinsic algebra calculation without those hypotheses .
- lem-trf-cotangent-quadratic-relation-invariance vs lem-trf-rational-node-quadratic-completion: the existing lemma descends a geometric node to an F-linear completed quadratic normal form; the new node has no geometric-node hypotheses or descent conclusion .
- lem-trf-cotangent-quadratic-relation-invariance vs lem-trf-formal-binary-morse: the existing lemma normalizes a series with nondegenerate quadratic term; it neither constructs a minimal quotient nor derives its quadratic term, depth or intrinsic relation space .
- lem-trf-cotangent-quadratic-relation-invariance vs lem-trf-formal-jacobian-quadratic-criterion: the existing item states the three-way quadratic-model equivalence; the new node isolates only the indicated algebraic component and asserts no such equivalence .
- lem-trf-cotangent-quadratic-relation-invariance vs lem-sfb-separable-node-quadratic-completion: the existing lemma is about completed local rings of finite-type geometric nodes with separable residue fields; the new node supplies the indicated formal or intrinsic algebra calculation without those hypotheses .

## Original argument retained for the new workers

The following is the ten-step proof from the returned repository item, verbatim (the node statements above are the delivery; these paragraphs are proof material for the future workers). No new node has proof steps.

### Returned step 1

First put the presentation into minimal coordinates, without any assumption (a), (b) or (c). By [lem-weil-pbc-power-series-field-cohen-regular-complete], $T$ is complete Noetherian regular local of dimension $n$. Let $t$ be the dimension of $(I+\mathfrak n^2)/\mathfrak n^2$. Choose $g_1,\ldots,g_t\in I$ whose linear terms are a basis of this space, and extend their linear terms by those of $z_1,\ldots,z_e\in\mathfrak n$ to a basis of $\mathfrak n/\mathfrak n^2$, where $e=n-t$. This space has basis the original variables by coefficient comparison. By [lem-weil-pbc-nakayama-local-generators], this list generates $\mathfrak n$, so it is a regular system of $n$ parameters. By [lem-weil-pbc-power-series-full-coordinates-field] it is a system of $F$-algebra power-series coordinates. Replace each original generator $f_j$ by $h_j=f_j(0,\ldots,0,z_1,\ldots,z_e)$; their differences belong to $(g_1,\ldots,g_t)$ by [lem-weil-pbc-power-series-quotient-variables]. Consequently $I=(g_1,\ldots,g_t,h_1,\ldots,h_s)$ and $R\cong S/H$, where $S=F[[z_1,\ldots,z_e]]$, $\mathfrak p=(z_1,\ldots,z_e)$ and $H=(h_1,\ldots,h_s)\subseteq\mathfrak p^2$. The last inclusion follows because every linear term of an element of $I$ lies in the span of the $g_i$. Thus $\mathfrak m/\mathfrak m^2$ has $F$-basis the classes of the $z_i$ and dimension $e$.

Uses: lem-weil-pbc-power-series-field-cohen-regular-complete, lem-weil-pbc-nakayama-local-generators, lem-weil-pbc-power-series-full-coordinates-field, lem-weil-pbc-power-series-quotient-variables.

### Returned step 2

By [lem-trf-formal-jacobian-minor-invariance], compute $J$ with the coordinates and generators from step 1. The Jacobian is block diagonal with an identity block of size $t$ and the residual matrix $B=(\partial h_j/\partial z_i)$; the off-diagonal blocks are zero because the $h_j$ involve only the $z_i$. If $e=0$ or $e=1$, the identity block supplies an $(n-1)$-minor equal to $1$, so $J=R$. If $e\ge2$, its $(n-1)$-minors are either zero or signed minors of $B$ of size at least $e-1$. Every $(e-1)$-minor occurs by adjoining the whole identity block; larger minor ideals are contained in it by [lem-trf-fitting-ideal-minor-inclusions](1). Hence $J$ is exactly the ideal of $(e-1)$-minors of $B$. Since $H\subseteq\mathfrak p^2$, the entries of $B$ are in $\mathfrak m$, and therefore $J\subseteq\mathfrak m^{e-1}$.

Uses: lem-trf-formal-jacobian-minor-invariance, lem-trf-fitting-ideal-minor-inclusions.

### Returned step 3

Assume (a). The equality $J=\mathfrak m$ rules out $e=0,1$ by step 2, since the maximal ideal is proper. If $e\ge3$, step 2 gives $\mathfrak m\subseteq\mathfrak m^2$, hence $\mathfrak m=\mathfrak m^2$. The maximal ideal is generated by the $e$ variables, so [lem-weil-pbc-nakayama-local-generators], applied to this finite $R$-module, gives $\mathfrak m=0$. Then $R$ is a field and has depth $0$: every element of its maximal ideal is zero, and zero is not a nonzerodivisor on the nonzero module $R$. This contradicts (a). Thus $e=2$.

Uses: lem-weil-pbc-nakayama-local-generators, def-weil-pbc-depth.

### Returned step 4

Write $S=F[[u,v]]$ and $\mathfrak p=(u,v)$ in the presentation of step 1. By [lem-weil-pbc-power-series-field-cohen-regular-complete], $S$ is regular local of dimension $2$. Its quotient $S/H\cong R$ has depth $1$, and $H\subseteq\mathfrak p^2\subseteq\mathfrak p$. Apply [lem-trf-regular-surface-depth-one-principal] to obtain $H=(f)$ with $f\ne0$. Since $f\in H$, it has no constant or linear term. By [lem-trf-formal-jacobian-minor-invariance] replace the residual generators by $f$; the original $J$, as computed in step 2, is now $(\overline{f_u},\overline{f_v})$.

Uses: lem-weil-pbc-power-series-field-cohen-regular-complete, lem-trf-regular-surface-depth-one-principal, lem-trf-formal-jacobian-minor-invariance.

### Returned step 5

Let $Q=au^2+buv+cv^2$ be the degree-two part of $f$. Termwise differentiation gives $f_u\equiv2au+bv$ and $f_v\equiv bu+2cv$ modulo $\mathfrak p^2$. Because $H\subseteq\mathfrak p^2$, the classes of $u,v$ form a basis of $\mathfrak m/\mathfrak m^2$. The equality $J=\mathfrak m$ therefore says that the two displayed linear forms span a two-dimensional space. Their matrix has determinant $4ac-b^2$, which is consequently nonzero. This proves the required discriminant condition in every characteristic.

Uses: none.

### Returned step 6

Apply [lem-trf-formal-binary-morse] to the series $f$ of step 4, whose quadratic part is nondegenerate by step 5. Its continuous $F$-algebra automorphism sends $(f)$ to $(Q)$, so it induces a complete local $F$-algebra isomorphism $R\cong F[[u,v]]/(Q)$. All algebraic isomorphisms here preserve the maximal ideals and their powers, hence the adic topologies. This proves (a) implies (b).

Uses: lem-trf-formal-binary-morse.

### Returned step 7

Forgetting $F$-linearity and continuity in (b) gives the ring isomorphism required by (c).

Uses: none.

### Returned step 8

To prove (c) implies (a), first compute the depth of the model $M=F[[u,v]]/(Q)$ in (c). Put $S_0=F[[u,v]]$. By [lem-weil-pbc-power-series-field-cohen-regular-complete], $S_0$ is a Noetherian local domain of dimension $2$. The regular-parameter theorem [lem-weil-pbc-regular-local-generators-regular-sequence] makes $u,v$ a regular sequence, so its depth is at least $2$. It is at most $2$ by [lem-weil-pbc-depth-le-support-dimension], since the support of $S_0$ as its own module is its entire prime spectrum, of dimension $2$. Thus its depth is exactly $2$. Nondegeneracy implies $Q\ne0$, so multiplication by $Q$ is injective on the domain $S_0$, and $Q\in(u,v)$. By [lem-weil-pbc-depth-drops-by-one], $S_0/(Q)$ has module depth $1$ over $S_0$; [lem-weil-pbc-depth-over-quotient-ring] identifies this with its ring depth. A ring isomorphism preserves maximal ideals and regular sequences, so (c) gives $\operatorname{depth}R=1$.

Uses: lem-weil-pbc-power-series-field-cohen-regular-complete, lem-weil-pbc-regular-local-generators-regular-sequence, lem-weil-pbc-depth-le-support-dimension, lem-weil-pbc-depth-drops-by-one, lem-weil-pbc-depth-over-quotient-ring.

### Returned step 9

The ring isomorphism of (c) induces an isomorphism of residue fields $\sigma:F\to F$ and a $\sigma$-semilinear bijection on cotangent spaces (multiplication by a residue class is defined using any lift, so it commutes with the induced maps). The model has cotangent dimension $2$, since $(Q)\subseteq(u,v)^2$. Thus $e=2$ in step 1. As in step 4, [lem-weil-pbc-power-series-field-cohen-regular-complete] and [lem-trf-regular-surface-depth-one-principal], using the depth just proved, give $H=(f)$ for $f\ne0$ with $f\in\mathfrak p^2$. No coefficient-field compatibility of the given ring isomorphism has been asserted.

Uses: lem-weil-pbc-power-series-field-cohen-regular-complete, lem-trf-regular-surface-depth-one-principal.

### Returned step 10

Use the degree-two multiplication map: a homogeneous binary quadratic in the classes of a cotangent basis maps to its product class in $\mathfrak m^2/\mathfrak m^3$. For the model its kernel is the one-dimensional span of $Q$: modulo $(u,v)^3$, a multiple of $Q$ is just its constant multiplier times $Q$. This kernel and its generator transfer through the ring isomorphism of (c). Under a change of cotangent basis by $P\in\mathrm{GL}_2(F)$, and the residue-field isomorphism $\sigma$, the polar matrix becomes $P^{\mathsf T}\sigma(B)P$, so its determinant becomes $(\det P)^2\sigma(\det B)\ne0$. In the minimal presentation $S/(f)$ of step 9, the degree-two kernel is zero if $f$ has order at least $3$, and otherwise is the span of the degree-two part $f_2$: again compare constant terms of multipliers of $f$ modulo $\mathfrak p^3$. Hence $f_2$ is a nonzero scalar multiple of a nondegenerate quadratic. Its two partial derivatives form a basis modulo $\mathfrak m^2$, by the explicit matrix calculation in step 5. By [lem-weil-pbc-nakayama-local-generators] they generate $\mathfrak m$. Finally [lem-trf-formal-jacobian-minor-invariance] and the block computation of step 2 identify their generated ideal with the original $J$. Thus $J=\mathfrak m$; together with step 8 this is (a), completing the three-way equivalence.

Uses: lem-weil-pbc-nakayama-local-generators, lem-trf-formal-jacobian-minor-invariance.

## What remains

The four new nodes are intentionally unsplit and await independent workers. The item itself has no unfinished assembly argument. No mathematical statement error was found. The dry run and delivery result are recorded by the delivery command; no local checker or compiler was run.

## Dry-run correction

The first dry run rejected the binary polar matrix row separator immediately followed by b as doubled command escaping. I inserted a space between the TeX row break and the next b entry and updated both verbatim citation quotes. This changes no formula or mathematical assertion.
