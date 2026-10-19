# Q44 repair report

## Files written

- dag/nodes/sec-trace-formula/lem-trf-algebraic-relative-dualizing-isomorphism.json: repaired statement split, unchanged target statement; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-polynomial-diagonal-rhom-reduction.json: statement-only natural comparison for arbitrary relatively perfect T; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-semidualizing-rhom-conservative.json: statement-only detection theorem for arbitrary semidualizing objects over Noetherian rings; no Mathlib match.
- citations.json: exact statement excerpts for every proof-step citation.

## Attachments

None. Searches of the project Lean source for the blueprint tag, relative-dualizing terminology and proposed new notions found no closed project declaration stating this item or either prerequisite. Upstream sorry declarations are not attachments. No Lean was written or compiled.

## WANTED

None. The proof below is agent-written using the Stacks source already present. The source fields of the new nodes explicitly distinguish derived corollaries from verbatim source statements.

## Returned defects and corrections

The returned head relied on the finite-projective chain statement lem-pc-perfect-ring-hom-tensor-dual-iso for a derived assertion it does not state. It also omitted comparison of representatives with RHom, case-(3) evaluation hypotheses, the p2 symmetry, final restriction identifications, and the definition check for R-perfectness. The first unpushed repair attempted to add six nodes, but still asserted a false change of base ring for Tor bounds. Those six unpushed drafts are superseded, rather than delivered as unnecessary or false prerequisites. Their search records are retained in searches.jsonl; the preceding report is retained locally as report-before-polynomial-repair.md and is explicitly superseded by this report.

Concrete failing inference: let R=k be a field, A=k[e]/(e^2), and T=k=A/(e). Then T is pseudo-coherent over the Noetherian ring A and is R-flat. But for B=A tensor_k A, its induced object along either coprojection has infinite Tor dimension over B: tensoring its periodic free resolution with the residue field of B leaves a zero-differential complex with nonzero terms in every negative degree. Thus R-perfectness alone cannot check the required finite lower B-Tor bound of Tag 0ATK(3). This is an error in the previously written route, not an excuse to assume A is regular or weaken the target. The displayed use of case (3) in the source's brief uniqueness proof needs a relative comparison beyond the chain lemma; this repair supplies a different explicit polynomial comparison. The nearest blueprint ancestry and unit are retained; only this invalid affine uniqueness calculation is replaced. No geometric step of the unit is changed.

The target is true and unchanged; there is no STATEMENT-DISPUTED target. Definition 0DHS literally defines R-perfect as pseudo-coherent over A plus finite Tor dimension over R. This is exactly the expanded item hypothesis (the interval is uniform over every R-module); Definition 0E2C then adds the diagonal RHom condition. There is no extra choice of generator in either statement.

## Derivation supporting the polynomial comparison node

Read more-algebra.tex Tags 068X, 07VI, 0A65, 0A6A and 0DHS, and dualizing.tex Tag 0BZW. This is a general functor comparison, with no assumption that a diagonal Hom is A, and is not a restatement of the item. Here is its derivation for a future splitter; it is intentionally a statement-only prerequisite in this delivery.

Fix P=R[x_1,...,x_n] onto A and Q=P tensor_R A=A[x_1,...,x_n]. P is Noetherian. The bounded finite A-cohomology of T is finite over P, so T is pseudo-coherent over P. The fibers of R to P have global dimension n; Tag 068X makes both A and T perfect over P (A has R-Tor amplitude [0,0]). Let D=RHom_P(T,P), with its A-action by precomposition. Perfect biduality identifies T with RHom_P(D,P), respecting A-actions. Put J=D tensor_R^L A; since A is R-flat this is scalar extension and J is a B-module as well as a Q-module. The perfect scalar-extension comparison gives

T tensor_R^L A = RHom_Q(J,Q).

The B-action on the Hom object is precomposition by the B-action on J. Tensor-Hom adjunction with that bimodule action gives

RHom_B(A,RHom_Q(J,Q)) = RHom_Q(A tensor_B^L J,Q) = RHom_Q(D,Q).

The second equality is extension-of-scalars associativity: J is extension of D along the first coprojection, and multiplication composed with that coprojection is the identity. This is a derived equality; no Tor-independence of the multiplication module is assumed. Q acts on D through x_i mapping to its image a_i in A. The kernel of Q to A is the regular sequence x_i-a_i. Its finite Koszul resolution identifies RHom_Q(A,Q) with A[-n]. Coinduction adjunction therefore identifies the last Hom with RHom_A(D,A)[-n], including its residual A-action along p1.

On the other side C=RHom_P(A,P)[n] is P-perfect. Tensor-Hom adjunction and P-biduality give

RHom_A(C,T) = RHom_P(C tensor_A^L D,P)
             = RHom_A(D,RHom_P(C,P))
             = RHom_A(D,A[-n]).

These constructions are natural in T. They give the asserted comparison in D(A), not merely an equality of cohomology groups. All underived models are used only after choosing finite-projective P-models or the finite Koszul Q-model; general tensor and Hom are derived. In particular this argument never claims that T or its induced B-module is B-perfect. The polynomial presentation can have redundant generators; adding a variable shifts the Koszul and C formulas together, preserving the comparison.

## Derivation supporting the semidualizing detection node

Read dualizing.tex Tag 0BFR (complete Noetherian local rings have dualizing complexes) and Tag 0A7C (biduality on the whole coherent derived category, not only bounded coherent objects), and more-algebra.tex Tag 0A6A(3) and the discussion of derived Nakayama. This node is a generic detection assertion; it does not mention a relative algebra, a tensor-square diagonal or a relative dualizing condition.

Suppose RHom_A(C,Z)=0. If Z were nonzero, localize at a maximal ideal in its cohomological support and complete. Flat base change of RHom is applicable because C is pseudo-coherent and Z is bounded below. It also preserves the scalar homothety condition, and faithful flatness preserves nonzero finite cohomology. We reduce to a complete Noetherian local ring S with nonzero C and Z and RHom_S(C,Z)=0. Choose a dualizing complex omega by 0BFR. The dual D(Z)=RHom_S(Z,omega) is bounded coherent and nonzero by 0A7C. Derived Nakayama, or the top-cohomology Nakayama argument, shows that both C tensor_S^L k and D(Z) tensor_S^L k are nonzero bounded-above complexes. Their tensor over the residue field k is nonzero, since complexes of vector spaces split into their cohomology. Hence C tensor_S^L D(Z) is nonzero. It is bounded above with finite cohomology in each degree (use bounded-above finite-free resolutions), although it need not be bounded below.

Tensor-Hom adjunction and biduality identify its omega-dual with RHom_S(C,Z), which is zero. Tag 0A7C applies also to this possibly unbounded-below coherent complex and its square is the identity, a contradiction. Thus Z=0. Applying this to the cone of f gives the isomorphism-detection clause, since derived Hom is exact and cones of bounded finite complexes remain bounded finite. The scalar homothety is used to ensure C remains nonzero at every nonzero local ring, including after completion; it is not a claim that C is a perfect generator.

## Review by Q44

I compared the retained sandbox statement with the current read-only repository: it is unchanged, while the current main still has this item unsplit. I restored the exact main-branch blueprint ancestor chain rather than the shortened chain in the failed draft. I read the source of the item (0E2D and 0E2C), the exact R-perfect definition (0DHS), and the sources of the two new general prerequisites listed above. I searched the DAG, the full current blueprint and the Lean source before creating either new id. The Mathlib searches use this item's search log, and their recorded queries, hit names, digests and availability come from that log; the group-cohomology hits, ordinary finite-presentation theorems and categorical conservative-functor definitions do not assert either prerequisite. The original search records are retained, not replaced with unrun searches.

Step 1 uses the exact existing Noetherian pseudo-coherence criterion: it really supplies finite cohomology, while boundedness follows directly by testing the stated Tor interval on Q=R. I verified that the interval is uniform for all R-modules and that nothing translates it into finite Tor dimension over B. The source definition itself, not an existence theorem about representatives, gives the equivalence with R-perfect.

Step 2 uses the existing lem-trf-algebraic-shriek-relative-perfect statement. It explicitly supplies bounded finite cohomology and the scalar-action isomorphism for C, not just an abstract object isomorphism. Flat finite presentation gives finite type, and the Noetherian hypotheses are those of the item. A polynomial presentation exists by the given finite-presentation definition. No assertion of uniqueness is taken from this node and there is no dependency cycle through the parent rigidity item.

Step 3 uses exactly the formula in the new polynomial-diagonal reduction node, which is natural in an arbitrary relatively perfect T and is in D(A). I checked the orientation of p1 and the residual A-action in the bimodule/Koszul derivation. Restricting the supplied D(B) isomorphism along p1 is an ordinary functor operation, and its target is A because multiplication after p1 is identity. There is no p2 assumption left to justify. Restriction along multiplication was the wrong functor direction in the old draft and is not used.

Step 4 uses the right-adjoint internal-Hom statement of the existing projective Hom/evaluation model; its statement explicitly describes the tensor-Hom adjunction. C has a bounded-above projective model by the pseudo-coherence supplied in Step 2, so its stated hypothesis holds. The scalar map is the adjunct of identity, and naturality gives RHom(C,f_T)h=g_T. This proves that the actual morphism induced by f_T is an isomorphism, rather than inferring an arbitrary morphism from two isomorphic Hom objects. No finite-projective chain evaluation theorem is being promoted to a derived isomorphism.

Step 5 applies the new detection statement precisely to C and f_T: all boundedness, finite generation, homothety and Hom-isomorphism hypotheses were checked in Steps 1, 2 and 4. The last composition is elementary. These cited statements were opened and their relevant clauses copied verbatim to citations.json; no definition-only citation is used for a non-elementary theorem. The two off-unit tools are declared in split_report.tool_uses, and do not replace a geometric unit step.

Small cases checked: R=A and the zero ring; polynomial A over R, where C=A[n] and both sides of the reduction are T[-n]; finite flat algebras over a field, where C is the ordinary R-linear dual and the reduction is the derived coinduction adjunction; shifts T[r] (the formulas shift covariantly); and singular A, where the proof does not assume B-perfectness. If a nonzero ring had T=0, its required diagonal Hom could not be A; at the zero ring all objects and conclusions are zero. Arbitrary choices of the isomorphisms g_T are allowed, and the final result asserts no normalization. Every item proof step is shorter than 2000 characters; neither of the new non-elementary lemmas is hidden in a long step or split recursively. The auxiliary derivations above explain their correctness but their JSON proof lists remain empty as required.

## What remains unfinished

No part of the item's proof is left unstated. The two new general lemmas are deliberately unsplit stage-1 prerequisites. No Mathlib leaf or attachment is claimed.

## Not duplicates

lem-trf-polynomial-diagonal-rhom-reduction vs lem-weil-coefficient-frobenius: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Coefficient biduality at finite and integral stages. It does not state this functor comparison. Shared source tags: 07VI.

lem-trf-polynomial-diagonal-rhom-reduction vs def-sf-coefficient-duality: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Coefficient duality and bounded finite-cohomology complexes. It does not state this functor comparison. Shared source tags: 07VI.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-sf-finite-projective-dual: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Ordinary duals of finite projective modules. It does not state this functor comparison. Shared source tags: 07VI.

lem-trf-polynomial-diagonal-rhom-reduction vs sk-thm-sf-identification: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is The derived Poincaré pairing is the duality isomorphism. It does not state this functor comparison. Shared source tags: 07VI.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-trf-relative-duality-polynomial-chart: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is General polynomial-chart model and refinement comparison for coherent relative duality. It does not state this functor comparison. Shared source tags: 0BZW.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-trf-algebraic-shriek-relative-perfect: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Relative perfection of algebraic upper shriek for flat Noetherian algebras. It does not state this functor comparison. Shared source tags: 07VI, 0BZW.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-trf-algebraic-shriek-calculus: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Algebraic upper shriek: polynomial models, coinduction, composition and flat base change. It does not state this functor comparison. Shared source tags: 0A6A.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-trf-flat-polynomial-quotient-perfect: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Perfectness of a flat finite-type polynomial quotient. It does not state this functor comparison. Shared source tags: 0BZW.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-trf-pseudocoherent-rhom-flat-base-change: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Flat scalar extension of derived Hom from a pseudo-coherent complex. It does not state this functor comparison. Shared source tags: 0A6A.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-trf-relative-dualizing-pair-rigidity: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Rigidity of already given coherent relative dualizing pairs. It does not state this functor comparison. Shared source tags: 0BZW.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-trf-perfect-complex-derived-biduality: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Derived duality for perfect complexes. It does not state this functor comparison. Shared source tags: 07VI.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-trf-algebraic-shriek-derived-hom-adjunction: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Derived coinduction adjunction and scalar evaluation comparison. It does not state this functor comparison. Shared source tags: 0BZW.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-pc-perfect-ring-hom-tensor-differential: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Signed tensor-dual evaluation commutes with differentials. It does not state this functor comparison. Shared source tags: 0A6A.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-pc-ring-extension-finite-support-product: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Scalar extension of a finite-support limiting product. It does not state this functor comparison. Shared source tags: 0A6A.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-pc-perfect-ring-hom-tensor-dual-iso: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Finite-projective Hom is tensor with the explicit dual. It does not state this functor comparison. Shared source tags: 0A6A.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-pc-ring-hom-extension-transport: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Transport an ordinary normalized Hom comparison to the one-point ring site. It does not state this functor comparison. Shared source tags: 0A6A.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-pc-affine-polynomial-localized-tor-of-stalkwise: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Affine localized Tor bound from the supported stalk. It does not state this functor comparison. Shared source tags: 068X.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-sc-proper-flat-image-global-hom-base-change-isIso: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Affine global Hom scalar extension out of a proper flat perfect direct image. It does not state this functor comparison. Shared source tags: 0A6A.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-pc-finite-projective-ring-hom-extension: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Normalized tensor-Hom isomorphism for one finite projective module. It does not state this functor comparison. Shared source tags: 0A6A.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-pc-affine-polynomial-localized-finite-projective-dimension: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Pointwise finite projective dimension of an affine polynomial presentation. It does not state this functor comparison. Shared source tags: 068X.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-pc-localized-polynomial-tor-bound: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Transfer of a Tor bound from the base to a localized polynomial ring. It does not state this functor comparison. Shared source tags: 068X.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-pc-ring-extension-internal-hom-ext: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Pure tensors detect maps to internal Hom. It does not state this functor comparison. Shared source tags: 0A6A.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-pc-perfect-ring-hom-tensor-degree-map: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Existence of the normalized degreewise evaluation map. It does not state this functor comparison. Shared source tags: 0A6A.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-sc-finite-pushforward-derived-hom-qcoherent: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Finite pushforward algebra gives quasi-coherent derived Hom. It does not state this functor comparison. Shared source tags: 0A6A.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-pc-ring-projective-internal-hom-exact: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Projective internal Hom is exact on the one-object ring site. It does not state this functor comparison. Shared source tags: 0A6A.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-pc-perfect-ring-hom-tensor-precomposition: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Signed tensor-dual evaluation: precomposition term. It does not state this functor comparison. Shared source tags: 0A6A.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-pc-perfect-ring-hom-kflat: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is K-flatness of Hom from a bounded finite-projective ring complex. It does not state this functor comparison. Shared source tags: 0A6A.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-pc-perfect-ring-dual-term-flat: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Flat terms of the explicit finite-projective ring dual. It does not state this functor comparison. Shared source tags: 0A6A.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-pc-perfect-ring-hom-tensor-degree-isiso: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Invertibility of normalized finite-projective degreewise evaluation. It does not state this functor comparison. Shared source tags: 0A6A.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-pc-perfect-ring-hom-scalar-extension: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Finite-projective Hom-complex scalar extension. It does not state this functor comparison. Shared source tags: 0A6A.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-pc-perfect-ring-hom-tensor-postcomposition: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Signed tensor-dual evaluation: postcomposition term. It does not state this functor comparison. Shared source tags: 0A6A.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-pc-affine-sections-finite-tor-of-stalkwise: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Affine coordinate rings have finite Tor dimension from stalkwise finite Tor dimension. It does not state this functor comparison. Shared source tags: 068X.

lem-trf-polynomial-diagonal-rhom-reduction vs def-pc-perfect-rhom-base-change-map: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Canonical RHom scalar-extension map on perfect representatives. It does not state this functor comparison. Shared source tags: 0A6A.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-pc-perfect-ring-hom-tensor-degrees: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Signed tensor-dual evaluation is invertible in each degree. It does not state this functor comparison. Shared source tags: 0A6A.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-pc-perfect-ring-hom-tensor-degree-condition: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Signed evaluation degree interfaces. It does not state this functor comparison. Shared source tags: 0A6A.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-pc-base-change-rhom-perfect: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is RHom base change for a perfect complex. It does not state this functor comparison. Shared source tags: 0A6A.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-pc-bounded-ring-hom-extension-degree: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Finite-support assembly of degreewise tensor-Hom comparisons. It does not state this functor comparison. Shared source tags: 0A6A.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-pc-ring-bounded-projective-extension: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is K-flatness and scalar-extension projectivity for bounded ring complexes. It does not state this functor comparison. Shared source tags: 0A6A.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-pc-affine-polynomial-resolution-of-stalkwise: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Polynomial affine resolution from stalkwise finite Tor dimension. It does not state this functor comparison. Shared source tags: 068X.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-pc-localized-polynomial-finite-projective-dimension: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Finite Tor over the base gives finite projective dimension over a localized polynomial ring. It does not state this functor comparison. Shared source tags: 068X.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-sfb-internal-hom-dual-constructible-models: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Constructible models for duals of locally constant perfect complexes. It does not state this functor comparison. Shared source tags: 07VI.

lem-trf-polynomial-diagonal-rhom-reduction vs lem-weil-point-fibre-equivalence: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is The fibre functor at the geometric point is an equivalence. It does not state this functor comparison. Shared source tags: 0A6A.

lem-trf-polynomial-diagonal-rhom-reduction vs prop-pod-biduality-at-the-point: the new statement is a natural comparison between tensor-square diagonal derived Hom and RHom from the polynomial dualizing object for arbitrary relatively perfect T; the existing statement is Biduality at the point. It does not state this functor comparison. Shared source tags: 07VI, 0A6A.

lem-trf-semidualizing-rhom-conservative vs lem-trf-algebraic-shriek-calculus: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is Algebraic upper shriek: polynomial models, coinduction, composition and flat base change. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

lem-trf-semidualizing-rhom-conservative vs lem-trf-pseudocoherent-rhom-flat-base-change: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is Flat scalar extension of derived Hom from a pseudo-coherent complex. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

lem-trf-semidualizing-rhom-conservative vs lem-pc-perfect-ring-hom-tensor-differential: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is Signed tensor-dual evaluation commutes with differentials. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

lem-trf-semidualizing-rhom-conservative vs lem-pc-ring-extension-finite-support-product: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is Scalar extension of a finite-support limiting product. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

lem-trf-semidualizing-rhom-conservative vs lem-pc-perfect-ring-hom-tensor-dual-iso: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is Finite-projective Hom is tensor with the explicit dual. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

lem-trf-semidualizing-rhom-conservative vs lem-pc-ring-hom-extension-transport: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is Transport an ordinary normalized Hom comparison to the one-point ring site. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

lem-trf-semidualizing-rhom-conservative vs lem-sc-proper-flat-image-global-hom-base-change-isIso: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is Affine global Hom scalar extension out of a proper flat perfect direct image. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

lem-trf-semidualizing-rhom-conservative vs lem-pc-finite-projective-ring-hom-extension: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is Normalized tensor-Hom isomorphism for one finite projective module. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

lem-trf-semidualizing-rhom-conservative vs lem-pc-ring-extension-internal-hom-ext: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is Pure tensors detect maps to internal Hom. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

lem-trf-semidualizing-rhom-conservative vs lem-pc-perfect-ring-hom-tensor-degree-map: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is Existence of the normalized degreewise evaluation map. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

lem-trf-semidualizing-rhom-conservative vs lem-sc-finite-pushforward-derived-hom-qcoherent: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is Finite pushforward algebra gives quasi-coherent derived Hom. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

lem-trf-semidualizing-rhom-conservative vs lem-pc-ring-projective-internal-hom-exact: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is Projective internal Hom is exact on the one-object ring site. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

lem-trf-semidualizing-rhom-conservative vs lem-pc-perfect-ring-hom-tensor-precomposition: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is Signed tensor-dual evaluation: precomposition term. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

lem-trf-semidualizing-rhom-conservative vs lem-pc-perfect-ring-hom-kflat: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is K-flatness of Hom from a bounded finite-projective ring complex. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

lem-trf-semidualizing-rhom-conservative vs lem-pc-perfect-ring-dual-term-flat: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is Flat terms of the explicit finite-projective ring dual. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

lem-trf-semidualizing-rhom-conservative vs lem-pc-perfect-ring-hom-tensor-degree-isiso: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is Invertibility of normalized finite-projective degreewise evaluation. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

lem-trf-semidualizing-rhom-conservative vs lem-pc-perfect-ring-hom-scalar-extension: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is Finite-projective Hom-complex scalar extension. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

lem-trf-semidualizing-rhom-conservative vs lem-pc-perfect-ring-hom-tensor-postcomposition: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is Signed tensor-dual evaluation: postcomposition term. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

lem-trf-semidualizing-rhom-conservative vs def-pc-perfect-rhom-base-change-map: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is Canonical RHom scalar-extension map on perfect representatives. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

lem-trf-semidualizing-rhom-conservative vs lem-pc-perfect-ring-hom-tensor-degrees: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is Signed tensor-dual evaluation is invertible in each degree. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

lem-trf-semidualizing-rhom-conservative vs lem-pc-perfect-ring-hom-tensor-degree-condition: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is Signed evaluation degree interfaces. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

lem-trf-semidualizing-rhom-conservative vs lem-pc-base-change-rhom-perfect: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is RHom base change for a perfect complex. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

lem-trf-semidualizing-rhom-conservative vs lem-pc-bounded-ring-hom-extension-degree: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is Finite-support assembly of degreewise tensor-Hom comparisons. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

lem-trf-semidualizing-rhom-conservative vs lem-pc-ring-bounded-projective-extension: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is K-flatness and scalar-extension projectivity for bounded ring complexes. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

lem-trf-semidualizing-rhom-conservative vs lem-weil-point-fibre-equivalence: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is The fibre functor at the geometric point is an equivalence. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

lem-trf-semidualizing-rhom-conservative vs prop-pod-biduality-at-the-point: the new statement detects all bounded coherent isomorphisms from the scalar homothety of an arbitrary C; the existing statement is Biduality at the point. It does not assert this semidualizing detection theorem. Shared source tags: 0A6A.

